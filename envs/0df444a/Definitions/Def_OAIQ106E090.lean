-- Prove2me | Definitions.Def_OAIQ106E090
-- name    : OAIQ106E090
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:00:14.362194+00:00
-- url     : https://prove2.me/theorems/9e2eaf55-b5be-423a-8864-124618e41b59
-- title:
--   Definitions bundle OAIQ106E090 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7401 declarations of OpenAI's Lean: 7401 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw13620step0`, `OAI.MUB6.Certificate.MixedSemantics.raw13620step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13620step1`, `OAI.MUB6.Certificate.MixedSemantics.raw13620step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13620step2`, `OAI.MUB6.Certificate.MixedSemantics.raw13620step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13621`, `OAI.MUB6.Certificate.MixedSemantics.raw13621Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13621step0`, `OAI.MUB6.Certificate.MixedSemantics.raw13621step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13621step1`, `OAI.MUB6.Certificate.MixedSemantics.raw13621step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13621step2`, `OAI.MUB6.Certificate.MixedSemantics.raw13621step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13622`, `OAI.MUB6.Certificate.MixedSemantics.raw13622Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13622step0`, `OAI.MUB6.Certificate.MixedSemantics.raw13622step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13622step1`, `OAI.MUB6.Certificate.MixedSemantics.raw13622step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13622step2`, `OAI.MUB6.Certificate.MixedSemantics.raw13622step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13622step3`, `OAI.MUB6.Certificate.MixedSemantics.raw13622step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13623`, `OAI.MUB6.Certificate.MixedSemantics.raw13623Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13623step0`, `OAI.MUB6.Certificate.MixedSemantics.raw13623step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13623step1`, `OAI.MUB6.Certificate.MixedSemantics.raw13623step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13624`, `OAI.MUB6.Certificate.MixedSemantics.raw13624Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13624step0`, `OAI.MUB6.Certificate.MixedSemantics.raw13624step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13624step1`, `OAI.MUB6.Certificate.MixedSemantics.raw13624step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13624step2`, `OAI.MUB6.Certificate.MixedSemantics.raw13624step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw13625`, `OAI.MUB6.Certificate.MixedSemantics.raw13625Labels` and 7361 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical10`, `MutuallyUnbiased_MixedSemantics_Canonical106`, `MutuallyUnbiased_MixedSemantics_Canonical107`, `MutuallyUnbiased_MixedSemantics_Canonical108`, `MutuallyUnbiased_MixedSemantics_Canonical109`, `MutuallyUnbiased_MixedSemantics_Canonical11`, `MutuallyUnbiased_MixedSemantics_Canonical110`, `MutuallyUnbiased_MixedSemantics_Canonical111`, `MutuallyUnbiased_MixedSemantics_Canonical112`, `MutuallyUnbiased_MixedSemantics_Canonical113`, `MutuallyUnbiased_MixedSemantics_Canonical114`, `MutuallyUnbiased_MixedSemantics_Canonical115`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound48_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36_e`.
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

def raw13Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw13step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw13step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw14 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]

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

def raw136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw136step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw137 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw137Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw137step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw137step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw138 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw138step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw138step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw139 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw139Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw139step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw139step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw140 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw140step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw140step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw141 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw141Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw141step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw141step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw142 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw142step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw142step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw143 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw143Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw143step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw143step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw146 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 2, -3]]
def raw146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw146step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw147 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 2, -3]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1362step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1362step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1363 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1364 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1364Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1364step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1364step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1365 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1365step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1365step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1366 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1367 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1367Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1367step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1368 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1368step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1368step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1369 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1370 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1370Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1370step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1371 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1371step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1371step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1372 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1373 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1373Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1373step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1373step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1374 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1374step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1375 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1376 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1376Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1376step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1376step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1377 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1377step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1378 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1379 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1379Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1379step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1379step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1379step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1380 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1380step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1381 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1382 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1382Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1382step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1382step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1383 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1383step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1384 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1385 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1385Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1385step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1385step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1386 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1386step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1387 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1388 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1388Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1388step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1388step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1389 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 4, -2]]
def raw1389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1389step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw1389step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw1389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1390 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 4, -2]]
def raw1390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1390step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw1390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1391 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 4, -2]]
def raw1391Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1391step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1391step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1392 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw1392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1392step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw1392step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw1392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1393 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw1393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1393step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw1393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1394 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw1394Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1394step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw1394step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw1394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1395 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1395step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1395step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1396 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1396step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1397 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1397Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1397step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw1397step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1397step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1398 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1398step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1398step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1399 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1399step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1400 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1400Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1400step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw1400step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1401 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1401step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1402 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1403 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1403Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1403step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1404 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1404step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1405 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1406 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1406Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1406step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1407 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw1407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1407step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw1407step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw1407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13620step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13621 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13621step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13622 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13622step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13622step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13623 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13623step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13624 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13624step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13625 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13625step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13626 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw13626step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw13626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13627 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13627step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13627step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13627step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13628 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13628step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13629 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13629step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13630 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13630step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13630step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13630step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13631step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13631step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13631step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13632 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13632step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13633 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13633step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13633step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13634 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13634step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13635step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13635step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13635step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13636step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13636step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13637step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13637step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13638 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13638step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13639 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13639step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13640 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13640step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13640step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13640step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13640step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13641step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13641step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13642 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13642step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13643 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13644 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13645 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13646 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13647 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13649 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13650 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13651 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw13652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13659step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13659step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13662 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13664 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13669 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13669step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13670 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13671 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13673step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13673step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13673step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13675step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13675step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13675step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13676step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13676step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13676step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13677step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13677step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13677step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13682step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13683step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw13692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw13697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13698step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw13702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13720step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw13722step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw13727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw13732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13734step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13735step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13738step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13738step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13739step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13740step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13741step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13743step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13744step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13745step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13748step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw13749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13749step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13750step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13750step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13750step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13751step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13751step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw13752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13753step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13753step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw13754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13754step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13755step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13755step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13755step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13756step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13756step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw13757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13757step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13757step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13757step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw13758step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13758step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13758step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13759step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13759step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13760step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13761step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13761step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw13762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13762step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13762step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13769 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]
def raw13769Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13769step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw13769step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13769step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw13769step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13776step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13779step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13780step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13781step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13782step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13782step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13783step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13783step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13784step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13785step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13786step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13787step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13787step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13788step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13789step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13790step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13791step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13792step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw13793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13794step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13795step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13796step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw13798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13798step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13798step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw13799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13799step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13800step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13802step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13802step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13803step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13803step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw13804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13804step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13804step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13808step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13817step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13818step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw13823step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw13828step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw13829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw13834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13835 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13835step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13835step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13836 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13836step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13837 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13837step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13838 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13838step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13839 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13839step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13839step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13839step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13840step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13840step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13840step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13841 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13841step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13842step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13842step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13843step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13844 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13844step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13844step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13845step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13846step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13847step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13848 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13848step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13848step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13848step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13849 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13849step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13850 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13850step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13851 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13851step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13852 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13852step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13852step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13852step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13853 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13853step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13853step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13854 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13854step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13855 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13855step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13856step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13857 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13857step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13858 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13859 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13860 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13861 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13862 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13863 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13864 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13865 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13865step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13866 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13867 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13868 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13869 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13870 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13871 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13871step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13873 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw13873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13874 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13875 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13875step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13876 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13877 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13878 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13881step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13881step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13881step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13882step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13882step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13882step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13882step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13883step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13883step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13883step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13883step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13883step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13899step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw13902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13904step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13904step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13904step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13907step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw13907step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13907step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw13907step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw13909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw13910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13911step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13912step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw13912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13913step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13914step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13918step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13921step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13924step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13924step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13925step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw13926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13927step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13927step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13927step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw13927step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13928step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13928step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13928step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13928step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13929step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13929step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13929step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13932step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw13932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13937step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw13937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13938step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw13938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13940step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13940step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13940step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13941step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13941step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13941step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13941step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13941step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13941step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13942step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13942step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13942step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13942step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13942step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13943step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13943step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13943step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13943step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13943step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13944step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13944step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13944step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13945step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13945step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13946step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13946step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13947step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13947step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13948step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13948step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13949step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13949step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13949step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13951step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13951step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13951step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13951step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13953step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13953step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13953step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13954step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13954step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw13954step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13954step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13954step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13954step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13954step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw13955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13955step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13955step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13955step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw13956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw13956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw13957step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw13957step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13957step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13957step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13957step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13957step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw13958step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw13958step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13958step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13958step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13958step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13958step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13959step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13959step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13959step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13959step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13959step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13959step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13959step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13960step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13961step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw13962step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13962step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13962step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13962step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13962step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13963step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw13963step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw13963step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13963step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13963step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13963step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13964step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13964step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw13964step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13964step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw13964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13965step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw13965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw13965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13966step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw13966step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw13966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13967step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw13967step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw13967step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13967step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw13967step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13968step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw13968step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw13968step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13968step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw13968step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13969step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13970step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13970step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13971step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw13971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13972step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13972step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13972step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13972step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13973step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13974step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13975step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13975step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13976step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13976step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13977step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13978step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13979step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13979step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13980step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13981step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13982step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13983step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13983step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw13984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13984step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw13984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13984step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, 1, -2]]
def raw13984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13984step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw13984step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13984step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw13984step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw13985step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13985step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw13985step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13986step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13986step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13986step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13987step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13987step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13988step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw13989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw13989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw13989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw13989step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13989step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw13989step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13990step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13990step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13993step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13993step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw13993step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13993step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw13993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13994step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw13997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw13997step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw13998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw14001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14001step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14001step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw14002Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw14002step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14003Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14003step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14003step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw14003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14004Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14004step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw14004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14005step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw14005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw14006Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14006step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14006step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14006step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14006step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14006step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw14006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw14007Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw14007step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw14007step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw14007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14008Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14008step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14008step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14009Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14009step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw14010step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw14011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw14011step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw14011step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw14011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14012Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14012step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14012step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14013 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14013step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14013step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14014 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14014step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14014step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14015 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14015step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14015step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14016 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14016step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14016step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14017 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14017step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14017step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14017step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14018step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14018step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14019step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw14020step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw14020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14021 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw14021step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14021step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw14021step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14021step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw14021step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14022 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14022step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14023 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14023step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14024 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14024step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14024step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14024step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14024step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14025 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14025step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw14025step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14025step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw14025step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14026 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw14026step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14026step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw14026step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14026step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw14026step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14027 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14027step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14028 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14028step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14029 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw14029step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw14029step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14030 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14030step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14030step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14030step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14030step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14030step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14030step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14031 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14031step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14032step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14032step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14032step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14033 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14033step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14034 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14034step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14035 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14035step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14035step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14036 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14036step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14036step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw14036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14037step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14039step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14040step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw14040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14041 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14041step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14041step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw14041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14042 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw14042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw14043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw14043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14044 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14044step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14044step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14044step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw14044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14045step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw14045step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14045step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw14045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14046 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14046step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14046step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw14048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14049step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw14049step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw14049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14050 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14050step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14052step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14055step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]
def raw14055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14055step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw14055step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw14055step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw14055step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14056step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14060step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14068step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw14068step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14068step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw14068step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw14072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14072step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw14072step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14073step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14073step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14074step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14074step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14074step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14074step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14075step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14076step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14076step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14076step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14077step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14077step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14077step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14077step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14077step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1408 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw1408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1408step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw1408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1409 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw1409Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1409step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def raw1409step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def raw1409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1410 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw1410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1410step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw1410step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw1410step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1411 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw1411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1411step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw1411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1412 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw1412Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1412step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw1412step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1412step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1413 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1413step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1413step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1415Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1415step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1415step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1415step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1416 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1416step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1417 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1418 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1418Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw1418step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw1418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1419 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1419step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1420 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1421 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1421Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw1421step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1421step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1422 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1422step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1423 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1424 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1424Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1424step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1424step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1425 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1425step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1426 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1427 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1427Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1427step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1427step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1428 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw1428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1428step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw1428step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw1428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1429 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw1429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1429step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw1429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1430 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw1430Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1430step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw1430step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw1430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1431 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1431step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1432 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1433 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1433Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1433step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1433step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1433step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1433step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1434 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw1434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1434step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1434step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1435 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw1435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1435step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1436 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw1436Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1436step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1436step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1436step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1436step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1437 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw1437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1437step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1437step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1438 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw1438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1438step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1439 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw1439Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1439step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1439step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1440 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1440step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1441 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1442 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1442Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1443 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1443step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1443step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1444 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1444step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1445 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1445Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1445step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1445step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1446 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 3, -3]]
def raw1446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1446step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw1446step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1446step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw1446step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1447 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 3, -3]]
def raw1447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1447step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw1447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1448 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 3, -3]]
def raw1448Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1448step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw1448step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1448step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw1448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1449 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1449step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1449step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1450 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1451 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1451Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1451step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1452 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1452step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1452step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1453 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1453step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1454 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1454Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1454step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw1454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw1454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw1454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1455 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1455step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1455step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1455step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1456 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1456step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1457 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1457Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1457step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1457step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1457step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1458 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 3, -2]]
def raw1458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1458step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw1458step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1458step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw1458step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1459 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 3, -2]]
def raw1459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1459step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw1459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1460 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 3, -2]]
def raw1460Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1460step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw1460step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1460step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw1460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1460step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw1460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1461 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 2, 0], ![0, 2, -2]]
def raw1461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1461step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw1461step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1461step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw1461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1462 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 2, 0], ![0, 2, -2]]
def raw1462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1462step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw1462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1463 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 2, 0], ![0, 2, -2]]
def raw1463Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1463step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw1463step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1463step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw1463step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1463step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw1463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1464 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1464step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw1464step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1464step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw1464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1465 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1465step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw1465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1466 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1466Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1466step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw1466step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1466step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]
def raw1466step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1466step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]
def raw1466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1467 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 4, -2]]
def raw1467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1467step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw1467step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1467step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw1467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1468 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 4, -2]]
def raw1468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1468step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw1468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1469 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 4, -2]]
def raw1469Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1469step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def raw1469step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1469step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def raw1469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1470 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1470step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1471 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1472 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1472Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw1472step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1472step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1472step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1473 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1473step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14087step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw14092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw14092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw14097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14103step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14103step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14104step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14104step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14105step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14105step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14105step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14105step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14105step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14106step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14106step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14107step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14107step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14107step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14107step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14107step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14107step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14107step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14108step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14108step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14109step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14109step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14109step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14110step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14111step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14111step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14112step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14112step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14112step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14112step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14113step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14113step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14113step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14114step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14115step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14115step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14115step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14115step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14116step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14116step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14116step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14116step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14117step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14117step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14117step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14117step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14117step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14117step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14118step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw14118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14118step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14118step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14118step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw14119step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14119step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw14120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14120step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14120step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14120step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14121step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14121step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14121step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14121step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14121step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw14122step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw14122step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14122step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14122step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14122step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14122step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14122step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14122step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14123Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14123step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14123step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14123step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14123step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14124step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14124step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14125Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14125step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14125step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14125step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14125step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14125step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14126step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14126step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw14127Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14127step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14127step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw14127step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14127step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14127step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14127step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14128step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14128step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14129step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14129step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14129step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14130step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14130step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14130step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14131step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14131step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14131step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14131step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14132step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14132step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14132step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14133step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14134step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14134step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14134step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14134step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw14135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14136step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14136step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14136step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14136step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14137step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14137step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14138step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14139step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14140step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14142step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14144step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14146step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14146step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw14151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw14151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14151step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw14151step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14151step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw14151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw14152step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw14152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14153step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14154step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14155step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14156step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14156step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw14157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw14157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14157step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14158step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14158step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14159step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14160step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14160step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14161step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14161step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw14162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw14162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw14162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14162step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14162step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14162step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw14165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14176step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw14181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw14181step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw14181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw14182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw14187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw14187step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14187step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14188step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14189step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14191step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw14192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw14192step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw14192step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14192step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14193 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14193step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14194 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14194step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14194step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14195 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14195step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14196 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw14196step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw14196step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14196step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw14196step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14197 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw14197step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw14197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14198 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw14198step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw14198step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14199 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw14199step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw14199step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14200 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw14200step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw14200step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw14200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14201 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14201step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14202 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14202step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14202step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14203 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14203step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14203step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14203step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14204 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14204step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14204step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14205 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14205step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14205step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14206 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14206step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14206step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14207 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14207Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14208 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14208Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14208step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14209Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14209step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14210 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14210Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14210step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14211 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14211Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14212 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14212Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14212step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14213 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14213Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14213step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw14213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14214Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14214step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14215 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14215Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14216 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14216Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14216step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14217 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14218 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14218Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14219 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14219Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14219step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14220 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14220Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14220step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14222step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw14222step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw14222step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw14222step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14223step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14223step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14223step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14223step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14224step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14224step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14224step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14224step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14225step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14225step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14225step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw14245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw14245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw14250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw14250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14251 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14251step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14252 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14252step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14253 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14253step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14254 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14254step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14255 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14255step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw14255step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw14255step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14255step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw14255step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14255step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14256 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14256step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14257 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14257step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14257step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14257step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14257step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14258 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14258step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14259 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14259step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14259step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14260 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14260step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14261 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw14261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw14261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14261step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14261step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14261step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14261step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw14262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14262step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14263 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw14263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw14263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14263step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14264step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14264step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14265step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14265step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14265step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14266step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14266step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14266step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14267step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14267step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14267step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw14284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14287step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14288step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14288step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14288step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14289step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14289step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14291step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14291step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14292step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14292step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14292step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14293step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14293step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14294step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14295step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14296step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14296step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14296step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14296step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14296step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14297step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14297step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14297step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw14298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14298step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14298step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw14299step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14299step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14299step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw14300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14300step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw14301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14301step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14301step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14301step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw14302step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14302step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14303step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14303step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14305step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14305step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw14306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14306step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14306step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14306step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw14307step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14307step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14307step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14308step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14309step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14309step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw14310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14310step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14310step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14310step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw14311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14311step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14311step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14311step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14312step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14312step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14312step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14312step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14313step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw14314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14314step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14314step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14314step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw14315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14315step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14315step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14315step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14316step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14316step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14316step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14317step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw14318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14318step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14318step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14318step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw14319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14319step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14319step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14319step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14320step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14321step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14322step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw14323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw14323step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14323step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14323step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw14324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw14324step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14324step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14324step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14325step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14326step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14327step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw14328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw14328step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14328step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14328step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14328step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14329step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14329step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14330step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14330step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14330step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14330step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14331step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14331step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14331step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14332step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14332step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14332step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14332step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14333step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14333step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14333step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14333step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14334step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14334step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14334step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14334step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14339step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14339step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw14339step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14339step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14348step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14349step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14353step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw14354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14360step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw14360step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14361step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw14361step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14361step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw14361step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw14362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14362step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14362step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14362step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw14363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14363step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14363step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14363step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14364step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw14364step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14365step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw14365step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw14366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14366step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14366step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14366step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw14367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14367step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14367step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14367step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14368step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14368step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw14368step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14368step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw14368step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14369step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw14369step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14369step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw14369step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14370step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw14370step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14370step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw14370step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw14371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14371step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14371step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14371step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw14371step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14371step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw14371step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw14372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14372step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14372step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14372step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14372step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw14372step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14372step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw14372step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14373step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14373step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw14373step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14373step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw14373step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14374step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw14374step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14374step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw14374step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14375step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw14375step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14375step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw14375step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw14376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw14376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw14376step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14376step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw14376step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14376step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw14376step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw14407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw14420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw14423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14425step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw14425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw14427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw14431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw14431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw14432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw14432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw14435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw14435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw14436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14436step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw14436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw14442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14443 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0], ![0, 0]]
def raw14443Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14443step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]
def raw14443step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14443step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw14443step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, -1, 0], ![0, 2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw14456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw14456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw14457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw14458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw14459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14460step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14461step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14461step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14462step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14463step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14463step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14463step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14464step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14467step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14467step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14468step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14468step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14468step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14469step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14469step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14469step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14469step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14471step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14472step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14473step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14479step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14479step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14479step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14483step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14483step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14483step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw14484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14485step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14486step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14487step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14487step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14487step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14487step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14488step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14489step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw14492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw14496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw14514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw14515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw14515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw14516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14521step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14525step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14525step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14525step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14525step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14526step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14526step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14527step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14529step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14529step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14529step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14529step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14530step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14531step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14533Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14533step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14534step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14535step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14535step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14535step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14536step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14537step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14537step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14538step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14539step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14539step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14539step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14539step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw14540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14540step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14541step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw14542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14542step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14543step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw14544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14545step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14547step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14549step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw14552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14556 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]
def raw14556Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14556step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw14556step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14556step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw14556step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw14560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw14576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw14639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14641step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14642step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14643step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw14645step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14645step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw14646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14646step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14646step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14647step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14647step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw14648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14648step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14648step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw14649step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14650Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14650step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14650step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14651Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14651step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14651step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14651step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14652Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14653Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14653step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14654Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14654step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14654step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14654step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14655Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw14655step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14655step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14655step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -1, 0], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw14656step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14656step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14656step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14657Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw14657step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14657step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14657step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14658step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14659Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw14659step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw14659step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14659step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw14659step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14660Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw14660step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw14660step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14660step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw14660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14661Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14661step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14662Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14662step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14663Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14663step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14664Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14664step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14665Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw14665step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw14665step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14665step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw14665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14666Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14666step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14667Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14667step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14668Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14668step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw14669Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14669step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14671step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14674step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw14674step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14676 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]
def raw14676Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14676step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]
def raw14676step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14676step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw14676step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14676step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw14676step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14677step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw14679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw14679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw14681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw14681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw14682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw14682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw14684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw14686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14687step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw14687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw14689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14690step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14693step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14695step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14699step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14703 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14704 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14704step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14704step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14704step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14704step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14709step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14709step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14709step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14711step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14711step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14711step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14712step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14712step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14713step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14713step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14714step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14714step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14724step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14729step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14729step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw14730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14730step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14730step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14731 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14732 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14733 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14734 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14735 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14738 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14738step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14739 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14741step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14742step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14743 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14743step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14745step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw14746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


