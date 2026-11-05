-- Prove2me | Definitions.Def_OAIQ106E095
-- name    : OAIQ106E095
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:07:45.425309+00:00
-- url     : https://prove2.me/theorems/8e118419-a433-46b8-861d-fe78c079430a
-- title:
--   Definitions bundle OAIQ106E095 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7606 declarations of OpenAI's Lean: 7606 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw18991step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18991step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18992`, `OAI.MUB6.Certificate.MixedSemantics.raw18992Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18992step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18992step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18992step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18992step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18992step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18992step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18993`, `OAI.MUB6.Certificate.MixedSemantics.raw18993Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18993step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18993step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18993step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18993step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18994`, `OAI.MUB6.Certificate.MixedSemantics.raw18994Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18994step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18994step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18994step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18994step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18994step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18994step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18994step3`, `OAI.MUB6.Certificate.MixedSemantics.raw18994step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18995`, `OAI.MUB6.Certificate.MixedSemantics.raw18995Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18995step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18995step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18995step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18995step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18995step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18995step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18996`, `OAI.MUB6.Certificate.MixedSemantics.raw18996Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18996step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18996step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18996step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18996step1Labels` and 7566 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical14.lean), [`MutuallyUnbiased_MixedSemantics_Canonical148`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical148.lean), [`MutuallyUnbiased_MixedSemantics_Canonical149`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical149.lean), [`MutuallyUnbiased_MixedSemantics_Canonical15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical15.lean), [`MutuallyUnbiased_MixedSemantics_Canonical150`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical150.lean), [`MutuallyUnbiased_MixedSemantics_Canonical151`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical151.lean), [`MutuallyUnbiased_MixedSemantics_Canonical152`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical152.lean), [`MutuallyUnbiased_MixedSemantics_Canonical153`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical153.lean), [`MutuallyUnbiased_MixedSemantics_Canonical154`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical154.lean), [`MutuallyUnbiased_MixedSemantics_Canonical155`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical155.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1030_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37_e`.
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

def raw18Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]

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

def raw189Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw189step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw190 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw191 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw191Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw191step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw192 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw193 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw193Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw193step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw196 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw197 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw197Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw197step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw198 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw199 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]

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

def raw1899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1899step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1900 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1901 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1901Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1901step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1901step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1901step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1902step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1904Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1904step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1904step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1905step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1907Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1907step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1908 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1908step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1909 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1910 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1910Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1910step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1910step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1911 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1911step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1912 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1913 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1913Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1913step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1913step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1914step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1915 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1916 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1916Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1916step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1917 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1917step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1918 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1919 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1919Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1919step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1919step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw18991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18992step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18992step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18993step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18994step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18994step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18995step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18996step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18997step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18998step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18998step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw18999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw18999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18999step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw19000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw19000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19000step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw19001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw19001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw19002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw19002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw19002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw19002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19007step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19007step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw19007step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19007step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19008step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19009step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19010step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19011step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19011step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw19020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw19020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19021step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19021step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw19026step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw19026step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19026step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw19026step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw19027step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19027step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19027step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw19028step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19028step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19028step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19028step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19029step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19029step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19029step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19030step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw19032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw19032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19032step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw19033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19033step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19034step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19034step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19035step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19036step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19036step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw19037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw19037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw19038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19038step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw19039step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw19039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19040step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19040step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw19041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw19041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19041step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19041step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw19042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19042step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw19043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw19043step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw19043step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw19044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19044step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw19045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19045step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19045step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19045step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19045step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw19046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19046step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw19047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19047step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw19048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw19049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19049step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw19050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19050step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19050step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19050step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19051 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19051step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19051step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19052 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw19052step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19052step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19053 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19053step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19054 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw19054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19054step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19055 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19055step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19056 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19056step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19056step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19056step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19056step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw19057step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19057step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19057step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19057step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19058step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw19059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19059step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19060step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19060step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19061 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19061step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19061step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw19061step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19061step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw19061step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19061step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19062step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19062step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19063step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw19064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw19064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19064step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19065 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19065step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19065step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19065step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19065step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19066step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19066step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19066step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw19067step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19067step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19067step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw19068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19068step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19069step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19070 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw19070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19070step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19070step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw19071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19071step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19071step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw19072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw19072step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19072step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19072step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19072step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw19073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19073step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw19074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19074step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19075 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw19075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19075step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19075step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19075step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw19076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19076step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19076step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19076step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw19077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw19077step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19077step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19077step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19077step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw19078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19078step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19078step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw19079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19079step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19081step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19081step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19081step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19082step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19082step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19082step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19083step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19083step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19083step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19083step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19084step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19084step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19084step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19084step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19085step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19086step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19087step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19088step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19089step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19089step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19089step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19090step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19095step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw19099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19100step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19105step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw19107step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19107step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw19108step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19108step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19108step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw19109step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19109step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19109step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19110step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19111step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19111step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19112step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19113step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19113step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19113step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19113step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19114step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19114step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19114step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19115step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19115step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19116step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19116step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19117step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19117step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19117step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19117step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19118step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19119step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw19120step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw19120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19120step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw19120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19121step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19121step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19121step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19122step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19122step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19122step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19123Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19123step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19123step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19124step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19124step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19124step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19125Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19125step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19125step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19125step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19126step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19126step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19127Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19127step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19127step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19128step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19128step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw19129step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19129step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19129step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19129step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19130step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19130step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19131step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19131step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19131step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19131step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19133step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19133step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19133step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19134step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19134step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19134step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19135step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19135step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19135step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19136step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19137step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19138step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19139step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19140step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19140step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19140step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19141step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19141step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19142step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19142step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19142step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19143step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19143step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19143step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19143step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19144step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19144step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19145step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19150step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19151step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19151step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19151step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19151step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19152step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19152step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19152step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19152step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19153step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19153step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19153step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19153step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19154step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19154step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19155step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw19156step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19156step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19156step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19156step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw19157step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19157step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19157step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw19158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw19158step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19158step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19158step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19158step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19159step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19160step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw19161step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19161step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19161step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19161step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw19162step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19162step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19162step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw19163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw19163step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19163step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19163step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19163step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw19164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19164step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19165step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19165step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19166step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19166step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19166step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19167step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw19168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19168step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19168step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw19169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw19169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19169step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19169step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19170step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw19171step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw19171step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2]]
def raw19172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19172step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19172step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2]]
def raw19173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19173step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19173step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19173step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19174step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19174step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19174step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19175step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19175step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19175step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19175step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw19176step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw19176step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw19176step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19177step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw19177step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19177step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19177step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19177step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19178step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19178step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19179step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19180step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19180step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19181step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19181step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19182step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19182step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19182step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19183step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19184step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19184step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19185step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw19186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19186step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19186step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19187step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19187step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19187step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19187step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19188step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19188step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19189step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19190step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw19191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19191step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19191step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19191step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19191step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw19192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw19192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19192step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19192step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19192step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19192step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19194step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw19195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw19195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw19195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19195step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw19195step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19196step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19196step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19196step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19197step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19197step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19197step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19198step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19198step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19198step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19198step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19199step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19199step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19199step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19199step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1920 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1920step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1921 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1922 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1922Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1922step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1923 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1923step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1924 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1925 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1925Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1925step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1925step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1926 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1926step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1926step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1927 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1927step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1928 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1928Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1928step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw1928step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw1928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1929 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1929step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1929step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1930 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1930step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1931 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1931Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1931step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw1931step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw1931step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw1931step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1932 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw1932step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw1932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1933 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw1933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1934 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1934Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1935 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw1935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw1935step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw1935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1936 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw1936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1937 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw1937Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw1937step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1937step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw1937step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1937step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw1937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1941 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1941step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1942 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1943 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1943Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw1943step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw1943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1943step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw1943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1944 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1944step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1945 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1946 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1946Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1947 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw1947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw1947step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw1947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1948 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw1948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1949 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw1949Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw1949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw1949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw1949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1950 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw1950step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw1950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1951 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1952 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1952Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw1952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw1952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw1952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1953 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1953step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1954 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1955 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1955Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw1955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw1955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw1955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1956 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw1956step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw1956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1957 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw1957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1958 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1958Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1959 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw1959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw1959step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw1959step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1960 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw1960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1961 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw1961Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw1961step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw1961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw1961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1962 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw1962step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw1962step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1963 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1964 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1964Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1965 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw1965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw1965step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw1965step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1966 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw1966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1967 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw1967Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw1967step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw1967step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw1967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1971 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 2, -2], ![-2, 3, -1]]
def raw1971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw1971step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw1971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1972 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 2, -2], ![-2, 3, -1]]
def raw1972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1972step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw1972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1973 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 2, -2], ![-2, 3, -1]]
def raw1973Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw1973step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw1973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1989 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1989step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1990 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1991 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1991Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1991step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1992 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1992step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1993 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1994 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1994Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1994step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1994step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19200step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19200step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19202step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19202step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19202step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19202step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19206step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19206step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19206step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19206step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw19208step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19208step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19208step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19208step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw19209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19209step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19209step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19209step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19209step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19210step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19210step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19210step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw19212step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19212step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19212step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19213step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19213step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19213step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19213step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw19214step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw19214step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw19214step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw19216step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19216step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19216step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19216step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw19217step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19217step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19217step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19218step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19218step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19218step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19218step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19219step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19220step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19221step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19221step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19221step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19221step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19222step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19222step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19222step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19222step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19223step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19223step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19223step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19223step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19223step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19224step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19224step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19224step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19225Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19225step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19225step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19225step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19226Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19226step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19226step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19226step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19227Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19227step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19227step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19227step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19227step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19227step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19228Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19228step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19228step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19228step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19229Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19229step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19229step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19229step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19230Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw19230step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19230step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19230step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19230step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19231Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw19231step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19231step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19231step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19231step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19232Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19232step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19232step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19232step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19233Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19233step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19233step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19233step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw19234step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19234step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19235Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19235step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19235step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19235step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw19236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw19236step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19236step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw19236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19237Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19237step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19237step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw19238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw19238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw19239step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw19239step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19241step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19241step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19241step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19242step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19242step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19242step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19242step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19243step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19243step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19243step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19243step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19244step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19244step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19244step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19244step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19245step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19245step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19245step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19246step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19246step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19246step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19247step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19248step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19249step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19250step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19253step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19254step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19254step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19254step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19255step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19255step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19255step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19256step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19257step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19257step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19257step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw19258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19258step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19258step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19258step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19258step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19259step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19260step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19260step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19260step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19261step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19262step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19262step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19262step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw19263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19263step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19263step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19263step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw19264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19264step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19265step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19265step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19265step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19266step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19267step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19267step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19267step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19268step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19268step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw19269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19269step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19269step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19269step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw19271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw19271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw19277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw19278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw19279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw19288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19292step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw19293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19293step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw19294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw19299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19300step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19301step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19302step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19303 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw19303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw19303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw19304step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw19304step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw19304step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19305 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw19305step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw19305step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19305step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw19305step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19306 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19306step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19306step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19306step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19307 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19307step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19307step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19307step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19308 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw19308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw19308step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw19308step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19308step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw19308step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19309step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19309step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19309step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19309step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19310 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19310step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19311 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw19311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw19311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19311step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19311step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19311step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19311step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19312step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19312step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19312step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19312step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19313 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19313step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19313step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19313step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19313step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19314 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw19314step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19314step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19314step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19315 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw19315step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19315step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19315step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19316 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw19316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19316step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19316step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19316step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw19317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19317step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19317step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19317step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19317step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw19318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19318step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19318step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19318step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19319 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw19319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw19319step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19319step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19319step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19320 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw19320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw19320step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19320step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19320step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19320step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19321 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw19321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19321step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19321step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19321step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19321step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19322step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19322step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19322step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19322step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19323 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19323step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19323step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19323step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19324step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19325step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19325step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19325step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19326step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19326step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19326step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19326step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19327step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19327step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19327step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19327step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw19334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw19334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19338step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19339step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19339step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19339step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19339step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19340step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19340step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19340step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19340step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw19341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19341step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19341step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19341step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw19342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19342step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19342step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19342step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw19346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw19347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw19350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw19351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw19352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw19353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw19354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw19355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw19359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19360step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw19360step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw19361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19361step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19361step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw19362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19362step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19362step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19363step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw19363step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19363step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw19363step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19364step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw19364step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19364step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19364step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw19365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19365step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw19365step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19365step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw19365step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw19366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19366step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19366step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw19366step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19366step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw19366step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19367step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw19367step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19367step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw19367step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19368step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw19368step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19368step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19368step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw19369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19369step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19369step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19369step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw19369step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19370 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19370step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19370step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19370step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19371step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19371step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19371step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19372 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19372step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19372step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19372step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19373 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19373step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19373step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19374 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19374step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19375step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19375step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19376step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19376step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19376step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19377step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19377step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19377step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19377step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19378step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19378step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19378step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19378step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19379step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19380step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19381step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19381step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19381step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19382step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19383step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19384step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19385step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19385step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19385step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw19386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19386step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19388step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw19389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19390 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19390step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19390step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19391 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19391step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw19391step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19391step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19391step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19392 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw19392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19392step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19392step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19392step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19393 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw19393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19393step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19393step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19393step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19394step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw19394step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19394step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19394step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw19395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19395step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19395step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19395step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw19396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19396step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19396step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19396step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19397step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw19397step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19397step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19397step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19398step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw19398step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19398step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19398step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw19399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19399step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw19399step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19399step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19399step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19399step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19399step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw19400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19400step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw19400step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19400step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19400step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19400step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19400step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19401step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw19401step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19401step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19401step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19402step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw19402step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19402step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19402step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw19403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19403step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw19403step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19403step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19403step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19403step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19403step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19404step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19404step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19404step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19404step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19405step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw19405step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19405step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19405step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw19406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19406step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw19406step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19406step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19406step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19406step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19406step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19407step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw19407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw19411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw19411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw19411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19411step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw19411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw19412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw19412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw19412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19412step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw19412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19413 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw19413Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19413step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw19413step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19413step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw19413step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19413step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw19413step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19413step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw19413step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19414 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19414step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-3, -1, 4]]
def raw19414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19414step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw19414step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw19415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19416 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw19416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19417 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw19417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19418 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19418step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19418step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19418step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 0, 4]]
def raw19419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 0, 4]]
def raw19419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-4, 0, 4]]
def raw19419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19419step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-4, 0, 4]]
def raw19419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19419step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw19419step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19420 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-4, 4]]
def raw19420Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19420step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![0, 0], ![-4, 4]]
def raw19420step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19420step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![-4, 4]]
def raw19420step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19420step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-4, 4]]
def raw19420step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19420step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![4, -4], ![-4, 4]]
def raw19420step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19420step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]
def raw19420step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19426 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw19426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19427 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19427step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw19427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19428 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19428step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw19428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19429step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19437step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19440step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw19441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw19441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw19441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19441step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw19442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw19442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19442step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw19442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19442step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw19442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19443 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw19443Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19443step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw19443step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19443step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw19443step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19444 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19445 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19446 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19446step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19446step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19447 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 0, 4]]
def raw19447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 0, 4]]
def raw19447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-4, 0, 4]]
def raw19447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-4, 3, 1]]
def raw19452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![4, -3, -1]]
def raw19452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw19453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw19453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw19454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw19454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw19455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19455step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw19455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![4, 0, -4]]
def raw19456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![4, 0, -4]]
def raw19456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, -1, 2], ![4, 0, -4]]
def raw19456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw19456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19456step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw19456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![3, 1, -4]]
def raw19457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![3, 1, -4]]
def raw19457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![3, 1, -4]]
def raw19457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw19457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19457step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw19457step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19458 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2], ![4, -4]]
def raw19458Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19458step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-2, 2], ![4, -4]]
def raw19458step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19458step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![4, -4]]
def raw19458step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19458step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw19458step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19458step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw19458step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw19466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19466step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw19466step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -3, -2]]
def raw19471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![5, -3, -2]]
def raw19471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![5, -3, -2]]
def raw19471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19471step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19472 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw19472Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19472step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]
def raw19472step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19472step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw19472step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19473step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19474 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 2, 0], ![-2, -2, 4]]
def raw19474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19474step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw19474step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19475 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19476 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19477 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19477step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19477step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19477step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19478 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19479 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, -2, 4]]
def raw19481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 2, -4], ![-2, -2, 4]]
def raw19481step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def raw19481step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![4, -1, -3]]
def raw19482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw19482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19482step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![4, -1, -3]]
def raw19483step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw19483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw19483step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw19484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw19484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw19485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw19485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw19486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw19486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![4, -1, -3]]
def raw19486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw19486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19486step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw19486step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw19487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw19487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19487step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw19487step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19488 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![3, -3]]
def raw19488Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19488step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![3, -3]]
def raw19488step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19488step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw19488step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19488step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw19488step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19488step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw19488step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -2, 2], ![3, 0, -3]]
def raw19489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw19489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw19492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw19492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw19492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw19494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw19494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw19495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw19495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw19496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw19496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw19497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw19497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw19497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw19497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw19498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw19498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19499 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw19499Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19499step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw19499step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19499step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw19499step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19499step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19499step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw19500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw19502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw19503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw19503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw19503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19504step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19504step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19504step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19504step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19504step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19504step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19504step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19504step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19505step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19505step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19505step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19506step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19506step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19506step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19506step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19507step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19507step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19507step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19508step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19508step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19508step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19508step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19508step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19508step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19509step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19509step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19509step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19510step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19510step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19510step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19511step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19511step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19512step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19512step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19512step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19512step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19512step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19512step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19512step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19513step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19513step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19513step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19514step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19514step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19515step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19515step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19515step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19516step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19516step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19516step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19516step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19516step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19516step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19517step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19517step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19517step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19517step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19518step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19518step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19519step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19519step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![5, -3, -2]]
def raw19520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 3, 2], ![5, -3, -2]]
def raw19520step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19520step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19520step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19520step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19521step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19521step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19521step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19521step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19521step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19521step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19522step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19522step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19522step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19522step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19522step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19522step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19522step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19523step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19523step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19523step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19523step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19523step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19523step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19523step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19523step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19524step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19524step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19524step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19524step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19524step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19524step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19524step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19525step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19525step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19525step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw19525step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19525step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw19525step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19525step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19525step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19526step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19526step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19526step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw19526step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19526step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw19526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19526step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19526step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19527step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19527step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19527step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw19527step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19527step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw19527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19527step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19527step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19528step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19528step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19528step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw19528step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19528step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw19528step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19528step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19528step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19529step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19529step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19529step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![3, -1, -2]]
def raw19529step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19529step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw19529step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19529step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]
def raw19529step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19530step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19530step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19530step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19531step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19532step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19533step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19534step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw19534step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19534step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19534step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19535step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19535step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19535step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19535step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19535step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19536step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19537step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19538step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19539step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19539step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw19539step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19539step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19540step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19540step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19540step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19540step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19541step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19541step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19542step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19543step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19544step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19544step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw19544step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19544step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19545step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19545step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19545step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19546step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19547step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19548step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19549step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19549step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw19549step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19549step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19549step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19550step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19550step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![5, -3, -2]]
def raw19550step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19550step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 3, 2], ![5, -3, -2]]
def raw19550step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19550step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19550step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19551step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19551step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19551step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19551step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19551step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19551step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19552step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19552step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19552step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19552step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19552step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19552step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19552step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19553step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19553step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19553step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19553step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19553step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19553step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19554step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19554step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19554step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19554step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19554step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19554step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19554step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19555 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19555step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19555step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19555step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19555step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19555step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19555step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19556 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19556step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19556step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19556step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19556step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19556step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19557 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19557step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19557step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19557step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19557step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19557step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19557step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19558 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19558step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19558step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19558step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19558step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19558step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19558step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, -1, 4]]
def raw19559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![3, 1, -4], ![-3, -1, 4]]
def raw19559step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19559step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19559step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19559step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19560step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19560step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19560step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19560step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19560step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19560step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19561 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19561step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19561step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19561step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19562 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19562step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19563 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19563step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19563step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19563step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19564 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19564step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19564step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19564step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19564step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19564step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19564step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19564step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19565 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19565step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19565step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19565step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19565step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19565step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19566 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19566step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19567 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19567step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19567step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19568 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19568step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19568step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19569 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19569step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19569step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19569step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19569step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19569step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19569step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19569step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19570step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19570step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19570step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19570step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19570step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19571 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19571step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19571step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19572 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19572step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19572step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19572step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19573 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19573step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19573step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19574 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19574step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19574step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19574step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19574step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19574step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19574step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19574step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19575step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19575step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19575step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19575step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19575step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19576 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19576step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19576step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19577 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19577step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19577step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19578 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19578step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19578step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19579 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19579step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19579step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19579step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19579step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19579step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19579step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19579step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -3, 4]]
def raw19580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -3, 4]]
def raw19580step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19580step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19580step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19580step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19581 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19581step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19581step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19581step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19581step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19581step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19581step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19581step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19582 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19582step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19582step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19582step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19582step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19582step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19582step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19582step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19583 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19583step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19583step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19583step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19583step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19583step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19583step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19583step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19583step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19584 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19584step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19584step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19584step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19584step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19584step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19584step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19584step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19584step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19585 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19585step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19585step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19585step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19585step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-4, 3, 1]]
def raw19585step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19585step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19585step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19586 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19586step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19586step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19586step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-4, 3, 1]]
def raw19586step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19586step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19586step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19587 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19587step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19587step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19587step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-4, 3, 1]]
def raw19587step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19587step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19587step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19588 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19588step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19588step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19588step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-4, 3, 1]]
def raw19588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19588step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19588step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19589 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19589step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19589step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, -1, 4]]
def raw19589step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19589step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![3, 1, -4], ![-3, -1, 4]]
def raw19589step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19589step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 3, 1], ![4, -3, -1]]
def raw19589step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19590step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19590step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19590step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19590step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19591 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19591step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19592 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19592step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19593 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19594 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19594step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19594step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19594step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19594step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19594step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19595step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19595step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19595step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19596 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19596step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19597 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19597step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19597step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19598 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19598step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19599 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19599step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19599step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19599step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19599step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19599step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19600step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19600step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19600step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19600step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19600step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19600step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19601 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19601step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19602 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19602step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19603 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19603step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19604 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19604step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19604step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19604step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19604step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19605step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19605step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19605step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19605step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19605step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19606 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19606step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19607 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19607step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19607step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19608 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19608step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19609 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19609step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19609step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19609step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19609step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19609step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19609step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19610 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19610step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19610step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -3, 4]]
def raw19610step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19610step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -3, 4]]
def raw19610step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19610step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19610step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19611 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19611step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19611step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19611step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19611step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19611step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19611step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19611step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19611step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19612 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19612step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19612step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19612step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19612step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19612step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19612step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19612step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19613step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19613step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19613step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19613step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19613step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19613step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19613step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19614 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19614step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19614step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19614step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19614step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19614step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19614step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19615 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19615step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19615step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19615step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19616 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19616step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19616step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19617 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19617step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19617step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, -1, 4]]
def raw19618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![3, 1, -4], ![-3, -1, 4]]
def raw19618step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def raw19618step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19619step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19619step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19619step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19622step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19623step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19623step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19623step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19626step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19626step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19627step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19627step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19627step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19629step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19630step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19630step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19630step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19630step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19631step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def raw19631step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19631step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw19631step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19631step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw19631step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19632step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19632step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19633step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19633step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19633step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19634step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19634step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19634step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![5, -2, -3]]
def raw19635step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-5, 3, 2]]
def raw19635step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw19635step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19636step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19636step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19637step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19637step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19637step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19638step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![5, -2, -3]]
def raw19639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19639step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19639step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw19640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw19640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw19641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw19641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19642step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw19642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19642step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw19642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19643step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw19643step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19643step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 1, 0], ![-3, 2, 1]]
def raw19643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19643step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![3, -2, -1]]
def raw19643step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19644step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19647step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19648step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw19648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19649step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19652step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19653step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19653step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw19653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19654step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19654step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19657step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19658step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw19658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19659step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19659step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def raw19659step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19659step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw19659step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw19660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19661step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw19661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19662step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw19662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19663step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19663step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![5, -2, -3]]
def raw19663step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19663step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw19663step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19664step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19665step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19665step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19666step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19666step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19667step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19667step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![5, -2, -3]]
def raw19667step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19667step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 1, 0], ![-4, 2, 2]]
def raw19667step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19667step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19667step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19668Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19668step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19668step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw19668step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19668step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19668step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19668step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19669Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19669step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19669step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19670Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19670step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19670step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19671Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19671step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19671step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19671step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19671step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19672Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19672step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19672step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw19672step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19672step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19672step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19672step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19672step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19673Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19673step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19673step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19674Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19674step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19674step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19675Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19675step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19675step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19675step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19675step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19676Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19676step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19676step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw19676step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19676step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19676step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19676step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19677Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19677step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19677step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19678Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19678step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19678step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19679Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19679step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19679step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19679step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19679step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19680Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19680step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19680step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19680step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def raw19680step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19680step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -3, 4], ![-2, 1, 1]]
def raw19680step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19680step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw19680step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19680step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw19680step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19681Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19681step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19681step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19681step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19681step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19682Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19682step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19682step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19682step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19682step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19683Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19683step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19683step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19683step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19683step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19684Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19684step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19684step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19684step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![5, -2, -3]]
def raw19684step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19684step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-2, -3, 5]]
def raw19684step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19684step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw19684step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19684step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw19684step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19685Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19685step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19685step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19685step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19685step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19686Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19686step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19686step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19686step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19686step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19686step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19687Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19687step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19687step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19687step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19687step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19688Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19688step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19688step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19688step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![5, -2, -3]]
def raw19688step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19688step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw19688step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19688step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw19688step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw19689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw19690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw19691step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19692step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def raw19692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![5, -2, -3]]
def raw19693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-5, 3, 2]]
def raw19693step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw19693step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19696step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19696step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19699step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19700step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19701step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19701step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19702step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw19703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-3, 1, 2]]
def raw19703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw19703step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19705step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![5, -2, -3]]
def raw19706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19706step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19707step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19707step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19708step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19708step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19708step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19709step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19709step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19709step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19709step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19710step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19710step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19710step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19710step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19710step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19711step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19711step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19712step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19712step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19712step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19713step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19713step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19713step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19714step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19714step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19714step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19714step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19715step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19715step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19715step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19716step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19716step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19716step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19717step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19717step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19717step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19717step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19718step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19718step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19718step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19718step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19718step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19718step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19718step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19719step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![4, -3, -1]]
def raw19719step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19719step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19719step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19719step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19719step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19720step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19720step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19720step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19720step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19721step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19721step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19721step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19721step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19721step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19722step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19722step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19722step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19722step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19722step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19723step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![5, -4, -1]]
def raw19723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19723step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-5, 2, 3]]
def raw19723step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19723step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw19723step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19723step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw19723step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19724step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19724step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19724step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19724step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19724step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19725step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19725step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19725step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19725step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19726step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19726step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19726step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19726step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19727step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![5, -4, -1]]
def raw19727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19727step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-1, -1, 2], ![-4, 2, 2]]
def raw19727step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19727step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw19727step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19727step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw19727step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw19728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw19728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw19728step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19728step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw19728step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19728step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw19728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19728step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw19728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19729step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19732step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19732step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19733step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19734step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19736step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19737step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19737step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19738step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19739step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19740step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19740step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19740step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19740step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19741step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19741step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19741step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![4, -3, -1]]
def raw19741step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19741step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19742step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19742step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19742step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19742step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19743step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19743step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19744step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19744step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19744step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19745step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19745step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19745step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![5, -4, -1]]
def raw19745step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19745step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-5, 2, 3]]
def raw19745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19745step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw19745step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19746step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19746step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19746step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19747step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19747step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19747step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19747step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19748step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19748step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19749step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19749step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19749step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![5, -4, -1]]
def raw19749step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19749step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-1, -1, 2], ![-4, 2, 2]]
def raw19749step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19749step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw19749step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19754 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19754step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19754step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19754step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19758 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19758step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19758step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19758step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19762 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19762step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19762step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, -2, 4]]
def raw19766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 2, -4], ![-2, -2, 4]]
def raw19766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw19766step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19766step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw19766step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19767 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19767step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19767step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw19767step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19767step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19767step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19767step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19767step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19824 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19824step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19824step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19824step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19825 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19826 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -3, 4]]
def raw19828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -3, 4]]
def raw19828step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def raw19828step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19829 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19829step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19829step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![3, 1, -4]]
def raw19829step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![4, 0, -4]]
def raw19830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw19830step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw19830step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19831step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw19831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19831step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw19831step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19832step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw19832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19832step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw19832step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw19833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19833step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw19833step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![4, 0, -4]]
def raw19834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-3, 1, 2]]
def raw19834step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw19834step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![3, 1, -4]]
def raw19835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw19835step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw19835step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19836 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![-2, 2], ![4, -4]]
def raw19836Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19836step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![4, -4]]
def raw19836step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19836step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![4, -4]]
def raw19836step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19836step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![4, -4]]
def raw19836step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19836step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-2, 2], ![-2, 2]]
def raw19836step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19836step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw19836step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw19837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19837step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw19837step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw19838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw19838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw19839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19839step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw19839step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![5, -1, -4]]
def raw19840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![5, -1, -4]]
def raw19840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![5, -1, -4]]
def raw19840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19840step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![5, -1, -4]]
def raw19840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19840step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-1, -1, 2], ![-4, 2, 2]]
def raw19840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19840step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw19840step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw19841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw19842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw19843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw19844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw19844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw19844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19844step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![3, 1, -4]]
def raw19844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19850step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19850step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw19851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw19851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw19852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw19852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw19853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19853step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw19853step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, 0, -4]]
def raw19854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, 0, -4]]
def raw19854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![4, 0, -4]]
def raw19854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19854step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw19854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19854step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw19854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw19855step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw19855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19856 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![4, -4]]
def raw19856Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19856step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![4, -4]]
def raw19856step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19856step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![4, -4]]
def raw19856step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19856step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw19856step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19856step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw19856step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![4, 0, -4]]
def raw19859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![4, 0, -4]]
def raw19859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![4, 0, -4]]
def raw19859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19859step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![5, -1, -4]]
def raw19860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![5, -1, -4]]
def raw19860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![5, -1, -4]]
def raw19860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19860step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19860step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw19861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw19862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw19863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw19864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw19864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw19864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![4, -1, -3]]
def raw19870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![4, -1, -3]]
def raw19871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw19871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19871step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw19871step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw19872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw19873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![4, -1, -3]]
def raw19874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw19874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19874step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw19874step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![3, 0, -3]]
def raw19875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw19875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19876 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw19876Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19876step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw19876step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19876step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw19876step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19876step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw19876step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![3, 0, -3]]
def raw19881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw19881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19887step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19887step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw19887step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19887step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19887step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw19888step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19888step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw19889step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19889step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw19890step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19890step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![3, 0, -3]]
def raw19891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 0, 3], ![3, 0, -3]]
def raw19891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw19891step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw19891step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw19891step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19892step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19895step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19896step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19896step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19897step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19899step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19900step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19901step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19902step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19905step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19906step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19907step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19911step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19911step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19912step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![5, -2, -3]]
def raw19912step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19912step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19912step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-4, 1, 3]]
def raw19913step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19913step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-4, 1, 3]]
def raw19914step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19914step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-4, 1, 3]]
def raw19915step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19915step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19916step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-4, 1, 3]]
def raw19916step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19916step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19917Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19917step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19917step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19917step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19917step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19917step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19917step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19917step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19917step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19918Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19918step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19918step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19918step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19918step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19918step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19918step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19918step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19918step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19919Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19919step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19919step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19919step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19919step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19919step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19919step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19919step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19919step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19920Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19920step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19920step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19920step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19920step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19920step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19920step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19920step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19920step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19921Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19921step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19921step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19921step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![3, 0, -3]]
def raw19921step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19921step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 0, 3], ![3, 0, -3]]
def raw19921step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19921step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw19921step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19922Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19922step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19922step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19922step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19922step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19922step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw19922step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19922step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19922step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19922step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19922step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19923Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19923step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19923step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19923step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19923step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19923step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19924Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19924step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19924step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19924step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19924step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19924step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19924step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19925Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19925step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19925step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19925step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19925step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19926Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19926step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19926step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19926step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19926step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19926step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw19926step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19926step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19926step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19926step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19926step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19927Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19927step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19927step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19927step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19927step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19927step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw19927step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19927step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19927step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19927step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19927step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19928Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19928step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19928step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19928step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19928step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19928step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19928step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19929Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19929step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19929step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19929step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19929step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19929step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19930Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19930step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19930step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19930step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19930step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19930step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19931Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19931step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19931step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19931step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19931step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19931step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw19931step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19931step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19931step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19931step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19931step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19932Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19932step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19932step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19932step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19932step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19932step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw19932step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19932step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19932step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19932step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19932step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19933Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19933step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19933step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19933step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19933step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19933step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19934Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19934step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19934step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19934step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19934step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19935Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19935step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19935step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19935step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19935step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19935step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19936Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19936step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19936step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19936step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19936step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19936step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw19936step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19936step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19936step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19936step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19936step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19937Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19937step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19937step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19937step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19937step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19937step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw19937step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19937step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19937step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19937step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19937step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19938Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19938step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19938step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19938step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19939step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19940step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19940step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19940step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19940step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19941step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19941step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19941step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19941step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw19941step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19941step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19941step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19941step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19941step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19942step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19942step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![5, -2, -3]]
def raw19942step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19942step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19942step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19942step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw19942step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19942step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw19942step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19943step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19943step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19943step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19943step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19943step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19943step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19943step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19944step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19944step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19944step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19944step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19944step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19944step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19944step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19945step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19945step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19945step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19945step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19945step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19945step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19945step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19945step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19946step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19946step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19946step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19946step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19946step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19946step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19946step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19947step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![4, -1, -3]]
def raw19947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19947step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19948step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19949step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


