-- Prove2me | Definitions.Def_OAIQ106E092
-- name    : OAIQ106E092
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:04:52.543016+00:00
-- url     : https://prove2.me/theorems/0f1ca28b-dea0-4c28-9282-9b0effc97986
-- title:
--   Definitions bundle OAIQ106E092 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7274 declarations of OpenAI's Lean: 7274 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw15846step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15847`, `OAI.MUB6.Certificate.MixedSemantics.raw15847Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15847step0`, `OAI.MUB6.Certificate.MixedSemantics.raw15847step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15847step1`, `OAI.MUB6.Certificate.MixedSemantics.raw15847step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15848`, `OAI.MUB6.Certificate.MixedSemantics.raw15848Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15848step0`, `OAI.MUB6.Certificate.MixedSemantics.raw15848step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15848step1`, `OAI.MUB6.Certificate.MixedSemantics.raw15848step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15848step2`, `OAI.MUB6.Certificate.MixedSemantics.raw15848step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15849`, `OAI.MUB6.Certificate.MixedSemantics.raw15849Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15849step0`, `OAI.MUB6.Certificate.MixedSemantics.raw15849step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15849step1`, `OAI.MUB6.Certificate.MixedSemantics.raw15849step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15849step2`, `OAI.MUB6.Certificate.MixedSemantics.raw15849step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1584Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1584step0`, `OAI.MUB6.Certificate.MixedSemantics.raw1584step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1584step1`, `OAI.MUB6.Certificate.MixedSemantics.raw1584step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1585`, `OAI.MUB6.Certificate.MixedSemantics.raw15850`, `OAI.MUB6.Certificate.MixedSemantics.raw15850Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15850step0`, `OAI.MUB6.Certificate.MixedSemantics.raw15850step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15850step1`, `OAI.MUB6.Certificate.MixedSemantics.raw15850step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15850step2`, `OAI.MUB6.Certificate.MixedSemantics.raw15850step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15851`, `OAI.MUB6.Certificate.MixedSemantics.raw15851Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15851step0` and 7234 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical12`, `MutuallyUnbiased_MixedSemantics_Canonical123`, `MutuallyUnbiased_MixedSemantics_Canonical124`, `MutuallyUnbiased_MixedSemantics_Canonical125`, `MutuallyUnbiased_MixedSemantics_Canonical126`, `MutuallyUnbiased_MixedSemantics_Canonical127`, `MutuallyUnbiased_MixedSemantics_Canonical128`, `MutuallyUnbiased_MixedSemantics_Canonical129`, `MutuallyUnbiased_MixedSemantics_Canonical13`, `MutuallyUnbiased_MixedSemantics_Canonical130`, `MutuallyUnbiased_MixedSemantics_Canonical131`, `MutuallyUnbiased_MixedSemantics_Canonical132`, `MutuallyUnbiased_MixedSemantics_Canonical133`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound40_e`.
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

def raw15Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw15step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw15step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw16 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]
def raw16Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw16step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw16step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]

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

def raw158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw158step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw159 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 1, 1], ![0, 2, -2]]
def raw159Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw159step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw159step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw160 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 3, -1]]
def raw160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw160step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw160step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw160step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw161 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 3, -1]]
def raw161Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw161step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw161step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw162 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 1, -1], ![-2, 1, 1], ![1, 2, -3]]
def raw162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw162step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw162step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw163 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 1, -1], ![-2, 1, 1], ![1, 2, -3]]
def raw163Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw163step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw163step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw164 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw165 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw165Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw165step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw166 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw166step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw166step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw167 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw167Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw167step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw167step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw168 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 2, -3], ![-2, 2, 0]]
def raw168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw168step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw168step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw169 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 2, -3], ![-2, 2, 0]]
def raw169Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw169step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw169step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw170 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1584step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1584step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1585 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1585step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1586 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1586Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1586step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw1586step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw1586step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw1586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1587 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1587step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1587step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1588 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1588step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1589 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1589Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1589step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw1589step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw1589step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw1589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1590 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1590step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1591 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1592 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1592Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw1592step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1592step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1593 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1593step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1595Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw1595step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1595step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1595step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1596 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1596step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1596step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1597 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1598 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1598Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1598step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1599step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1601Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw1601step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1601step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1601step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1602 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1602step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1603 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1604 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1604Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw1604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1608step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1610 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1610Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw1610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1611 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1611step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1613 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1613Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw1613step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1613step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1614 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw1614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw1614step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw1614step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1615 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw1615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw1615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1616 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw1616Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw1616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw1616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw1616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1617 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1617step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1618 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1619 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1619Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw1619step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1620 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1620step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1621 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1621Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1622 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1622Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1622step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1623 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1623step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1624 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1625 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1625Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1626 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1626step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1627 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1628 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1628Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1629 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1629step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1630 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1631 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1631Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1631step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1632step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1634Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1634step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1635 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1635step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1636 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1637 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1637Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw1637step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1637step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1638 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1638step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1639 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1640 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1640Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw1640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1641 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1641step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1642 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1643Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw1643step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1643step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1644step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1644step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1645 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1646 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1646Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw1646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1646step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1646step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1647step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1649Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw1649step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1650step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1652 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1652Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw1652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1652step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1652step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1653step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1654 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1655 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1655Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw1655step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1655step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1655step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1656 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1656step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1657 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1658Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw1658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1658step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1659 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1659step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1660 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1661 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1661Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw1661step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw1661step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw1661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1662 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1662step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1663 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15847Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15847step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15848Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15848step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15848step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15849Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15849step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15849step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15850Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15850step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15850step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15851Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15851step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15852step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw15853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15853step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15853step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15855step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw15857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15858 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15858step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15858step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15859 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15859step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15859step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15859step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15860 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw15861step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw15861step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15861step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw15861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15862 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15862step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15862step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15862step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15862step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15863 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15864step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15864step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15864step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15865 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15866 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15867 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15868step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15868step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15868step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15868step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15870 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15871 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15872step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15873 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15874 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15876 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15876step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15877 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15878 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15880 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15882 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15885 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15885step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15889 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15891Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15892step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15892step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15893step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15893step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15894step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15894step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15895step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15896step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15896step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15897 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15897step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15897step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15897step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15897step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15899 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15899step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15900step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15900step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15900step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15900step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15900step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15901 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15901step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15901step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15901step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15901step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15902step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15903 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15903Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15903step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15904 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15904Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15904step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15904step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15905Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15905step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15905step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15905step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15906Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15906step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15906step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15906step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15907 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15907Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15907step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15908 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15910 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15911 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15912 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15973step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15973step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15973step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15974step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15974step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15975step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15975step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15975step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15976step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15976step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15977step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15977step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15978step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15978step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15979step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15979step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15980step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15981step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15982step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15983step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15983step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15984step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw15985step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw15985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15985step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw15985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15987step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15987step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15988step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15989step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15990step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15990step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15992step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15993step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw15994step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15994step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw15994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15994step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw15994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15995step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw15996step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw15996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15997step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw15998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw15998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw15999step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw15999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw15999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16000step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16001step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw16002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16009 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]
def raw16009Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16009step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw16009step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16009step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw16009step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16028step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16028step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16028step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16029step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16029step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16029step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16030step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16030step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16030step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16030step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16031step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16031step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16031step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16032step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16032step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16032step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16033step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16034step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16035step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16037step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16038step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16038step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16038step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16038step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16039step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16040step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16040step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16040step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16041step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16042step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16042step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16042step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16042step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16043step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16043step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16043step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16044step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16044step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw16045step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16045step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16045step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16045step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw16047step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16047step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16047step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw16049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16049step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16049step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16049step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16049step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw16050step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16050step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16050step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16050step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16051step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16051step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16051step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16052step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16052step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16053step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16053step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16053step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16053step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw16054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16054step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16054step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16054step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16054step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw16079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw16080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw16084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16085step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16088step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16089step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16089step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16091step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16091step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16092step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16092step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16093step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16093step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16094step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16095step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16095step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16096step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw16097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16097step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw16097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16098step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16098step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw16099step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw16099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16099step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw16099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16100step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16100step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16101step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16101step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16101step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16103step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16103step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16104step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16104step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw16105step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16105step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16105step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw16106step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16106step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw16107step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16107step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw16108step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw16108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16108step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw16108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw16109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16109step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16109step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16109step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw16110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16110step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16113step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16113step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw16114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16121 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw16121Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16121step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw16121step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16121step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw16121step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw16129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw16137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw16140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16141 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16142 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16142step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16143 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16144 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw16145step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw16145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16145step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw16145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16146 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16146step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16146step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16146step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16147 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16147step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16147step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16147step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16148 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw16148step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16148step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16148step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16149 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16149step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16149step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16150step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16150step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16150step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16151 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16151step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16151step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16151step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16151step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16152 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw16152step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16152step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16152step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16152step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16153 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16153step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16153step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16154step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16154step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16155 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16155step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16155step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16155step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16156 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16156step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16156step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16156step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16156step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16157step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16157step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16157step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16158 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16158step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16158step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16158step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16158step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16159 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16159step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16159step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16159step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16159step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16160 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16160step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16161 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16162 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16163 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16164 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw16166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw16166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16167 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16168 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16169 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw16169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16170 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16172 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16172step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16174 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16175 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16176 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw16176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16177 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16179 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16180 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16181step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16183 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16184 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16185 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16186 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16186step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16189step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16189step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16190step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16191 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16191step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16193 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16193step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16194 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16195step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16195step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16196 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16197 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16197step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16198 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16199step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16199step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16200 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16200step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16200step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16200step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16201 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16201step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16201step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16202step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16202step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16202step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16203 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16203step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16203step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16204 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16205 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16205step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16206 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16207 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16208 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16209 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16210 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16211 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16212 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16213 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16215 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16216 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw16216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16217 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16218 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16219step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16219step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16219step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16219step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16219step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16220step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16220step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16220step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16220step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16221step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16221step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16221step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16221step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1]]
def raw16222step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16222step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16223step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16223step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16223step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16223step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16223step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16223step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16227step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw16227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16230step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16230step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16230step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16230step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16235step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16235step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16240step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw16240step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16240step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw16240step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16240step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw16240step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16241step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16241step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16241step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16241step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16242step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16242step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16242step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16242step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw16243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw16243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16243step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16243step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16243step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16243step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16243step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw16244step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16244step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16244step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16244step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16244step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16245step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw16245step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16245step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw16245step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16246step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16246step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16246step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16246step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16247step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16247step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16247step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16247step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw16248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw16248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16248step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![3, -2, -1]]
def raw16248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16248step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16248step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16248step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16248step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16248step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16248step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16249step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16249step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16249step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16252step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16252step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1]]
def raw16252step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16252step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16252step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16252step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16253step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16253step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16253step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16253step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16254step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16254step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16255step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16257step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16257step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16257step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16257step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw16257step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16257step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]
def raw16257step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16257step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw16257step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16258step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16259step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16262step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16262step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16262step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16262step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16265step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16267step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16267step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16269step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16269step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw16269step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16270step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw16270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw16273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw16273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16273step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16273step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16274step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw16274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16274step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16274step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16275step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16275step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw16275step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw16278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw16278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16278step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![3, -2, -1]]
def raw16278step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16278step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16278step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16278step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16278step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1]]
def raw16279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16279step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16279step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1]]
def raw16282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16282step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1]]
def raw16283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16283step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16283step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16283step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16283step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16283step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw16284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16284step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16284step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16284step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16284step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16284step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16286step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16287step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16287step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16287step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16287step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16288step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16288step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16290step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16291step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16291step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16291step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16291step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16292step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16292step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![2, -1, -1]]
def raw16293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16294step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16295step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw16296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw16296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw16296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16296step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16296step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16296step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![3, -2, -1]]
def raw16297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw16297step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw16297step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16297step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw16297step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16298step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16298step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16298step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16298step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16299step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16299step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16299step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16299step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw16300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw16300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw16300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16300step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16300step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16300step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16300step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1]]
def raw16301step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16301step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16301step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16302step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1]]
def raw16304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw16304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16304step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16304step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1]]
def raw16305step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16305step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw16305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16305step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16305step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw16306step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16314step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![2, -1, -1]]
def raw16315step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw16318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw16318step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw16318step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![3, -2, -1]]
def raw16319step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw16319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw16319step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16321step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw16322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw16322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw16322step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16322step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16323 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16323step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16324 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16325 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16325step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16325step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw16326step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16326step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw16326step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16326step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw16326step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16327 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16327step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16327step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16327step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16327step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16328 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16328step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16328step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16328step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16328step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16328step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16328step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16329 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16329step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16329step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16329step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16329step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16329step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16330step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16330step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16330step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16330step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16331 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16331step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16331step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16331step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw16332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16332step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16332step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16332step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16332step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16333 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16333step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16333step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16333step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16333step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw16334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16334step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16334step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16334step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16334step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16335 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16335step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16335step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16335step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16335step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16336 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw16336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16336step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16336step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16336step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16397Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16397step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16397step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16397step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16397step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16397step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16398step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16399Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16399step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16399step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16399step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16399step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16399step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16400step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16400step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16401Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16401step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16401step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16401step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16401step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16402step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16402step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16402step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16402step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16403step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16404step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16404step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16404step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16405step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16405step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16405step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16406step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16406step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16407step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16407step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16409step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16409step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16411step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16411step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16412step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16412step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16412step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16413step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16413step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16413step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16414step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16414step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16415step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16415step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16416step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16416step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16416step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16417step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16418step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16419Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16419step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16420step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16420step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw16421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw16421step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16421step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16422step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16422step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16423step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-2, 1, 1], ![-2, -1, 3]]
def raw16423step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw16423step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16423step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw16423step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16425step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw16426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw16426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16433 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![-1, 1], ![1, -1]]
def raw16433Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16433step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw16433step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16433step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw16433step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16443step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16444step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16445step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16445step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16445step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16445step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16446step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16446step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16446step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16447step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16447step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16447step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16447step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16447step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16448step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16449step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16449step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16450step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16450step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16450step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16451step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16451step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16452step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16454step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16455step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16455step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16455step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16456step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16456step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16457step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16458step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16459step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16460step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16460step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16460step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16461step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16461step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16461step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16461step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16462step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16465step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16467step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16467step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16468step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw16468step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16468step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw16468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16469step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16469step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16469step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16469step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16470step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16470step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16470step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16470step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw16471step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16471step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16471step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16471step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16472step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16474step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16475step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16476step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw16480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw16481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw16498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw16501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16502step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16502step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16502step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16503step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16504step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16506step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16507step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16507step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16507step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16508step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16509step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16509step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16509step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16510step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16510step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16510step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16511step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16511step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16511step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16513step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16513step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16514step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16515step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16515step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw16518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16518step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16519step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16520step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16520step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16521step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16521step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16522step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16525step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16527step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw16527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16527step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16527step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16531step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16538 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw16538Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16538step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw16538step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16538step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw16538step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16538step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw16538step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16557step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw16563step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16563step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16563step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16563step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16566 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16569step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16571 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw16572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw16572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16573 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16573step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16573step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16574 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16574step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw16574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw16574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16575 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw16575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw16577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16578 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw16578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16579 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16581 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw16581step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16582 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16583Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16583step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16583step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16583step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16583step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16584Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16584step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16584step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16584step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16584step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16584step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16584step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16585Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16585step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16585step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16585step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16585step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16585step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16586Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16586step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16586step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16586step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16586step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16586step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16587 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16587Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16587step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16587step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16587step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16587step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16588 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16588Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16588step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16588step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16588step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16588step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16589 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16589Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16589step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16589step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16590Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16590step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16590step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16590step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16590step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16590step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16591 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16591step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16591step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16591step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16591step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16592 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16593step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16593step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16593step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw16594step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16594step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16594step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16594step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16595step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16595step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw16598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw16600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw16601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw16634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw16634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw16635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1664 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1664Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw1664step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw1664step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw1664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1665step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1667Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw1667step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1667step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1667step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1667step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1668 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1668step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1669 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1670 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1670Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw1670step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw1670step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw1670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1671 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1671step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1672 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1673 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1673Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw1673step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1673step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1674 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1674step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1675 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1676 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1676Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw1676step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw1676step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw1676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1677 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 1, -3], ![-2, 3, -1]]
def raw1677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1677step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1677step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1678 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 1, -3], ![-2, 3, -1]]
def raw1678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1678step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1679 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 1, -3], ![-2, 3, -1]]
def raw1679Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1679step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw1679step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1679step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1686step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1687 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1688 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1688Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1688step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1689 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1689step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1690 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1691Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1691step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1691step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1691step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1691step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1692step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1694Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1694step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1694step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1694step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1695step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1695step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1697Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1697step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1697step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1697step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1697step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1698step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1700Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1700step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1700step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1701step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw16640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw16642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw16643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw16646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw16647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw16648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16650step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16650step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw16652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw16653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw16656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw16656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw16657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw16657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw16658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw16661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw16661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw16661step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16661step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16663step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16664step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16665step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16666step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16666step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16667step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw16669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16671step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16672step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw16673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16676step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16680step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16680step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16680step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16680step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16681step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16681step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16681step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16682step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16686step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16687step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16692Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16692step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16692step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16693Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16693step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16693step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16694Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16694step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16695Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16695step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16695step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16696Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16696step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16696step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16697Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16697step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16697step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16697step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16697step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16697step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16698Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16698step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16698step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16699step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16699step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16700step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16700step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16701step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16701step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16701step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16702step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16703step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16706step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw16717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw16717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16717step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw16717step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw16723step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw16723step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw16723step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw16725step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw16725step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw16725step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16727 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16727step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16727step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16727step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16728 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16730step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw16730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16730step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw16730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw16731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw16731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16733step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw16735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw16735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16737step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16737step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16737step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16737step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16738step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16738step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16738step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16738step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16739step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16739step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16739step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16740step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16740step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16740step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16741step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16742step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16743step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16744step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16745step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16746step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16751step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16756step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16758step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16758step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16758step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16758step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16759step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16759step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16760step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16760step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16760step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16760step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw16761step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16761step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16761step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16761step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw16762step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16762step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16762step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw16765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16765step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16774step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16776step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw16787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw16791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw16792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw16795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16796step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16797step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16797step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16800step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16801step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16805step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16805step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16806step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16808step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16809step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16810step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16810step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16811step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16811step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16813step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16813step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16814step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16815step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16815step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16816step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16819step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw16821step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16821step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw16821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw16825step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16825step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16832 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw16832Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16832step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw16832step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16832step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw16832step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw16837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16838 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16838step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16838step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16838step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16840step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16840step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16841 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16842 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16843step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16844 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16844step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16844step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16845step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16845step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16845step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16846step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16846step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16847step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16847step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16847step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16848 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16849 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16849step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16849step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16850 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16850step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16850step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16850step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16850step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16851 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16851step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16852 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16852step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16852step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16852step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16853 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16854 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16854step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16854step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16854step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16855 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16855step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16855step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16855step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16856step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16857step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16858 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16858step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16858step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16859 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw16859step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16859step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16859step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16860 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16860step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16860step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16860step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16861 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16861step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16862 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16862step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16863 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16863step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16864 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16865 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16865step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16866 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16867 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16868 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16869 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16870 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16873 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16874 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16875 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16876 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16877 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16878 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16879 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16882 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16883 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16884 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16888step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16888step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16891 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16891step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16891step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16892 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16893 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16894 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16895 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16895step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16896 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16896step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16896step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16897 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16897step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16899step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16901step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16903Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16903step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16903step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16903step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16904Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16904step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16905Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16905step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16906Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16906step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16907 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16907Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16907step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16908Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16908step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16908step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16908step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16909Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16909step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16909step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16909step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16909step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16909step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16909step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16910 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16910Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16910step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16910step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16910step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16910step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16910step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16911 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16911Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16911step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16911step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16911step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16912 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16912Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16912step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16912step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16912step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16913 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16913Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16913step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16913step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16913step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16914Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16914step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16914step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16914step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16914step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16915 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16915Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16915step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16915step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16915step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16915step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16915step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16916 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16916Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16916step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16918 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16919 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16919step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16920 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16921 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw16921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16921step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw16975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw16976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw16977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw16978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw16981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw16981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw16982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw16983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw16984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw16985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw16986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw16986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17017step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17023 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]
def raw17023Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17023step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw17023step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17023step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw17023step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17023step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17023step2Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw17024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw17024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw17027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw17027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw17027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw17028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17029 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17030 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17031 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17031step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17032 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17033 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17034step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17035step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17035step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end


