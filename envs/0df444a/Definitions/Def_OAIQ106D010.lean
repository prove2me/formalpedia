-- Prove2me | Definitions.Def_OAIQ106D010
-- name    : OAIQ106D010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:01:31.044217+00:00
-- url     : https://prove2.me/theorems/af0d0854-3a43-4aee-a6f5-7b826dc4c247
-- title:
--   Definitions bundle OAIQ106D010 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6182 declarations of OpenAI's Lean: 6182 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw15484step2`, `OAI.MUB6.Certificate.MixedSemantics.raw15485`, `OAI.MUB6.Certificate.MixedSemantics.raw15485step0`, `OAI.MUB6.Certificate.MixedSemantics.raw15485step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15485step1`, `OAI.MUB6.Certificate.MixedSemantics.raw15485step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15485step2`, `OAI.MUB6.Certificate.MixedSemantics.raw15485step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15486`, `OAI.MUB6.Certificate.MixedSemantics.raw15486Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15486step0`, `OAI.MUB6.Certificate.MixedSemantics.raw15486step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15486step1`, `OAI.MUB6.Certificate.MixedSemantics.raw15486step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15486step2`, `OAI.MUB6.Certificate.MixedSemantics.raw15486step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15487`, `OAI.MUB6.Certificate.MixedSemantics.raw15487Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15487step0`, `OAI.MUB6.Certificate.MixedSemantics.raw15487step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15488`, `OAI.MUB6.Certificate.MixedSemantics.raw15488Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15488step0`, `OAI.MUB6.Certificate.MixedSemantics.raw15488step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15488step1`, `OAI.MUB6.Certificate.MixedSemantics.raw15488step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15489`, `OAI.MUB6.Certificate.MixedSemantics.raw15489Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15489step0`, `OAI.MUB6.Certificate.MixedSemantics.raw15489step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw15489step1`, `OAI.MUB6.Certificate.MixedSemantics.raw15489step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1548Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1548step0`, `OAI.MUB6.Certificate.MixedSemantics.raw1548step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1548step1`, `OAI.MUB6.Certificate.MixedSemantics.raw1548step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1549`, `OAI.MUB6.Certificate.MixedSemantics.raw15490`, `OAI.MUB6.Certificate.MixedSemantics.raw15490Labels` and 6142 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical12`, `MutuallyUnbiased_MixedSemantics_Canonical120`, `MutuallyUnbiased_MixedSemantics_Canonical121`, `MutuallyUnbiased_MixedSemantics_Canonical122`, `MutuallyUnbiased_MixedSemantics_Canonical123`, `MutuallyUnbiased_MixedSemantics_Canonical124`, `MutuallyUnbiased_MixedSemantics_Canonical125`, `MutuallyUnbiased_MixedSemantics_Canonical126`, `MutuallyUnbiased_MixedSemantics_Canonical127`, `MutuallyUnbiased_MixedSemantics_Canonical128`, `MutuallyUnbiased_MixedSemantics_Singletons44`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2041`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2045`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound818`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound821`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound843`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound851`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound855`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound892`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911` and `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments`.
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

def raw154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw154step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw155 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw155Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw155step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw155step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw156 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw156step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw157 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw157Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw157step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw157step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw158 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 1, 1], ![0, 2, -2]]
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

def raw1548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1548step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1549 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1550 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1550Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw1550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw1550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1554 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1554step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1555 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1556Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1556step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1557 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1557step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1558 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1559 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1559Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw1559step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1560 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1560step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1561 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1562 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1562Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1562step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1563 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1563step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1564 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1565 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1565Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1565step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1565step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1566 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1566step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1567 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1568 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1568Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1569 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1569step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1570 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1571 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1571Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1571step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1571step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1572 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1572step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1573 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1574 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1574Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1574step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1575 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1575step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1576 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1577 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1577Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1577step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1577step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1578 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1578step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1579 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1580 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1580Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1580step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1580step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1581 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1581step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1581step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1582 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1582step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1583 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1583Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1583step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw1583step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw1583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1584 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 2, -1], ![-1, 3, -2]]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw15485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]

def raw15485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15485step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15485step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw15486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15486step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15486step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw15504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw15508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15509step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15509step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15511step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15514step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15514step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15515step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15515step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15517step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15517step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15518step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15519step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15520step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15520step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15521step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15521step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15525step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw15526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15527step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw15530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw15534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15546step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15546step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15546step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15546step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15547step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15548step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15548step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15548step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15548step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15549step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15550step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15551step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15551step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15551step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw15552step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15552step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15552step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15552step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15553step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15554step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15555step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15556step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15556step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15556step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15557step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15558step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15559step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15560step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15561step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15561step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15561step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15562step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15563step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw15568step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw15568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15569step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15569step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15569step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15570step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15570step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15571step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15571step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw15572step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15572step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15572step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw15582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw15598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw15602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15603step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15603step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15605step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15607step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15611step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15611step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw15612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15612step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15613step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15613step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15615step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15617step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15617step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15619step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15620step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15621step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15622step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15623step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw15628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw15628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw15628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15639 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw15639Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15639step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw15639step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15639step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw15639step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15639step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw15639step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw15644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15661step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15664 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15664step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15664step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15664step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15665step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15665step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15669step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15682step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15682step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15682step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15683step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw15694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15699step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15702step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15706 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15707 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15711 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw15714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15715 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15716 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15717step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15717step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15718step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15719step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15721 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15722 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15722step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15723step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15723step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15724step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15726step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15727step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15727step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15728step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15729step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15729step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15730step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15731step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15734step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw15736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15738 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15739 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15740 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15741 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15742 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw15744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15746 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15751 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw15754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15756 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15757 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw15791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw15791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15795step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15796step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15798step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15800step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15802step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15802step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15804step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15805step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15805step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw15809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15809step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw15813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw15831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw15835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15837step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15839step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15840step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15840step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw15841step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15841step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15842step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15843step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15844step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15845step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15845step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15846step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
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

def raw16504step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2832 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


