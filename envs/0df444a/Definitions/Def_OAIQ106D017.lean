-- Prove2me | Definitions.Def_OAIQ106D017
-- name    : OAIQ106D017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:04:51.125584+00:00
-- url     : https://prove2.me/theorems/932919c7-9ce8-4a13-8e75-ef4999105880
-- title:
--   Definitions bundle OAIQ106D017 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5084 declarations of OpenAI's Lean: 5084 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw19925step0`, `OAI.MUB6.Certificate.MixedSemantics.raw19925step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19925step1`, `OAI.MUB6.Certificate.MixedSemantics.raw19925step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19925step2`, `OAI.MUB6.Certificate.MixedSemantics.raw19925step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19925step3`, `OAI.MUB6.Certificate.MixedSemantics.raw19925step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19926`, `OAI.MUB6.Certificate.MixedSemantics.raw19926Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step0`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step1`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step2`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step3`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step4`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step4Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step5`, `OAI.MUB6.Certificate.MixedSemantics.raw19926step5Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19927`, `OAI.MUB6.Certificate.MixedSemantics.raw19927Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step0`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step1`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step2`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step3`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step4`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step4Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step5`, `OAI.MUB6.Certificate.MixedSemantics.raw19927step5Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19928`, `OAI.MUB6.Certificate.MixedSemantics.raw19928Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw19928step0`, `OAI.MUB6.Certificate.MixedSemantics.raw19928step0Labels` and 5044 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical15.lean), [`MutuallyUnbiased_MixedSemantics_Canonical155`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical155.lean), [`MutuallyUnbiased_MixedSemantics_Canonical156`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical156.lean), [`MutuallyUnbiased_MixedSemantics_Canonical157`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical157.lean), [`MutuallyUnbiased_MixedSemantics_Canonical158`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical158.lean), [`MutuallyUnbiased_MixedSemantics_Canonical159`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical159.lean), [`MutuallyUnbiased_MixedSemantics_Canonical16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical16.lean), [`MutuallyUnbiased_MixedSemantics_Canonical160`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical160.lean), [`MutuallyUnbiased_MixedSemantics_Singletons19`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Singletons19.lean), [`MutuallyUnbiased_MixedSemantics_Singletons44`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Singletons44.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2359`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1098`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1031`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1071`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound934` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982`.
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

def raw1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw1step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw19Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw19step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw20 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]

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

def raw199Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw199step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw200 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw200step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw201 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw201Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw201step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw204 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-2, 2, 0], ![0, 3, -3]]
def raw204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw204step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw205 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-2, 2, 0], ![0, 3, -3]]

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
def raw1994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1994step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1995 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1995step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1996 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1997 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1997Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1997step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1997step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2007 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2007step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2008 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2009 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2009Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2009step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2009step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2010 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2010step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2010step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2011 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2012 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2012Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2012step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2013 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2013step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2014 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2015 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2015Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw2015step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2016 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2016step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2017 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2018 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2018Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw2018step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2019step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2021 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2021Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2021step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2021step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2021step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2022 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2022step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2023 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2024 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2024Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw2024step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw2024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2025 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2025step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2026 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2027 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2027Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw2027step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2027step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2028 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2028step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2028step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2029 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2030 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2030Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2030step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2031 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 1, -2], ![-1, 3, -2]]
def raw2031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2031step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw2031step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw2031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2032 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 1, -2], ![-1, 3, -2]]
def raw2032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2032step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw2032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2033 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 1, -2], ![-1, 3, -2]]
def raw2033Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2033step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw2033step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw2033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2034 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 2, -3]]
def raw2034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2034step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw2034step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw2034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2035 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 2, -3]]
def raw2035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2035step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw2035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2036 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 2, -3]]
def raw2036Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2036step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw2036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw2036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2043step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2043step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2044 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2045Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw2045step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw2045step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2045step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw2045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw19950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19950step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19951step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19952step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![5, -2, -3]]
def raw19952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19952step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19953 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw19953Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19953step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw19953step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19953step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]
def raw19953step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19953step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]
def raw19953step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19953step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw19953step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19954 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19954step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -3, 4]]
def raw19954step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19954step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19954step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19954step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19954step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19955 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19955step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19955step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19955step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19956 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19956step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19956step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19956step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19957 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19957step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -3, 4]]
def raw19957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19957step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19957step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19957step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19957step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19958 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19958step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19958step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19958step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19958step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19959 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19959step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19959step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19959step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19959step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19960 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19960step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -3, 4]]
def raw19960step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19960step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19960step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19960step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19960step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19961 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19961step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19961step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19961step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19962 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19962step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19962step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19963 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19963step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -3, 4]]
def raw19963step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19963step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19963step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19963step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19963step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19964 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19964step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19964step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19964step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19964step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19965 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19965step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19965step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19965step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19965step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19965step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19966 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19966step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19966step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19967step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -4, 4]]
def raw19967step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 4, -4], ![0, -4, 4]]
def raw19967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![4, -4], ![-4, 4]]
def raw19967step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw19967step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]
def raw19967step5Labels : Fin 2 → Fin 3 := ![1, 2]

def raw19967step6 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]
def raw19967step6Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19968 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19968step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19968step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19968step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19968step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw19968step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19968step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19968step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19968step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19968step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19969 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19969step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19969step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw19969step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19969step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19969step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19969step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19969step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19970 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19970step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19970step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19970step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19970step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw19970step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19970step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19970step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19970step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19970step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw19971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19971step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw19972step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19972step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19973step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw19973step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19974step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![4, 0, -4]]
def raw19974step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19974step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw19974step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw19974step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw19974step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw19974step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw19974step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw19974step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw19974step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19975step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![3, 1, -4]]
def raw19975step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19975step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19975step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19975step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19975step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw19976step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19978step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw19979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def raw19979step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw19980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw19981step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19983step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19984step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19984step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw19984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19984step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def raw19984step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw19985step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw19986step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19987step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw19989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19989step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def raw19989step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw19990step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19991step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw19991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19992step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19994step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19994step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw19995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw19995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw19995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19995step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw19995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![5, -1, -4]]
def raw19996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-5, 2, 3]]
def raw19996step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw19996step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19997step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19997step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19998step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19999step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![5, -1, -4]]
def raw20000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 0, 1], ![-4, 1, 3]]
def raw20000step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![4, -1, -3]]
def raw20000step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20002step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20003step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20004step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20004step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![4, 0, -4]]
def raw20004step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20004step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw20004step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20004step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw20004step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20004step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw20004step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20005step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20005step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![3, 1, -4]]
def raw20005step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20005step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20005step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20005step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20005step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20006step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20006step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20006step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20008step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20009step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20009step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20010step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20010step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20011step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20011step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20013step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20014step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20015step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20015step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20016step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20017Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20017step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20017step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20018step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20019Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20019step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20019step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20019step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20019step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20020step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20020step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20020step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20021Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20021step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20021step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20021step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20021step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20021step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw20021step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20021step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw20021step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20022step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20022step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20022step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20022step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20022step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20022step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20023Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20023step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20023step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20023step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20023step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20023step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20024Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20024step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20024step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20024step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20024step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20024step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20024step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20025step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20025step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20025step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20025step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20025step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20025step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20025step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20025step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20026step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20026step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20026step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![5, -1, -4]]
def raw20026step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20026step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw20026step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20026step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw20026step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20027Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20027step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20027step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20027step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20028step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20028step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20028step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20028step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20029step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20030step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20030step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![5, -1, -4]]
def raw20030step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20030step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![3, 1, -4]]
def raw20030step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20030step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![3, 1, -4]]
def raw20030step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![4, 0, -4]]
def raw20031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw20031step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw20031step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20033step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20035step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![5, -1, -4]]
def raw20036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-5, 2, 3]]
def raw20036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw20036step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20037 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![4, -4]]
def raw20037Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20037step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![4, -4]]
def raw20037step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20037step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![4, -4]]
def raw20037step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20037step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw20037step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20037step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw20037step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20037step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw20037step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20042step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20042step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20042step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20045step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20045step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20046step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20046step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20047step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20048step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20048step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20049step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20067step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20067step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20067step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20067step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20067step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20068step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20068step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20068step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20068step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20068step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20069step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20069step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20069step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20069step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20070step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20070step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20070step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20070step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20070step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20071step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20071step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20071step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20071step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20071step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20072step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20072step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20072step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20072step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20073step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20073step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20073step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20073step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20073step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20074step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20074step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20074step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20074step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20074step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20075step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20075step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20075step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20075step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20075step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20075step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20076step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20076step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20076step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20076step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20077step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20077step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20077step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20077step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20078step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20078step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20078step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20078step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20078step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20078step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20079step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20079step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20079step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20079step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20080step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20080step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20080step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20080step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20081step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20081step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20081step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20081step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20082step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20082step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20082step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20083step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20083step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20083step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20083step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 5, 0], ![5, -5, 0]]
def raw20083step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20083step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]
def raw20083step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20084step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20084step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20084step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20084step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![5, -5]]
def raw20084step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20084step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-4, 4]]
def raw20084step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20084step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20084step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20085step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20085step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20085step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20085step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20085step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![5, -5]]
def raw20085step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20085step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-4, 4]]
def raw20085step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20085step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20085step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20086step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20086step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20086step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20086step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20086step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![5, -5]]
def raw20086step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20086step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-4, 4]]
def raw20086step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20086step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20086step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20087Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20087step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20087step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20087step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20087step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20087step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![5, -5]]
def raw20087step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20087step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-4, 4]]
def raw20087step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20087step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20087step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20088step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw20092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw20092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw20092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20092step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 1, -3], ![2, -2, 0]]
def raw20092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20092step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw20092step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-3, 0, 3]]
def raw20093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw20093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw20093step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20094 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def raw20094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20095 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def raw20095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20096 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def raw20096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20097 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20097step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-3, 0, 3]]
def raw20097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20097step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20097step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20098 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw20098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw20098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw20098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20098step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![2, -3, 1], ![-4, 1, 3]]
def raw20098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20098step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw20098step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20099 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![-3, 3]]
def raw20099Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20099step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![-1, 1], ![-3, 3]]
def raw20099step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20099step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-1, 1], ![-3, 3]]
def raw20099step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20099step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw20099step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20099step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw20099step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw20100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20100step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw20100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw20101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20101step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw20101step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw20102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw20102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]
def raw20103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw20103step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw20103step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![-2, -1, 3]]
def raw20104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw20104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw20104step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20105 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -2, 3], ![-3, 2, 1]]
def raw20105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw20105step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20106 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -2, 3], ![-3, 2, 1]]
def raw20106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20106step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw20106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -2, 3], ![-3, 2, 1]]
def raw20107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20107step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw20107step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw20111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw20111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw20111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw20116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw20116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw20116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw20116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw20119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw20119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw20119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw20120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw20120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw20120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw20120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20120step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20121 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20122 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20123 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20124 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw20124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw20124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw20124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20129 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20130 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw20130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw20130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20131 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw20131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw20131step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20132 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw20132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw20132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20133step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20134 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20135 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20136step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw20140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20140step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw20140step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw20141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw20141step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw20141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw20141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20142 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]
def raw20142Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20142step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw20142step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20142step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw20142step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20142step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw20142step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20142step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw20142step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20143step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20143step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20143step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw20143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20143step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20143step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20144Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20144step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20145Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20145step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20145step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw20146Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw20146step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw20146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw20147Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw20147step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw20147step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, -1, 2], ![-4, 3, 1]]
def raw20147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw20147step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20148 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20148Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20148step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw20148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20148step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw20148step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20149 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20149step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20150 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20151 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20151step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20152 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20153 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20153step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20153step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20154 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20154Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw20154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw20154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20155 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20155Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw20155step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw20155step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20156 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20156Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20156step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![3, -3, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20156step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw20156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20156step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw20156step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20157 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20157Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw20157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20157step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw20157step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20158 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20158Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20158step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw20158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20158step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw20158step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20159 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20159Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw20159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw20159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20160 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20160Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw20160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw20160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20161 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20161step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20161step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20162 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw20162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw20162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20163 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw20163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw20163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20164 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw20164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw20164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw20165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw20165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20166 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20166Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw20166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def raw20166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw20170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20170step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw20174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw20174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw20174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![4, -1, -3]]
def raw20175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![4, -1, -3]]
def raw20175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![4, -1, -3]]
def raw20175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, -1, 2], ![-4, 3, 1]]
def raw20175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20175step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw20175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20176 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![3, -3]]
def raw20176Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20176step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-2, 2], ![3, -3]]
def raw20176step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20176step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![3, -3]]
def raw20176step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20176step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]
def raw20176step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20176step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw20176step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20176step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw20176step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20177 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20178 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20179 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw20179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw20179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw20179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20179step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20190step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw20194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw20194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw20195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw20195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20196 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw20196Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20196step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw20196step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20196step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw20196step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw20197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20197step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw20201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20202 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20203 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20204 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20205 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20209 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw20209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20210 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20211 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20211step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20212 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw20212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20213 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20213step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20214 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw20214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw20220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw20220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw20220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw20224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20225 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20226 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20227 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw20227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw20227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw20231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20231step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20232step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw20232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw20232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw20233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw20233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw20234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw20234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw20234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw20234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw20235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw20235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw20235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20236 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![3, -3]]
def raw20236Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20236step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![3, -3]]
def raw20236step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20236step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw20236step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20236step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw20236step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw20238step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20243 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw20243Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20243step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw20243step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20243step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw20243step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20244Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20245Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw20247Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw20247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw20247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20248Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20249Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20250Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw20251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw20251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw20251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20252Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20252step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20253Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20255 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20255step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20255step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20256 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw20256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20256step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def raw20256step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20257 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw20257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20258 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20258step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw20258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20259 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20259step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20260 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20260step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20262step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20262step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20262step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20263 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20263step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20264 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20264step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20264step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20265 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20265step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20265step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw20265step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20266 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20267 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20268 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20268step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20268step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20269 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20269step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20269step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20269step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20270 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20271 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw20273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20273step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![3, -1, -2]]
def raw20273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw20274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw20275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw20276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw20276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20276step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw20276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw20281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw20281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20282step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20283 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]
def raw20283Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20283step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]
def raw20283step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20283step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw20283step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw20286Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw20287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw20287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw20287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20289Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20290step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw20291Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw20291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20291step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20292Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20292step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw20293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw20293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -3, -1]]
def raw20294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![4, -3, -1]]
def raw20294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20295 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20295Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20296 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw20296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw20296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20297 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20298 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20298Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20298step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20299 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20300 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20301step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20302step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, -2, 3]]
def raw20303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20303step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw20303step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20304 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20305 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20305step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20305step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20306 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20307 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20308 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20309 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20310 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw20311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw20313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw20314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw20314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw20314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw20316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw20316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw20319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw20319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw20319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20321 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw20321Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20321step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]
def raw20321step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20321step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw20321step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw20323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw20325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw20325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw20325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw20327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw20327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw20329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw20330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw20330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw20330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw20330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw20330step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw20331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw20331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20332 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![0, 0], ![3, -3]]
def raw20332Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20332step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![3, -3]]
def raw20332step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20332step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw20332step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20332step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw20332step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20332step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw20332step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw20334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw20337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20339 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw20339Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20339step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw20339step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw20343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw20345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20345step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw20346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw20347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw20348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw20348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw20348step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20350 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]
def raw20350Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20350step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw20350step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20350step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw20350step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20350step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw20350step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20351step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20351step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20351step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20352step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20354step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20354step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20354step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20355step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20356step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20357step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20357step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20357step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20357step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20357step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20358step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20359step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20359step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20360step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![3, -1, -2]]
def raw20360step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20360step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw20360step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20360step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw20360step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20361step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20361step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20361step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20362step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20362step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20362step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20362step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20363step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20363step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20363step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20363step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20363step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20364step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20364step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20366step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20367step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20367step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20370step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw20370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw20374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20378step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20378step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![3, -1, -2]]
def raw20378step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20378step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw20378step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20379step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20380step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20381step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20381step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20381step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw20382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw20382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw20382step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20382step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw20382step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20382step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw20382step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw20383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw20383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw20383step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20383step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![4, -2, -2]]
def raw20383step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20383step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw20383step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20383step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw20383step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20384step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20384step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20386step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20387step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20387step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20388step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20388step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20389step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20390step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20390step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20390step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20391step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20392step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20392step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20393step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![3, -2, -1]]
def raw20393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20393step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw20393step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20393step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw20393step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20394step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20394step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20394step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20395step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20395step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20396step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20396step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20396step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20397step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20400step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20401step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20404step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20405step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20405step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20405step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20408step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20409step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20409step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![3, -2, -1]]
def raw20409step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20409step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw20409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20410step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20411step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20412step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20412step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20412step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw20413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw20413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw20413step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20413step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw20413step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20413step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw20413step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20414 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20414step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20414step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20414step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20414step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20415 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20415step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20415step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20416 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20416step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20416step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20417 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20417step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, -2, 3]]
def raw20417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20417step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw20417step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20417step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw20417step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20418 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20418step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw20418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20418step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20418step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20418step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20418step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20419 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20419step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20419step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20419step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20420 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20420step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20421 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20421step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20421step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20422 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20422step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20422step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20422step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20423 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20423step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20423step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20423step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20423step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20423step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20424 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20424step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20424step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20424step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20424step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20425 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20425step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20426 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20426step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20427 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20427step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20427step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20427step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20427step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20428 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20428step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20428step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20428step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20428step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20429 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20429step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20429step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20430 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20430step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20431 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20431step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20431step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20432 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20432step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20432step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20432step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20432step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20433 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20433step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20433step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20433step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20434 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20434step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, -2, 3]]
def raw20434step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20434step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20434step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20434step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20434step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20435 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20435step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20435step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20435step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20435step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20436 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20436step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20436step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20436step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20436step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20437 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20437step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20437step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20437step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20437step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20438 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20438step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20438step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20438step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20438step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20438step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20438step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20439 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20439step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -3, 3]]
def raw20439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20439step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20439step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20439step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20439step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20440 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20440step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20440step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20440step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20440step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20440step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20441 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20441step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20441step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20441step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20441step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20442 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20442step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20442step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20442step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20442step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20442step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20443 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20443step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -3, 3]]
def raw20443step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20443step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20443step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20443step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20443step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20444 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20444step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20444step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20444step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20444step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20445 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20445step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20445step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20445step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20446 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20446step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20447 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20447step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20447step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, -2, 3]]
def raw20447step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20447step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw20447step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20447step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw20447step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20448 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20448step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20448step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20448step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw20448step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20448step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20448step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20448step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20448step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20449 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20449step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20449step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20449step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20449step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20450 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20451 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20452 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20452step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20452step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20453 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20453step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20453step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20453step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20453step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20454 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20454step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20454step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20454step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20455 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20455step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20455step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20456 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20456step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20457 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20457step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20457step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20457step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20457step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20457step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20458 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20458step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20458step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20458step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20458step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20458step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20458step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20458step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20459 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20459Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20459step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20459step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20459step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20459step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20459step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20459step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20460 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20460step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20461 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20461Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20461step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20461step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20462 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20462step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20462step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20462step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20462step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20462step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20462step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20462step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20463 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20463Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20463step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20463step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20463step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20463step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20463step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20463step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20464 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20464step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20464step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20464step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, -2, 3]]
def raw20464step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20464step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![3, -2, -1]]
def raw20464step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20464step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![3, -2, -1]]
def raw20464step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20465 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20465Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20465step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20465step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20465step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20465step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20465step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20465step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20466 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20466Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20466step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20466step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20466step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20466step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20466step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20467 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20467Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20467step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20467step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20467step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20467step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20467step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20468 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20468Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20468step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20468step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20468step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20468step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20468step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20468step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20468step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20468step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20469 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20469Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20469step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20469step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20469step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -3, 3]]
def raw20469step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20469step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw20469step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20469step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw20469step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20470 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20470step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20470step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20470step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20470step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20470step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20470step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20471 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20471Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20471step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20471step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20471step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20471step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20472 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20472Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20472step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20472step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20472step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20472step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20472step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20472step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20473Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20473step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20473step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20473step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -3, 3]]
def raw20473step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20473step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw20473step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20473step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw20473step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20474 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20475 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, -2, 3]]
def raw20476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw20476step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw20476step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20477 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20477step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw20477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20477step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw20477step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20478step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, -2, 3]]
def raw20479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw20479step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw20479step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2049step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2050 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2051Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw2051step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2051step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw2052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw2052step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw2052step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -3, 3]]
def raw20480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw20480step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw20480step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20481step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20483step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20483step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20484step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20486step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20486step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20486step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20487step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20487step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20488step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20488step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20489step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20489step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20489step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20490step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20490step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20491step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20491step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20492step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20492step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20492step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20492step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20493step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20493step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20493step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20494step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20494step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20494step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20495step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20495step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20495step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20496step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw20496step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw20496step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20497step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20500step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20503step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20506step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20506step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20506step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20507step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20508step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20509step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20510step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20510step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20510step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20511step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20511step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20511step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20511step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20511step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20512step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20513step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20513step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20514step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20514step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20514step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20514step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20515step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20516step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20517step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20517step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20517step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20517step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20517step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20520step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20520step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-3, 1, 2]]
def raw20520step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20520step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw20520step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20520step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw20520step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20521step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20521step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20521step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20522step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20522step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20523step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20523step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20523step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20534step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20534step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20535step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20536step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20536step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20537step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20537step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20537step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1265 : Fin 2 → Fin 1 := ![0, 0]

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

def singletonSmall2829 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


