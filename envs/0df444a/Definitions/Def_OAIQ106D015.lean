-- Prove2me | Definitions.Def_OAIQ106D015
-- name    : OAIQ106D015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:04:29.466308+00:00
-- url     : https://prove2.me/theorems/066a55f3-651c-464c-836c-177bd44bf0b4
-- title:
--   Definitions bundle OAIQ106D015 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4229 declarations of OpenAI's Lean: 4229 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw18677step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18677step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18677step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18677step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18677step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18678`, `OAI.MUB6.Certificate.MixedSemantics.raw18678Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18678step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18678step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18678step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18678step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18678step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18678step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18679`, `OAI.MUB6.Certificate.MixedSemantics.raw18679Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18679step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18679step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18679step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18679step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18679step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18679step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18679step3`, `OAI.MUB6.Certificate.MixedSemantics.raw18679step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18680`, `OAI.MUB6.Certificate.MixedSemantics.raw18680Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18680step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18680step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18680step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18680step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18680step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18680step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18681`, `OAI.MUB6.Certificate.MixedSemantics.raw18681Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18681step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18681step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18681step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18681step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18681step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18681step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18682` and 4189 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical14.lean), [`MutuallyUnbiased_MixedSemantics_Canonical145`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical145.lean), [`MutuallyUnbiased_MixedSemantics_Canonical146`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical146.lean), [`MutuallyUnbiased_MixedSemantics_Canonical147`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical147.lean), [`MutuallyUnbiased_MixedSemantics_Canonical148`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical148.lean), [`MutuallyUnbiased_MixedSemantics_Canonical149`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical149.lean), [`MutuallyUnbiased_MixedSemantics_Canonical15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical15.lean), [`MutuallyUnbiased_MixedSemantics_Canonical150`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical150.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound979`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988`.
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]

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

def raw19269step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


