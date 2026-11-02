-- Prove2me | Definitions.Def_OAIQ106D031
-- name    : OAIQ106D031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:15:58.959031+00:00
-- url     : https://prove2.me/theorems/10308e2b-fe56-4477-b437-7eb5b5646e6b
-- title:
--   Definitions bundle OAIQ106D031 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7225 declarations of OpenAI's Lean: 7225 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw35974step2`, `OAI.MUB6.Certificate.MixedSemantics.raw35974step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35974step3`, `OAI.MUB6.Certificate.MixedSemantics.raw35974step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35975`, `OAI.MUB6.Certificate.MixedSemantics.raw35975Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35975step0`, `OAI.MUB6.Certificate.MixedSemantics.raw35975step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35975step1`, `OAI.MUB6.Certificate.MixedSemantics.raw35975step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35975step2`, `OAI.MUB6.Certificate.MixedSemantics.raw35975step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35975step3`, `OAI.MUB6.Certificate.MixedSemantics.raw35975step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35976`, `OAI.MUB6.Certificate.MixedSemantics.raw35976Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35976step0`, `OAI.MUB6.Certificate.MixedSemantics.raw35976step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35976step1`, `OAI.MUB6.Certificate.MixedSemantics.raw35976step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35976step2`, `OAI.MUB6.Certificate.MixedSemantics.raw35976step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35977`, `OAI.MUB6.Certificate.MixedSemantics.raw35977Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35977step0`, `OAI.MUB6.Certificate.MixedSemantics.raw35977step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35977step1`, `OAI.MUB6.Certificate.MixedSemantics.raw35977step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35977step2`, `OAI.MUB6.Certificate.MixedSemantics.raw35977step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35977step3`, `OAI.MUB6.Certificate.MixedSemantics.raw35977step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35978`, `OAI.MUB6.Certificate.MixedSemantics.raw35978Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35978step0`, `OAI.MUB6.Certificate.MixedSemantics.raw35978step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35978step1`, `OAI.MUB6.Certificate.MixedSemantics.raw35978step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35978step2`, `OAI.MUB6.Certificate.MixedSemantics.raw35978step2Labels` and 7185 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical28`, `MutuallyUnbiased_MixedSemantics_Canonical281`, `MutuallyUnbiased_MixedSemantics_Canonical282`, `MutuallyUnbiased_MixedSemantics_Canonical283`, `MutuallyUnbiased_MixedSemantics_Canonical284`, `MutuallyUnbiased_MixedSemantics_Canonical285`, `MutuallyUnbiased_MixedSemantics_Canonical286`, `MutuallyUnbiased_MixedSemantics_Canonical287`, `MutuallyUnbiased_MixedSemantics_Canonical288`, `MutuallyUnbiased_MixedSemantics_Canonical289`, `MutuallyUnbiased_MixedSemantics_Canonical29`, `MutuallyUnbiased_MixedSemantics_Canonical290`, `MutuallyUnbiased_MixedSemantics_Canonical291`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2087`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound93` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`.
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

def raw35Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw35step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw35step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw36 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw36Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw359Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw359step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw360 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3]]
def raw360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw360step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw361 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3]]
def raw361Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw361step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw362 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw362step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw363 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw363Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw363step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw364 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw364Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw365 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw365Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw365step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw366 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw366Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw366step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw367 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw367Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw367step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw368 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 3, -2]]
def raw368Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw368step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw368step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw369 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 3, -2]]
def raw369Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw369step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw369step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw370 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw370Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw371Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw371step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw372 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw372Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw372step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw373 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw3625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw3626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw3627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3628Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw3628step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3630 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]
def raw3630Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3630step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw3630step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3630step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw3630step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3630step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw3630step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw3643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![2, -1, -1], ![2, 0, -2]]
def raw3649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3653step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![3, -1, -2]]
def raw3653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw3654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3657step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw3657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3657step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw3657step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3657step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3657step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3657step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3657step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw3658step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3658step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3658step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3658step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3659step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3662 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3662step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3662step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3663step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3667step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3668step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3673step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3678step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-3, 0, 3]]
def raw3678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3678step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw3678step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3683step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]
def raw3683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3683step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3683step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3683step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3683step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3684step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3684step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3687step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3687step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw3687step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3687step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw3687step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3688step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3688step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3689step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw3689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3692step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3697step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3703step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3703step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3708step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-3, 0, 3]]
def raw3708step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-3, 3, 0]]
def raw3708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3708step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw3708step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35974step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35974step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35974step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35975step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35975step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35975step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35975step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35976step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35976step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35976step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35977step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35978step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35978step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35978step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35979step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35979step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35979step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw35980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw35980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35980step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw35980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35981step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35981step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35982step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35982step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35982step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35982step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35983step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35983step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35983step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35984step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35984step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35984step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw35985step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35985step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35987step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35987step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35988step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35989step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw35990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw35990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw35990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35992step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw35995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw35995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw35995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35997step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35997step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw35999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw35999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35999step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35999step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35999step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, -1, 3]]
def raw36000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw36000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw36000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw36001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36001step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw36002step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36002step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw36003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw36004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw36004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw36004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36004step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36039step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36039step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36039step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36040step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36040step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36040step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36040step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![2, 0, -2]]
def raw36041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36041step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36041step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36041step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36041step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36041step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36042step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36042step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36042step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36042step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36043step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw36044step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw36044step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw36044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw36045step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36045step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36045step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![2, 0, -2]]
def raw36046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw36046step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36046step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw36046step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36046step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw36046step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36047step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36047step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36047step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36047step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36050step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36050step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36050step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36050step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36051step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36051step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36051step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36052step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36052step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36053step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36053step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36055step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36055step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36055step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw36056step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw36056step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36056step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36056step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36056step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36057step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36057step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36057step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36058step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36058step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36060step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36060step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36060step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36060step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36061step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36061step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36061step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36061step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36062step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36062step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36063step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw36065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw36066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw36066step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw36067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw36067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36067step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw36067step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36068step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36068step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36068step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36068step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36068step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36069step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36069step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36069step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36070step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36070step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36070step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36071step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![2, 0, -2]]
def raw36071step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36071step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36071step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36071step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36071step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36071step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36072step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36073step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw36073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw36073step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36073step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw36073step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36075step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36075step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36075step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36075step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36076step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![2, 0, -2]]
def raw36076step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36076step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw36076step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36076step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw36076step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36077step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36077step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw36078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw36078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw36078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36079step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36079step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36079step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36081step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36081step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36081step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36081step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36081step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36082step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36083step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw36083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw36083step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36083step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw36083step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36084step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36084step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36084step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36084step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36085step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36086step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw36086step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36086step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw36086step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36086step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36086step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36086step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36086step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36087step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36087step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36087step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36087step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw36088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw36088step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36088step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw36088step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36089step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36089step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36089step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36091step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36091step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36092step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36092step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36092step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3]]
def raw36093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw36093step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36093step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw36093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw36094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw36094step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36094step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw36094step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw36095step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw36095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36095step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw36095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw36096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw36096step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36096step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw36096step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw36097step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-2, -1, 3]]
def raw36097step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw36097step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36097step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw36097step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36098step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36098step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36100step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36100step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36101step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36103step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36104step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36104step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36104step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw36105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36105step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36106step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36106step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36107step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36107step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36108step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw36110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw36110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36110step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36110step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36110step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36111step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36111step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36112step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36112step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36112step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36112step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36113step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36113step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36113step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36113step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36114step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36114step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36114step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36114step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36115step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36116step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36116step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36116step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36116step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36117step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36117step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36117step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36117step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36118step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36118step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36119step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36119step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36119step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36120step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36120step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36120step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36120step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36121step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36122step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36122step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36123step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36123step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36123step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36123step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw36124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw36124step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36124step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw36124step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36125step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36125step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36125step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw36126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw36126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36126step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36126step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36127step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36131step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36132step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36133step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36135step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36135step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36136step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36136step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36137step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36137step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36137step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36137step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36138step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36138step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36139step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36140step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw36142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw36142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36142step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36142step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36181step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36181step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36183step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36184step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36186step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36186step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36187step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36189step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36191step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36195step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36196step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36197step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw36198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw36198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36198step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36198step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw36199step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw36199step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw36202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw36202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36202step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw36203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw36203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw36203step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36206step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36207step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw36208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw36208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw36208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36211step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36211step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw36213step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36213step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36213step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36217step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36217step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36218step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36219step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw36220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw36220step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36221step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw36221step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw36221step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36221step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw36221step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36223step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36223step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36223step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical283
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw36224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw36224step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36224step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36289step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36292step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36294step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36295step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36297step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36299step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36299step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36301step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36303step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36306step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36306step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36306step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36307step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36309step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw36310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw36311step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36311step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36313step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36315step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw36316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36316step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36316step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36317step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36317step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36319step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36321step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36323step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36323step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36325step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36326step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36327step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw36329step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36329step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36331step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw36332step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36332step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical284
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36355 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36355step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36363 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36363step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36367 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36367step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36371step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36371step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36373 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36373step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36373step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36374step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36374step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36374step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36375 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36375step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36377 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw36377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36377step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw36385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36386step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36390step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36392step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36392step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36392step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36392step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36394step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36396step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw36398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw36398step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw36398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw36399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw36399step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw36399step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36400step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36400step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36400step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36401step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36401step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36401step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw36402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36402step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36402step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36402step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36403step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw36404step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36404step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36404step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw36405step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36405step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw36406step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36406step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw36407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36407step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36407step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw36408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw36409step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36409step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36411step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36411step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36412step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36412step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36413step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36413step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36415step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36416step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36416step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36416step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36417step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36417step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36417step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36418step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36419Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36419step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw36420step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw36420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw36421step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw36421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36422step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36423step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw36424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36446step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36446step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36447step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36448step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36450step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36450step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36452step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36455step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36455step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36457step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36457step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36457step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw36458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36459step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36461step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36461step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw36462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36462step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36462step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36462step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36463Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36463step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36463step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36463step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36464step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36464step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36464step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36465Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36465step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36465step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36465step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36465step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36465step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36466Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36466step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36466step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36466step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36467Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw36467step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36467step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36467step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36467step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36468Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36468step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36468step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36469Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36469step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36469step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36469step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36470step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36470step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36470step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36470step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36470step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36471Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw36471step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36471step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36471step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36472Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw36472step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36472step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36472step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36473Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw36473step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36473step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36473step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36474Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw36474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36474step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36474step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36475Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36475step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw36475step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36475step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36475step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36475step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36476Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36476step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36476step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36476step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36477Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36477step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36477step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36477step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36478Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36478step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36479Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36479step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical285
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw36480Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36480step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36480step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36481Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw36481step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw36481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36482Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw36482step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36482step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36482step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36483Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36483step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36483step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw36484Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36484step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw36484step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw36484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36523 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36523step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36523step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36533step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36533step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36533step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36533step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36534step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36535step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36539step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36544step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw36547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36548step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw36551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36551step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36551step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36552step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw36553step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36553step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36553step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36553step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36554step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36554step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36554step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36555step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36555step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36555step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw36557step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw36557step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36557step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw36557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36558step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36559step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36559step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36559step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36559step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36560step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36560step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36561step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36561step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36562step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36563Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw36563step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw36563step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36563step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw36563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36564step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36564step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36564step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36565Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36565step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36565step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36565step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36566Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36566step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36566step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36567Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36567step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36567step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36567step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw36568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw36568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36568step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw36568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw36569Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36569step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36569step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36569step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw36570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36570step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36571Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw36571step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw36571step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw36571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw36573Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36573step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36573step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36591step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36591step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36591step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36591step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36592step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36592step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36593step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36593step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw36594step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw36594step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36594step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw36594step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw36595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36595step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36595step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36596step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36596step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36596step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36596step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36597step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36607step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36607step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical286
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw36611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw36611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw36612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw36612step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36612step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw36612step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw36613step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw36613step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36613step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw36613step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36614step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36615step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36615step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36615step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw36616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw36616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36616step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36616step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36616step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36617step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36619step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw36619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36619step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36619step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36619step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36620step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36620step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36620step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw36622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36624step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw36624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw36624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw36625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw36625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36627step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw36629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36629step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36630step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36631step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw36632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw36632step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36632step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw36632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36633step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36634step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36636step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36636step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36636step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36636step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw36637step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36637step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36637step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36637step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw36638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36638step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36638step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw36639step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36639step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw36641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw36641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36641step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36641step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36641step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36641step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw36642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw36642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36643step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw36643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw36643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw36645step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw36646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw36646step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw36646step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw36646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36666step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36666step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36668step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36668step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36668step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36669step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36671step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36673step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36673step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36674step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36679step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw36682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw36682step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36684step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw36688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw36688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw36689step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw36689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw36690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36691step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36691step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36691step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36692step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36692step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36692step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36692step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw36693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw36693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw36693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36693step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36693step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36693step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36693step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36694Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36694step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36694step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36694step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36694step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36695Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36695step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36695step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36695step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36695step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36696Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36696step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36696step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36696step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36696step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36696step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36697Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36697step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36697step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36697step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36697step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36697step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36697step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36698Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36698step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36698step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36698step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36698step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36699step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36699step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36699step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36699step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36699step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36700step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36701step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36701step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36701step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36702step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36702step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw36702step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36704step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36705step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36706step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36708step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36708step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw36709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw36709step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36709step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw36709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36711step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw36712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw36712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw36712step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw36714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw36715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36715step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw36716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw36718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw36718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw36719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw36719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw36720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw36720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw36720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw36722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw36723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw36723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw36723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw36723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw36723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical287
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36747step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36749step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw36749step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36749step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw36749step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36749step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw36749step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw36750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36750step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36750step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw36762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw36762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36765step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw36766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw36766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36766step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 0, -1], ![2, 0, -2]]
def raw36770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36770step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw36770step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36770step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw36770step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36770step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw36770step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw36771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36771step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36771step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36771step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36772step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -1, -1], ![2, 0, -2]]
def raw36779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw36786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36787step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![3, -1, -2]]
def raw36788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36788step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36788step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36790step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36791step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36791step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36792step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36792step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36792step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36792step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw36793step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw36793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36794step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36795step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36795step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36795step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36796step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36799step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36800step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36800step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw36801step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw36801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36802step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36804step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![2, 1, -3]]
def raw36805step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36805step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36805step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36805step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw36806step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw36806step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36807step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36809step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![2, 1, -3]]
def raw36810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36810step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36810step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw36811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw36811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw36811step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw36811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw36812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw36812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw36813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw36814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![3, 0, -3]]
def raw36814step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw36814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36814step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36814step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw36815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw36815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36817step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36817step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36817step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36817step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36817step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36818step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36818step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36819step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36821step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36821step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36821step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36822step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36822step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36825step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36825step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36826step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36827step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36828step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36828step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36829step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36829step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36831step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![2, 1, -3]]
def raw36831step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36831step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36831step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36831step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36831step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36832step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36833step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36834step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36835step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36836step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![2, 1, -3]]
def raw36836step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36836step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36836step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36836step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36836step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw36837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw36837step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36838step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36839step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw36840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![3, 0, -3]]
def raw36840step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36840step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36859step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw36859step0Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36859step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw36859step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36859step2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw36859step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw36860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36860step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36861step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36862step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36862step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw36863step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw36863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical288
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36865step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36866step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36867step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36867step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36867step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36868step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36873step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36878step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 1, -2]]
def raw36882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36883step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw36887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36888 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 3, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36888step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36888step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36888step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36889 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36889step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36889step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36889step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36890 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36890step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36891 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36891step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36892step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36892step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36892step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36893 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36893step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw36893step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw36893step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw36893step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw36893step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw36893step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw36894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36894step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36894step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36894step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36894step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36895 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36895step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36895step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36896step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36896step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36896step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36896step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36896step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36897step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36897step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36898step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36899step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw36900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36900step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36900step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36900step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36900step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw36901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36901step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36901step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36901step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw36902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36902step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw36903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36903step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36904step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36905 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw36905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw36905step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw36905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw36906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw36906step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36906step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36906step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw36907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36907step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw36908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36908step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical289
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37017Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37017step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37017step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![2, -2]]
def raw37017step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37017step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw37017step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw37018Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37018step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37018step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37018step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw37018step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37018step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw37018step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37019step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37019step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37019step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37019step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw37020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37020step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37020step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37020step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37021step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37021step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![2, -2], ![1, -1], ![2, -2]]
def raw37021step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37021step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw37021step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37022step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]
def raw37022step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37022step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37022step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw37023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw37023step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![2, -2, 0]]
def raw37023step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37023step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw37023step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37024step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37024step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![1, -1], ![3, -3]]
def raw37024step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37024step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw37024step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37025step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw37025step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37025step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![1, -1], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37025step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37025step2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37025step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw37026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37026step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37026step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37026step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw37026step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37026step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw37026step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37026step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw37026step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37027step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37028step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw37029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37029step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw37030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37030step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37030step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37030step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37030step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37031step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37032step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw37033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37033step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37033step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw37034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37034step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37035step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw37036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw37036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37036step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw37037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37037step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw37038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37038step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw37039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37039step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37045step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37046step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37046step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37046step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37047step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37047step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37047step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37048step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37048step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37048step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37048step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37049step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37050step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37052step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37052step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37053step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37055step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37057step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37057step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37058step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37060step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37060step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37062step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37063step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw37064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw37065step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw37065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37067step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37068step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw37069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37069step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37071step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37072step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37072step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37075step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37077step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37077step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37077step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw37079step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw37079step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37079step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw37079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37081step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37081step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37081step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37082step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37083step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37083step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37085step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37088step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37089step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37089step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37091step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37091step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37092step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37092step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37093step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37093step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw37094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37094step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw37095step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw37095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37095step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw37095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw37099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37099step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37100step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37102step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37102step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37103step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37103step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37103step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37104step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37105step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37106step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37107step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37108step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37109step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37110step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37111step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37111step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw37112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37112step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3713step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]
def raw3713step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3714step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3714step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3716 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3716step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw3718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw3718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3720step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3721 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-3, 3]]
def raw3721Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![0, 0], ![-3, 3]]
def raw3721step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![-3, 3]]
def raw3721step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![-3, 3]]
def raw3721step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![3, -3], ![-3, 3]]
def raw3721step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw3721step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3722step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-2, 2, 0], ![-2, 2, 0]]
def raw3724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-3, 3, 0]]
def raw3725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw3726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical290
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37127step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37127step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37128step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37128step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37128step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37129step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37129step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37129step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37130step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37130step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37130step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37131step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37132step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37132step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37133step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37133step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37133step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37133step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37134step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37134step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37134step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw37135step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37135step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37138step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37138step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37138step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37139step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37139step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37139step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37140step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37140step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37140step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37143step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37143step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37143step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37143step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37144step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37144step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw37145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37145step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37145step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37145step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37145step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37146step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37148step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37148step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37148step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37148step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37149step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37149step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37149step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw37150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37150step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37150step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37150step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37150step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37151step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37153step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37153step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37154step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37154step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37155step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37155step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37155step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37156step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37157step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37157step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37157step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37158step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37158step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37158step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37159step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37159step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37160step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37160step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37160step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37160step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw37161step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37161step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37161step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37162step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37162step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37163step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37163step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37165step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37165step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37167step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37169step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37170step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37170step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37171step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37172step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37172step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37173step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37174step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw37175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37175step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37176step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37177step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37178step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37179step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw37180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw37181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw37181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw37181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37185step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37185step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37200step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37206step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37207step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw37208step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37208step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37209step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37209step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37209step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37210step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37210step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37210step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37211step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37212step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37213step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37213step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37213step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37214step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37214step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37214step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37215step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37216step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw37217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37217step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37232step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw37232step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37232step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw37232step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw37233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37233step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw37233step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37233step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw37233step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw37234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37234step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37234step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw37234step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37234step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw37234step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37235step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]
def raw37235step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37235step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37235step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37236step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37236step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw37236step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37236step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37236step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw37237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37237step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw37237step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37237step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37237step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw37238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37238step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw37238step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37238step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37238step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37239step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]
def raw37239step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37239step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37239step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw37240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw37240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37240step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw37240step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37240step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37240step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw37241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw37241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37241step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw37241step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37241step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37241step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw37242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37242step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]
def raw37242step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37242step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37242step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw37243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37243step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37243step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw37245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37246step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw37247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical291
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37248step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw37249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw37250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37251step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37251step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37251step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37252step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37252step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37253step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37253step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37253step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37254step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37255step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37256step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37257step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37258step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37258step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw37259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37259step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw37260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37260step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw37261step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37261step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37261step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw37262step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37262step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37262step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw37263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37263step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37263step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37263step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37263step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37266step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37268step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37269step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37269step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37270step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37271step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37273step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37273step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37274step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37275step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37276step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37278step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37279step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37280step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37281step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37283step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw37284step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw37284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37285step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37286step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37287step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw37288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37288step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw37289step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw37289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw37290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw37291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw37293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37298step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37299step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37299step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37299step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37300step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37301step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37301step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37301step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37302step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37302step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw37303step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37303step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37305step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37305step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37306step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37307step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw37308step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37308step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37309step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37309step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37309step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37309step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37310step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37310step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37311step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37311step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37313step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37313step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw37314step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw37314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37314step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw37314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37315step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37317step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw37318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37319step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw37323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37323step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37324step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37324step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37325step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![2, -2]]
def raw37325step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37325step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37325step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw37326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw37326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37326step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw37326step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37326step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw37326step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37326step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37326step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw37327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37327step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw37327step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37327step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37327step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37328step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw37328step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37328step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![1, -1], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37328step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37328step2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37328step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw37329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37329step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw37329step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37329step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw37329step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37329step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw37329step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37330 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-3, -2, 5]]
def raw37330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![3, 2, -5], ![-3, -2, 5]]
def raw37330step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw37330step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw37331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw37332step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


