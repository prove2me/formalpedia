-- Prove2me | Definitions.Def_OAIQ106D064
-- name    : OAIQ106D064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:29:37.428799+00:00
-- url     : https://prove2.me/theorems/14482575-59c8-472a-bd8b-bc9ce6d49142
-- title:
--   Definitions bundle OAIQ106D064 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2193 declarations of OpenAI's Lean: 2193 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.raw7562step0`, `OAI.MUB6.Certificate.PairSemantics.raw7562step1`, `OAI.MUB6.Certificate.PairSemantics.raw7563`, `OAI.MUB6.Certificate.PairSemantics.raw7563step0`, `OAI.MUB6.Certificate.PairSemantics.raw7563step1`, `OAI.MUB6.Certificate.PairSemantics.raw7564`, `OAI.MUB6.Certificate.PairSemantics.raw7565`, `OAI.MUB6.Certificate.PairSemantics.raw7565step0`, `OAI.MUB6.Certificate.PairSemantics.raw7566`, `OAI.MUB6.Certificate.PairSemantics.raw7566step0`, `OAI.MUB6.Certificate.PairSemantics.raw7566step1`, `OAI.MUB6.Certificate.PairSemantics.raw7567`, `OAI.MUB6.Certificate.PairSemantics.raw7568`, `OAI.MUB6.Certificate.PairSemantics.raw7568step0`, `OAI.MUB6.Certificate.PairSemantics.raw7568step1`, `OAI.MUB6.Certificate.PairSemantics.raw7568step2`, `OAI.MUB6.Certificate.PairSemantics.raw7569`, `OAI.MUB6.Certificate.PairSemantics.raw7569step0`, `OAI.MUB6.Certificate.PairSemantics.raw756step0`, `OAI.MUB6.Certificate.PairSemantics.raw756step1`, `OAI.MUB6.Certificate.PairSemantics.raw7570`, `OAI.MUB6.Certificate.PairSemantics.raw7571`, `OAI.MUB6.Certificate.PairSemantics.raw7571step0`, `OAI.MUB6.Certificate.PairSemantics.raw7572`, `OAI.MUB6.Certificate.PairSemantics.raw7573`, `OAI.MUB6.Certificate.PairSemantics.raw7573step0`, `OAI.MUB6.Certificate.PairSemantics.raw7573step1`, `OAI.MUB6.Certificate.PairSemantics.raw7573step2`, `OAI.MUB6.Certificate.PairSemantics.raw7574`, `OAI.MUB6.Certificate.PairSemantics.raw7574step0`, `OAI.MUB6.Certificate.PairSemantics.raw7574step1`, `OAI.MUB6.Certificate.PairSemantics.raw7574step2`, `OAI.MUB6.Certificate.PairSemantics.raw7575`, `OAI.MUB6.Certificate.PairSemantics.raw7575step0`, `OAI.MUB6.Certificate.PairSemantics.raw7576`, `OAI.MUB6.Certificate.PairSemantics.raw7576step0`, `OAI.MUB6.Certificate.PairSemantics.raw7577`, `OAI.MUB6.Certificate.PairSemantics.raw7578`, `OAI.MUB6.Certificate.PairSemantics.raw7578step0`, `OAI.MUB6.Certificate.PairSemantics.raw7578step1` and 2153 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Canonical0`, `MutuallyUnbiased_PairSemantics_Canonical2`, `MutuallyUnbiased_PairSemantics_Canonical23`, `MutuallyUnbiased_PairSemantics_Canonical236`, `MutuallyUnbiased_PairSemantics_Canonical237`, `MutuallyUnbiased_PairSemantics_Canonical238`, `MutuallyUnbiased_PairSemantics_Canonical239`, `MutuallyUnbiased_PairSemantics_Canonical24`, `MutuallyUnbiased_PairSemantics_Canonical240`, `MutuallyUnbiased_PairSemantics_Canonical241`, `MutuallyUnbiased_PairSemantics_Canonical242`, `MutuallyUnbiased_PairSemantics_Canonical243`, `MutuallyUnbiased_PairSemantics_Canonical244`, `MutuallyUnbiased_PairSemantics_Canonical245`, `MutuallyUnbiased_PairSemantics_Canonical246`, `MutuallyUnbiased_PairSemantics_Canonical247`, `MutuallyUnbiased_PairSemantics_Canonical248`, `MutuallyUnbiased_PairSemantics_Canonical249`, `MutuallyUnbiased_PairSemantics_Canonical25`, `MutuallyUnbiased_PairSemantics_Canonical250`, `MutuallyUnbiased_PairSemantics_Canonical251`, `MutuallyUnbiased_PairSemantics_Canonical252`, `MutuallyUnbiased_PairSemantics_Canonical253`, `MutuallyUnbiased_PairSemantics_Canonical254`, `MutuallyUnbiased_PairSemantics_Canonical255`, `MutuallyUnbiased_PairSemantics_Canonical256`, `MutuallyUnbiased_PairSemantics_Canonical257`, `MutuallyUnbiased_PairSemantics_Canonical258`, `MutuallyUnbiased_PairSemantics_Canonical259`, `MutuallyUnbiased_PairSources_Data`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D140`; the statement `OAI.MUB6.Certificate.PairSemantics.canonical7982`; the proof of `OAI.MUB6.Certificate.PairSemantics.canonical7982`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw7step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw8 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw75step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, -1, -1], ![1, 1, -2]]

def raw75step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-2, 1, 1], ![-1, -1, 2]]

def raw75step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def raw76 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

def raw76step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw76step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw77 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]

def raw77step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

def raw78 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]

def raw78step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]

def raw78step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def raw79 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw79step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw79step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw80 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw80step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]

def raw80step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw81 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw81step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw81step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw82 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw756step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw757step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]

def raw757step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw759 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]

def raw759step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw759step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]

def raw759step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw760 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]

def raw760step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw761 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]

def raw761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw762 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]

def raw762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw763 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]

def raw763step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![1, 1, 0, -2], ![2, -1, 0, -1]]

def raw763step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]

def raw763step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw765 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical236
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7562step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![2, -2, 0, 0], ![-1, 3, -1, -1]]

def raw7562step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7563 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7563step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -2, 1], ![0, 1, 2, -3], ![0, -2, 0, 2], ![-1, 1, 0, 0]]

def raw7563step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7564 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw7565 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw7565step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7566 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, -3, 2]]

def raw7566step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -2, 1], ![0, 1, 0, -1], ![0, -1, -1, 2], ![-1, 0, 3, -2]]

def raw7566step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7567 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw7568 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw7568step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![2, 1, 0, -3], ![-1, 0, -2, 3]]

def raw7568step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -2, 1], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def raw7568step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw7569 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7569step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw7570 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw7571 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7571step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw7572 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw7573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7573step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-1, 0, 0, 0, 1], ![0, 0, 1, 1, -2], ![2, 0, 0, 0, -2], ![-1, 0, -1, -1, 3]]

def raw7573step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, 0, -2], ![-1, -1, -1, 3]]

def raw7573step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7574 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7574step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![2, 0, 0, -2], ![-1, 0, -1, 2]]

def raw7574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw7574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, -2, 3]]

def raw7576step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4]]

def raw7578 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -3, 3]]

def raw7578step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![2, 1, 0, -3], ![-1, -1, -1, 3]]

def raw7578step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7579 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -3, 4]]

def raw7579step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![2, 1, 0, -3], ![-1, -1, -2, 4]]

def raw7579step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw7580 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw7580step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -1, 0, -1], ![-1, 0, -1, 2]]

def raw7580step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 0, 1], ![1, 0, 1, -2]]

def raw7580step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw7581 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 0, 0, 0], ![1, -1, -2, 2]]

def raw7581step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-1, -1, 0, 2]]

def raw7581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw7581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7582 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, -1, 2]]

def raw7582step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, -1, -1], ![-1, -1, 0, 2]]

def raw7582step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 0, 1, 1], ![1, 1, 0, -2]]

def raw7582step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw7583 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7583step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, 0, -2], ![-1, -1, -1, 3]]

def raw7583step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical237
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -3, 4]]

def raw7584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 0, 1, -3], ![-1, -1, -2, 4]]

def raw7584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw7585 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7585step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![-1, -1, 2]]

def raw7585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -2, -3, 4]]

def raw7586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, 1, 0, -3], ![-1, -2, -1, 4]]

def raw7586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw7587 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, -3, 3]]

def raw7587step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![2, 1, -3], ![-1, -2, 3]]

def raw7587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def raw7588 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, -4, 2], ![1, -2, 2, -1]]

def raw7588step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, -4, 2], ![-1, 2, -1]]

def raw7588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 4, -2], ![1, -2, 1]]

def raw7588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7589 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, -3, 1], ![1, -2, 1, 0]]

def raw7589step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![-1, 1, 0]]

def raw7589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 3, -1], ![1, -1, 0]]

def raw7589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7590 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -2, -1, 2]]

def raw7590step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![-1, -1, 2]]

def raw7590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![1, 1, -2]]

def raw7590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw7591 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def raw7591step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, 0, -2], ![-1, -2, 3]]

def raw7591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw7592 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 2, 1, -3], ![1, -2, -3, 4]]

def raw7592step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![2, 1, -3], ![-1, -3, 4]]

def raw7592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -2, 2], ![-2, -1, 3], ![1, 3, -4]]

def raw7592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw7593 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, -4, 1], ![1, -3, 2, 0]]

def raw7593step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, -4, 2], ![-1, 1, 0]]

def raw7593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 4, -2], ![1, -1, 0]]

def raw7593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw7594 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, -2, -1], ![1, -3, 0, 2]]

def raw7594step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![-1, -1, 2]]

def raw7594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 2, 0], ![1, 1, -2]]

def raw7594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw7595 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, -1, -2], ![1, -3, -1, 3]]

def raw7595step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, -1, -1], ![-1, -2, 3]]

def raw7595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 1, 1], ![1, 2, -3]]

def raw7595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw7596 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 3, 0, -3], ![1, -3, -2, 4]]

def raw7596step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 3, -3], ![2, 0, -2], ![-1, -3, 4]]

def raw7596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -3, 3], ![-2, 0, 2], ![1, 3, -4]]

def raw7596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def raw7597 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 4, -3, -1], ![1, -4, 1, 2]]

def raw7597step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 4, -4], ![2, -3, 1], ![-1, -1, 2]]

def raw7597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -4, 4], ![-2, 3, -1], ![1, 1, -2]]

def raw7597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def raw7598 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -3, 1, 1], ![0, 3, -3, 0]]

def raw7598step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![2, 1, -3], ![-1, 1, 0]]

def raw7598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-2, -1, 3], ![1, -1, 0]]

def raw7598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7599 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, -3, 4], ![0, 2, 1, -3]]

def raw7599step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, -3, 1], ![-1, 4, -3]]

def raw7599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-2, 3, -1], ![1, -4, 3]]

def raw7599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw7600 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, -1, 2], ![0, 2, -1, -1]]

def raw7600step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![-1, 2, -1]]

def raw7600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-2, 1, 1], ![1, -2, 1]]

def raw7600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw7601 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, 0, 1], ![0, 2, -2, 0]]

def raw7601step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![-1, 1, 0]]

def raw7601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw7602 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, -2, 2, -1], ![0, 2, -4, 2]]

def raw7602step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![2, 2, -4], ![-1, -1, 2]]

def raw7602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![-2, -2, 4], ![1, 1, -2]]

def raw7602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7603 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![1, 2, 0, -3], ![0, -2, -2, 4]]

def raw7603step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 2, -2], ![2, 0, -2], ![-1, -3, 4]]

def raw7603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, -2, 2], ![-2, 0, 2], ![1, 3, -4]]

def raw7603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw7604 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![2, -3, 1, 0], ![-1, 3, -3, 1]]

def raw7604step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -3, 3], ![2, 1, -3], ![-1, 0, 1]]

def raw7604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 3, -3], ![-2, -1, 3], ![1, 0, -1]]

def raw7604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def raw7605 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![2, -2, 0, 0], ![-1, 2, -2, 1]]

def raw7605step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![-1, 0, 1]]

def raw7605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw7606 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![2, -2, 1, -1], ![-1, 2, -3, 2]]

def raw7606step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -2, 2], ![2, 1, -3], ![-1, -1, 2]]

def raw7606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 2, -2], ![-2, -1, 3], ![1, 1, -2]]

def raw7606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def raw7607 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![3, -3, 0, 0], ![-2, 3, -2, 1]]

def raw7607step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![0, -3, 3], ![2, 0, -2], ![-1, 0, 1]]

def raw7607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 3, -3], ![-2, 0, 2], ![1, 0, -1]]

def raw7607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def raw7608 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![3, -2, 0, -1], ![-2, 2, -2, 2]]

def raw7608step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![0, -2, 2], ![2, 0, -2], ![-1, -1, 2]]

def raw7608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 2, -2], ![-2, 0, 2], ![1, 1, -2]]

def raw7608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def raw7609 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![-1, 0, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7609step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -3, 2], ![1, 0, 3, -4], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw7609step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7610 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw7610step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -3, 2], ![1, 0, 2, -3], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw7610step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7611 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -3, 1, 2], ![1, 3, -4, 0]]

def raw7611step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![3, 1, -4], ![-2, 2, 0]]

def raw7611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-3, -1, 4], ![2, -2, 0]]

def raw7611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

def raw7612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![3, -3, 0, 0], ![-2, 4, -1, -1]]

def raw7612step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw7613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![3, -3, 0, 0], ![-2, 4, -2, 0]]

def raw7613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -2, 1], ![-3, 3, 0, 0], ![2, -4, 2, 0]]

def raw7613step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw7614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2]]

def raw7614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, -3, 2], ![0, 1, 1, -2], ![0, 0, 2, -2], ![-1, -1, 0, 2]]

def raw7614step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def raw7615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4]]

def raw7615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, 1, -2], ![3, 0, 0, -3], ![-2, -1, -1, 4]]

def raw7615step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, 0, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7616 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, -3, 3]]

def raw7616step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![3, 0, -3], ![-2, -1, 3]]

def raw7616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw7617 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -2, -3, 4]]

def raw7617step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 2, -2], ![3, 0, -3], ![-2, -2, 4]]

def raw7617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw7618 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![1, -3, 1, 1], ![0, 3, -4, 1]]

def raw7618step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![3, 1, -4], ![-2, 1, 1]]

def raw7618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-3, -1, 4], ![2, -1, -1]]

def raw7618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

def raw7619 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![1, -2, 1, 0], ![0, 2, -4, 2]]

def raw7619step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![3, 1, -4], ![-2, 0, 2]]

def raw7619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def raw7620 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![2, -3, 1, 0], ![-1, 3, -4, 2]]

def raw7620step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -3, 3], ![3, 1, -4], ![-2, 0, 2]]

def raw7620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 3, -3], ![-3, -1, 4], ![2, 0, -2]]

def raw7620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

def raw7621 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![2, -2, 1, -1], ![-1, 2, -4, 3]]

def raw7621step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![0, -2, 2], ![3, 1, -4], ![-2, -1, 3]]

def raw7621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![0, 2, -2], ![-3, -1, 4], ![2, 1, -3]]

def raw7621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

def raw7622 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]

def raw7622step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7623 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def raw7623step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7624 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw7624step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw7625 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw7625step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7625step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7626 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]

def raw7626step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7626step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7627 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]

def raw7627step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7627step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7628 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3], ![0, 0]]

def raw7628step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]

def raw7628step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7628step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7629 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw7629step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw7629step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7629step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7630 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw7630step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7630step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7631 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw7631step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7631step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7632 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]

def raw7632step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw7632step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7632step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7633 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw7633step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7633step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7634 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7634step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7635 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw7635step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw7635step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7636 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7636step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7637 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2], ![0, 0]]

def raw7637step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7637step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7638 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![0, 0], ![1, -1]]

def raw7638step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7638step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7639 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7639step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7640 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0]]

def raw7640step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7640step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7641 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0], ![0, 0]]

def raw7641step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0]]

def raw7641step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7641step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7642 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7642step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7643 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3], ![0, 0]]

def raw7643step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7643step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7644 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![4, -4]]

def raw7644step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7645 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![3, -3]]

def raw7645step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7646 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def raw7646step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def raw7647 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]

def raw7647step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7648 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![4, -4]]

def raw7648step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7649 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![3, -3]]

def raw7649step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def raw7650 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![4, -4]]

def raw7650step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![4, -4]]

def raw7650step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw7651 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]

def raw7651step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw7652 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]

def raw7652step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw7653 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]

def raw7653step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]

def raw7653step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7653step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7654 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw7654step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7654step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7655 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw7655step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7655step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7656 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]

def raw7656step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7656step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7657 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw7657step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7657step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7658 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7659 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7659step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7660 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw7660step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7660step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7661 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7661step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7662 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]

def raw7662step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7662step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7663 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7663step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7664 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3], ![0, 0]]

def raw7664step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7664step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7665 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3], ![0, 0], ![0, 0]]

def raw7665step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3], ![0, 0]]

def raw7665step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7665step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7666 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]

def raw7666step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7666step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7667 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw7667step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw7667step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7667step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7667step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7668 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw7668step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def raw7668step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7669 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw7669step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7669step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7669step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7670 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def raw7670step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7671 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7671step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7671step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7672 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![0, 0]]

def raw7672step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7672step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7672step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7673 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7673step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7673step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7674 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7674step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7675 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7675step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7675step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7676 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw7676step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw7676step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7677 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw7677step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7678 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7679 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw7679step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw769 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]

def raw769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw770 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def raw770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw771 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]

def raw771step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]

def raw771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw772 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]

def raw772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]

def raw773 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw774 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]

def raw774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw775 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

def raw776 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw777 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw778 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw778step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def raw779 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]

def raw779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw780 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw781 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw781step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw782 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw782step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw783 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw784 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]

def raw784step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]

def raw784step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw785 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw786 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw787 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw788 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0]]

def raw788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw789 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw790 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]

def raw790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw791 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def raw791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw792 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def raw792step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]

def raw792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw793 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

def raw793step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw794 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]

def raw794step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw795 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]

def raw795step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-3, 3, 0]]

def raw795step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def raw796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw797 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![0, 2, -2], ![2, 0, -2]]

def raw797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def raw798 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, -1, 0], ![1, 3, -4]]

def raw799 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]

def raw799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7680 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw7680step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw7680step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7682 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![-1, 1]]

def raw7682step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7683 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7683step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7684 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1]]

def raw7684step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7685 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw7685step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7685step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7686 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0]]

def raw7686step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw7686step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7686step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7687 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def raw7687step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0]]

def raw7687step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw7687step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7687step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7688 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]

def raw7688step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7689 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0], ![-1, 1]]

def raw7689step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]

def raw7689step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7690 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![-1, 1]]

def raw7690step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7691 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![0, 0], ![-1, 1]]

def raw7691step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![-1, 1]]

def raw7691step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7692 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]

def raw7692step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]

def raw7692step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7692step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7693 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]

def raw7693step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7693step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7694 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2], ![0, 0]]

def raw7694step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]

def raw7694step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7694step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7695 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]

def raw7695step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7695step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7696 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7696step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7696step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7697 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7697step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7697step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7698 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw7698step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]

def raw7698step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7698step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7698step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7699 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]

def raw7699step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7699step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7699step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7700 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2], ![0, 0]]

def raw7700step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]

def raw7700step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7700step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7700step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7701 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7701step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7701step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7702 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw7702step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]

def raw7702step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7703 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]

def raw7703step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7704 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw7704step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]

def raw7704step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7705 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7705step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7705step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7706 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2], ![0, 0]]

def raw7706step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7706step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7706step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7707 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-1, 1], ![2, -2]]

def raw7707step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7707step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7707step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7709 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1]]

def raw7709step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw7710 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![-2, 2], ![2, -2]]

def raw7710step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7710step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7712 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![-1, 1], ![1, -1]]

def raw7712step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7712step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7714 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]

def raw7714step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7714step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7715 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7715step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]

def raw7715step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7715step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7716 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![2, -2], ![-1, 1]]

def raw7716step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7716step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7717 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![2, -2], ![0, 0], ![-1, 1]]

def raw7717step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![2, -2], ![-1, 1]]

def raw7717step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7717step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7718 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw7719 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![0, 0], ![2, -2]]

def raw7719step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7719step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7720 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]

def raw7720step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7721 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw7721step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]

def raw7721step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7722 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7722step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7723 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![0, 0]]

def raw7723step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7723step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7724 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw7724step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![0, 0]]

def raw7724step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7724step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7726 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7726step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]

def raw7726step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7728 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]

def raw7728step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7729 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![1, -1]]

def raw7729step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw7729step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7729step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7730 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw7730step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7730step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7731 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7731step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7732 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0]]

def raw7732step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7732step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7733 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def raw7733step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0]]

def raw7733step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7733step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7735 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0]]

def raw7735step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw7738 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7738step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7740 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1], ![0, 0]]

def raw7740step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7740step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7741 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1], ![0, 0], ![0, 0]]

def raw7741step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1], ![0, 0]]

def raw7741step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7741step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7742 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7742step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7742step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7743 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def raw7743step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7743step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7743step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical242
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7744 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![-2, 2]]

def raw7744step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7745 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![0, 0], ![1, -1]]

def raw7745step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7745step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7746 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7746step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7747 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1], ![0, 0]]

def raw7747step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7747step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7748 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1], ![0, 0], ![0, 0]]

def raw7748step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1], ![0, 0]]

def raw7748step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-2, 2], ![1, -1]]

def raw7748step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7749 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7749step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7750 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![0, 0], ![1, -1]]

def raw7750step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1]]

def raw7750step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7751 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1]]

def raw7751step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7752 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0]]

def raw7752step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![-1, 1], ![1, -1]]

def raw7752step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7753 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw7753step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7753step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7754 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0], ![0, 0]]

def raw7754step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw7754step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7754step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7755 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0], ![0, 0], ![0, 0]]

def raw7755step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0], ![0, 0]]

def raw7755step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![0, 0]]

def raw7755step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7755step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7756 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7756step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![-1, 1]]

def raw7756step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7757 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def raw7757step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7757step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7758 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![0, 0], ![-1, 1]]

def raw7758step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![0, 0], ![-1, 1]]

def raw7758step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7758step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw7759 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-2, 2], ![0, 0], ![0, 0]]

def raw7759step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-2, 2], ![0, 0]]

def raw7759step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-2, 2]]

def raw7759step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw7760 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![1, -1], ![-1, 1], ![-1, 1]]

def raw7760step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw7761 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![3, -3], ![-1, 1], ![-1, 1]]

def raw7761step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw7762 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, 0, 2, -2], ![1, -1, 2, -2]]

def raw7762step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-4, 2, 2], ![4, -2, -2]]

def raw7762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![2, 2, -4]]

def raw7763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw7764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7766 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def raw7766step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 1, 0, -2], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw7766step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def raw7767 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7767step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 1, 0, 2], ![3, -1, 0, -2]]

def raw7767step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7768step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 1, 1, 1], ![3, -1, -1, -1]]

def raw7768step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw7769 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, -1, 0, 0]]

def raw7769step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw7769step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def raw7770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 2, -2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7771 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7771step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 2, 0, 1], ![3, -2, 0, -1]]

def raw7771step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw7772 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 2, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw7772step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 2, 1, 0], ![3, -2, -1, 0]]

def raw7772step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def raw7773 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7773step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-3, 3, 0, 0], ![3, -3, 0, 0]]

def raw7773step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def raw7774 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7774step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 1, 0], ![-3, 3, 0, 0], ![3, -1, -1, -1]]

def raw7774step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw7775 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw7775step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-3, 2, 1], ![3, -1, -2]]

def raw7775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical243
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7776 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 3, -2], ![1, 0, 0, -1]]

def raw7776step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-3, 3, 0], ![3, -2, -1]]

def raw7776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def raw7777 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7778 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7778step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-3, 1, 2, 0], ![3, -1, -2, 0]]

def raw7778step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw7779 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7779step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 1, 0, 2], ![3, -1, -1, -1]]

def raw7779step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw7780 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7780step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 1, 1, 1], ![3, -1, -2, 0]]

def raw7780step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

def raw7781 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![1, -1, 2, -2]]

def raw7781step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 1, 2], ![3, -1, -2]]

def raw7781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def raw7782 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7782step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-3, 2, 0, 1], ![3, -2, -1, 0]]

def raw7782step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw7783 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7783step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 2, 1], ![3, -2, -1]]

def raw7783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw7784 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7784step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 3, 0], ![3, -3, 0]]

def raw7784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def raw7785 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 4, -4], ![1, -1, -1, 1]]

def raw7785step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-3, 4, -1], ![3, -4, 1]]

def raw7785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw7786 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7786step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-3, 1, 2], ![3, -2, -1]]

def raw7786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def raw7787 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7787step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-3, 2, 1], ![3, -3, 0]]

def raw7787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def raw7788 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7788step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-3, 3, 0], ![3, -4, 1]]

def raw7788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def raw7789 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7790 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7791 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7792 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw7792step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![2, -2, 1, -1]]

def raw7793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 1, 0, -2], ![-2, -1, 2, 1], ![2, 1, -2, -1]]

def raw7793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw7794 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7795 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![2, -2, 0, 0]]

def raw7795step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![1, 1, 0, -2], ![-2, -1, 3, 0], ![2, 1, -3, 0]]

def raw7795step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![2, -1, 0, -1]]

def raw7796 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw7796step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw7796step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7797 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw7798 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw7798step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw7799 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, -1, 0, 0]]

def raw7799step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, -1, 3, 0], ![2, 1, -3, 0]]

def raw7799step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw7800 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7800step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7801 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7801step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw7802 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7802step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 0, 0, 2], ![2, 0, 0, -2]]

def raw7802step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7803 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7803step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 0, 1, 1], ![2, 0, -1, -1]]

def raw7803step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7804 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7804step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw7805 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7805step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 1, 0, 1], ![2, -1, 0, -1]]

def raw7805step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw7806 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7806step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 2, 0, 0], ![2, -2, 0, 0]]

def raw7806step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw7807 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, 3, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw7807step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-2, 3, -1, 0], ![2, -3, 1, 0]]

def raw7807step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical244
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7808 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -2, 0, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw7808step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 1, 0], ![-2, 0, 3, -1], ![2, 2, -4, 0]]

def raw7808step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7809 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -2, 1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7809step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 2, -2], ![0, 2, -1, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw7809step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def raw7810 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw7810step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -2, 1, 0], ![-2, 3, 0, -1], ![2, -1, -1, 0]]

def raw7810step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7811 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw7811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 2, -2], ![0, 1, 1, -2], ![0, 0, -2, 2], ![-1, 0, -1, 2]]

def raw7811step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw7812 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7812step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![-2, -1, 3, 0], ![2, 2, -4, 0]]

def raw7812step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw7813 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7814 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![1, 0, 0, -1]]

def raw7814step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-2, 2, 0], ![2, -1, -1]]

def raw7814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw7815 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 3, -2], ![1, 0, -1, 0]]

def raw7815step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-2, 3, -1], ![2, -2, 0]]

def raw7815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7816 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7817 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7817step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-2, -1, 3, 0], ![2, 1, -3, 0]]

def raw7817step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw7818 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, -1, 0, 3], ![2, 1, -1, -2]]

def raw7818step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw7819 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7819step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, -1, 2, 1], ![2, 1, -3, 0]]

def raw7819step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![2, 1, -2, -1], ![-2, -1, 3, 0]]

def raw7819step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw7820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7820step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, -1, 3, 0], ![2, 1, -4, 1]]

def raw7820step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![2, 1, -3, 0], ![-2, -1, 4, -1]]

def raw7820step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def raw7821 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7821step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![2, -1, -1, 0]]

def raw7821step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def raw7822 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7822step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, 1, 0, 1], ![2, -1, -1, 0]]

def raw7822step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw7823 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def raw7823step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-2, 1, 1], ![2, -1, -1]]

def raw7823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw7824 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0]]

def raw7824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7825 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7825step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-2, 3, -1, 0], ![2, -3, 0, 1]]

def raw7825step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7826 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def raw7827 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def raw7827step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-2, 3, -1], ![2, -3, 1]]

def raw7827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7828 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-2, 0, 2], ![2, -1, -1]]

def raw7828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def raw7829 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-2, 1, 1], ![2, -2, 0]]

def raw7829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def raw7830 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw7830step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![-2, 3, -1], ![2, -4, 2]]

def raw7830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![2, -3, 1], ![-2, 4, -2]]

def raw7830step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw7831 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw7831step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw7832 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7832step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw7833 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw7833step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 1, -1, -1], ![-1, -1, 0, 2], ![1, 1, 0, -2]]

def raw7833step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7834 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw7834step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw7835 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -2, 3, -1], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw7835step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, 2, -3, 1], ![0, -1, 2, -1], ![-1, 0, 0, 1]]

def raw7835step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw7836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7837 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![1, 0, 3, -4]]

def raw7837step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-1, -2, 3], ![1, 3, -4]]

def raw7837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 1, 0], ![1, 2, -3], ![-1, -3, 4]]

def raw7837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw7838 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7839 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7839step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical245
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7841 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, 2, -1], ![1, 0, -1, 0]]

def raw7841step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0]]

def raw7841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7843 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7844step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -2, 0, 3], ![1, 2, -1, -2]]

def raw7844step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![1, 2, 0, -3], ![-1, -2, 1, 2]]

def raw7844step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw7845 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7846 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7847 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7848 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![1, -1, 3, -3]]

def raw7848step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, -2, 3], ![1, 2, -3]]

def raw7848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw7849 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7849step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7850 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7851 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw7852 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw7853 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7854 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def raw7854step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, -1, 2, 0], ![1, 1, -2, 0]]

def raw7854step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7855 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def raw7856 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 3, -2]]

def raw7856step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, -1, 3], ![1, 1, 0, -2]]

def raw7856step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7857 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def raw7857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, 0, 2], ![1, 1, -1, -1]]

def raw7857step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7858 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def raw7858step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 1, -1], ![0, 0, 1, -1], ![0, -1, -1, 2], ![-1, 2, -1, 0]]

def raw7858step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def raw7859 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def raw7859step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, 2, 0], ![1, 1, -3, 1]]

def raw7859step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![1, 1, -2, 0], ![-1, -1, 3, -1]]

def raw7859step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw7860 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw7860step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, -1, 3, -1], ![1, 1, -4, 2]]

def raw7860step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![1, 1, -3, 1], ![-1, -1, 4, -2]]

def raw7860step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw7861 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7861step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 0, 1, 0], ![1, 0, -1, 0]]

def raw7861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw7861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw7862 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 0, 0], ![1, -1, 1, -1]]

def raw7862step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1]]

def raw7862step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7862step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7863 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, 0, 0]]

def raw7863step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 1, 0, 0], ![1, -1, 0, 0]]

def raw7863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw7863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw7864 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1]]

def raw7864step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![1, -1, -1, 1]]

def raw7864step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw7865 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw7865step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 1, 2, -2], ![1, -1, -3, 3]]

def raw7865step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw7866 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def raw7866step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0]]

def raw7866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw7867 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw7867step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 2, -1, 0], ![1, -2, 0, 1]]

def raw7867step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw7868 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7869 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1]]

def raw7869step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1]]

def raw7869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def raw7870 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def raw7871 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, -1, 2]]

def raw7871step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![-1, 3, -1, -1], ![1, -3, 0, 2]]

def raw7871step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, 1, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7872 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, -2, 2]]

def raw7872step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw7872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7873 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![1, -2, -2, 3], ![0, 1, 3, -4]]

def raw7873step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3], ![1, 3, -4]]

def raw7873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 2, -1], ![1, 2, -3], ![-1, -3, 4]]

def raw7873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7874 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![1, -1, -2, 2], ![0, 0, 3, -3]]

def raw7874step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def raw7874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw7877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw7877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7878 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw7878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7880 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1]]

def raw7880step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw7883 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -3, 3], ![1, 2, -3]]

def raw7883step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -1, 0], ![0, 3, -3], ![-1, -2, 3]]

def raw7883step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7884 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw7884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1]]

def raw7885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def raw7886 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0]]

def raw7886step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0]]

def raw7886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw7887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw7887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw7887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw7888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 3, -5]]

def raw7889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![-2, -3, 5]]

def raw7889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![2, 3, -5]]

def raw7890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, -3, 5]]

def raw7890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4]]

def raw7891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -3, 4]]

def raw7891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw7892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw7893 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]

def raw7893step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0]]

def raw7893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def raw7894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def raw7894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7895 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]

def raw7895step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def raw7896 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

def raw7896step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7897 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 1, 2, -4]]

def raw7897step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![-1, -1, -2, 4]]

def raw7897step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw7898 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, -1, 1]]

def raw7898step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, 0, 0], ![0, 1, -3, 2], ![0, -1, 2, -1], ![-1, 1, 1, -1]]

def raw7898step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw7899 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def raw7899step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![0, -1, 2, -1], ![0, 1, -3, 2]]

def raw7899step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, -1, 3, -2]]

def raw7899step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw7900 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7900step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, -2, 3]]

def raw7900step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7901 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw7901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![0, 2, -2], ![0, -3, 3]]

def raw7901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -1, 2], ![0, -2, 2], ![0, 3, -3]]

def raw7901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw7902 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-3, 1, 1, 1], ![4, -2, -2, 0]]

def raw7902step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![1, 1, -2], ![-1, 1, 0]]

def raw7902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw7903 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-3, 1, 2, 0], ![4, -2, -3, 1]]

def raw7903step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![1, 2, -3], ![-1, 0, 1]]

def raw7903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical247
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7904 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, -2, 1, 3], ![3, 1, -2, -2]]

def raw7904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![1, 1, -2], ![-1, 3, -2]]

def raw7904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

def raw7905 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, -2, 2, 2], ![3, 1, -3, -1]]

def raw7905step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![1, 2, -3], ![-1, 2, -1]]

def raw7905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw7906 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, -2, 3, 1], ![3, 1, -4, 0]]

def raw7906step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, -2, 1], ![1, 3, -4], ![-1, 1, 0]]

def raw7906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, -3, 4], ![1, -1, 0]]

def raw7906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7907 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, 1, 1, 0], ![3, -2, -2, 1]]

def raw7907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 1, -2], ![1, 1, -2], ![-1, 0, 1]]

def raw7907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw7908 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-2, 1, 2, -1], ![3, -2, -3, 2]]

def raw7908step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 1, -2], ![1, 2, -3], ![-1, -1, 2]]

def raw7908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw7909 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -3, 1, 3], ![2, 2, -2, -2]]

def raw7909step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![1, 1, -2], ![-1, 3, -2]]

def raw7909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def raw7910 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -3, 2, 2], ![2, 2, -3, -1]]

def raw7910step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![1, 2, -3], ![-1, 2, -1]]

def raw7910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, -2, 3], ![1, -2, 1]]

def raw7910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

def raw7911 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -3, 3, 1], ![2, 2, -4, 0]]

def raw7911step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![1, 3, -4], ![-1, 1, 0]]

def raw7911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, -3, 4], ![1, -1, 0]]

def raw7911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7912 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, -2, 5], ![2, 1, 1, -4]]

def raw7912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, -2, 1], ![-1, 5, -4]]

def raw7912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

def raw7913 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, 1, 2], ![2, 1, -2, -1]]

def raw7913step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![-1, 2, -1]]

def raw7913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def raw7914 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, 2, 1], ![2, 1, -3, 0]]

def raw7914step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, 2, -3], ![-1, 1, 0]]

def raw7914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, -2, 3], ![1, -1, 0]]

def raw7914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7915 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, -2, 3, 0], ![2, 1, -4, 1]]

def raw7915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![1, 3, -4], ![-1, 0, 1]]

def raw7915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, -3, 4], ![1, 0, -1]]

def raw7915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7916 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, 1, 1, -1], ![2, -2, -2, 2]]

def raw7916step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![-1, -1, 2]]

def raw7916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

def raw7917 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![-1, 1, 2, -2], ![2, -2, -3, 3]]

def raw7917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 1, -2], ![1, 2, -3], ![-1, -2, 3]]

def raw7917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

def raw7918 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -4, 2, 2], ![1, 3, -3, -1]]

def raw7918step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -4, 3], ![1, 2, -3], ![-1, 2, -1]]

def raw7918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 4, -3], ![-1, -2, 3], ![1, -2, 1]]

def raw7918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def raw7919 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -3, 1, 2], ![1, 2, -2, -1]]

def raw7919step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![-1, 2, -1]]

def raw7919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -1, 2], ![1, -2, 1]]

def raw7919step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7920 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -3, 2, 1], ![1, 2, -3, 0]]

def raw7920step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -3, 2], ![1, 2, -3], ![-1, 1, 0]]

def raw7920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 3, -2], ![-1, -2, 3], ![1, -1, 0]]

def raw7920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7921 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, -2, 4], ![1, 1, 1, -3]]

def raw7921step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![1, -2, 1], ![-1, 4, -3]]

def raw7921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw7922 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, 1, 1], ![1, 1, -2, 0]]

def raw7922step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![-1, 1, 0]]

def raw7922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw7923 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, 3, -1], ![1, 1, -4, 2]]

def raw7923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![1, 3, -4], ![-1, -1, 2]]

def raw7923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 2, -1], ![-1, -3, 4], ![1, 1, -2]]

def raw7923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def raw7924 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7924step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, -1, 1], ![0, 1, 3, -4], ![0, -1, -1, 2], ![-1, 1, -1, 1]]

def raw7924step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw7925 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw7925step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw7926 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw7927 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7927step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def raw7928 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw7928step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, -1, 1, -1], ![1, 1, 0, -2], ![-1, 0, -1, 2]]

def raw7928step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw7929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def raw7930 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw7930step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw7931 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw7932 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7932step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 0, 1, -2], ![-1, 0, -2, 3]]

def raw7932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw7932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw7933 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, -1, -2, 2]]

def raw7933step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 0, -1], ![1, 1, 0, -2], ![-1, -1, 0, 2]]

def raw7933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw7933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw7934 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7934step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 1, 0, -2], ![-1, -1, -1, 3]]

def raw7934step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw7935 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -3, 4]]

def raw7935step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 1, 1, -3], ![-1, -1, -2, 4]]

def raw7935step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical248
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7936 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, -2, 2]]

def raw7936step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![-1, -1, 2]]

def raw7936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def raw7937 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, -3, 3]]

def raw7937step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![-1, -2, 3]]

def raw7937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw7938 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw7938step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![-1, -2, 3]]

def raw7938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def raw7939 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -2, -3, 4]]

def raw7939step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![1, 2, -3], ![-1, -3, 4]]

def raw7939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

def raw7940 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![1, -4, 2, 1], ![0, 3, -3, 0]]

def raw7940step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -4, 3], ![1, 2, -3], ![-1, 1, 0]]

def raw7940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 4, -3], ![-1, -2, 3], ![1, -1, 0]]

def raw7940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw7941 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![1, -3, 1, 1], ![0, 2, -2, 0]]

def raw7941step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![-1, 1, 0]]

def raw7941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 3, -2], ![-1, -1, 2], ![1, -1, 0]]

def raw7941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw7942 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![1, 1, 1, -3], ![0, -2, -2, 4]]

def raw7942step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![-1, -3, 4]]

def raw7942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw7943 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![-1, -3, 2, 2], ![2, 2, -4, 0]]

def raw7943step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -3, 2], ![2, 2, -4], ![-2, 2, 0]]

def raw7943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-2, -2, 4], ![2, -2, 0]]

def raw7943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

def raw7944 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![-1, 3, -3, 1], ![2, -4, 1, 1]]

def raw7944step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 3, -4], ![2, -3, 1], ![-2, 1, 1]]

def raw7944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -3, 4], ![-2, 3, -1], ![2, -1, -1]]

def raw7944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def raw7945 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![-1, 3, -2, 0], ![2, -4, 0, 2]]

def raw7945step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![1, 3, -4], ![2, -2, 0], ![-2, 0, 2]]

def raw7945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -3, 4], ![-2, 2, 0], ![2, 0, -2]]

def raw7945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

def raw7946 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -3, 2, 1], ![1, 2, -4, 1]]

def raw7946step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -3, 2], ![2, 2, -4], ![-2, 1, 1]]

def raw7946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw7947 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -2, 0, 2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw7947step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, -2, 2], ![0, 2, 0, -2], ![0, -1, 0, 1], ![-1, 0, 2, -1]]

def raw7947step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw7948 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -2, 2, 0], ![1, 1, -4, 2]]

def raw7948step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![2, 2, -4], ![-2, 0, 2]]

def raw7948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, 2, -1], ![-2, -2, 4], ![2, 0, -2]]

def raw7948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw7949 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw7949step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -1, -2, 2], ![0, 1, 1, -2], ![0, -1, 0, 1], ![-1, 1, 1, -1]]

def raw7949step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw7950 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def raw7950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![2, 0, -2], ![-2, -1, 3]]

def raw7950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw7951 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -2, -3, 4]]

def raw7951step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 1, -2], ![2, 1, -3], ![-2, -2, 4]]

def raw7951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def raw7952 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 3, -3, 0], ![1, -4, 1, 2]]

def raw7952step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 3, -4], ![2, -3, 1], ![-2, 0, 2]]

def raw7952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -3, 4], ![-2, 3, -1], ![2, 0, -2]]

def raw7952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def raw7953 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 3, -2, -1], ![1, -4, 0, 3]]

def raw7953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![1, 3, -4], ![2, -2, 0], ![-2, -1, 3]]

def raw7953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-1, -3, 4], ![-2, 2, 0], ![2, 1, -3]]

def raw7953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def raw7954 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![1, -3, 2, 0], ![0, 2, -4, 2]]

def raw7954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -3, 2], ![2, 2, -4], ![-2, 0, 2]]

def raw7954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def raw7955 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![1, -2, 2, -1], ![0, 1, -4, 3]]

def raw7955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -2, 1], ![2, 2, -4], ![-2, -1, 3]]

def raw7955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-1, 2, -1], ![-2, -2, 4], ![2, 1, -3]]

def raw7955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

def raw7956 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 1, 0]]

def raw7956step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-3, 1, 1, 1], ![2, -1, -1, 0]]

def raw7956step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![3, -1, -1, -1], ![-2, 1, 1, 0]]

def raw7956step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7957 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -2, 0, 1]]

def raw7957step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-3, 1, 2, 0], ![2, -1, -2, 1]]

def raw7957step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![3, -1, -2, 0], ![-2, 1, 2, -1]]

def raw7957step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw7958 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, -2, 0, 1]]

def raw7958step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-3, 2, 1, 0], ![2, -2, -1, 1]]

def raw7958step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![3, -2, -1, 0], ![-2, 2, 1, -1]]

def raw7958step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

def raw7959 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw7959step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 2, -1], ![0, 1, 1, -2], ![0, 1, -2, 1], ![-1, 0, -1, 2]]

def raw7959step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7960 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1]]

def raw7960step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 2, -1], ![0, 1, 1, -2], ![0, 1, -3, 2], ![-1, 0, 0, 1]]

def raw7960step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw7961 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, -1, 3, -2], ![1, -1, -1, 1]]

def raw7961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, -1, -1], ![-2, 3, -1], ![1, -2, 1]]

def raw7961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw7962 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def raw7962step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-2, -1, 3, 0], ![1, 1, -3, 1]]

def raw7962step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![2, 1, -3, 0], ![-1, -1, 3, -1]]

def raw7962step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw7963 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1]]

def raw7963step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-2, 1, 1, 0], ![1, -1, -1, 1]]

def raw7963step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, 0, 2], ![2, -1, -1, 0], ![-1, 1, 1, -1]]

def raw7963step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def raw7964 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, -2, 1], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def raw7964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![-2, 3, -1], ![1, -3, 2]]

def raw7964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

def raw7965 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def raw7966 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 0, 1]]

def raw7966step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def raw7967 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def raw7967step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![-1, -1, 3, -1], ![0, 1, -3, 2]]

def raw7967step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7968 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, -1, -3, 4], ![0, -1, 2, -1], ![1, 0, 1, -2]]

def raw7968step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 0, 1], ![0, 1, 3, -4], ![0, 1, -2, 1], ![-1, 0, -1, 2]]

def raw7968step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7969 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def raw7969step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, -2, 0, 1], ![0, 1, 3, -4], ![0, 0, -2, 2], ![-1, 1, -1, 1]]

def raw7969step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw7970 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -2, 3]]

def raw7970step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, 1, 1, -2], ![-1, -1, -1, 3]]

def raw7970step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw7971 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -2, -3, 4]]

def raw7971step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, 1, 2, -3], ![-1, -1, -2, 4]]

def raw7971step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw7972 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, -2, -3, 4]]

def raw7972step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![0, 2, 1, -3], ![-1, -2, -1, 4]]

def raw7972step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw7973 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 2, -2], ![1, -2, -2, 3]]

def raw7973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![0, 2, -2], ![-1, -2, 3]]

def raw7973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw7974 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -3, 4]]

def raw7974step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![2, 0, 0, -2], ![1, 1, 1, -3], ![-2, -1, -1, 4]]

def raw7974step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, 1, -3]]

def raw7975 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, 1, -1], ![1, -2, -2, 3]]

def raw7975step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![1, 1, -2], ![-2, -1, 3]]

def raw7975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def raw7976 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, 2, -2], ![1, -2, -3, 4]]

def raw7976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![2, 0, -2], ![1, 2, -3], ![-2, -2, 4]]

def raw7976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def raw7977 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -3, 2]]

def raw7977step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![3, -3], ![-2, 2]]

def raw7977step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw7979 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7979step0 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7979step1 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7979step2 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7979step3 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw7980 : Matrix (Fin 4) (Fin 1) ℤ := ![![0], ![0], ![0], ![0]]

def raw7980step0 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7980step1 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7980step2 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7980step3 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7980step4 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw7981 : Matrix (Fin 5) (Fin 1) ℤ := ![![0], ![0], ![0], ![0], ![0]]

def raw7981step0 : Matrix (Fin 4) (Fin 1) ℤ := ![![0], ![0], ![0], ![0]]

def raw7981step1 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7981step2 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7981step3 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7981step4 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7981step5 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw7982 : Matrix (Fin 6) (Fin 1) ℤ := ![![0], ![0], ![0], ![0], ![0], ![0]]

def raw7982step0 : Matrix (Fin 5) (Fin 1) ℤ := ![![0], ![0], ![0], ![0], ![0]]

def raw7982step1 : Matrix (Fin 4) (Fin 1) ℤ := ![![0], ![0], ![0], ![0]]

def raw7982step2 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![0]]

def raw7982step3 : Matrix (Fin 2) (Fin 1) ℤ := ![![0], ![0]]

def raw7982step4 : Matrix (Fin 1) (Fin 1) ℤ := ![![0]]

def raw7982step5 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw7982step6 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def raw7983 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![0, 2, -2], ![1, 0, -1]]

def raw7983step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw7984 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 2, -1], ![1, 2, -3]]

def raw7984step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-1, -2, 3]]

def raw7984step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw7985 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 3, -2], ![1, 1, -2]]

def raw7985step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

def raw7986 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![-1, 4, -3], ![1, 0, -1]]

def raw7986step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 4, -4], ![1, -1, 0]]

def raw7987 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![0, 2, -2], ![0, 2, -2]]

def raw7987step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def raw7988 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -4, 4], ![0, 4, -4]]

def raw7988step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

def raw7989 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 2, -3]]

def raw7989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -2, 3]]

def raw7989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def raw7990 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 1, -2]]

def raw7990step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def raw7991 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, -1, 2], ![0, 4, -4], ![1, 0, -1]]

def raw7991step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

def raw7992 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw7992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7993 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1]]

def raw7993step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def raw7995 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 2, -1], ![1, 1, -2]]

def raw7995step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw7996 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![1, 0, -1]]

def raw7996step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

def raw7997 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 4, -3], ![1, -1, 0]]

def raw7997step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

def raw7998 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1]]

def raw7998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw7999 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1]]

def raw7999step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw800 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]

def raw801 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]

def raw802 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]

def raw802step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw803 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -2, 1], ![1, 3, -4]]

def raw804 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]

def raw804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw805 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw806 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]

def raw806step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw807 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]

def raw807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw808 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw812 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]

def raw812step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def raw813 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]

def raw813step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]

def raw813step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw814 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]

def raw815 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -4, 2], ![1, 3, -4]]

def raw815step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 3, -4], ![2, -4, 2]]

def raw817 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, -2, -1, 2], ![2, 1, -1, -2]]

def raw817step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, -1, -1], ![0, 2, -2]]

def raw817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def raw818 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, -2, 2, -1], ![2, 1, -4, 1]]

def raw818step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 2, -4], ![0, -1, 1]]

def raw818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def raw819 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, 1, -3, 1], ![2, -2, 1, -1]]

def raw819step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -3, 1], ![0, 1, -1]]

def raw819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def raw820 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![1, 2, -2, -1], ![2, -3, 0, 1]]

def raw820step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -2, 0], ![0, -1, 1]]

def raw820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def raw821 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 1, 2, 0], ![2, -2, -1, 1], ![1, 1, -1, -1]]

def raw821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, -1, -1], ![0, 1, -1]]

def raw821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-2, 1, 1], ![0, -1, 1]]

def raw821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw822 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]

def raw823 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 0, -1], ![2, 1, -3]]

def raw823step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]

def raw824 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 1, -2], ![2, 0, -2]]

def raw824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]

def raw825 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]

def raw825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]

def raw825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw826 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def raw828 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8001 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1]]

def raw8001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def raw8002 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0]]

def raw8002step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def raw8002step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw8003 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0]]

def raw8003step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 2, -2]]

def raw8003step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8005 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3]]

def raw8005step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw8006 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![0, 0, 0]]

def raw8006step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3]]

def raw8006step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def raw8007 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![0, 4, -4], ![0, -1, 1]]

def raw8007step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![4, -4], ![-1, 1]]

def raw8007step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

def raw8008 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8008step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -1, 0], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw8008step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8009 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw8009step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, 0, -3, -1]]

def raw8009step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8010 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -2, 1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 0, 1, 0]]

def raw8010step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8011 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw8011step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-1, -1, 1, 1]]

def raw8011step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8012 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -3, 2], ![0, -2, 0, 2], ![-1, 0, 1, 0]]

def raw8012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def raw8013 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8013step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![1, 0, -1, 0], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw8013step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8014 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8014step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![1, 0, -2, 1], ![0, -2, 0, 2], ![-1, 0, 1, 0]]

def raw8014step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8015 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, 0, -1]]

def raw8015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, -1, -2, -1]]

def raw8015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw8016 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, 0, 0, -1]]

def raw8016step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-1, 0, 0, 1]]

def raw8016step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8017 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![-1, 0, 1, 0]]

def raw8017step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw8018 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, 0, 0, 0]]

def raw8018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2]]

def raw8018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8019 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, 0, 0, 0]]

def raw8019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, -1, -3, 0]]

def raw8019step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, -1, -3, 0]]

def raw8019step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw8019step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw8020 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8020step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -2, 2], ![1, -2, -1, 2], ![-1, 0, 1, 0]]

def raw8020step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw8021 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2]]

def raw8021step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw8022 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, 0, 0, 0]]

def raw8022step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2]]

def raw8022step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw8023 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1]]

def raw8023step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw8024 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2]]

def raw8024step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

def raw8025 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw8025step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -1, 0], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 0, 0, 1]]

def raw8025step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8026 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 2, 0], ![-1, 1, 1, -1], ![3, 0, -3, 0]]

def raw8026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw8027 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8027step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1]]

def raw8027step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw8028 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8028step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0]]

def raw8028step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw8029 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw8029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-1, -1, 2, 0]]

def raw8029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def raw8030 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw8030step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -3, 2], ![0, -1, 2, -1], ![-1, -1, 0, 2]]

def raw8030step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def raw8031 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw8031step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8032 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8032step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![-1, -1, 3, -1], ![3, 1, -4, 0]]

def raw8032step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw8033 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8033step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 0, 1, 0]]

def raw8033step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8034 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 2, 3, -4], ![1, 0, -2, 1]]

def raw8034step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![-1, 3, -2], ![3, -4, 1]]

def raw8034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def raw8035 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw8035step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -1, 1], ![1, 0, -1, 0], ![0, -2, 1, 1], ![-1, 0, 0, 1]]

def raw8035step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8036 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8036step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -1, 1], ![1, -1, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0]]

def raw8036step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8037 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8037step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![-1, 1, 1, -1], ![3, -1, -2, 0]]

def raw8037step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw8038 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, -1, 0], ![1, 0, 0, -1]]

def raw8038step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8039 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![0, 0, 0, 0]]

def raw8039step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1]]

def raw8039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8040 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, 0, -1, 0]]

def raw8040step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, -1, 1], ![-1, 0, 1, 0]]

def raw8040step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def raw8041 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8041step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1]]

def raw8041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw8042 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8042step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 1, -3], ![0, -1, 1]]

def raw8042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw8043 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8043step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8044 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8044step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -2, 2], ![0, -1, 1, 0], ![1, -1, 0, 0], ![-1, 0, 0, 1]]

def raw8044step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8045 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1]]

def raw8045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8046 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1]]

def raw8046step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8047 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0]]

def raw8047step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw8048 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4]]

def raw8048step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw8049 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, 0, -1]]

def raw8049step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![-1, -1, 2, 0], ![3, 0, -2, -1]]

def raw8049step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8050 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, 0, 0]]

def raw8050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-2, 1, 1, 0], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw8050step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw8050step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8050step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8051 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![-1, 0, 2, -1], ![3, -1, -2, 0]]

def raw8051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw8052 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 0, 0]]

def raw8052step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2]]

def raw8052step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]

def raw8052step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

def raw8053 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8053step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![-1, 2, -1], ![3, -4, 1]]

def raw8053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 4, -1]]

def raw8053step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -2, 0], ![1, -2, 1], ![-3, 4, -1]]

def raw8053step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw8054 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8054step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8055 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw8055step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, 0, 1, -2], ![0, -1, -3, 4], ![-1, -1, 2, 0]]

def raw8055step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw8056 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8056step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw8057 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8057step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 2, 0], ![0, 0, 2, -2], ![2, 1, -4, 1]]

def raw8057step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![2, 0, -2, 0], ![0, 0, -2, 2], ![-2, -1, 4, -1]]

def raw8057step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8058 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8058step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8059 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8059step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8060 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw8060step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw8061 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8061step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8062 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, -2, 3, -1], ![2, 2, -4, 0]]

def raw8062step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8063 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw8063step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, -1, 1, -1], ![0, -1, 2, -1], ![-1, 0, -3, 4]]

def raw8063step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical252
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8064 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, -1, 2, -1], ![2, 1, -3, 0]]

def raw8064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8065 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw8065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, -1, 1, -1], ![0, -1, -3, 4], ![-1, 0, 2, -1]]

def raw8065step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw8066 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def raw8066step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 0, 2, -1]]

def raw8066step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def raw8067 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 2, 2, -3], ![1, 0, -2, 1]]

def raw8067step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![0, 2, -2], ![2, -3, 1]]

def raw8067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 3, -1]]

def raw8067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw8068 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 2, 3, -4], ![1, 0, -3, 2]]

def raw8068step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![0, 3, -3], ![2, -4, 2]]

def raw8068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -2, 0], ![0, -3, 3], ![-2, 4, -2]]

def raw8068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def raw8069 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4]]

def raw8069step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 2, -2], ![0, -2, -2, 4]]

def raw8069step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, -2, 4]]

def raw8069step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw8070 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8070step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, -1, -3, 4], ![-1, 0, 1, 0]]

def raw8070step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw8071 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8071step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![0, -1, 2, -1], ![2, 1, -3, 0]]

def raw8071step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw8072 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![-1, 2, 3, -4], ![1, 0, -2, 1]]

def raw8072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![0, -1, 3, -2], ![2, 1, -4, 1]]

def raw8072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![2, 0, -2, 0], ![0, 1, -3, 2], ![-2, -1, 4, -1]]

def raw8072step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw8073 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def raw8073step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -2, 0], ![-2, -1, -1, 4]]

def raw8073step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw8074 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8074step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8074step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw8075 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8075step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw8076 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8076step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw8077 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 3, -3], ![1, 0, -1, 0]]

def raw8077step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, -3, 3], ![-1, 0, 1, 0]]

def raw8077step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw8078 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8078step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, 0, -2, 4]]

def raw8078step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw8079 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![0, 0, -1, 1]]

def raw8079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4], ![0, -1, 1]]

def raw8079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw8080 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8080step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8081 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8081step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw8082 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8082step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8082step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def raw8083 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8083step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8083step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw8084 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8084step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw8085 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8085step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8086 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, -2, 1]]

def raw8086step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -1, 1], ![1, -2, -1, 2], ![-1, 0, 2, -1]]

def raw8086step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw8087 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, -2, 1], ![1, 0, 0, -1]]

def raw8087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8088 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![0, 0, 0, 0]]

def raw8088step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0]]

def raw8088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8089 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, 0, -1, 1]]

def raw8089step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![0, -1, 1]]

def raw8089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw8090 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8091 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, 0, 0, -1]]

def raw8091step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8092 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, 0, 0, 0]]

def raw8092step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0]]

def raw8092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8093 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0]]

def raw8093step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

def raw8094 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8094step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -3, 3], ![1, -1, 1, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0]]

def raw8094step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def raw8095 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, 0, -1, 0]]

def raw8095step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -3, 3], ![0, -1, 1, 0], ![1, -1, 1, -1], ![-1, 0, 1, 0]]

def raw8095step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8096 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, 0, -1, 1]]

def raw8096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1]]

def raw8096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8097 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1]]

def raw8097step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, 0, -3, 3], ![0, -2, 3, -1]]

def raw8097step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![-2, 3, -1]]

def raw8097step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

def raw8098 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4]]

def raw8098step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]

def raw8098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw8098step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw8098step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw8099 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3]]

def raw8099step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 2, -1], ![0, -1, -2, 3]]

def raw8099step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw8099step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8100 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![0, -1, 2, -1], ![2, 0, -2, 0]]

def raw8100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8101 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8101step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw8102 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, -1, 1]]

def raw8102step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1]]

def raw8102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1]]

def raw8102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8103 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8103step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw8104 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, 0, -2, 1]]

def raw8104step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 0, 1], ![1, -1, -2, 2], ![-1, 0, 2, -1]]

def raw8104step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8105 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, -1, 1]]

def raw8105step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -1, 0, 1], ![0, -1, -1, 2], ![0, 0, 1, -1]]

def raw8105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1]]

def raw8105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw8106 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8106step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8106step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-2, -1, 3], ![0, 1, -1]]

def raw8106step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw8107 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 0, 2], ![0, 2, 2, -4], ![0, 0, -2, 2]]

def raw8107step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, 0, -2], ![0, -2, -2, 4], ![0, 0, 2, -2]]

def raw8107step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-2, -2, 4], ![0, 2, -2]]

def raw8107step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def raw8108 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8108step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8109 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8109step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8110 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw8110step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw8111 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8111step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8112 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8112step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8113 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw8113step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8114 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8114step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8115 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8115step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![1, 0, -1, 0], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 0, 0, 1]]

def raw8115step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw8116 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8116step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![1, 0, -1, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 1, 0]]

def raw8116step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8117 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8117step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![1, 0, -1, 0], ![0, -2, 2, 0], ![-1, 0, 0, 1]]

def raw8117step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw8118 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8118step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8119 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -2, 2], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8119step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![1, -2, 2, -1], ![1, 2, -3, 0]]

def raw8119step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw8120 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 1, -3]]

def raw8120step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 2, -2], ![0, -2, -1, 3]]

def raw8120step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw8120step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8121 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8121step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 2, -2], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 2, -2], ![-2, -2, 4], ![0, 1, -1]]

def raw8121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw8122 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8122step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8123 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw8123step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw8124 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8124step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw8124step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw8125 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8125step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw8125step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw8126 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8126step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -2, 3], ![-1, 0, 1, 0]]

def raw8126step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw8127 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8127step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8127step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical254
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8128 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8128step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8128step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw8129 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8129step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 0, -2, 4]]

def raw8129step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw8130 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8130step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8131 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8131step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8131step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw8132 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8132step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw8133 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, 0, 0, -1]]

def raw8133step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8134 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8134step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8135 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8135step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8135step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw8136 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 0, 0]]

def raw8136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2]]

def raw8136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw8137 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, -1, 1]]

def raw8137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![0, -1, 1]]

def raw8137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

def raw8138 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8138step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw8139 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8139step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8140 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8140step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8140step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw8141 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw8141step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8142 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8142step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8143 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8143step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8144 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8144step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8145 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 2, -2, 1], ![1, 0, 0, -1]]

def raw8145step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![1, 1, -2, 0], ![1, -1, 1, -1]]

def raw8145step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw8146 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, -3, 2], ![1, 0, 0, -1]]

def raw8146step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 3, -2], ![-1, 0, 0, 1]]

def raw8146step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def raw8147 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![0, 0, 0, 0]]

def raw8147step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -2, 3, -1], ![0, 0, 0, 0]]

def raw8147step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -2, 3, -1]]

def raw8147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw8147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw8148 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8148step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8149 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8149step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1]]

def raw8149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw8149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw8150 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, 0, 0, -1]]

def raw8150step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8151 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![1, 0, -1, 0]]

def raw8151step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![-1, 0, 1, 0]]

def raw8151step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8152 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, 0, 0, 0]]

def raw8152step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 0, 0]]

def raw8152step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0]]

def raw8152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]

def raw8152step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def raw8153 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, 0, -1, 1]]

def raw8153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1]]

def raw8153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8154 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![0, 0, 0, 0]]

def raw8154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -2, 2, 0], ![0, 0, 0, 0]]

def raw8154step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -2, 2, 0]]

def raw8154step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]

def raw8154step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw8155 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 2, -3, 1]]

def raw8155step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -2, 2], ![0, -2, 3, -1]]

def raw8155step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -2, 2], ![-2, 3, -1]]

def raw8155step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

def raw8156 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3]]

def raw8156step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

def raw8157 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2]]

def raw8157step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

def raw8158 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, 0, -1, 0]]

def raw8158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw8159 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, -1, 1]]

def raw8159step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![0, -1, 1]]

def raw8159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8160 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8160step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8161 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1]]

def raw8161step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def raw8162 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0]]

def raw8162step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def raw8164 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1]]

def raw8164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def raw8165 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0]]

def raw8165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw8166 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1]]

def raw8166step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def raw8167 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![1, 0, -1]]

def raw8167step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

def raw8168 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 1, -2]]

def raw8168step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def raw8169 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![1, -1, 0]]

def raw8169step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

def raw8170 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 4, -3], ![0, -2, 2], ![1, 0, -1]]

def raw8170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

def raw8171 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![0, 4, -4]]

def raw8171step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![4, -4]]

def raw8171step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

def raw8172 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![-1, 4, -3], ![1, -1, 0]]

def raw8172step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def raw8173 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def raw8173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![-2, -1, 3]]

def raw8173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw8174 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def raw8174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8175 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2], ![-3, 0, 3]]

def raw8175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def raw8176 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def raw8176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw8177 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def raw8177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw8178 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def raw8179 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def raw8179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw8180 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def raw8180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def raw8181 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def raw8181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw8182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def raw8182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw8183 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![0, -1, 1]]

def raw8183step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![4, -4], ![-1, 1]]

def raw8183step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def raw8184 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def raw8184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def raw8185 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def raw8185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def raw8186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw8187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def raw8187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def raw8188 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def raw8188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw8189 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def raw8189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0]]

def raw8189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw8191 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1]]

def raw8191step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8192 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0]]

def raw8192step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def raw8193 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2], ![-3, 0, 3]]

def raw8193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def raw8195 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0]]

def raw8195step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1]]

def raw8195step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def raw8197 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

def raw8197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw8198 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def raw8198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw8199 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def raw8199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw8200 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def raw8200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw8201 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8202 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def raw8203 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def raw8203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8204 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1]]

def raw8204step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw8204step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8205 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def raw8206 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def raw8206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw8207 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def raw8208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def raw8208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8209 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def raw8209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8210 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw8211 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def raw8211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw8212 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def raw8212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def raw8213 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def raw8213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw8214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def raw8214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8215 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2]]

def raw8215step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8216 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2], ![0, 0, 0]]

def raw8216step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2]]

def raw8216step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

def raw8217 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![0, -1, 1]]

def raw8217step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![3, -3], ![-1, 1]]

def raw8217step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def raw8218 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def raw8218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8219 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def raw8219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def raw8220 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def raw8220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw8221 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 1, 0, 3], ![4, 1, -2, -3]]

def raw8221step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 1, 1], ![2, 0, -2], ![0, 3, -3]]

def raw8221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![-2, 0, 2], ![0, -3, 3]]

def raw8221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw8222 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 2, -1, 3], ![4, 0, -1, -3]]

def raw8222step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 2, 0], ![2, -1, -1], ![0, 3, -3]]

def raw8222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def raw8223 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 2, 0, 2], ![4, 0, -2, -2]]

def raw8223step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 2, 0], ![2, 0, -2], ![0, 2, -2]]

def raw8223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8224 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 3, -1, 2], ![4, -1, -1, -2]]

def raw8224step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 3, -1], ![2, -1, -1], ![0, 2, -2]]

def raw8224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

def raw8225 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 1, -1, 3], ![3, 1, -1, -3]]

def raw8225step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 1, 1], ![2, -1, -1], ![0, 3, -3]]

def raw8225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

def raw8226 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 1, 0, 2], ![3, 1, -2, -2]]

def raw8226step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 1, 1], ![2, 0, -2], ![0, 2, -2]]

def raw8226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]

def raw8226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw8227 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 2, -1, 2], ![3, 0, -1, -2]]

def raw8227step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 2, 0], ![2, -1, -1], ![0, 2, -2]]

def raw8227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def raw8228 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 2, 0, 1], ![3, 0, -2, -1]]

def raw8228step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 2, 0], ![2, 0, -2], ![0, 1, -1]]

def raw8228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def raw8229 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 2, 2, -1], ![3, 0, -4, 1]]

def raw8229step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 2, 0], ![2, 2, -4], ![0, -1, 1]]

def raw8229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -2, 4], ![0, 1, -1]]

def raw8229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw8230 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 3, -1, 1], ![3, -1, -1, -1]]

def raw8230step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 3, -1], ![2, -1, -1], ![0, 1, -1]]

def raw8230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw8231 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 4, 0, -1], ![3, -2, -2, 1]]

def raw8231step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 4, -2], ![2, 0, -2], ![0, -1, 1]]

def raw8231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def raw8232 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 0, 3, -1], ![2, 2, -5, 1]]

def raw8232step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 0, 2], ![2, 3, -5], ![0, -1, 1]]

def raw8232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, -3, 5], ![0, 1, -1]]

def raw8232step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw8233 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 1, -1, 2], ![2, 1, -1, -2]]

def raw8233step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 1, 1], ![2, -1, -1], ![0, 2, -2]]

def raw8233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def raw8234 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 1, 2, -1], ![2, 1, -4, 1]]

def raw8234step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 1, 1], ![2, 2, -4], ![0, -1, 1]]

def raw8234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw8235 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 2, -1, 1], ![2, 0, -1, -1]]

def raw8235step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![2, -1, -1], ![0, 1, -1]]

def raw8235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def raw8236 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 2, 1, -1], ![2, 0, -3, 1]]

def raw8236step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![2, 1, -3], ![0, -1, 1]]

def raw8236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![-2, -1, 3], ![0, 1, -1]]

def raw8236step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw8237 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 2, 2, -2], ![2, 0, -4, 2]]

def raw8237step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![2, 2, -4], ![0, -2, 2]]

def raw8237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![-2, -2, 4], ![0, 2, -2]]

def raw8237step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw8238 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 4, 0, -2], ![2, -2, -2, 2]]

def raw8238step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 4, -2], ![2, 0, -2], ![0, -2, 2]]

def raw8238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def raw8239 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8239step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8240 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8240step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8241 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8241step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8242 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8242step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw8243 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, 1, 0], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8243step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8244 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, 3, -2], ![1, 2, -5, 2]]

def raw8244step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![2, 3, -5], ![0, -2, 2]]

def raw8244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, 0, -2], ![-2, -3, 5], ![0, 2, -2]]

def raw8244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def raw8245 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 1, 2, -2], ![1, 1, -4, 2]]

def raw8245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![2, 2, -4], ![0, -2, 2]]

def raw8245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -1, -1], ![-2, -2, 4], ![0, 2, -2]]

def raw8245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def raw8246 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 2, 1, -2], ![1, 0, -3, 2]]

def raw8246step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![2, 1, -3], ![0, -2, 2]]

def raw8246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -2, 0], ![-2, -1, 3], ![0, 2, -2]]

def raw8246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def raw8247 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -2, 2], ![0, 2, 0, -2]]

def raw8247step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![2, 0, -2]]

def raw8247step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

def raw8248 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8248step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8249 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8249step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8250 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8250step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8251 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, 0, -1, 0]]

def raw8251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8252 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8252step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8253 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8253step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8254 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8254step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw8255 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1]]

def raw8255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]

def raw8255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical258
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8256 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, 0, -1, 0]]

def raw8256step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8257 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, -1, 1]]

def raw8257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]

def raw8257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw8258 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![0, 0, -1, 1]]

def raw8258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![0, -1, 1]]

def raw8258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw8259 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, 1, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8259step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![1, -1, 3, -3], ![0, -1, 0, 1], ![-1, 0, 0, 1]]

def raw8259step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw8260 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8260step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![-1, 0, 0, 1]]

def raw8260step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8261 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8261step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![0, -1, 3, -2], ![0, -1, 0, 1], ![0, 0, 0, 0]]

def raw8261step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![0, -1, 3, -2], ![0, -1, 0, 1]]

def raw8261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1]]

def raw8261step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def raw8262 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, -1, 1, -1], ![-1, 3, -3, 1]]

def raw8262step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![2, 1, -3], ![0, -1, 1]]

def raw8262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def raw8263 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, 0, 0, -1], ![-1, 2, -2, 1]]

def raw8263step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![2, 0, -2], ![0, -1, 1]]

def raw8263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def raw8264 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, 0, 1, -2], ![-1, 2, -3, 2]]

def raw8264step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![2, 1, -3], ![0, -2, 2]]

def raw8264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![2, 0, -2], ![-2, -1, 3], ![0, 2, -2]]

def raw8264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def raw8265 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, 1, 1, -3], ![-1, 1, -3, 3]]

def raw8265step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![2, 1, -3], ![0, -3, 3]]

def raw8265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![2, -1, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def raw8266 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![2, -1, 1, -2], ![-2, 3, -3, 2]]

def raw8266step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-2, -1, 3], ![2, 1, -3], ![0, -2, 2]]

def raw8266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def raw8267 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![2, 0, 0, -2], ![-2, 2, -2, 2]]

def raw8267step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-2, 0, 2], ![2, 0, -2], ![0, -2, 2]]

def raw8267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def raw8268 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![2, 0, 1, -3], ![-2, 2, -3, 3]]

def raw8268step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-2, 0, 2], ![2, 1, -3], ![0, -3, 3]]

def raw8268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, 0, -2], ![-2, -1, 3], ![0, 3, -3]]

def raw8268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def raw8269 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 3, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8269step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 3, -1, -1]]

def raw8269step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw8270 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 3, -1], ![0, 1, -3, 2], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 2, 0, -1]]

def raw8270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw8271 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 3, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 2, -1, 0]]

def raw8271step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 2, -1, 0]]

def raw8271step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![3, -3, 0], ![-1, 2, -1]]

def raw8271step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

def raw8272 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8272step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8273 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw8273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw8274 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![-3, 3, 0, 0], ![4, -2, -2, 0]]

def raw8274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![3, -3, 0, 0], ![-4, 2, 2, 0]]

def raw8274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw8275 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw8275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 1, -1, 1]]

def raw8275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw8276 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![1, -1, -1, 1], ![0, -1, -2, 3], ![-1, 1, 0, 0]]

def raw8276step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def raw8277 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw8277step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw8277step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw8278 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, -1, 2, -1], ![0, 2, 1, -3]]

def raw8278step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 1, -2, 1], ![0, -2, -1, 3]]

def raw8278step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]

def raw8278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

def raw8279 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2]]

def raw8279step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw8279step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw8279step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def raw8280 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8280step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8281 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, 1, -1]]

def raw8281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![-3, 1, 1, 1], ![4, -1, -2, -1]]

def raw8281step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw8282 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, 0, 0]]

def raw8282step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![-1, 1, 0, 0]]

def raw8282step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw8283 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, 1, 0]]

def raw8283step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![0, 1, -1, 0]]

def raw8283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2], ![1, -1, 0]]

def raw8283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def raw8284 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, 2, -1]]

def raw8284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -1, 1], ![0, -2, 0, 2], ![0, 1, -2, 1]]

def raw8284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-2, 0, 2], ![1, -2, 1]]

def raw8284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def raw8285 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -1, 0, 0]]

def raw8285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw8285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw8285step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8286 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2]]

def raw8286step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

def raw8287 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -1, 1, 0]]

def raw8287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -2, 2], ![0, -2, 0, 2], ![0, 1, -1, 0]]

def raw8287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 0, 2], ![1, -1, 0]]

def raw8287step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8288 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 1, 1, -2], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw8288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![-3, 1, 2, 0], ![4, -2, -2, 0]]

def raw8288step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![3, -1, -2, 0], ![-4, 2, 2, 0]]

def raw8288step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

def coordinateChunk0 : Array (Fin 909) := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64]

end MUB6.Certificate.PairSourceBridge

end OAI
end


