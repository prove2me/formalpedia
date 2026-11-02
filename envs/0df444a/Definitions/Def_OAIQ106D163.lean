-- Prove2me | Definitions.Def_OAIQ106D163
-- name    : OAIQ106D163
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:26:17.213841+00:00
-- url     : https://prove2.me/theorems/f99ee859-2a24-47eb-83c2-0a5fc7d15d5c
-- title:
--   Definitions bundle OAIQ106D163 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 496 declarations of OpenAI's Lean: 496 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow16881`, `OAI.MUB6.Certificate.GramRows.rawRow16882`, `OAI.MUB6.Certificate.GramRows.rawRow16883`, `OAI.MUB6.Certificate.GramRows.rawRow16884`, `OAI.MUB6.Certificate.GramRows.rawRow16885`, `OAI.MUB6.Certificate.GramRows.rawRow16886`, `OAI.MUB6.Certificate.GramRows.rawRow16887`, `OAI.MUB6.Certificate.GramRows.rawRow16888`, `OAI.MUB6.Certificate.GramRows.rawRow16889`, `OAI.MUB6.Certificate.GramRows.rawRow1689`, `OAI.MUB6.Certificate.GramRows.rawRow16890`, `OAI.MUB6.Certificate.GramRows.rawRow16891`, `OAI.MUB6.Certificate.GramRows.rawRow16892`, `OAI.MUB6.Certificate.GramRows.rawRow16893`, `OAI.MUB6.Certificate.GramRows.rawRow16894`, `OAI.MUB6.Certificate.GramRows.rawRow16895`, `OAI.MUB6.Certificate.GramRows.rawRow16896`, `OAI.MUB6.Certificate.GramRows.rawRow16897`, `OAI.MUB6.Certificate.GramRows.rawRow16898`, `OAI.MUB6.Certificate.GramRows.rawRow16899`, `OAI.MUB6.Certificate.GramRows.rawRow1690`, `OAI.MUB6.Certificate.GramRows.rawRow16900`, `OAI.MUB6.Certificate.GramRows.rawRow16901`, `OAI.MUB6.Certificate.GramRows.rawRow16902`, `OAI.MUB6.Certificate.GramRows.rawRow16903`, `OAI.MUB6.Certificate.GramRows.rawRow16904`, `OAI.MUB6.Certificate.GramRows.rawRow16905`, `OAI.MUB6.Certificate.GramRows.rawRow16906`, `OAI.MUB6.Certificate.GramRows.rawRow16907`, `OAI.MUB6.Certificate.GramRows.rawRow16908`, `OAI.MUB6.Certificate.GramRows.rawRow16909`, `OAI.MUB6.Certificate.GramRows.rawRow1691`, `OAI.MUB6.Certificate.GramRows.rawRow16910`, `OAI.MUB6.Certificate.GramRows.rawRow16911`, `OAI.MUB6.Certificate.GramRows.rawRow16912`, `OAI.MUB6.Certificate.GramRows.rawRow16913`, `OAI.MUB6.Certificate.GramRows.rawRow16914`, `OAI.MUB6.Certificate.GramRows.rawRow16915`, `OAI.MUB6.Certificate.GramRows.rawRow16916`, `OAI.MUB6.Certificate.GramRows.rawRow16917` and 456 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block155`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block155.lean), [`MutuallyUnbiased_GramRows_Block156`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block156.lean), [`MutuallyUnbiased_GramRows_Block157`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block157.lean), [`MutuallyUnbiased_GramRows_Block158`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block158.lean), [`MutuallyUnbiased_GramRows_Block159`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block159.lean), [`MutuallyUnbiased_GramRows_Block168`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block168.lean), [`MutuallyUnbiased_GramRows_Block37`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block37.lean), [`MutuallyUnbiased_TaoCertificate_TargetMerge2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/TargetMerge2.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D090`, `OAIQ106D092`, `OAIQ106D094` and `OAIQ106D140` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D200`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094
import Definitions.Def_OAIQ106D140

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16881 : Integer.Sparse Key := [(key798, 4), (key804, 4), (key771, 4), (key873, -4), (key798, -4), (key804, -4), (key804, -4), (key771, -4), (key779, -4), (key804, 12)]

def rawRow16882 : Integer.Sparse Key := [(key804, 4), (key771, 4), (key798, 4), (key804, -4), (key873, -4), (key798, -4), (key779, -4), (key804, -4), (key771, -4), (key804, 12)]

def rawRow16883 : Integer.Sparse Key := [(key804, 4), (key798, 4), (key771, 4), (key873, -4), (key804, -4), (key798, -4), (key804, -4), (key779, -4), (key771, -4), (key804, 12)]

def rawRow16884 : Integer.Sparse Key := [(key798, 4), (key798, 4), (key873, 4), (key771, -4), (key804, -4), (key804, -4), (key771, -4), (key804, -4), (key804, -4), (key779, 12)]

def rawRow16885 : Integer.Sparse Key := [(key798, 4), (key873, 4), (key798, 4), (key804, -4), (key771, -4), (key804, -4), (key804, -4), (key771, -4), (key804, -4), (key779, 12)]

def rawRow16886 : Integer.Sparse Key := [(key873, 4), (key798, 4), (key798, 4), (key804, -4), (key804, -4), (key771, -4), (key804, -4), (key804, -4), (key771, -4), (key779, 12)]

def rawRow16887 : Integer.Sparse Key := [(key2147, -1), (key2152, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2176, 2), (key2176, 2), (key2187, 2), (key2147, -1), (key2152, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2240, 2), (key2246, 2), (key2240, 2), (key2253, 2), (key2246, 2), (key2253, 2), (key2276, -1), (key2279, -1), (key2276, -1), (key2287, -1), (key2279, -1), (key2287, -1), (key2176, 2), (key2176, 2), (key2187, 2), (key2276, -1), (key2279, -1), (key2276, -1), (key2287, -1), (key2279, -1), (key2287, -1)]

def rawRow16888 : Integer.Sparse Key := [(key2152, -1), (key2147, -1), (key2166, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2176, 2), (key2187, 2), (key2176, 2), (key2152, -1), (key2147, -1), (key2166, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2246, 2), (key2240, 2), (key2253, 2), (key2240, 2), (key2253, 2), (key2246, 2), (key2279, -1), (key2276, -1), (key2287, -1), (key2276, -1), (key2287, -1), (key2279, -1), (key2176, 2), (key2187, 2), (key2176, 2), (key2279, -1), (key2276, -1), (key2287, -1), (key2276, -1), (key2287, -1), (key2279, -1)]

def rawRow16889 : Integer.Sparse Key := [(key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2147, -1), (key2147, -1), (key2187, 2), (key2176, 2), (key2176, 2), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2147, -1), (key2147, -1), (key2253, 2), (key2253, 2), (key2246, 2), (key2246, 2), (key2240, 2), (key2240, 2), (key2287, -1), (key2287, -1), (key2279, -1), (key2279, -1), (key2276, -1), (key2276, -1), (key2187, 2), (key2176, 2), (key2176, 2), (key2287, -1), (key2287, -1), (key2279, -1), (key2279, -1), (key2276, -1), (key2276, -1)]

def rawRow16890 : Integer.Sparse Key := [(key2028, -1), (key2033, -1), (key2147, -1), (key2166, -1), (key2176, -1), (key2187, -1), (key2033, 2), (key2152, 2), (key2166, 2), (key2058, -1), (key2063, -1), (key2240, -1), (key2253, -1), (key2276, -1), (key2287, -1), (key2058, 2), (key2069, 2), (key2147, 2), (key2166, 2), (key2279, 2), (key2287, 2), (key2063, -1), (key2069, -1), (key2152, -1), (key2166, -1), (key2246, -1), (key2253, -1), (key2079, 2), (key2276, 2), (key2287, 2), (key2079, -1), (key2085, -1), (key2176, -1), (key2187, -1), (key2279, -1), (key2287, -1)]

def rawRow16891 : Integer.Sparse Key := [(key2033, -1), (key2028, -1), (key2166, -1), (key2147, -1), (key2187, -1), (key2176, -1), (key2033, 2), (key2166, 2), (key2152, 2), (key2063, -1), (key2058, -1), (key2253, -1), (key2240, -1), (key2287, -1), (key2276, -1), (key2069, 2), (key2058, 2), (key2166, 2), (key2147, 2), (key2287, 2), (key2279, 2), (key2069, -1), (key2063, -1), (key2166, -1), (key2152, -1), (key2253, -1), (key2246, -1), (key2079, 2), (key2287, 2), (key2276, 2), (key2085, -1), (key2079, -1), (key2187, -1), (key2176, -1), (key2287, -1), (key2279, -1)]

def rawRow16892 : Integer.Sparse Key := [(key2147, -1), (key2176, -1), (key2028, -1), (key2187, -1), (key2033, -1), (key2166, -1), (key2152, 2), (key2033, 2), (key2166, 2), (key2240, -1), (key2276, -1), (key2058, -1), (key2287, -1), (key2063, -1), (key2253, -1), (key2147, 2), (key2279, 2), (key2058, 2), (key2287, 2), (key2069, 2), (key2166, 2), (key2152, -1), (key2246, -1), (key2063, -1), (key2253, -1), (key2069, -1), (key2166, -1), (key2276, 2), (key2079, 2), (key2287, 2), (key2176, -1), (key2279, -1), (key2079, -1), (key2287, -1), (key2085, -1), (key2187, -1)]

def rawRow16893 : Integer.Sparse Key := [(key2176, -1), (key2147, -1), (key2187, -1), (key2028, -1), (key2166, -1), (key2033, -1), (key2152, 2), (key2166, 2), (key2033, 2), (key2276, -1), (key2240, -1), (key2287, -1), (key2058, -1), (key2253, -1), (key2063, -1), (key2279, 2), (key2147, 2), (key2287, 2), (key2058, 2), (key2166, 2), (key2069, 2), (key2246, -1), (key2152, -1), (key2253, -1), (key2063, -1), (key2166, -1), (key2069, -1), (key2276, 2), (key2287, 2), (key2079, 2), (key2279, -1), (key2176, -1), (key2287, -1), (key2079, -1), (key2187, -1), (key2085, -1)]

def rawRow16894 : Integer.Sparse Key := [(key2166, -1), (key2187, -1), (key2033, -1), (key2176, -1), (key2028, -1), (key2147, -1), (key2166, 2), (key2033, 2), (key2152, 2), (key2253, -1), (key2287, -1), (key2063, -1), (key2276, -1), (key2058, -1), (key2240, -1), (key2166, 2), (key2287, 2), (key2069, 2), (key2279, 2), (key2058, 2), (key2147, 2), (key2166, -1), (key2253, -1), (key2069, -1), (key2246, -1), (key2063, -1), (key2152, -1), (key2287, 2), (key2079, 2), (key2276, 2), (key2187, -1), (key2287, -1), (key2085, -1), (key2279, -1), (key2079, -1), (key2176, -1)]

def rawRow16895 : Integer.Sparse Key := [(key2187, -1), (key2166, -1), (key2176, -1), (key2033, -1), (key2147, -1), (key2028, -1), (key2166, 2), (key2152, 2), (key2033, 2), (key2287, -1), (key2253, -1), (key2276, -1), (key2063, -1), (key2240, -1), (key2058, -1), (key2287, 2), (key2166, 2), (key2279, 2), (key2069, 2), (key2147, 2), (key2058, 2), (key2253, -1), (key2166, -1), (key2246, -1), (key2069, -1), (key2152, -1), (key2063, -1), (key2287, 2), (key2276, 2), (key2079, 2), (key2287, -1), (key2187, -1), (key2279, -1), (key2085, -1), (key2176, -1), (key2079, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16896 : Integer.Sparse Key := [(key2058, -1), (key2063, -1), (key2240, -1), (key2253, -1), (key2276, -1), (key2287, -1), (key2079, 2), (key2276, 2), (key2287, 2), (key2028, -1), (key2033, -1), (key2147, -1), (key2166, -1), (key2176, -1), (key2187, -1), (key2058, 2), (key2069, 2), (key2147, 2), (key2166, 2), (key2279, 2), (key2287, 2), (key2079, -1), (key2085, -1), (key2176, -1), (key2187, -1), (key2279, -1), (key2287, -1), (key2033, 2), (key2152, 2), (key2166, 2), (key2063, -1), (key2069, -1), (key2152, -1), (key2166, -1), (key2246, -1), (key2253, -1)]

def rawRow16897 : Integer.Sparse Key := [(key2063, -1), (key2058, -1), (key2253, -1), (key2240, -1), (key2287, -1), (key2276, -1), (key2079, 2), (key2287, 2), (key2276, 2), (key2033, -1), (key2028, -1), (key2166, -1), (key2147, -1), (key2187, -1), (key2176, -1), (key2069, 2), (key2058, 2), (key2166, 2), (key2147, 2), (key2287, 2), (key2279, 2), (key2085, -1), (key2079, -1), (key2187, -1), (key2176, -1), (key2287, -1), (key2279, -1), (key2033, 2), (key2166, 2), (key2152, 2), (key2069, -1), (key2063, -1), (key2166, -1), (key2152, -1), (key2253, -1), (key2246, -1)]

def rawRow16898 : Integer.Sparse Key := [(key2240, -1), (key2276, -1), (key2058, -1), (key2287, -1), (key2063, -1), (key2253, -1), (key2276, 2), (key2079, 2), (key2287, 2), (key2147, -1), (key2176, -1), (key2028, -1), (key2187, -1), (key2033, -1), (key2166, -1), (key2147, 2), (key2279, 2), (key2058, 2), (key2287, 2), (key2069, 2), (key2166, 2), (key2176, -1), (key2279, -1), (key2079, -1), (key2287, -1), (key2085, -1), (key2187, -1), (key2152, 2), (key2033, 2), (key2166, 2), (key2152, -1), (key2246, -1), (key2063, -1), (key2253, -1), (key2069, -1), (key2166, -1)]

def rawRow16899 : Integer.Sparse Key := [(key2276, -1), (key2240, -1), (key2287, -1), (key2058, -1), (key2253, -1), (key2063, -1), (key2276, 2), (key2287, 2), (key2079, 2), (key2176, -1), (key2147, -1), (key2187, -1), (key2028, -1), (key2166, -1), (key2033, -1), (key2279, 2), (key2147, 2), (key2287, 2), (key2058, 2), (key2166, 2), (key2069, 2), (key2279, -1), (key2176, -1), (key2287, -1), (key2079, -1), (key2187, -1), (key2085, -1), (key2152, 2), (key2166, 2), (key2033, 2), (key2246, -1), (key2152, -1), (key2253, -1), (key2063, -1), (key2166, -1), (key2069, -1)]

def rawRow16900 : Integer.Sparse Key := [(key2253, -1), (key2287, -1), (key2063, -1), (key2276, -1), (key2058, -1), (key2240, -1), (key2287, 2), (key2079, 2), (key2276, 2), (key2166, -1), (key2187, -1), (key2033, -1), (key2176, -1), (key2028, -1), (key2147, -1), (key2166, 2), (key2287, 2), (key2069, 2), (key2279, 2), (key2058, 2), (key2147, 2), (key2187, -1), (key2287, -1), (key2085, -1), (key2279, -1), (key2079, -1), (key2176, -1), (key2166, 2), (key2033, 2), (key2152, 2), (key2166, -1), (key2253, -1), (key2069, -1), (key2246, -1), (key2063, -1), (key2152, -1)]

def rawRow16901 : Integer.Sparse Key := [(key2287, -1), (key2253, -1), (key2276, -1), (key2063, -1), (key2240, -1), (key2058, -1), (key2287, 2), (key2276, 2), (key2079, 2), (key2187, -1), (key2166, -1), (key2176, -1), (key2033, -1), (key2147, -1), (key2028, -1), (key2287, 2), (key2166, 2), (key2279, 2), (key2069, 2), (key2147, 2), (key2058, 2), (key2287, -1), (key2187, -1), (key2279, -1), (key2085, -1), (key2176, -1), (key2079, -1), (key2166, 2), (key2152, 2), (key2033, 2), (key2253, -1), (key2166, -1), (key2246, -1), (key2069, -1), (key2152, -1), (key2063, -1)]

def rawRow16902 : Integer.Sparse Key := [(key2058, -1), (key2079, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2287, -1), (key2063, 2), (key2063, 2), (key2253, 2), (key2058, -1), (key2079, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2287, -1), (key2028, 2), (key2085, 2), (key2028, 2), (key2187, 2), (key2085, 2), (key2187, 2), (key2033, -1), (key2069, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2166, -1), (key2063, 2), (key2063, 2), (key2253, 2), (key2033, -1), (key2069, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2166, -1)]

def rawRow16903 : Integer.Sparse Key := [(key2079, -1), (key2058, -1), (key2287, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2063, 2), (key2253, 2), (key2063, 2), (key2079, -1), (key2058, -1), (key2287, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2085, 2), (key2028, 2), (key2187, 2), (key2028, 2), (key2187, 2), (key2085, 2), (key2069, -1), (key2033, -1), (key2166, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2063, 2), (key2253, 2), (key2063, 2), (key2069, -1), (key2033, -1), (key2166, -1), (key2033, -1), (key2166, -1), (key2069, -1)]

def rawRow16904 : Integer.Sparse Key := [(key2287, -1), (key2287, -1), (key2079, -1), (key2079, -1), (key2058, -1), (key2058, -1), (key2253, 2), (key2063, 2), (key2063, 2), (key2287, -1), (key2287, -1), (key2079, -1), (key2079, -1), (key2058, -1), (key2058, -1), (key2187, 2), (key2187, 2), (key2085, 2), (key2085, 2), (key2028, 2), (key2028, 2), (key2166, -1), (key2166, -1), (key2069, -1), (key2069, -1), (key2033, -1), (key2033, -1), (key2253, 2), (key2063, 2), (key2063, 2), (key2166, -1), (key2166, -1), (key2069, -1), (key2069, -1), (key2033, -1), (key2033, -1)]

def rawRow16905 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key362, -2), (key366, 6), (key731, -2), (key733, -2), (key733, -2), (key865, 2), (key867, 2), (key865, 2), (key881, 2), (key867, 2), (key881, 2), (key927, -2), (key927, -2), (key938, -2), (key750, 6), (key927, -2), (key927, -2), (key938, -2)]

def rawRow16906 : Integer.Sparse Key := [(key362, -2), (key360, -2), (key362, -2), (key366, 6), (key733, -2), (key731, -2), (key733, -2), (key867, 2), (key865, 2), (key881, 2), (key865, 2), (key881, 2), (key867, 2), (key927, -2), (key938, -2), (key927, -2), (key750, 6), (key927, -2), (key938, -2), (key927, -2)]

def rawRow16907 : Integer.Sparse Key := [(key362, -2), (key362, -2), (key360, -2), (key366, 6), (key733, -2), (key733, -2), (key731, -2), (key881, 2), (key881, 2), (key867, 2), (key867, 2), (key865, 2), (key865, 2), (key938, -2), (key927, -2), (key927, -2), (key750, 6), (key938, -2), (key927, -2), (key927, -2)]

def rawRow16908 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key362, 6), (key865, -2), (key867, -2), (key927, -2), (key731, 2), (key733, 2), (key865, 2), (key881, 2), (key927, 2), (key938, 2), (key733, -2), (key867, -2), (key881, -2), (key927, 6), (key750, -2), (key927, -2), (key938, -2)]

def rawRow16909 : Integer.Sparse Key := [(key362, -2), (key360, -2), (key366, -2), (key362, 6), (key867, -2), (key865, -2), (key927, -2), (key733, 2), (key731, 2), (key881, 2), (key865, 2), (key938, 2), (key927, 2), (key733, -2), (key881, -2), (key867, -2), (key927, 6), (key750, -2), (key938, -2), (key927, -2)]

def rawRow16910 : Integer.Sparse Key := [(key360, -2), (key366, -2), (key362, -2), (key362, 6), (key865, -2), (key927, -2), (key867, -2), (key865, 2), (key927, 2), (key731, 2), (key938, 2), (key733, 2), (key881, 2), (key867, -2), (key733, -2), (key881, -2), (key927, 6), (key927, -2), (key750, -2), (key938, -2)]

def rawRow16911 : Integer.Sparse Key := [(key366, -2), (key360, -2), (key362, -2), (key362, 6), (key927, -2), (key865, -2), (key867, -2), (key927, 2), (key865, 2), (key938, 2), (key731, 2), (key881, 2), (key733, 2), (key867, -2), (key881, -2), (key733, -2), (key927, 6), (key927, -2), (key938, -2), (key750, -2)]

def rawRow16912 : Integer.Sparse Key := [(key362, -2), (key366, -2), (key360, -2), (key362, 6), (key867, -2), (key927, -2), (key865, -2), (key881, 2), (key938, 2), (key733, 2), (key927, 2), (key731, 2), (key865, 2), (key881, -2), (key733, -2), (key867, -2), (key927, 6), (key938, -2), (key750, -2), (key927, -2)]

def rawRow16913 : Integer.Sparse Key := [(key366, -2), (key362, -2), (key360, -2), (key362, 6), (key927, -2), (key867, -2), (key865, -2), (key938, 2), (key881, 2), (key927, 2), (key733, 2), (key865, 2), (key731, 2), (key881, -2), (key867, -2), (key733, -2), (key927, 6), (key938, -2), (key927, -2), (key750, -2)]

def rawRow16914 : Integer.Sparse Key := [(key529, -2), (key531, -2), (key537, -2), (key537, 6), (key360, -2), (key362, -2), (key366, -2), (key731, 2), (key733, 2), (key865, 2), (key881, 2), (key927, 2), (key938, 2), (key750, -2), (key927, -2), (key938, -2), (key733, 6), (key733, -2), (key867, -2), (key881, -2)]

def rawRow16915 : Integer.Sparse Key := [(key531, -2), (key529, -2), (key537, -2), (key537, 6), (key362, -2), (key360, -2), (key366, -2), (key733, 2), (key731, 2), (key881, 2), (key865, 2), (key938, 2), (key927, 2), (key750, -2), (key938, -2), (key927, -2), (key733, 6), (key733, -2), (key881, -2), (key867, -2)]

def rawRow16916 : Integer.Sparse Key := [(key529, -2), (key537, -2), (key531, -2), (key537, 6), (key360, -2), (key366, -2), (key362, -2), (key865, 2), (key927, 2), (key731, 2), (key938, 2), (key733, 2), (key881, 2), (key927, -2), (key750, -2), (key938, -2), (key733, 6), (key867, -2), (key733, -2), (key881, -2)]

def rawRow16917 : Integer.Sparse Key := [(key537, -2), (key529, -2), (key531, -2), (key537, 6), (key366, -2), (key360, -2), (key362, -2), (key927, 2), (key865, 2), (key938, 2), (key731, 2), (key881, 2), (key733, 2), (key927, -2), (key938, -2), (key750, -2), (key733, 6), (key867, -2), (key881, -2), (key733, -2)]

def rawRow16918 : Integer.Sparse Key := [(key531, -2), (key537, -2), (key529, -2), (key537, 6), (key362, -2), (key366, -2), (key360, -2), (key881, 2), (key938, 2), (key733, 2), (key927, 2), (key731, 2), (key865, 2), (key938, -2), (key750, -2), (key927, -2), (key733, 6), (key881, -2), (key733, -2), (key867, -2)]

def rawRow16919 : Integer.Sparse Key := [(key537, -2), (key531, -2), (key529, -2), (key537, 6), (key366, -2), (key362, -2), (key360, -2), (key938, 2), (key881, 2), (key927, 2), (key733, 2), (key865, 2), (key731, 2), (key938, -2), (key927, -2), (key750, -2), (key733, 6), (key881, -2), (key867, -2), (key733, -2)]

def rawRow16920 : Integer.Sparse Key := [(key529, -2), (key537, -2), (key537, -2), (key531, 6), (key529, -2), (key537, -2), (key537, -2), (key360, 2), (key366, 2), (key731, 2), (key938, 2), (key750, 2), (key938, 2), (key733, -2), (key733, -2), (key881, -2), (key867, 6), (key733, -2), (key733, -2), (key881, -2)]

def rawRow16921 : Integer.Sparse Key := [(key537, -2), (key529, -2), (key537, -2), (key531, 6), (key537, -2), (key529, -2), (key537, -2), (key366, 2), (key360, 2), (key938, 2), (key731, 2), (key938, 2), (key750, 2), (key733, -2), (key881, -2), (key733, -2), (key867, 6), (key733, -2), (key881, -2), (key733, -2)]

def rawRow16922 : Integer.Sparse Key := [(key537, -2), (key537, -2), (key529, -2), (key531, 6), (key537, -2), (key537, -2), (key529, -2), (key676, 2), (key676, 2), (key366, 2), (key366, 2), (key360, 2), (key731, 2), (key881, -2), (key733, -2), (key733, -2), (key867, 6), (key881, -2), (key733, -2), (key733, -2)]

def rawRow16923 : Integer.Sparse Key := [(key1989, 2), (key1989, 2), (key1994, 2), (key1999, -2), (key2003, -2), (key2003, -2), (key1989, 2), (key1989, 2), (key1994, 2), (key2268, -1), (key2272, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2294, -1), (key1999, -2), (key2003, -2), (key2003, -2), (key2268, -1), (key2272, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2294, -1), (key2324, 4), (key2324, 4), (key2336, 4)]

def rawRow16924 : Integer.Sparse Key := [(key1989, 2), (key1994, 2), (key1989, 2), (key2003, -2), (key1999, -2), (key2003, -2), (key1989, 2), (key1994, 2), (key1989, 2), (key2272, -1), (key2268, -1), (key2294, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2003, -2), (key1999, -2), (key2003, -2), (key2272, -1), (key2268, -1), (key2294, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2324, 4), (key2336, 4), (key2324, 4)]

def rawRow16925 : Integer.Sparse Key := [(key1994, 2), (key1989, 2), (key1989, 2), (key2003, -2), (key2003, -2), (key1999, -2), (key1994, 2), (key1989, 2), (key1989, 2), (key2294, -1), (key2294, -1), (key2272, -1), (key2272, -1), (key2268, -1), (key2268, -1), (key2003, -2), (key2003, -2), (key1999, -2), (key2294, -1), (key2294, -1), (key2272, -1), (key2272, -1), (key2268, -1), (key2268, -1), (key2336, 4), (key2324, 4), (key2324, 4)]

def rawRow16926 : Integer.Sparse Key := [(key1989, 2), (key1999, 2), (key2003, 2), (key1989, -2), (key1994, -2), (key2003, -2), (key2234, 2), (key2268, 2), (key2272, 2), (key1989, -1), (key1994, -1), (key2234, -1), (key2259, -1), (key2272, -1), (key2294, -1), (key2268, -2), (key2272, -2), (key2324, -2), (key1999, -1), (key2003, -1), (key2268, -1), (key2294, -1), (key2324, -1), (key2336, -1), (key2003, 4), (key2272, 4), (key2294, 4)]

def rawRow16927 : Integer.Sparse Key := [(key1989, 2), (key2003, 2), (key1999, 2), (key1994, -2), (key1989, -2), (key2003, -2), (key2234, 2), (key2272, 2), (key2268, 2), (key1994, -1), (key1989, -1), (key2259, -1), (key2234, -1), (key2294, -1), (key2272, -1), (key2272, -2), (key2268, -2), (key2324, -2), (key2003, -1), (key1999, -1), (key2294, -1), (key2268, -1), (key2336, -1), (key2324, -1), (key2003, 4), (key2294, 4), (key2272, 4)]

def rawRow16928 : Integer.Sparse Key := [(key1999, 2), (key1989, 2), (key2003, 2), (key1989, -2), (key2003, -2), (key1994, -2), (key2268, 2), (key2234, 2), (key2272, 2), (key2234, -1), (key2272, -1), (key1989, -1), (key2294, -1), (key1994, -1), (key2259, -1), (key2268, -2), (key2324, -2), (key2272, -2), (key2268, -1), (key2324, -1), (key1999, -1), (key2336, -1), (key2003, -1), (key2294, -1), (key2272, 4), (key2003, 4), (key2294, 4)]

def rawRow16929 : Integer.Sparse Key := [(key1999, 2), (key2003, 2), (key1989, 2), (key2003, -2), (key1989, -2), (key1994, -2), (key2268, 2), (key2272, 2), (key2234, 2), (key2272, -1), (key2234, -1), (key2294, -1), (key1989, -1), (key2259, -1), (key1994, -1), (key2324, -2), (key2268, -2), (key2272, -2), (key2324, -1), (key2268, -1), (key2336, -1), (key1999, -1), (key2294, -1), (key2003, -1), (key2272, 4), (key2294, 4), (key2003, 4)]

def rawRow16930 : Integer.Sparse Key := [(key2003, 2), (key1989, 2), (key1999, 2), (key1994, -2), (key2003, -2), (key1989, -2), (key2272, 2), (key2234, 2), (key2268, 2), (key2259, -1), (key2294, -1), (key1994, -1), (key2272, -1), (key1989, -1), (key2234, -1), (key2272, -2), (key2324, -2), (key2268, -2), (key2294, -1), (key2336, -1), (key2003, -1), (key2324, -1), (key1999, -1), (key2268, -1), (key2294, 4), (key2003, 4), (key2272, 4)]

def rawRow16931 : Integer.Sparse Key := [(key2003, 2), (key1999, 2), (key1989, 2), (key2003, -2), (key1994, -2), (key1989, -2), (key2272, 2), (key2268, 2), (key2234, 2), (key2294, -1), (key2259, -1), (key2272, -1), (key1994, -1), (key2234, -1), (key1989, -1), (key2324, -2), (key2272, -2), (key2268, -2), (key2336, -1), (key2294, -1), (key2324, -1), (key2003, -1), (key2268, -1), (key1999, -1), (key2294, 4), (key2272, 4), (key2003, 4)]

def rawRow16932 : Integer.Sparse Key := [(key2234, 2), (key2268, 2), (key2272, 2), (key2268, -2), (key2272, -2), (key2324, -2), (key1989, 2), (key1999, 2), (key2003, 2), (key1999, -1), (key2003, -1), (key2268, -1), (key2294, -1), (key2324, -1), (key2336, -1), (key1989, -2), (key1994, -2), (key2003, -2), (key1989, -1), (key1994, -1), (key2234, -1), (key2259, -1), (key2272, -1), (key2294, -1), (key2003, 4), (key2272, 4), (key2294, 4)]

def rawRow16933 : Integer.Sparse Key := [(key2234, 2), (key2272, 2), (key2268, 2), (key2272, -2), (key2268, -2), (key2324, -2), (key1989, 2), (key2003, 2), (key1999, 2), (key2003, -1), (key1999, -1), (key2294, -1), (key2268, -1), (key2336, -1), (key2324, -1), (key1994, -2), (key1989, -2), (key2003, -2), (key1994, -1), (key1989, -1), (key2259, -1), (key2234, -1), (key2294, -1), (key2272, -1), (key2003, 4), (key2294, 4), (key2272, 4)]

def rawRow16934 : Integer.Sparse Key := [(key2268, 2), (key2234, 2), (key2272, 2), (key2268, -2), (key2324, -2), (key2272, -2), (key1999, 2), (key1989, 2), (key2003, 2), (key2268, -1), (key2324, -1), (key1999, -1), (key2336, -1), (key2003, -1), (key2294, -1), (key1989, -2), (key2003, -2), (key1994, -2), (key2234, -1), (key2272, -1), (key1989, -1), (key2294, -1), (key1994, -1), (key2259, -1), (key2272, 4), (key2003, 4), (key2294, 4)]

def rawRow16935 : Integer.Sparse Key := [(key2268, 2), (key2272, 2), (key2234, 2), (key2324, -2), (key2268, -2), (key2272, -2), (key1999, 2), (key2003, 2), (key1989, 2), (key2324, -1), (key2268, -1), (key2336, -1), (key1999, -1), (key2294, -1), (key2003, -1), (key2003, -2), (key1989, -2), (key1994, -2), (key2272, -1), (key2234, -1), (key2294, -1), (key1989, -1), (key2259, -1), (key1994, -1), (key2272, 4), (key2294, 4), (key2003, 4)]

def rawRow16936 : Integer.Sparse Key := [(key2272, 2), (key2234, 2), (key2268, 2), (key2272, -2), (key2324, -2), (key2268, -2), (key2003, 2), (key1989, 2), (key1999, 2), (key2294, -1), (key2336, -1), (key2003, -1), (key2324, -1), (key1999, -1), (key2268, -1), (key1994, -2), (key2003, -2), (key1989, -2), (key2259, -1), (key2294, -1), (key1994, -1), (key2272, -1), (key1989, -1), (key2234, -1), (key2294, 4), (key2003, 4), (key2272, 4)]

def rawRow16937 : Integer.Sparse Key := [(key2272, 2), (key2268, 2), (key2234, 2), (key2324, -2), (key2272, -2), (key2268, -2), (key2003, 2), (key1999, 2), (key1989, 2), (key2336, -1), (key2294, -1), (key2324, -1), (key2003, -1), (key2268, -1), (key1999, -1), (key2003, -2), (key1994, -2), (key1989, -2), (key2294, -1), (key2259, -1), (key2272, -1), (key1994, -1), (key2234, -1), (key1989, -1), (key2294, 4), (key2272, 4), (key2003, 4)]

def rawRow16938 : Integer.Sparse Key := [(key2268, 2), (key2268, 2), (key2324, 2), (key2234, -2), (key2272, -2), (key2272, -2), (key2268, 2), (key2268, 2), (key2324, 2), (key1989, -1), (key2003, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key2294, -1), (key2234, -2), (key2272, -2), (key2272, -2), (key1989, -1), (key2003, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key2294, -1), (key1994, 4), (key1994, 4), (key2259, 4)]

def rawRow16939 : Integer.Sparse Key := [(key2268, 2), (key2324, 2), (key2268, 2), (key2272, -2), (key2234, -2), (key2272, -2), (key2268, 2), (key2324, 2), (key2268, 2), (key2003, -1), (key1989, -1), (key2294, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key2272, -2), (key2234, -2), (key2272, -2), (key2003, -1), (key1989, -1), (key2294, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key1994, 4), (key2259, 4), (key1994, 4)]

def rawRow16940 : Integer.Sparse Key := [(key2324, 2), (key2268, 2), (key2268, 2), (key2272, -2), (key2272, -2), (key2234, -2), (key2324, 2), (key2268, 2), (key2268, 2), (key2294, -1), (key2294, -1), (key2003, -1), (key2003, -1), (key1989, -1), (key1989, -1), (key2272, -2), (key2272, -2), (key2234, -2), (key2294, -1), (key2294, -1), (key2003, -1), (key2003, -1), (key1989, -1), (key1989, -1), (key2259, 4), (key1994, 4), (key1994, 4)]

def rawRow16941 : Integer.Sparse Key := [(key2027, 2), (key2033, 2), (key2033, 2), (key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2027, 2), (key2033, 2), (key2033, 2), (key2146, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2146, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2239, 2), (key2246, 2), (key2239, 2), (key2253, 2), (key2246, 2), (key2253, 2)]

def rawRow16942 : Integer.Sparse Key := [(key2033, 2), (key2027, 2), (key2033, 2), (key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2033, 2), (key2027, 2), (key2033, 2), (key2152, -1), (key2146, -1), (key2166, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2246, 2), (key2239, 2), (key2253, 2), (key2239, 2), (key2253, 2), (key2246, 2)]

def rawRow16943 : Integer.Sparse Key := [(key2033, 2), (key2033, 2), (key2027, 2), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2033, 2), (key2033, 2), (key2027, 2), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2146, -1), (key2146, -1), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2146, -1), (key2146, -1), (key2253, 2), (key2253, 2), (key2246, 2), (key2246, 2), (key2239, 2), (key2239, 2)]

def rawRow16944 : Integer.Sparse Key := [(key2057, 2), (key2063, 2), (key2092, 2), (key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2146, 2), (key2152, 2), (key2194, 2), (key2027, -1), (key2033, -1), (key2146, -1), (key2166, -1), (key2194, -1), (key2200, -1), (key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2057, -1), (key2063, -1), (key2239, -1), (key2253, -1), (key2303, -1), (key2310, -1), (key2057, 2), (key2069, 2), (key2146, 2), (key2166, 2), (key2305, 2), (key2310, 2)]

def rawRow16945 : Integer.Sparse Key := [(key2063, 2), (key2057, 2), (key2092, 2), (key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2152, 2), (key2146, 2), (key2194, 2), (key2033, -1), (key2027, -1), (key2166, -1), (key2146, -1), (key2200, -1), (key2194, -1), (key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2063, -1), (key2057, -1), (key2253, -1), (key2239, -1), (key2310, -1), (key2303, -1), (key2069, 2), (key2057, 2), (key2166, 2), (key2146, 2), (key2310, 2), (key2305, 2)]

def rawRow16946 : Integer.Sparse Key := [(key2057, 2), (key2092, 2), (key2063, 2), (key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2146, 2), (key2194, 2), (key2152, 2), (key2146, -1), (key2194, -1), (key2027, -1), (key2200, -1), (key2033, -1), (key2166, -1), (key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2239, -1), (key2303, -1), (key2057, -1), (key2310, -1), (key2063, -1), (key2253, -1), (key2146, 2), (key2305, 2), (key2057, 2), (key2310, 2), (key2069, 2), (key2166, 2)]

def rawRow16947 : Integer.Sparse Key := [(key2092, 2), (key2057, 2), (key2063, 2), (key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2194, 2), (key2146, 2), (key2152, 2), (key2194, -1), (key2146, -1), (key2200, -1), (key2027, -1), (key2166, -1), (key2033, -1), (key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2303, -1), (key2239, -1), (key2310, -1), (key2057, -1), (key2253, -1), (key2063, -1), (key2305, 2), (key2146, 2), (key2310, 2), (key2057, 2), (key2166, 2), (key2069, 2)]

def rawRow16948 : Integer.Sparse Key := [(key2063, 2), (key2092, 2), (key2057, 2), (key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2152, 2), (key2194, 2), (key2146, 2), (key2166, -1), (key2200, -1), (key2033, -1), (key2194, -1), (key2027, -1), (key2146, -1), (key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2253, -1), (key2310, -1), (key2063, -1), (key2303, -1), (key2057, -1), (key2239, -1), (key2166, 2), (key2310, 2), (key2069, 2), (key2305, 2), (key2057, 2), (key2146, 2)]

def rawRow16949 : Integer.Sparse Key := [(key2092, 2), (key2063, 2), (key2057, 2), (key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2194, 2), (key2152, 2), (key2146, 2), (key2200, -1), (key2166, -1), (key2194, -1), (key2033, -1), (key2146, -1), (key2027, -1), (key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2310, -1), (key2253, -1), (key2303, -1), (key2063, -1), (key2239, -1), (key2057, -1), (key2310, 2), (key2166, 2), (key2305, 2), (key2069, 2), (key2146, 2), (key2057, 2)]

def rawRow16950 : Integer.Sparse Key := [(key2146, 2), (key2152, 2), (key2194, 2), (key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2057, 2), (key2063, 2), (key2092, 2), (key2057, -1), (key2063, -1), (key2239, -1), (key2253, -1), (key2303, -1), (key2310, -1), (key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2027, -1), (key2033, -1), (key2146, -1), (key2166, -1), (key2194, -1), (key2200, -1), (key2057, 2), (key2069, 2), (key2146, 2), (key2166, 2), (key2305, 2), (key2310, 2)]

def rawRow16951 : Integer.Sparse Key := [(key2152, 2), (key2146, 2), (key2194, 2), (key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2063, 2), (key2057, 2), (key2092, 2), (key2063, -1), (key2057, -1), (key2253, -1), (key2239, -1), (key2310, -1), (key2303, -1), (key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2033, -1), (key2027, -1), (key2166, -1), (key2146, -1), (key2200, -1), (key2194, -1), (key2069, 2), (key2057, 2), (key2166, 2), (key2146, 2), (key2310, 2), (key2305, 2)]

def rawRow16952 : Integer.Sparse Key := [(key2146, 2), (key2194, 2), (key2152, 2), (key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2057, 2), (key2092, 2), (key2063, 2), (key2239, -1), (key2303, -1), (key2057, -1), (key2310, -1), (key2063, -1), (key2253, -1), (key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2146, -1), (key2194, -1), (key2027, -1), (key2200, -1), (key2033, -1), (key2166, -1), (key2146, 2), (key2305, 2), (key2057, 2), (key2310, 2), (key2069, 2), (key2166, 2)]

def rawRow16953 : Integer.Sparse Key := [(key2194, 2), (key2146, 2), (key2152, 2), (key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2092, 2), (key2057, 2), (key2063, 2), (key2303, -1), (key2239, -1), (key2310, -1), (key2057, -1), (key2253, -1), (key2063, -1), (key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2194, -1), (key2146, -1), (key2200, -1), (key2027, -1), (key2166, -1), (key2033, -1), (key2305, 2), (key2146, 2), (key2310, 2), (key2057, 2), (key2166, 2), (key2069, 2)]

def rawRow16954 : Integer.Sparse Key := [(key2152, 2), (key2194, 2), (key2146, 2), (key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2063, 2), (key2092, 2), (key2057, 2), (key2253, -1), (key2310, -1), (key2063, -1), (key2303, -1), (key2057, -1), (key2239, -1), (key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2166, -1), (key2200, -1), (key2033, -1), (key2194, -1), (key2027, -1), (key2146, -1), (key2166, 2), (key2310, 2), (key2069, 2), (key2305, 2), (key2057, 2), (key2146, 2)]

def rawRow16955 : Integer.Sparse Key := [(key2194, 2), (key2152, 2), (key2146, 2), (key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2092, 2), (key2063, 2), (key2057, 2), (key2310, -1), (key2253, -1), (key2303, -1), (key2063, -1), (key2239, -1), (key2057, -1), (key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2200, -1), (key2166, -1), (key2194, -1), (key2033, -1), (key2146, -1), (key2027, -1), (key2310, 2), (key2166, 2), (key2305, 2), (key2069, 2), (key2146, 2), (key2057, 2)]

def rawRow16956 : Integer.Sparse Key := [(key2239, 2), (key2303, 2), (key2303, 2), (key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2239, 2), (key2303, 2), (key2303, 2), (key2057, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2310, -1), (key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2057, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2310, -1), (key2027, 2), (key2095, 2), (key2027, 2), (key2200, 2), (key2095, 2), (key2200, 2)]

def rawRow16957 : Integer.Sparse Key := [(key2303, 2), (key2239, 2), (key2303, 2), (key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2303, 2), (key2239, 2), (key2303, 2), (key2092, -1), (key2057, -1), (key2310, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2095, 2), (key2027, 2), (key2200, 2), (key2027, 2), (key2200, 2), (key2095, 2)]

def rawRow16958 : Integer.Sparse Key := [(key2303, 2), (key2303, 2), (key2239, 2), (key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2303, 2), (key2303, 2), (key2239, 2), (key2310, -1), (key2310, -1), (key2092, -1), (key2092, -1), (key2057, -1), (key2057, -1), (key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2310, -1), (key2310, -1), (key2092, -1), (key2092, -1), (key2057, -1), (key2057, -1), (key2200, 2), (key2200, 2), (key2095, 2), (key2095, 2), (key2027, 2), (key2027, 2)]

def rawRow16959 : Integer.Sparse Key := [(key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2092, 2), (key2092, 2), (key2095, 2), (key2146, 1), (key2152, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2194, -2), (key2194, -2), (key2200, -2), (key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2146, 1), (key2152, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2092, 2), (key2092, 2), (key2095, 2), (key2194, -2), (key2194, -2), (key2200, -2)]

def rawRow16960 : Integer.Sparse Key := [(key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2092, 2), (key2095, 2), (key2092, 2), (key2152, 1), (key2146, 1), (key2166, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2194, -2), (key2200, -2), (key2194, -2), (key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2152, 1), (key2146, 1), (key2166, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2092, 2), (key2095, 2), (key2092, 2), (key2194, -2), (key2200, -2), (key2194, -2)]

def rawRow16961 : Integer.Sparse Key := [(key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2095, 2), (key2092, 2), (key2092, 2), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2146, 1), (key2146, 1), (key2200, -2), (key2194, -2), (key2194, -2), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2146, 1), (key2146, 1), (key2095, 2), (key2092, 2), (key2092, 2), (key2200, -2), (key2194, -2), (key2194, -2)]

def rawRow16962 : Integer.Sparse Key := [(key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2033, 2), (key2063, 2), (key2069, 2), (key2027, 1), (key2033, 1), (key2146, 1), (key2166, 1), (key2194, 1), (key2200, 1), (key2033, -2), (key2152, -2), (key2166, -2), (key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2057, 1), (key2063, 1), (key2239, 1), (key2253, 1), (key2303, 1), (key2310, 1), (key2194, 2), (key2303, 2), (key2305, 2), (key2092, -2), (key2303, -2), (key2310, -2)]

def rawRow16963 : Integer.Sparse Key := [(key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, 1), (key2027, 1), (key2166, 1), (key2146, 1), (key2200, 1), (key2194, 1), (key2033, -2), (key2166, -2), (key2152, -2), (key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2063, 1), (key2057, 1), (key2253, 1), (key2239, 1), (key2310, 1), (key2303, 1), (key2194, 2), (key2305, 2), (key2303, 2), (key2092, -2), (key2310, -2), (key2303, -2)]

def rawRow16964 : Integer.Sparse Key := [(key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2063, 2), (key2033, 2), (key2069, 2), (key2146, 1), (key2194, 1), (key2027, 1), (key2200, 1), (key2033, 1), (key2166, 1), (key2152, -2), (key2033, -2), (key2166, -2), (key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2239, 1), (key2303, 1), (key2057, 1), (key2310, 1), (key2063, 1), (key2253, 1), (key2303, 2), (key2194, 2), (key2305, 2), (key2303, -2), (key2092, -2), (key2310, -2)]

def rawRow16965 : Integer.Sparse Key := [(key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2063, 2), (key2069, 2), (key2033, 2), (key2194, 1), (key2146, 1), (key2200, 1), (key2027, 1), (key2166, 1), (key2033, 1), (key2152, -2), (key2166, -2), (key2033, -2), (key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2303, 1), (key2239, 1), (key2310, 1), (key2057, 1), (key2253, 1), (key2063, 1), (key2303, 2), (key2305, 2), (key2194, 2), (key2303, -2), (key2310, -2), (key2092, -2)]

def rawRow16966 : Integer.Sparse Key := [(key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, 1), (key2200, 1), (key2033, 1), (key2194, 1), (key2027, 1), (key2146, 1), (key2166, -2), (key2033, -2), (key2152, -2), (key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2253, 1), (key2310, 1), (key2063, 1), (key2303, 1), (key2057, 1), (key2239, 1), (key2305, 2), (key2194, 2), (key2303, 2), (key2310, -2), (key2092, -2), (key2303, -2)]

def rawRow16967 : Integer.Sparse Key := [(key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2069, 2), (key2063, 2), (key2033, 2), (key2200, 1), (key2166, 1), (key2194, 1), (key2033, 1), (key2146, 1), (key2027, 1), (key2166, -2), (key2152, -2), (key2033, -2), (key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2310, 1), (key2253, 1), (key2303, 1), (key2063, 1), (key2239, 1), (key2057, 1), (key2305, 2), (key2303, 2), (key2194, 2), (key2310, -2), (key2303, -2), (key2092, -2)]

def rawRow16968 : Integer.Sparse Key := [(key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2194, 2), (key2303, 2), (key2305, 2), (key2057, 1), (key2063, 1), (key2239, 1), (key2253, 1), (key2303, 1), (key2310, 1), (key2092, -2), (key2303, -2), (key2310, -2), (key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2027, 1), (key2033, 1), (key2146, 1), (key2166, 1), (key2194, 1), (key2200, 1), (key2033, 2), (key2063, 2), (key2069, 2), (key2033, -2), (key2152, -2), (key2166, -2)]

def rawRow16969 : Integer.Sparse Key := [(key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2194, 2), (key2305, 2), (key2303, 2), (key2063, 1), (key2057, 1), (key2253, 1), (key2239, 1), (key2310, 1), (key2303, 1), (key2092, -2), (key2310, -2), (key2303, -2), (key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2033, 1), (key2027, 1), (key2166, 1), (key2146, 1), (key2200, 1), (key2194, 1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, -2), (key2166, -2), (key2152, -2)]

def rawRow16970 : Integer.Sparse Key := [(key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2303, 2), (key2194, 2), (key2305, 2), (key2239, 1), (key2303, 1), (key2057, 1), (key2310, 1), (key2063, 1), (key2253, 1), (key2303, -2), (key2092, -2), (key2310, -2), (key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2146, 1), (key2194, 1), (key2027, 1), (key2200, 1), (key2033, 1), (key2166, 1), (key2063, 2), (key2033, 2), (key2069, 2), (key2152, -2), (key2033, -2), (key2166, -2)]

def rawRow16971 : Integer.Sparse Key := [(key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2303, 2), (key2305, 2), (key2194, 2), (key2303, 1), (key2239, 1), (key2310, 1), (key2057, 1), (key2253, 1), (key2063, 1), (key2303, -2), (key2310, -2), (key2092, -2), (key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2194, 1), (key2146, 1), (key2200, 1), (key2027, 1), (key2166, 1), (key2033, 1), (key2063, 2), (key2069, 2), (key2033, 2), (key2152, -2), (key2166, -2), (key2033, -2)]

def rawRow16972 : Integer.Sparse Key := [(key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2305, 2), (key2194, 2), (key2303, 2), (key2253, 1), (key2310, 1), (key2063, 1), (key2303, 1), (key2057, 1), (key2239, 1), (key2310, -2), (key2092, -2), (key2303, -2), (key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2166, 1), (key2200, 1), (key2033, 1), (key2194, 1), (key2027, 1), (key2146, 1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, -2), (key2033, -2), (key2152, -2)]

def rawRow16973 : Integer.Sparse Key := [(key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2305, 2), (key2303, 2), (key2194, 2), (key2310, 1), (key2253, 1), (key2303, 1), (key2063, 1), (key2239, 1), (key2057, 1), (key2310, -2), (key2303, -2), (key2092, -2), (key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2200, 1), (key2166, 1), (key2194, 1), (key2033, 1), (key2146, 1), (key2027, 1), (key2069, 2), (key2063, 2), (key2033, 2), (key2166, -2), (key2152, -2), (key2033, -2)]

def rawRow16974 : Integer.Sparse Key := [(key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2152, 2), (key2152, 2), (key2246, 2), (key2057, 1), (key2092, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2310, 1), (key2063, -2), (key2063, -2), (key2253, -2), (key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2057, 1), (key2092, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2310, 1), (key2152, 2), (key2152, 2), (key2246, 2), (key2063, -2), (key2063, -2), (key2253, -2)]

def rawRow16975 : Integer.Sparse Key := [(key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2152, 2), (key2246, 2), (key2152, 2), (key2092, 1), (key2057, 1), (key2310, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2063, -2), (key2253, -2), (key2063, -2), (key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2092, 1), (key2057, 1), (key2310, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2152, 2), (key2246, 2), (key2152, 2), (key2063, -2), (key2253, -2), (key2063, -2)]

def rawRow16976 : Integer.Sparse Key := [(key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2246, 2), (key2152, 2), (key2152, 2), (key2310, 1), (key2310, 1), (key2092, 1), (key2092, 1), (key2057, 1), (key2057, 1), (key2253, -2), (key2063, -2), (key2063, -2), (key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2310, 1), (key2310, 1), (key2092, 1), (key2092, 1), (key2057, 1), (key2057, 1), (key2246, 2), (key2152, 2), (key2152, 2), (key2253, -2), (key2063, -2), (key2063, -2)]

def rawRow16977 : Integer.Sparse Key := [(key2058, -1), (key2063, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2079, 2), (key2079, 2), (key2085, 2), (key2147, 1), (key2152, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2176, -2), (key2176, -2), (key2187, -2), (key2058, -1), (key2063, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2147, 1), (key2152, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2079, 2), (key2079, 2), (key2085, 2), (key2176, -2), (key2176, -2), (key2187, -2)]

def rawRow16978 : Integer.Sparse Key := [(key2063, -1), (key2058, -1), (key2069, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2079, 2), (key2085, 2), (key2079, 2), (key2152, 1), (key2147, 1), (key2166, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2176, -2), (key2187, -2), (key2176, -2), (key2063, -1), (key2058, -1), (key2069, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2152, 1), (key2147, 1), (key2166, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2079, 2), (key2085, 2), (key2079, 2), (key2176, -2), (key2187, -2), (key2176, -2)]

def rawRow16979 : Integer.Sparse Key := [(key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2058, -1), (key2058, -1), (key2085, 2), (key2079, 2), (key2079, 2), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2147, 1), (key2147, 1), (key2187, -2), (key2176, -2), (key2176, -2), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2058, -1), (key2058, -1), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2147, 1), (key2147, 1), (key2085, 2), (key2079, 2), (key2079, 2), (key2187, -2), (key2176, -2), (key2176, -2)]

def rawRow16980 : Integer.Sparse Key := [(key2028, -1), (key2033, -1), (key2058, -1), (key2069, -1), (key2079, -1), (key2085, -1), (key2033, 2), (key2063, 2), (key2069, 2), (key2028, 1), (key2033, 1), (key2147, 1), (key2166, 1), (key2176, 1), (key2187, 1), (key2033, -2), (key2152, -2), (key2166, -2), (key2147, -1), (key2152, -1), (key2240, -1), (key2246, -1), (key2276, -1), (key2279, -1), (key2058, 1), (key2063, 1), (key2240, 1), (key2253, 1), (key2276, 1), (key2287, 1), (key2176, 2), (key2276, 2), (key2279, 2), (key2079, -2), (key2276, -2), (key2287, -2)]

def rawRow16981 : Integer.Sparse Key := [(key2033, -1), (key2028, -1), (key2069, -1), (key2058, -1), (key2085, -1), (key2079, -1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, 1), (key2028, 1), (key2166, 1), (key2147, 1), (key2187, 1), (key2176, 1), (key2033, -2), (key2166, -2), (key2152, -2), (key2152, -1), (key2147, -1), (key2246, -1), (key2240, -1), (key2279, -1), (key2276, -1), (key2063, 1), (key2058, 1), (key2253, 1), (key2240, 1), (key2287, 1), (key2276, 1), (key2176, 2), (key2279, 2), (key2276, 2), (key2079, -2), (key2287, -2), (key2276, -2)]

def rawRow16982 : Integer.Sparse Key := [(key2058, -1), (key2079, -1), (key2028, -1), (key2085, -1), (key2033, -1), (key2069, -1), (key2063, 2), (key2033, 2), (key2069, 2), (key2147, 1), (key2176, 1), (key2028, 1), (key2187, 1), (key2033, 1), (key2166, 1), (key2152, -2), (key2033, -2), (key2166, -2), (key2240, -1), (key2276, -1), (key2147, -1), (key2279, -1), (key2152, -1), (key2246, -1), (key2240, 1), (key2276, 1), (key2058, 1), (key2287, 1), (key2063, 1), (key2253, 1), (key2276, 2), (key2176, 2), (key2279, 2), (key2276, -2), (key2079, -2), (key2287, -2)]

def rawRow16983 : Integer.Sparse Key := [(key2079, -1), (key2058, -1), (key2085, -1), (key2028, -1), (key2069, -1), (key2033, -1), (key2063, 2), (key2069, 2), (key2033, 2), (key2176, 1), (key2147, 1), (key2187, 1), (key2028, 1), (key2166, 1), (key2033, 1), (key2152, -2), (key2166, -2), (key2033, -2), (key2276, -1), (key2240, -1), (key2279, -1), (key2147, -1), (key2246, -1), (key2152, -1), (key2276, 1), (key2240, 1), (key2287, 1), (key2058, 1), (key2253, 1), (key2063, 1), (key2276, 2), (key2279, 2), (key2176, 2), (key2276, -2), (key2287, -2), (key2079, -2)]

def rawRow16984 : Integer.Sparse Key := [(key2069, -1), (key2085, -1), (key2033, -1), (key2079, -1), (key2028, -1), (key2058, -1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, 1), (key2187, 1), (key2033, 1), (key2176, 1), (key2028, 1), (key2147, 1), (key2166, -2), (key2033, -2), (key2152, -2), (key2246, -1), (key2279, -1), (key2152, -1), (key2276, -1), (key2147, -1), (key2240, -1), (key2253, 1), (key2287, 1), (key2063, 1), (key2276, 1), (key2058, 1), (key2240, 1), (key2279, 2), (key2176, 2), (key2276, 2), (key2287, -2), (key2079, -2), (key2276, -2)]

def rawRow16985 : Integer.Sparse Key := [(key2085, -1), (key2069, -1), (key2079, -1), (key2033, -1), (key2058, -1), (key2028, -1), (key2069, 2), (key2063, 2), (key2033, 2), (key2187, 1), (key2166, 1), (key2176, 1), (key2033, 1), (key2147, 1), (key2028, 1), (key2166, -2), (key2152, -2), (key2033, -2), (key2279, -1), (key2246, -1), (key2276, -1), (key2152, -1), (key2240, -1), (key2147, -1), (key2287, 1), (key2253, 1), (key2276, 1), (key2063, 1), (key2240, 1), (key2058, 1), (key2279, 2), (key2276, 2), (key2176, 2), (key2287, -2), (key2276, -2), (key2079, -2)]

def rawRow16986 : Integer.Sparse Key := [(key2147, -1), (key2152, -1), (key2240, -1), (key2246, -1), (key2276, -1), (key2279, -1), (key2176, 2), (key2276, 2), (key2279, 2), (key2058, 1), (key2063, 1), (key2240, 1), (key2253, 1), (key2276, 1), (key2287, 1), (key2079, -2), (key2276, -2), (key2287, -2), (key2028, -1), (key2033, -1), (key2058, -1), (key2069, -1), (key2079, -1), (key2085, -1), (key2028, 1), (key2033, 1), (key2147, 1), (key2166, 1), (key2176, 1), (key2187, 1), (key2033, 2), (key2063, 2), (key2069, 2), (key2033, -2), (key2152, -2), (key2166, -2)]

def rawRow16987 : Integer.Sparse Key := [(key2152, -1), (key2147, -1), (key2246, -1), (key2240, -1), (key2279, -1), (key2276, -1), (key2176, 2), (key2279, 2), (key2276, 2), (key2063, 1), (key2058, 1), (key2253, 1), (key2240, 1), (key2287, 1), (key2276, 1), (key2079, -2), (key2287, -2), (key2276, -2), (key2033, -1), (key2028, -1), (key2069, -1), (key2058, -1), (key2085, -1), (key2079, -1), (key2033, 1), (key2028, 1), (key2166, 1), (key2147, 1), (key2187, 1), (key2176, 1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, -2), (key2166, -2), (key2152, -2)]

def rawRow16988 : Integer.Sparse Key := [(key2240, -1), (key2276, -1), (key2147, -1), (key2279, -1), (key2152, -1), (key2246, -1), (key2276, 2), (key2176, 2), (key2279, 2), (key2240, 1), (key2276, 1), (key2058, 1), (key2287, 1), (key2063, 1), (key2253, 1), (key2276, -2), (key2079, -2), (key2287, -2), (key2058, -1), (key2079, -1), (key2028, -1), (key2085, -1), (key2033, -1), (key2069, -1), (key2147, 1), (key2176, 1), (key2028, 1), (key2187, 1), (key2033, 1), (key2166, 1), (key2063, 2), (key2033, 2), (key2069, 2), (key2152, -2), (key2033, -2), (key2166, -2)]

def rawRow16989 : Integer.Sparse Key := [(key2276, -1), (key2240, -1), (key2279, -1), (key2147, -1), (key2246, -1), (key2152, -1), (key2276, 2), (key2279, 2), (key2176, 2), (key2276, 1), (key2240, 1), (key2287, 1), (key2058, 1), (key2253, 1), (key2063, 1), (key2276, -2), (key2287, -2), (key2079, -2), (key2079, -1), (key2058, -1), (key2085, -1), (key2028, -1), (key2069, -1), (key2033, -1), (key2176, 1), (key2147, 1), (key2187, 1), (key2028, 1), (key2166, 1), (key2033, 1), (key2063, 2), (key2069, 2), (key2033, 2), (key2152, -2), (key2166, -2), (key2033, -2)]

def rawRow16990 : Integer.Sparse Key := [(key2246, -1), (key2279, -1), (key2152, -1), (key2276, -1), (key2147, -1), (key2240, -1), (key2279, 2), (key2176, 2), (key2276, 2), (key2253, 1), (key2287, 1), (key2063, 1), (key2276, 1), (key2058, 1), (key2240, 1), (key2287, -2), (key2079, -2), (key2276, -2), (key2069, -1), (key2085, -1), (key2033, -1), (key2079, -1), (key2028, -1), (key2058, -1), (key2166, 1), (key2187, 1), (key2033, 1), (key2176, 1), (key2028, 1), (key2147, 1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, -2), (key2033, -2), (key2152, -2)]

def rawRow16991 : Integer.Sparse Key := [(key2279, -1), (key2246, -1), (key2276, -1), (key2152, -1), (key2240, -1), (key2147, -1), (key2279, 2), (key2276, 2), (key2176, 2), (key2287, 1), (key2253, 1), (key2276, 1), (key2063, 1), (key2240, 1), (key2058, 1), (key2287, -2), (key2276, -2), (key2079, -2), (key2085, -1), (key2069, -1), (key2079, -1), (key2033, -1), (key2058, -1), (key2028, -1), (key2187, 1), (key2166, 1), (key2176, 1), (key2033, 1), (key2147, 1), (key2028, 1), (key2069, 2), (key2063, 2), (key2033, 2), (key2166, -2), (key2152, -2), (key2033, -2)]

def rawRow16992 : Integer.Sparse Key := [(key2147, -1), (key2176, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2279, -1), (key2152, 2), (key2152, 2), (key2246, 2), (key2058, 1), (key2079, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2287, 1), (key2063, -2), (key2063, -2), (key2253, -2), (key2147, -1), (key2176, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2279, -1), (key2058, 1), (key2079, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2287, 1), (key2152, 2), (key2152, 2), (key2246, 2), (key2063, -2), (key2063, -2), (key2253, -2)]

def rawRow16993 : Integer.Sparse Key := [(key2176, -1), (key2147, -1), (key2279, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2152, 2), (key2246, 2), (key2152, 2), (key2079, 1), (key2058, 1), (key2287, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2063, -2), (key2253, -2), (key2063, -2), (key2176, -1), (key2147, -1), (key2279, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2079, 1), (key2058, 1), (key2287, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2152, 2), (key2246, 2), (key2152, 2), (key2063, -2), (key2253, -2), (key2063, -2)]

def rawRow16994 : Integer.Sparse Key := [(key2279, -1), (key2279, -1), (key2176, -1), (key2176, -1), (key2147, -1), (key2147, -1), (key2246, 2), (key2152, 2), (key2152, 2), (key2287, 1), (key2287, 1), (key2079, 1), (key2079, 1), (key2058, 1), (key2058, 1), (key2253, -2), (key2063, -2), (key2063, -2), (key2279, -1), (key2279, -1), (key2176, -1), (key2176, -1), (key2147, -1), (key2147, -1), (key2287, 1), (key2287, 1), (key2079, 1), (key2079, 1), (key2058, 1), (key2058, 1), (key2246, 2), (key2152, 2), (key2152, 2), (key2253, -2), (key2063, -2), (key2063, -2)]

def rawRow16995 : Integer.Sparse Key := [(key2151, 2), (key2151, 2), (key2169, 2), (key2175, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2189, -1), (key2151, 2), (key2151, 2), (key2169, 2), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2175, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2189, -1), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2328, 2), (key2330, 2), (key2328, 2), (key2333, 2), (key2330, 2), (key2333, 2)]

def rawRow16996 : Integer.Sparse Key := [(key2151, 2), (key2169, 2), (key2151, 2), (key2179, -1), (key2175, -1), (key2189, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2151, 2), (key2169, 2), (key2151, 2), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2330, 2), (key2328, 2), (key2333, 2), (key2328, 2), (key2333, 2), (key2330, 2)]

def rawRow16997 : Integer.Sparse Key := [(key2169, 2), (key2151, 2), (key2151, 2), (key2189, -1), (key2189, -1), (key2179, -1), (key2179, -1), (key2175, -1), (key2175, -1), (key2169, 2), (key2151, 2), (key2151, 2), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2189, -1), (key2189, -1), (key2179, -1), (key2179, -1), (key2175, -1), (key2175, -1), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2333, 2), (key2333, 2), (key2330, 2), (key2330, 2), (key2328, 2), (key2328, 2)]

def rawRow16998 : Integer.Sparse Key := [(key2032, 2), (key2175, 2), (key2189, 2), (key2032, -1), (key2037, -1), (key2151, -1), (key2169, -1), (key2179, -1), (key2189, -1), (key2062, 2), (key2275, 2), (key2289, 2), (key2062, -1), (key2072, -1), (key2151, -1), (key2169, -1), (key2281, -1), (key2289, -1), (key2078, -1), (key2082, -1), (key2275, -1), (key2289, -1), (key2328, -1), (key2333, -1), (key2078, -1), (key2087, -1), (key2175, -1), (key2189, -1), (key2330, -1), (key2333, -1), (key2082, 2), (key2087, 2), (key2179, 2), (key2189, 2), (key2281, 2), (key2289, 2)]

def rawRow16999 : Integer.Sparse Key := [(key2032, 2), (key2189, 2), (key2175, 2), (key2037, -1), (key2032, -1), (key2169, -1), (key2151, -1), (key2189, -1), (key2179, -1), (key2062, 2), (key2289, 2), (key2275, 2), (key2072, -1), (key2062, -1), (key2169, -1), (key2151, -1), (key2289, -1), (key2281, -1), (key2082, -1), (key2078, -1), (key2289, -1), (key2275, -1), (key2333, -1), (key2328, -1), (key2087, -1), (key2078, -1), (key2189, -1), (key2175, -1), (key2333, -1), (key2330, -1), (key2087, 2), (key2082, 2), (key2189, 2), (key2179, 2), (key2289, 2), (key2281, 2)]

def rawRow17000 : Integer.Sparse Key := [(key2175, 2), (key2032, 2), (key2189, 2), (key2151, -1), (key2179, -1), (key2032, -1), (key2189, -1), (key2037, -1), (key2169, -1), (key2275, 2), (key2062, 2), (key2289, 2), (key2151, -1), (key2281, -1), (key2062, -1), (key2289, -1), (key2072, -1), (key2169, -1), (key2275, -1), (key2328, -1), (key2078, -1), (key2333, -1), (key2082, -1), (key2289, -1), (key2175, -1), (key2330, -1), (key2078, -1), (key2333, -1), (key2087, -1), (key2189, -1), (key2179, 2), (key2281, 2), (key2082, 2), (key2289, 2), (key2087, 2), (key2189, 2)]

def rawRow17001 : Integer.Sparse Key := [(key2175, 2), (key2189, 2), (key2032, 2), (key2179, -1), (key2151, -1), (key2189, -1), (key2032, -1), (key2169, -1), (key2037, -1), (key2275, 2), (key2289, 2), (key2062, 2), (key2281, -1), (key2151, -1), (key2289, -1), (key2062, -1), (key2169, -1), (key2072, -1), (key2328, -1), (key2275, -1), (key2333, -1), (key2078, -1), (key2289, -1), (key2082, -1), (key2330, -1), (key2175, -1), (key2333, -1), (key2078, -1), (key2189, -1), (key2087, -1), (key2281, 2), (key2179, 2), (key2289, 2), (key2082, 2), (key2189, 2), (key2087, 2)]

def rawRow17002 : Integer.Sparse Key := [(key2189, 2), (key2032, 2), (key2175, 2), (key2169, -1), (key2189, -1), (key2037, -1), (key2179, -1), (key2032, -1), (key2151, -1), (key2289, 2), (key2062, 2), (key2275, 2), (key2169, -1), (key2289, -1), (key2072, -1), (key2281, -1), (key2062, -1), (key2151, -1), (key2289, -1), (key2333, -1), (key2082, -1), (key2328, -1), (key2078, -1), (key2275, -1), (key2189, -1), (key2333, -1), (key2087, -1), (key2330, -1), (key2078, -1), (key2175, -1), (key2189, 2), (key2289, 2), (key2087, 2), (key2281, 2), (key2082, 2), (key2179, 2)]

def rawRow17003 : Integer.Sparse Key := [(key2189, 2), (key2175, 2), (key2032, 2), (key2189, -1), (key2169, -1), (key2179, -1), (key2037, -1), (key2151, -1), (key2032, -1), (key2289, 2), (key2275, 2), (key2062, 2), (key2289, -1), (key2169, -1), (key2281, -1), (key2072, -1), (key2151, -1), (key2062, -1), (key2333, -1), (key2289, -1), (key2328, -1), (key2082, -1), (key2275, -1), (key2078, -1), (key2333, -1), (key2189, -1), (key2330, -1), (key2087, -1), (key2175, -1), (key2078, -1), (key2289, 2), (key2189, 2), (key2281, 2), (key2087, 2), (key2179, 2), (key2082, 2)]

def rawRow17004 : Integer.Sparse Key := [(key2062, 2), (key2275, 2), (key2289, 2), (key2078, -1), (key2082, -1), (key2275, -1), (key2289, -1), (key2328, -1), (key2333, -1), (key2032, 2), (key2175, 2), (key2189, 2), (key2078, -1), (key2087, -1), (key2175, -1), (key2189, -1), (key2330, -1), (key2333, -1), (key2032, -1), (key2037, -1), (key2151, -1), (key2169, -1), (key2179, -1), (key2189, -1), (key2062, -1), (key2072, -1), (key2151, -1), (key2169, -1), (key2281, -1), (key2289, -1), (key2082, 2), (key2087, 2), (key2179, 2), (key2189, 2), (key2281, 2), (key2289, 2)]

def rawRow17005 : Integer.Sparse Key := [(key2062, 2), (key2289, 2), (key2275, 2), (key2082, -1), (key2078, -1), (key2289, -1), (key2275, -1), (key2333, -1), (key2328, -1), (key2032, 2), (key2189, 2), (key2175, 2), (key2087, -1), (key2078, -1), (key2189, -1), (key2175, -1), (key2333, -1), (key2330, -1), (key2037, -1), (key2032, -1), (key2169, -1), (key2151, -1), (key2189, -1), (key2179, -1), (key2072, -1), (key2062, -1), (key2169, -1), (key2151, -1), (key2289, -1), (key2281, -1), (key2087, 2), (key2082, 2), (key2189, 2), (key2179, 2), (key2289, 2), (key2281, 2)]

def rawRow17006 : Integer.Sparse Key := [(key2275, 2), (key2062, 2), (key2289, 2), (key2275, -1), (key2328, -1), (key2078, -1), (key2333, -1), (key2082, -1), (key2289, -1), (key2175, 2), (key2032, 2), (key2189, 2), (key2175, -1), (key2330, -1), (key2078, -1), (key2333, -1), (key2087, -1), (key2189, -1), (key2151, -1), (key2179, -1), (key2032, -1), (key2189, -1), (key2037, -1), (key2169, -1), (key2151, -1), (key2281, -1), (key2062, -1), (key2289, -1), (key2072, -1), (key2169, -1), (key2179, 2), (key2281, 2), (key2082, 2), (key2289, 2), (key2087, 2), (key2189, 2)]

def rawRow17007 : Integer.Sparse Key := [(key2275, 2), (key2289, 2), (key2062, 2), (key2328, -1), (key2275, -1), (key2333, -1), (key2078, -1), (key2289, -1), (key2082, -1), (key2175, 2), (key2189, 2), (key2032, 2), (key2330, -1), (key2175, -1), (key2333, -1), (key2078, -1), (key2189, -1), (key2087, -1), (key2179, -1), (key2151, -1), (key2189, -1), (key2032, -1), (key2169, -1), (key2037, -1), (key2281, -1), (key2151, -1), (key2289, -1), (key2062, -1), (key2169, -1), (key2072, -1), (key2281, 2), (key2179, 2), (key2289, 2), (key2082, 2), (key2189, 2), (key2087, 2)]

def rawRow17008 : Integer.Sparse Key := [(key2289, 2), (key2062, 2), (key2275, 2), (key2289, -1), (key2333, -1), (key2082, -1), (key2328, -1), (key2078, -1), (key2275, -1), (key2189, 2), (key2032, 2), (key2175, 2), (key2189, -1), (key2333, -1), (key2087, -1), (key2330, -1), (key2078, -1), (key2175, -1), (key2169, -1), (key2189, -1), (key2037, -1), (key2179, -1), (key2032, -1), (key2151, -1), (key2169, -1), (key2289, -1), (key2072, -1), (key2281, -1), (key2062, -1), (key2151, -1), (key2189, 2), (key2289, 2), (key2087, 2), (key2281, 2), (key2082, 2), (key2179, 2)]

def rawRow17009 : Integer.Sparse Key := [(key2289, 2), (key2275, 2), (key2062, 2), (key2333, -1), (key2289, -1), (key2328, -1), (key2082, -1), (key2275, -1), (key2078, -1), (key2189, 2), (key2175, 2), (key2032, 2), (key2333, -1), (key2189, -1), (key2330, -1), (key2087, -1), (key2175, -1), (key2078, -1), (key2189, -1), (key2169, -1), (key2179, -1), (key2037, -1), (key2151, -1), (key2032, -1), (key2289, -1), (key2169, -1), (key2281, -1), (key2072, -1), (key2151, -1), (key2062, -1), (key2289, 2), (key2189, 2), (key2281, 2), (key2087, 2), (key2179, 2), (key2082, 2)]

def rawRow17010 : Integer.Sparse Key := [(key2078, 2), (key2078, 2), (key2333, 2), (key2062, -1), (key2082, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2289, -1), (key2078, 2), (key2078, 2), (key2333, 2), (key2032, -1), (key2087, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2189, -1), (key2062, -1), (key2082, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2289, -1), (key2032, -1), (key2087, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2189, -1), (key2037, 2), (key2072, 2), (key2037, 2), (key2169, 2), (key2072, 2), (key2169, 2)]

def rawRow17011 : Integer.Sparse Key := [(key2078, 2), (key2333, 2), (key2078, 2), (key2082, -1), (key2062, -1), (key2289, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2078, 2), (key2333, 2), (key2078, 2), (key2087, -1), (key2032, -1), (key2189, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2082, -1), (key2062, -1), (key2289, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2087, -1), (key2032, -1), (key2189, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2072, 2), (key2037, 2), (key2169, 2), (key2037, 2), (key2169, 2), (key2072, 2)]

def rawRow17012 : Integer.Sparse Key := [(key2333, 2), (key2078, 2), (key2078, 2), (key2289, -1), (key2289, -1), (key2082, -1), (key2082, -1), (key2062, -1), (key2062, -1), (key2333, 2), (key2078, 2), (key2078, 2), (key2189, -1), (key2189, -1), (key2087, -1), (key2087, -1), (key2032, -1), (key2032, -1), (key2289, -1), (key2289, -1), (key2082, -1), (key2082, -1), (key2062, -1), (key2062, -1), (key2189, -1), (key2189, -1), (key2087, -1), (key2087, -1), (key2032, -1), (key2032, -1), (key2169, 2), (key2169, 2), (key2072, 2), (key2072, 2), (key2037, 2), (key2037, 2)]

def rawRow17013 : Integer.Sparse Key := [(key776, 4), (key778, 4), (key778, 4), (key801, -2), (key803, -2), (key801, -2), (key811, -2), (key803, -2), (key811, -2), (key801, -2), (key803, -2), (key801, -2), (key811, -2), (key803, -2), (key811, -2), (key871, 4), (key876, 4), (key876, 4)]

def rawRow17014 : Integer.Sparse Key := [(key778, 4), (key776, 4), (key778, 4), (key803, -2), (key801, -2), (key811, -2), (key801, -2), (key811, -2), (key803, -2), (key803, -2), (key801, -2), (key811, -2), (key801, -2), (key811, -2), (key803, -2), (key876, 4), (key871, 4), (key876, 4)]

def rawRow17015 : Integer.Sparse Key := [(key778, 4), (key778, 4), (key776, 4), (key811, -2), (key811, -2), (key803, -2), (key803, -2), (key801, -2), (key801, -2), (key811, -2), (key811, -2), (key803, -2), (key803, -2), (key801, -2), (key801, -2), (key876, 4), (key876, 4), (key871, 4)]

def rawRow17016 : Integer.Sparse Key := [(key801, 4), (key803, 4), (key811, 4), (key776, -2), (key778, -2), (key801, -2), (key811, -2), (key836, -2), (key839, -2), (key801, -2), (key803, -2), (key871, -2), (key876, -2), (key931, -2), (key934, -2), (key801, 4), (key811, 4), (key934, 4)]

def rawRow17017 : Integer.Sparse Key := [(key803, 4), (key801, 4), (key811, 4), (key778, -2), (key776, -2), (key811, -2), (key801, -2), (key839, -2), (key836, -2), (key803, -2), (key801, -2), (key876, -2), (key871, -2), (key934, -2), (key931, -2), (key811, 4), (key801, 4), (key934, 4)]

def rawRow17018 : Integer.Sparse Key := [(key801, 4), (key811, 4), (key803, 4), (key801, -2), (key811, -2), (key776, -2), (key839, -2), (key778, -2), (key811, -2), (key871, -2), (key931, -2), (key801, -2), (key934, -2), (key803, -2), (key876, -2), (key801, 4), (key934, 4), (key811, 4)]

def rawRow17019 : Integer.Sparse Key := [(key811, 4), (key801, 4), (key803, 4), (key811, -2), (key801, -2), (key839, -2), (key776, -2), (key811, -2), (key778, -2), (key931, -2), (key871, -2), (key934, -2), (key801, -2), (key876, -2), (key803, -2), (key934, 4), (key801, 4), (key811, 4)]

def rawRow17020 : Integer.Sparse Key := [(key803, 4), (key811, 4), (key801, 4), (key836, -2), (key839, -2), (key778, -2), (key811, -2), (key776, -2), (key801, -2), (key876, -2), (key934, -2), (key803, -2), (key931, -2), (key801, -2), (key871, -2), (key811, 4), (key934, 4), (key801, 4)]

def rawRow17021 : Integer.Sparse Key := [(key811, 4), (key803, 4), (key801, 4), (key839, -2), (key836, -2), (key811, -2), (key778, -2), (key801, -2), (key776, -2), (key934, -2), (key876, -2), (key931, -2), (key803, -2), (key871, -2), (key801, -2), (key934, 4), (key811, 4), (key801, 4)]

def rawRow17022 : Integer.Sparse Key := [(key801, 4), (key803, 4), (key811, 4), (key801, -2), (key803, -2), (key871, -2), (key931, -2), (key876, -2), (key934, -2), (key776, -2), (key778, -2), (key801, -2), (key811, -2), (key836, -2), (key839, -2), (key801, 4), (key811, 4), (key934, 4)]

def rawRow17023 : Integer.Sparse Key := [(key803, 4), (key801, 4), (key811, 4), (key803, -2), (key801, -2), (key931, -2), (key871, -2), (key934, -2), (key876, -2), (key778, -2), (key776, -2), (key811, -2), (key801, -2), (key839, -2), (key836, -2), (key811, 4), (key801, 4), (key934, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17024 : Integer.Sparse Key := [(key801, 4), (key811, 4), (key803, 4), (key871, -2), (key876, -2), (key801, -2), (key934, -2), (key803, -2), (key931, -2), (key801, -2), (key811, -2), (key776, -2), (key839, -2), (key778, -2), (key811, -2), (key801, 4), (key934, 4), (key811, 4)]

def rawRow17025 : Integer.Sparse Key := [(key811, 4), (key801, 4), (key803, 4), (key876, -2), (key871, -2), (key934, -2), (key801, -2), (key931, -2), (key803, -2), (key811, -2), (key801, -2), (key839, -2), (key776, -2), (key811, -2), (key778, -2), (key934, 4), (key801, 4), (key811, 4)]

def rawRow17026 : Integer.Sparse Key := [(key803, 4), (key811, 4), (key801, 4), (key931, -2), (key934, -2), (key803, -2), (key876, -2), (key801, -2), (key871, -2), (key836, -2), (key839, -2), (key778, -2), (key811, -2), (key776, -2), (key801, -2), (key811, 4), (key934, 4), (key801, 4)]

def rawRow17027 : Integer.Sparse Key := [(key811, 4), (key803, 4), (key801, 4), (key934, -2), (key931, -2), (key876, -2), (key803, -2), (key871, -2), (key801, -2), (key839, -2), (key836, -2), (key811, -2), (key778, -2), (key801, -2), (key776, -2), (key934, 4), (key811, 4), (key801, 4)]

def rawRow17028 : Integer.Sparse Key := [(key871, 4), (key876, 4), (key876, 4), (key801, -2), (key811, -2), (key801, -2), (key934, -2), (key811, -2), (key934, -2), (key801, -2), (key811, -2), (key801, -2), (key934, -2), (key811, -2), (key934, -2), (key776, 4), (key839, 4), (key839, 4)]

def rawRow17029 : Integer.Sparse Key := [(key876, 4), (key871, 4), (key876, 4), (key811, -2), (key801, -2), (key934, -2), (key801, -2), (key934, -2), (key811, -2), (key811, -2), (key801, -2), (key934, -2), (key801, -2), (key934, -2), (key811, -2), (key839, 4), (key776, 4), (key839, 4)]

def rawRow17030 : Integer.Sparse Key := [(key876, 4), (key876, 4), (key871, 4), (key934, -2), (key934, -2), (key811, -2), (key811, -2), (key801, -2), (key801, -2), (key934, -2), (key934, -2), (key811, -2), (key811, -2), (key801, -2), (key801, -2), (key839, 4), (key839, 4), (key776, 4)]

def rawRow17031 : Integer.Sparse Key := [(key1976, 4), (key2218, 4), (key2224, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, -2), (key2266, -2), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, -2), (key2266, -2), (key1997, 4), (key2262, 4), (key2266, 4)]

def rawRow17032 : Integer.Sparse Key := [(key1976, 4), (key2224, 4), (key2218, 4), (key1983, -2), (key1981, -2), (key2224, -2), (key2218, -2), (key2266, -2), (key2262, -2), (key1983, -2), (key1981, -2), (key2224, -2), (key2218, -2), (key2266, -2), (key2262, -2), (key1997, 4), (key2266, 4), (key2262, 4)]

def rawRow17033 : Integer.Sparse Key := [(key2218, 4), (key1976, 4), (key2224, 4), (key2218, -2), (key2262, -2), (key1981, -2), (key2266, -2), (key1983, -2), (key2224, -2), (key2218, -2), (key2262, -2), (key1981, -2), (key2266, -2), (key1983, -2), (key2224, -2), (key2262, 4), (key1997, 4), (key2266, 4)]

def rawRow17034 : Integer.Sparse Key := [(key2218, 4), (key2224, 4), (key1976, 4), (key2262, -2), (key2218, -2), (key2266, -2), (key1981, -2), (key2224, -2), (key1983, -2), (key2262, -2), (key2218, -2), (key2266, -2), (key1981, -2), (key2224, -2), (key1983, -2), (key2262, 4), (key2266, 4), (key1997, 4)]

def rawRow17035 : Integer.Sparse Key := [(key2224, 4), (key1976, 4), (key2218, 4), (key2224, -2), (key2266, -2), (key1983, -2), (key2262, -2), (key1981, -2), (key2218, -2), (key2224, -2), (key2266, -2), (key1983, -2), (key2262, -2), (key1981, -2), (key2218, -2), (key2266, 4), (key1997, 4), (key2262, 4)]

def rawRow17036 : Integer.Sparse Key := [(key2224, 4), (key2218, 4), (key1976, 4), (key2266, -2), (key2224, -2), (key2262, -2), (key1983, -2), (key2218, -2), (key1981, -2), (key2266, -2), (key2224, -2), (key2262, -2), (key1983, -2), (key2218, -2), (key1981, -2), (key2266, 4), (key2262, 4), (key1997, 4)]

def rawRow17037 : Integer.Sparse Key := [(key1981, 4), (key1981, 4), (key2266, 4), (key1976, -2), (key1983, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key2224, -2), (key1981, -2), (key1997, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key2266, -2), (key1983, 4), (key1983, 4), (key2224, 4)]

def rawRow17038 : Integer.Sparse Key := [(key1981, 4), (key2266, 4), (key1981, 4), (key1983, -2), (key1976, -2), (key2224, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key1997, -2), (key1981, -2), (key2266, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key1983, 4), (key2224, 4), (key1983, 4)]

def rawRow17039 : Integer.Sparse Key := [(key2266, 4), (key1981, 4), (key1981, 4), (key2224, -2), (key2224, -2), (key1983, -2), (key1983, -2), (key1976, -2), (key1976, -2), (key2266, -2), (key2266, -2), (key1997, -2), (key1997, -2), (key1981, -2), (key1981, -2), (key2224, 4), (key1983, 4), (key1983, 4)]

def rawRow17040 : Integer.Sparse Key := [(key1983, 4), (key1983, 4), (key2262, 4), (key1976, -2), (key1981, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key2218, -2), (key1983, -2), (key1997, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key2262, -2), (key1981, 4), (key1981, 4), (key2218, 4)]

def rawRow17041 : Integer.Sparse Key := [(key1983, 4), (key2262, 4), (key1983, 4), (key1981, -2), (key1976, -2), (key2218, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key1997, -2), (key1983, -2), (key2262, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key1981, 4), (key2218, 4), (key1981, 4)]

def rawRow17042 : Integer.Sparse Key := [(key2262, 4), (key1983, 4), (key1983, 4), (key2218, -2), (key2218, -2), (key1981, -2), (key1981, -2), (key1976, -2), (key1976, -2), (key2262, -2), (key2262, -2), (key1997, -2), (key1997, -2), (key1983, -2), (key1983, -2), (key2218, 4), (key1981, 4), (key1981, 4)]

def rawRow17043 : Integer.Sparse Key := [(key1981, 4), (key1981, 4), (key2266, 4), (key1981, -2), (key1997, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key2266, -2), (key1976, -2), (key1983, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key2224, -2), (key1983, 4), (key1983, 4), (key2224, 4)]

def rawRow17044 : Integer.Sparse Key := [(key1981, 4), (key2266, 4), (key1981, 4), (key1997, -2), (key1981, -2), (key2266, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key1983, -2), (key1976, -2), (key2224, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key1983, 4), (key2224, 4), (key1983, 4)]

def rawRow17045 : Integer.Sparse Key := [(key2266, 4), (key1981, 4), (key1981, 4), (key2266, -2), (key2266, -2), (key1997, -2), (key1997, -2), (key1981, -2), (key1981, -2), (key2224, -2), (key2224, -2), (key1983, -2), (key1983, -2), (key1976, -2), (key1976, -2), (key2224, 4), (key1983, 4), (key1983, 4)]

def rawRow17046 : Integer.Sparse Key := [(key1997, 4), (key1997, 4), (key1997, 4), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1976, 4), (key1976, 4), (key1976, 4)]

def rawRow17047 : Integer.Sparse Key := [(key1983, 4), (key1983, 4), (key2262, 4), (key1983, -2), (key1997, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key2262, -2), (key1976, -2), (key1981, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key2218, -2), (key1981, 4), (key1981, 4), (key2218, 4)]

def rawRow17048 : Integer.Sparse Key := [(key1983, 4), (key2262, 4), (key1983, 4), (key1997, -2), (key1983, -2), (key2262, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key1981, -2), (key1976, -2), (key2218, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key1981, 4), (key2218, 4), (key1981, 4)]

def rawRow17049 : Integer.Sparse Key := [(key2262, 4), (key1983, 4), (key1983, 4), (key2262, -2), (key2262, -2), (key1997, -2), (key1997, -2), (key1983, -2), (key1983, -2), (key2218, -2), (key2218, -2), (key1981, -2), (key1981, -2), (key1976, -2), (key1976, -2), (key2218, 4), (key1981, 4), (key1981, 4)]

def rawRow17050 : Integer.Sparse Key := [(key1997, 4), (key1997, 4), (key1997, 4), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1976, 4), (key1976, 4), (key1976, 4)]

def rawRow17051 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, -2), (key63, 6), (key693, -2), (key697, -2), (key701, -2), (key693, 2), (key697, 2), (key845, 2), (key848, 2), (key854, 2), (key855, 2), (key701, -2), (key854, -2), (key855, -2), (key701, 6), (key701, -2), (key854, -2), (key855, -2)]

def rawRow17052 : Integer.Sparse Key := [(key56, -2), (key54, -2), (key63, -2), (key63, 6), (key697, -2), (key693, -2), (key701, -2), (key697, 2), (key693, 2), (key848, 2), (key845, 2), (key855, 2), (key854, 2), (key701, -2), (key855, -2), (key854, -2), (key701, 6), (key701, -2), (key855, -2), (key854, -2)]

def rawRow17053 : Integer.Sparse Key := [(key54, -2), (key63, -2), (key56, -2), (key63, 6), (key693, -2), (key701, -2), (key697, -2), (key845, 2), (key854, 2), (key693, 2), (key855, 2), (key697, 2), (key848, 2), (key854, -2), (key701, -2), (key855, -2), (key701, 6), (key854, -2), (key701, -2), (key855, -2)]

def rawRow17054 : Integer.Sparse Key := [(key63, -2), (key54, -2), (key56, -2), (key63, 6), (key701, -2), (key693, -2), (key697, -2), (key854, 2), (key845, 2), (key855, 2), (key693, 2), (key848, 2), (key697, 2), (key854, -2), (key855, -2), (key701, -2), (key701, 6), (key854, -2), (key855, -2), (key701, -2)]

def rawRow17055 : Integer.Sparse Key := [(key56, -2), (key63, -2), (key54, -2), (key63, 6), (key697, -2), (key701, -2), (key693, -2), (key848, 2), (key855, 2), (key697, 2), (key854, 2), (key693, 2), (key845, 2), (key855, -2), (key701, -2), (key854, -2), (key701, 6), (key855, -2), (key701, -2), (key854, -2)]

def rawRow17056 : Integer.Sparse Key := [(key63, -2), (key56, -2), (key54, -2), (key63, 6), (key701, -2), (key697, -2), (key693, -2), (key855, 2), (key848, 2), (key854, 2), (key697, 2), (key845, 2), (key693, 2), (key855, -2), (key854, -2), (key701, -2), (key701, 6), (key855, -2), (key854, -2), (key701, -2)]

def rawRow17057 : Integer.Sparse Key := [(key54, -2), (key63, -2), (key63, -2), (key56, 6), (key845, -2), (key854, -2), (key854, -2), (key693, 2), (key701, 2), (key693, 2), (key855, 2), (key701, 2), (key855, 2), (key697, -2), (key697, -2), (key848, -2), (key854, 6), (key701, -2), (key701, -2), (key855, -2)]

def rawRow17058 : Integer.Sparse Key := [(key63, -2), (key54, -2), (key63, -2), (key56, 6), (key854, -2), (key845, -2), (key854, -2), (key701, 2), (key693, 2), (key855, 2), (key693, 2), (key855, 2), (key701, 2), (key697, -2), (key848, -2), (key697, -2), (key854, 6), (key701, -2), (key855, -2), (key701, -2)]

def rawRow17059 : Integer.Sparse Key := [(key63, -2), (key63, -2), (key54, -2), (key56, 6), (key854, -2), (key854, -2), (key845, -2), (key855, 2), (key855, 2), (key701, 2), (key701, 2), (key693, 2), (key693, 2), (key848, -2), (key697, -2), (key697, -2), (key854, 6), (key855, -2), (key701, -2), (key701, -2)]

def rawRow17060 : Integer.Sparse Key := [(key56, -2), (key63, -2), (key63, -2), (key54, 6), (key848, -2), (key855, -2), (key855, -2), (key697, 2), (key701, 2), (key697, 2), (key854, 2), (key701, 2), (key854, 2), (key693, -2), (key693, -2), (key845, -2), (key855, 6), (key701, -2), (key701, -2), (key854, -2)]

def rawRow17061 : Integer.Sparse Key := [(key63, -2), (key56, -2), (key63, -2), (key54, 6), (key855, -2), (key848, -2), (key855, -2), (key701, 2), (key697, 2), (key854, 2), (key697, 2), (key854, 2), (key701, 2), (key693, -2), (key845, -2), (key693, -2), (key855, 6), (key701, -2), (key854, -2), (key701, -2)]

def rawRow17062 : Integer.Sparse Key := [(key63, -2), (key63, -2), (key56, -2), (key54, 6), (key855, -2), (key855, -2), (key848, -2), (key854, 2), (key854, 2), (key701, 2), (key701, 2), (key697, 2), (key697, 2), (key845, -2), (key693, -2), (key693, -2), (key855, 6), (key854, -2), (key701, -2), (key701, -2)]

def rawRow17063 : Integer.Sparse Key := [(key122, -2), (key128, -2), (key128, -2), (key128, 6), (key54, -2), (key63, -2), (key63, -2), (key693, 2), (key701, 2), (key693, 2), (key855, 2), (key701, 2), (key855, 2), (key701, -2), (key701, -2), (key855, -2), (key697, 6), (key697, -2), (key697, -2), (key848, -2)]

def rawRow17064 : Integer.Sparse Key := [(key128, -2), (key122, -2), (key128, -2), (key128, 6), (key63, -2), (key54, -2), (key63, -2), (key701, 2), (key693, 2), (key855, 2), (key693, 2), (key855, 2), (key701, 2), (key701, -2), (key855, -2), (key701, -2), (key697, 6), (key697, -2), (key848, -2), (key697, -2)]

def rawRow17065 : Integer.Sparse Key := [(key128, -2), (key128, -2), (key122, -2), (key128, 6), (key63, -2), (key63, -2), (key54, -2), (key855, 2), (key855, 2), (key701, 2), (key701, 2), (key693, 2), (key693, 2), (key855, -2), (key701, -2), (key701, -2), (key697, 6), (key848, -2), (key697, -2), (key697, -2)]

def rawRow17066 : Integer.Sparse Key := [(key128, -2), (key128, -2), (key128, -2), (key122, 6), (key199, -2), (key199, -2), (key199, -2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key54, -2), (key693, -2), (key693, -2), (key848, 6), (key697, -2), (key697, -2), (key697, -2)]

def rawRow17067 : Integer.Sparse Key := [(key198, -2), (key199, -2), (key199, -2), (key199, 6), (key56, -2), (key63, -2), (key63, -2), (key56, 2), (key63, 2), (key56, 2), (key128, 2), (key63, 2), (key128, 2), (key63, -2), (key63, -2), (key128, -2), (key54, 6), (key693, -2), (key693, -2), (key845, -2)]

def rawRow17068 : Integer.Sparse Key := [(key199, -2), (key198, -2), (key199, -2), (key199, 6), (key63, -2), (key56, -2), (key63, -2), (key63, 2), (key56, 2), (key128, 2), (key56, 2), (key128, 2), (key63, 2), (key63, -2), (key128, -2), (key63, -2), (key54, 6), (key693, -2), (key845, -2), (key693, -2)]

def rawRow17069 : Integer.Sparse Key := [(key199, -2), (key199, -2), (key198, -2), (key199, 6), (key63, -2), (key63, -2), (key56, -2), (key128, 2), (key128, 2), (key63, 2), (key63, 2), (key56, 2), (key56, 2), (key128, -2), (key63, -2), (key63, -2), (key54, 6), (key845, -2), (key693, -2), (key693, -2)]

def rawRow17070 : Integer.Sparse Key := [(key199, -2), (key199, -2), (key199, -2), (key198, 6), (key128, -2), (key128, -2), (key128, -2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key56, -2), (key56, -2), (key56, -2), (key122, 6), (key54, -2), (key693, -2), (key693, -2)]

def rawRow17071 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, -2), (key1985, 6), (key1973, -2), (key1978, -2), (key1985, -2), (key1973, 2), (key1978, 2), (key2209, 2), (key2215, 2), (key2226, 2), (key2230, 2), (key1985, -2), (key2226, -2), (key2230, -2), (key1985, 6), (key1985, -2), (key2226, -2), (key2230, -2)]

def rawRow17072 : Integer.Sparse Key := [(key1978, -2), (key1973, -2), (key1985, -2), (key1985, 6), (key1978, -2), (key1973, -2), (key1985, -2), (key1978, 2), (key1973, 2), (key2215, 2), (key2209, 2), (key2230, 2), (key2226, 2), (key1985, -2), (key2230, -2), (key2226, -2), (key1985, 6), (key1985, -2), (key2230, -2), (key2226, -2)]

def rawRow17073 : Integer.Sparse Key := [(key1973, -2), (key1985, -2), (key1978, -2), (key1985, 6), (key1973, -2), (key1985, -2), (key1978, -2), (key2209, 2), (key2226, 2), (key1973, 2), (key2230, 2), (key1978, 2), (key2215, 2), (key2226, -2), (key1985, -2), (key2230, -2), (key1985, 6), (key2226, -2), (key1985, -2), (key2230, -2)]

def rawRow17074 : Integer.Sparse Key := [(key1985, -2), (key1973, -2), (key1978, -2), (key1985, 6), (key1985, -2), (key1973, -2), (key1978, -2), (key2226, 2), (key2209, 2), (key2230, 2), (key1973, 2), (key2215, 2), (key1978, 2), (key2226, -2), (key2230, -2), (key1985, -2), (key1985, 6), (key2226, -2), (key2230, -2), (key1985, -2)]

def rawRow17075 : Integer.Sparse Key := [(key1978, -2), (key1985, -2), (key1973, -2), (key1985, 6), (key1978, -2), (key1985, -2), (key1973, -2), (key2215, 2), (key2230, 2), (key1978, 2), (key2226, 2), (key1973, 2), (key2209, 2), (key2230, -2), (key1985, -2), (key2226, -2), (key1985, 6), (key2230, -2), (key1985, -2), (key2226, -2)]

def rawRow17076 : Integer.Sparse Key := [(key1985, -2), (key1978, -2), (key1973, -2), (key1985, 6), (key1985, -2), (key1978, -2), (key1973, -2), (key2230, 2), (key2215, 2), (key2226, 2), (key1978, 2), (key2209, 2), (key1973, 2), (key2230, -2), (key2226, -2), (key1985, -2), (key1985, 6), (key2230, -2), (key2226, -2), (key1985, -2)]

def rawRow17077 : Integer.Sparse Key := [(key1973, -2), (key1985, -2), (key1985, -2), (key1978, 6), (key2209, -2), (key2226, -2), (key2226, -2), (key1973, 2), (key1985, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key2230, 2), (key1978, -2), (key1978, -2), (key2215, -2), (key2226, 6), (key1985, -2), (key1985, -2), (key2230, -2)]

def rawRow17078 : Integer.Sparse Key := [(key1985, -2), (key1973, -2), (key1985, -2), (key1978, 6), (key2226, -2), (key2209, -2), (key2226, -2), (key1985, 2), (key1973, 2), (key2230, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key1978, -2), (key2215, -2), (key1978, -2), (key2226, 6), (key1985, -2), (key2230, -2), (key1985, -2)]

def rawRow17079 : Integer.Sparse Key := [(key1985, -2), (key1985, -2), (key1973, -2), (key1978, 6), (key2226, -2), (key2226, -2), (key2209, -2), (key2230, 2), (key2230, 2), (key1985, 2), (key1985, 2), (key1973, 2), (key1973, 2), (key2215, -2), (key1978, -2), (key1978, -2), (key2226, 6), (key2230, -2), (key1985, -2), (key1985, -2)]

def rawRow17080 : Integer.Sparse Key := [(key1978, -2), (key1985, -2), (key1985, -2), (key1973, 6), (key2215, -2), (key2230, -2), (key2230, -2), (key1978, 2), (key1985, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key2226, 2), (key1973, -2), (key1973, -2), (key2209, -2), (key2230, 6), (key1985, -2), (key1985, -2), (key2226, -2)]

def rawRow17081 : Integer.Sparse Key := [(key1985, -2), (key1978, -2), (key1985, -2), (key1973, 6), (key2230, -2), (key2215, -2), (key2230, -2), (key1985, 2), (key1978, 2), (key2226, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key1973, -2), (key2209, -2), (key1973, -2), (key2230, 6), (key1985, -2), (key2226, -2), (key1985, -2)]

def rawRow17082 : Integer.Sparse Key := [(key1985, -2), (key1985, -2), (key1978, -2), (key1973, 6), (key2230, -2), (key2230, -2), (key2215, -2), (key2226, 2), (key2226, 2), (key1985, 2), (key1985, 2), (key1978, 2), (key1978, 2), (key2209, -2), (key1973, -2), (key1973, -2), (key2230, 6), (key2226, -2), (key1985, -2), (key1985, -2)]

def rawRow17083 : Integer.Sparse Key := [(key2209, -2), (key2226, -2), (key2226, -2), (key2226, 6), (key1973, -2), (key1985, -2), (key1985, -2), (key1973, 2), (key1985, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key2230, 2), (key1985, -2), (key1985, -2), (key2230, -2), (key1978, 6), (key1978, -2), (key1978, -2), (key2215, -2)]

def rawRow17084 : Integer.Sparse Key := [(key2226, -2), (key2209, -2), (key2226, -2), (key2226, 6), (key1985, -2), (key1973, -2), (key1985, -2), (key1985, 2), (key1973, 2), (key2230, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key1985, -2), (key2230, -2), (key1985, -2), (key1978, 6), (key1978, -2), (key2215, -2), (key1978, -2)]

def rawRow17085 : Integer.Sparse Key := [(key2226, -2), (key2226, -2), (key2209, -2), (key2226, 6), (key1985, -2), (key1985, -2), (key1973, -2), (key2230, 2), (key2230, 2), (key1985, 2), (key1985, 2), (key1973, 2), (key1973, 2), (key2230, -2), (key1985, -2), (key1985, -2), (key1978, 6), (key2215, -2), (key1978, -2), (key1978, -2)]

def rawRow17086 : Integer.Sparse Key := [(key2226, -2), (key2226, -2), (key2226, -2), (key2209, 6), (key2230, -2), (key2230, -2), (key2230, -2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1973, -2), (key1973, -2), (key1973, -2), (key2215, 6), (key1978, -2), (key1978, -2), (key1978, -2)]

def rawRow17087 : Integer.Sparse Key := [(key2215, -2), (key2230, -2), (key2230, -2), (key2230, 6), (key1978, -2), (key1985, -2), (key1985, -2), (key1978, 2), (key1985, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key2226, 2), (key1985, -2), (key1985, -2), (key2226, -2), (key1973, 6), (key1973, -2), (key1973, -2), (key2209, -2)]

def rawRow17088 : Integer.Sparse Key := [(key2230, -2), (key2215, -2), (key2230, -2), (key2230, 6), (key1985, -2), (key1978, -2), (key1985, -2), (key1985, 2), (key1978, 2), (key2226, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key1985, -2), (key2226, -2), (key1985, -2), (key1973, 6), (key1973, -2), (key2209, -2), (key1973, -2)]

def rawRow17089 : Integer.Sparse Key := [(key2230, -2), (key2230, -2), (key2215, -2), (key2230, 6), (key1985, -2), (key1985, -2), (key1978, -2), (key2226, 2), (key2226, 2), (key1985, 2), (key1985, 2), (key1978, 2), (key1978, 2), (key2226, -2), (key1985, -2), (key1985, -2), (key1973, 6), (key2209, -2), (key1973, -2), (key1973, -2)]

def rawRow17090 : Integer.Sparse Key := [(key2230, -2), (key2230, -2), (key2230, -2), (key2215, 6), (key2226, -2), (key2226, -2), (key2226, -2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1978, -2), (key1978, -2), (key1978, -2), (key2209, 6), (key1973, -2), (key1973, -2), (key1973, -2)]

def rawRow17091 : Integer.Sparse Key := [(key2015, 6), (key2015, -2), (key2044, -2), (key2045, -2), (key2015, 6), (key2015, -2), (key2129, -2), (key2132, -2), (key2015, -2), (key2044, -2), (key2045, -2), (key2015, -2), (key2129, -2), (key2132, -2), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, 2), (key2213, 2)]

def rawRow17092 : Integer.Sparse Key := [(key2015, 6), (key2015, -2), (key2045, -2), (key2044, -2), (key2015, 6), (key2015, -2), (key2132, -2), (key2129, -2), (key2015, -2), (key2045, -2), (key2044, -2), (key2015, -2), (key2132, -2), (key2129, -2), (key2045, 2), (key2044, 2), (key2132, 2), (key2129, 2), (key2213, 2), (key2212, 2)]

def rawRow17093 : Integer.Sparse Key := [(key2015, 6), (key2044, -2), (key2015, -2), (key2045, -2), (key2015, 6), (key2129, -2), (key2015, -2), (key2132, -2), (key2044, -2), (key2015, -2), (key2045, -2), (key2129, -2), (key2015, -2), (key2132, -2), (key2129, 2), (key2212, 2), (key2044, 2), (key2213, 2), (key2045, 2), (key2132, 2)]

def rawRow17094 : Integer.Sparse Key := [(key2015, 6), (key2044, -2), (key2045, -2), (key2015, -2), (key2015, 6), (key2129, -2), (key2132, -2), (key2015, -2), (key2044, -2), (key2045, -2), (key2015, -2), (key2129, -2), (key2132, -2), (key2015, -2), (key2212, 2), (key2129, 2), (key2213, 2), (key2044, 2), (key2132, 2), (key2045, 2)]

def rawRow17095 : Integer.Sparse Key := [(key2015, 6), (key2045, -2), (key2015, -2), (key2044, -2), (key2015, 6), (key2132, -2), (key2015, -2), (key2129, -2), (key2045, -2), (key2015, -2), (key2044, -2), (key2132, -2), (key2015, -2), (key2129, -2), (key2132, 2), (key2213, 2), (key2045, 2), (key2212, 2), (key2044, 2), (key2129, 2)]

def rawRow17096 : Integer.Sparse Key := [(key2015, 6), (key2045, -2), (key2044, -2), (key2015, -2), (key2015, 6), (key2132, -2), (key2129, -2), (key2015, -2), (key2045, -2), (key2044, -2), (key2015, -2), (key2132, -2), (key2129, -2), (key2015, -2), (key2213, 2), (key2132, 2), (key2212, 2), (key2045, 2), (key2129, 2), (key2044, 2)]

def rawRow17097 : Integer.Sparse Key := [(key2044, 6), (key2015, -2), (key2015, -2), (key2045, -2), (key2129, 6), (key2015, -2), (key2015, -2), (key2132, -2), (key2129, -2), (key2129, -2), (key2212, -2), (key2044, -2), (key2044, -2), (key2213, -2), (key2015, 2), (key2045, 2), (key2015, 2), (key2132, 2), (key2045, 2), (key2132, 2)]

def rawRow17098 : Integer.Sparse Key := [(key2044, 6), (key2015, -2), (key2045, -2), (key2015, -2), (key2129, 6), (key2015, -2), (key2132, -2), (key2015, -2), (key2129, -2), (key2212, -2), (key2129, -2), (key2044, -2), (key2213, -2), (key2044, -2), (key2045, 2), (key2015, 2), (key2132, 2), (key2015, 2), (key2132, 2), (key2045, 2)]

def rawRow17099 : Integer.Sparse Key := [(key2044, 6), (key2045, -2), (key2015, -2), (key2015, -2), (key2129, 6), (key2132, -2), (key2015, -2), (key2015, -2), (key2212, -2), (key2129, -2), (key2129, -2), (key2213, -2), (key2044, -2), (key2044, -2), (key2132, 2), (key2132, 2), (key2045, 2), (key2045, 2), (key2015, 2), (key2015, 2)]

def rawRow17100 : Integer.Sparse Key := [(key2045, 6), (key2015, -2), (key2015, -2), (key2044, -2), (key2132, 6), (key2015, -2), (key2015, -2), (key2129, -2), (key2132, -2), (key2132, -2), (key2213, -2), (key2045, -2), (key2045, -2), (key2212, -2), (key2015, 2), (key2044, 2), (key2015, 2), (key2129, 2), (key2044, 2), (key2129, 2)]

def rawRow17101 : Integer.Sparse Key := [(key2045, 6), (key2015, -2), (key2044, -2), (key2015, -2), (key2132, 6), (key2015, -2), (key2129, -2), (key2015, -2), (key2132, -2), (key2213, -2), (key2132, -2), (key2045, -2), (key2212, -2), (key2045, -2), (key2044, 2), (key2015, 2), (key2129, 2), (key2015, 2), (key2129, 2), (key2044, 2)]

def rawRow17102 : Integer.Sparse Key := [(key2045, 6), (key2044, -2), (key2015, -2), (key2015, -2), (key2132, 6), (key2129, -2), (key2015, -2), (key2015, -2), (key2213, -2), (key2132, -2), (key2132, -2), (key2212, -2), (key2045, -2), (key2045, -2), (key2129, 2), (key2129, 2), (key2044, 2), (key2044, 2), (key2015, 2), (key2015, 2)]

def rawRow17103 : Integer.Sparse Key := [(key2129, 6), (key2129, -2), (key2129, -2), (key2212, -2), (key2044, 6), (key2044, -2), (key2044, -2), (key2213, -2), (key2015, -2), (key2015, -2), (key2045, -2), (key2015, -2), (key2015, -2), (key2132, -2), (key2015, 2), (key2045, 2), (key2015, 2), (key2132, 2), (key2045, 2), (key2132, 2)]

def rawRow17104 : Integer.Sparse Key := [(key2129, 6), (key2129, -2), (key2212, -2), (key2129, -2), (key2044, 6), (key2044, -2), (key2213, -2), (key2044, -2), (key2015, -2), (key2045, -2), (key2015, -2), (key2015, -2), (key2132, -2), (key2015, -2), (key2045, 2), (key2015, 2), (key2132, 2), (key2015, 2), (key2132, 2), (key2045, 2)]

def rawRow17105 : Integer.Sparse Key := [(key2129, 6), (key2212, -2), (key2129, -2), (key2129, -2), (key2044, 6), (key2213, -2), (key2044, -2), (key2044, -2), (key2045, -2), (key2015, -2), (key2015, -2), (key2132, -2), (key2015, -2), (key2015, -2), (key2132, 2), (key2132, 2), (key2045, 2), (key2045, 2), (key2015, 2), (key2015, 2)]

def rawRow17106 : Integer.Sparse Key := [(key2212, 6), (key2129, -2), (key2129, -2), (key2129, -2), (key2213, 6), (key2044, -2), (key2044, -2), (key2044, -2), (key2132, -2), (key2132, -2), (key2132, -2), (key2045, -2), (key2045, -2), (key2045, -2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2)]

def rawRow17107 : Integer.Sparse Key := [(key2132, 6), (key2132, -2), (key2132, -2), (key2213, -2), (key2045, 6), (key2045, -2), (key2045, -2), (key2212, -2), (key2015, -2), (key2015, -2), (key2044, -2), (key2015, -2), (key2015, -2), (key2129, -2), (key2015, 2), (key2044, 2), (key2015, 2), (key2129, 2), (key2044, 2), (key2129, 2)]

def rawRow17108 : Integer.Sparse Key := [(key2132, 6), (key2132, -2), (key2213, -2), (key2132, -2), (key2045, 6), (key2045, -2), (key2212, -2), (key2045, -2), (key2015, -2), (key2044, -2), (key2015, -2), (key2015, -2), (key2129, -2), (key2015, -2), (key2044, 2), (key2015, 2), (key2129, 2), (key2015, 2), (key2129, 2), (key2044, 2)]

def rawRow17109 : Integer.Sparse Key := [(key2132, 6), (key2213, -2), (key2132, -2), (key2132, -2), (key2045, 6), (key2212, -2), (key2045, -2), (key2045, -2), (key2044, -2), (key2015, -2), (key2015, -2), (key2129, -2), (key2015, -2), (key2015, -2), (key2129, 2), (key2129, 2), (key2044, 2), (key2044, 2), (key2015, 2), (key2015, 2)]

def rawRow17110 : Integer.Sparse Key := [(key2213, 6), (key2132, -2), (key2132, -2), (key2132, -2), (key2212, 6), (key2045, -2), (key2045, -2), (key2045, -2), (key2129, -2), (key2129, -2), (key2129, -2), (key2044, -2), (key2044, -2), (key2044, -2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2)]

def rawRow17111 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, -2), (key699, 6), (key694, -2), (key696, -2), (key699, -2), (key694, 2), (key696, 2), (key846, 2), (key847, 2), (key850, 2), (key852, 2), (key699, -2), (key850, -2), (key852, -2), (key699, 6), (key699, -2), (key850, -2), (key852, -2)]

def rawRow17112 : Integer.Sparse Key := [(key696, -2), (key694, -2), (key699, -2), (key699, 6), (key696, -2), (key694, -2), (key699, -2), (key696, 2), (key694, 2), (key847, 2), (key846, 2), (key852, 2), (key850, 2), (key699, -2), (key852, -2), (key850, -2), (key699, 6), (key699, -2), (key852, -2), (key850, -2)]

def rawRow17113 : Integer.Sparse Key := [(key694, -2), (key699, -2), (key696, -2), (key699, 6), (key694, -2), (key699, -2), (key696, -2), (key846, 2), (key850, 2), (key694, 2), (key852, 2), (key696, 2), (key847, 2), (key850, -2), (key699, -2), (key852, -2), (key699, 6), (key850, -2), (key699, -2), (key852, -2)]

def rawRow17114 : Integer.Sparse Key := [(key699, -2), (key694, -2), (key696, -2), (key699, 6), (key699, -2), (key694, -2), (key696, -2), (key850, 2), (key846, 2), (key852, 2), (key694, 2), (key847, 2), (key696, 2), (key850, -2), (key852, -2), (key699, -2), (key699, 6), (key850, -2), (key852, -2), (key699, -2)]

def rawRow17115 : Integer.Sparse Key := [(key696, -2), (key699, -2), (key694, -2), (key699, 6), (key696, -2), (key699, -2), (key694, -2), (key847, 2), (key852, 2), (key696, 2), (key850, 2), (key694, 2), (key846, 2), (key852, -2), (key699, -2), (key850, -2), (key699, 6), (key852, -2), (key699, -2), (key850, -2)]

def rawRow17116 : Integer.Sparse Key := [(key699, -2), (key696, -2), (key694, -2), (key699, 6), (key699, -2), (key696, -2), (key694, -2), (key852, 2), (key847, 2), (key850, 2), (key696, 2), (key846, 2), (key694, 2), (key852, -2), (key850, -2), (key699, -2), (key699, 6), (key852, -2), (key850, -2), (key699, -2)]

def rawRow17117 : Integer.Sparse Key := [(key694, -2), (key699, -2), (key699, -2), (key696, 6), (key846, -2), (key850, -2), (key850, -2), (key694, 2), (key699, 2), (key694, 2), (key852, 2), (key699, 2), (key852, 2), (key696, -2), (key696, -2), (key847, -2), (key850, 6), (key699, -2), (key699, -2), (key852, -2)]

def rawRow17118 : Integer.Sparse Key := [(key699, -2), (key694, -2), (key699, -2), (key696, 6), (key850, -2), (key846, -2), (key850, -2), (key699, 2), (key694, 2), (key852, 2), (key694, 2), (key852, 2), (key699, 2), (key696, -2), (key847, -2), (key696, -2), (key850, 6), (key699, -2), (key852, -2), (key699, -2)]

def rawRow17119 : Integer.Sparse Key := [(key699, -2), (key699, -2), (key694, -2), (key696, 6), (key850, -2), (key850, -2), (key846, -2), (key852, 2), (key852, 2), (key699, 2), (key699, 2), (key694, 2), (key694, 2), (key847, -2), (key696, -2), (key696, -2), (key850, 6), (key852, -2), (key699, -2), (key699, -2)]

def rawRow17120 : Integer.Sparse Key := [(key696, -2), (key699, -2), (key699, -2), (key694, 6), (key847, -2), (key852, -2), (key852, -2), (key696, 2), (key699, 2), (key696, 2), (key850, 2), (key699, 2), (key850, 2), (key694, -2), (key694, -2), (key846, -2), (key852, 6), (key699, -2), (key699, -2), (key850, -2)]

def rawRow17121 : Integer.Sparse Key := [(key699, -2), (key696, -2), (key699, -2), (key694, 6), (key852, -2), (key847, -2), (key852, -2), (key699, 2), (key696, 2), (key850, 2), (key696, 2), (key850, 2), (key699, 2), (key694, -2), (key846, -2), (key694, -2), (key852, 6), (key699, -2), (key850, -2), (key699, -2)]

def rawRow17122 : Integer.Sparse Key := [(key699, -2), (key699, -2), (key696, -2), (key694, 6), (key852, -2), (key852, -2), (key847, -2), (key850, 2), (key850, 2), (key699, 2), (key699, 2), (key696, 2), (key696, 2), (key846, -2), (key694, -2), (key694, -2), (key852, 6), (key850, -2), (key699, -2), (key699, -2)]

def rawRow17123 : Integer.Sparse Key := [(key846, -2), (key850, -2), (key850, -2), (key850, 6), (key694, -2), (key699, -2), (key699, -2), (key694, 2), (key699, 2), (key694, 2), (key852, 2), (key699, 2), (key852, 2), (key699, -2), (key699, -2), (key852, -2), (key696, 6), (key696, -2), (key696, -2), (key847, -2)]

def rawRow17124 : Integer.Sparse Key := [(key850, -2), (key846, -2), (key850, -2), (key850, 6), (key699, -2), (key694, -2), (key699, -2), (key699, 2), (key694, 2), (key852, 2), (key694, 2), (key852, 2), (key699, 2), (key699, -2), (key852, -2), (key699, -2), (key696, 6), (key696, -2), (key847, -2), (key696, -2)]

def rawRow17125 : Integer.Sparse Key := [(key850, -2), (key850, -2), (key846, -2), (key850, 6), (key699, -2), (key699, -2), (key694, -2), (key852, 2), (key852, 2), (key699, 2), (key699, 2), (key694, 2), (key694, 2), (key852, -2), (key699, -2), (key699, -2), (key696, 6), (key847, -2), (key696, -2), (key696, -2)]

def rawRow17126 : Integer.Sparse Key := [(key850, -2), (key850, -2), (key850, -2), (key846, 6), (key852, -2), (key852, -2), (key852, -2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key694, -2), (key694, -2), (key694, -2), (key847, 6), (key696, -2), (key696, -2), (key696, -2)]

def rawRow17127 : Integer.Sparse Key := [(key847, -2), (key852, -2), (key852, -2), (key852, 6), (key696, -2), (key699, -2), (key699, -2), (key696, 2), (key699, 2), (key696, 2), (key850, 2), (key699, 2), (key850, 2), (key699, -2), (key699, -2), (key850, -2), (key694, 6), (key694, -2), (key694, -2), (key846, -2)]

def rawRow17128 : Integer.Sparse Key := [(key852, -2), (key847, -2), (key852, -2), (key852, 6), (key699, -2), (key696, -2), (key699, -2), (key699, 2), (key696, 2), (key850, 2), (key696, 2), (key850, 2), (key699, 2), (key699, -2), (key850, -2), (key699, -2), (key694, 6), (key694, -2), (key846, -2), (key694, -2)]

def rawRow17129 : Integer.Sparse Key := [(key852, -2), (key852, -2), (key847, -2), (key852, 6), (key699, -2), (key699, -2), (key696, -2), (key850, 2), (key850, 2), (key699, 2), (key699, 2), (key696, 2), (key696, 2), (key850, -2), (key699, -2), (key699, -2), (key694, 6), (key846, -2), (key694, -2), (key694, -2)]

def rawRow17130 : Integer.Sparse Key := [(key852, -2), (key852, -2), (key852, -2), (key847, 6), (key850, -2), (key850, -2), (key850, -2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key696, -2), (key696, -2), (key696, -2), (key846, 6), (key694, -2), (key694, -2), (key694, -2)]

def rawRow17131 : Integer.Sparse Key := [(key695, 4), (key849, 4), (key853, 4), (key698, -2), (key700, -2), (key849, -2), (key853, -2), (key888, -2), (key889, -2), (key698, -2), (key700, -2), (key849, -2), (key853, -2), (key888, -2), (key889, -2), (key712, 4), (key888, 4), (key889, 4)]

def rawRow17132 : Integer.Sparse Key := [(key695, 4), (key853, 4), (key849, 4), (key700, -2), (key698, -2), (key853, -2), (key849, -2), (key889, -2), (key888, -2), (key700, -2), (key698, -2), (key853, -2), (key849, -2), (key889, -2), (key888, -2), (key712, 4), (key889, 4), (key888, 4)]

def rawRow17133 : Integer.Sparse Key := [(key849, 4), (key695, 4), (key853, 4), (key849, -2), (key888, -2), (key698, -2), (key889, -2), (key700, -2), (key853, -2), (key849, -2), (key888, -2), (key698, -2), (key889, -2), (key700, -2), (key853, -2), (key888, 4), (key712, 4), (key889, 4)]

def rawRow17134 : Integer.Sparse Key := [(key849, 4), (key853, 4), (key695, 4), (key888, -2), (key849, -2), (key889, -2), (key698, -2), (key853, -2), (key700, -2), (key888, -2), (key849, -2), (key889, -2), (key698, -2), (key853, -2), (key700, -2), (key888, 4), (key889, 4), (key712, 4)]

def rawRow17135 : Integer.Sparse Key := [(key853, 4), (key695, 4), (key849, 4), (key853, -2), (key889, -2), (key700, -2), (key888, -2), (key698, -2), (key849, -2), (key853, -2), (key889, -2), (key700, -2), (key888, -2), (key698, -2), (key849, -2), (key889, 4), (key712, 4), (key888, 4)]

def rawRow17136 : Integer.Sparse Key := [(key853, 4), (key849, 4), (key695, 4), (key889, -2), (key853, -2), (key888, -2), (key700, -2), (key849, -2), (key698, -2), (key889, -2), (key853, -2), (key888, -2), (key700, -2), (key849, -2), (key698, -2), (key889, 4), (key888, 4), (key712, 4)]

def rawRow17137 : Integer.Sparse Key := [(key698, 4), (key698, 4), (key889, 4), (key695, -2), (key700, -2), (key695, -2), (key853, -2), (key700, -2), (key853, -2), (key698, -2), (key712, -2), (key698, -2), (key889, -2), (key712, -2), (key889, -2), (key700, 4), (key700, 4), (key853, 4)]

def rawRow17138 : Integer.Sparse Key := [(key698, 4), (key889, 4), (key698, 4), (key700, -2), (key695, -2), (key853, -2), (key695, -2), (key853, -2), (key700, -2), (key712, -2), (key698, -2), (key889, -2), (key698, -2), (key889, -2), (key712, -2), (key700, 4), (key853, 4), (key700, 4)]

def rawRow17139 : Integer.Sparse Key := [(key889, 4), (key698, 4), (key698, 4), (key853, -2), (key853, -2), (key700, -2), (key700, -2), (key695, -2), (key695, -2), (key889, -2), (key889, -2), (key712, -2), (key712, -2), (key698, -2), (key698, -2), (key853, 4), (key700, 4), (key700, 4)]

def rawRow17140 : Integer.Sparse Key := [(key700, 4), (key700, 4), (key888, 4), (key695, -2), (key698, -2), (key695, -2), (key849, -2), (key698, -2), (key849, -2), (key700, -2), (key712, -2), (key700, -2), (key888, -2), (key712, -2), (key888, -2), (key698, 4), (key698, 4), (key849, 4)]

def rawRow17141 : Integer.Sparse Key := [(key700, 4), (key888, 4), (key700, 4), (key698, -2), (key695, -2), (key849, -2), (key695, -2), (key849, -2), (key698, -2), (key712, -2), (key700, -2), (key888, -2), (key700, -2), (key888, -2), (key712, -2), (key698, 4), (key849, 4), (key698, 4)]

def rawRow17142 : Integer.Sparse Key := [(key888, 4), (key700, 4), (key700, 4), (key849, -2), (key849, -2), (key698, -2), (key698, -2), (key695, -2), (key695, -2), (key888, -2), (key888, -2), (key712, -2), (key712, -2), (key700, -2), (key700, -2), (key849, 4), (key698, 4), (key698, 4)]

def rawRow17143 : Integer.Sparse Key := [(key698, 4), (key698, 4), (key889, 4), (key698, -2), (key712, -2), (key698, -2), (key889, -2), (key712, -2), (key889, -2), (key695, -2), (key700, -2), (key695, -2), (key853, -2), (key700, -2), (key853, -2), (key700, 4), (key700, 4), (key853, 4)]

def rawRow17144 : Integer.Sparse Key := [(key698, 4), (key889, 4), (key698, 4), (key712, -2), (key698, -2), (key889, -2), (key698, -2), (key889, -2), (key712, -2), (key700, -2), (key695, -2), (key853, -2), (key695, -2), (key853, -2), (key700, -2), (key700, 4), (key853, 4), (key700, 4)]

def rawRow17145 : Integer.Sparse Key := [(key889, 4), (key698, 4), (key698, 4), (key889, -2), (key889, -2), (key712, -2), (key712, -2), (key698, -2), (key698, -2), (key853, -2), (key853, -2), (key700, -2), (key700, -2), (key695, -2), (key695, -2), (key853, 4), (key700, 4), (key700, 4)]

def rawRow17146 : Integer.Sparse Key := [(key82, 4), (key82, 4), (key82, 4), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key700, -2), (key700, -2), (key700, -2), (key700, -2), (key700, -2), (key700, -2), (key695, 4), (key695, 4), (key695, 4)]

def rawRow17147 : Integer.Sparse Key := [(key68, 4), (key68, 4), (key145, 4), (key68, -2), (key82, -2), (key68, -2), (key145, -2), (key82, -2), (key145, -2), (key58, -2), (key65, -2), (key58, -2), (key130, -2), (key65, -2), (key130, -2), (key65, 4), (key65, 4), (key130, 4)]

def rawRow17148 : Integer.Sparse Key := [(key68, 4), (key145, 4), (key68, 4), (key82, -2), (key68, -2), (key145, -2), (key68, -2), (key145, -2), (key82, -2), (key65, -2), (key58, -2), (key130, -2), (key58, -2), (key130, -2), (key65, -2), (key65, 4), (key130, 4), (key65, 4)]

def rawRow17149 : Integer.Sparse Key := [(key145, 4), (key68, 4), (key68, 4), (key145, -2), (key145, -2), (key82, -2), (key82, -2), (key68, -2), (key68, -2), (key130, -2), (key130, -2), (key65, -2), (key65, -2), (key58, -2), (key58, -2), (key130, 4), (key65, 4), (key65, 4)]

def rawRow17150 : Integer.Sparse Key := [(key82, 4), (key82, 4), (key82, 4), (key68, -2), (key68, -2), (key68, -2), (key68, -2), (key68, -2), (key68, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key58, 4), (key58, 4), (key58, 4)]

def rawRow17151 : Integer.Sparse Key := [(key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2026, 2), (key2144, 2), (key2145, 2), (key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2042, 2), (key2047, 2), (key2127, 2), (key2134, 2), (key2228, 2), (key2229, 2), (key2055, -1), (key2056, -1), (key2144, -1), (key2145, -1), (key2228, -1), (key2229, -1), (key2026, 2), (key2144, 2), (key2145, 2), (key2055, -1), (key2056, -1), (key2144, -1), (key2145, -1), (key2228, -1), (key2229, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17152 : Integer.Sparse Key := [(key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2026, 2), (key2145, 2), (key2144, 2), (key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2047, 2), (key2042, 2), (key2134, 2), (key2127, 2), (key2229, 2), (key2228, 2), (key2056, -1), (key2055, -1), (key2145, -1), (key2144, -1), (key2229, -1), (key2228, -1), (key2026, 2), (key2145, 2), (key2144, 2), (key2056, -1), (key2055, -1), (key2145, -1), (key2144, -1), (key2229, -1), (key2228, -1)]

def rawRow17153 : Integer.Sparse Key := [(key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2144, 2), (key2026, 2), (key2145, 2), (key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2127, 2), (key2228, 2), (key2042, 2), (key2229, 2), (key2047, 2), (key2134, 2), (key2144, -1), (key2228, -1), (key2055, -1), (key2229, -1), (key2056, -1), (key2145, -1), (key2144, 2), (key2026, 2), (key2145, 2), (key2144, -1), (key2228, -1), (key2055, -1), (key2229, -1), (key2056, -1), (key2145, -1)]

def rawRow17154 : Integer.Sparse Key := [(key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2144, 2), (key2145, 2), (key2026, 2), (key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2228, 2), (key2127, 2), (key2229, 2), (key2042, 2), (key2134, 2), (key2047, 2), (key2228, -1), (key2144, -1), (key2229, -1), (key2055, -1), (key2145, -1), (key2056, -1), (key2144, 2), (key2145, 2), (key2026, 2), (key2228, -1), (key2144, -1), (key2229, -1), (key2055, -1), (key2145, -1), (key2056, -1)]

def rawRow17155 : Integer.Sparse Key := [(key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2145, 2), (key2026, 2), (key2144, 2), (key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2134, 2), (key2229, 2), (key2047, 2), (key2228, 2), (key2042, 2), (key2127, 2), (key2145, -1), (key2229, -1), (key2056, -1), (key2228, -1), (key2055, -1), (key2144, -1), (key2145, 2), (key2026, 2), (key2144, 2), (key2145, -1), (key2229, -1), (key2056, -1), (key2228, -1), (key2055, -1), (key2144, -1)]

def rawRow17156 : Integer.Sparse Key := [(key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2145, 2), (key2144, 2), (key2026, 2), (key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2229, 2), (key2134, 2), (key2228, 2), (key2047, 2), (key2127, 2), (key2042, 2), (key2229, -1), (key2145, -1), (key2228, -1), (key2056, -1), (key2144, -1), (key2055, -1), (key2145, 2), (key2144, 2), (key2026, 2), (key2229, -1), (key2145, -1), (key2228, -1), (key2056, -1), (key2144, -1), (key2055, -1)]

def rawRow17157 : Integer.Sparse Key := [(key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2019, 2), (key2019, 2), (key2134, 2), (key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2), (key2019, -1), (key2047, -1), (key2019, -1), (key2134, -1), (key2047, -1), (key2134, -1), (key2055, 2), (key2055, 2), (key2229, 2), (key2026, -1), (key2056, -1), (key2026, -1), (key2145, -1), (key2056, -1), (key2145, -1)]

def rawRow17158 : Integer.Sparse Key := [(key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2019, 2), (key2134, 2), (key2019, 2), (key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2047, -1), (key2019, -1), (key2134, -1), (key2019, -1), (key2134, -1), (key2047, -1), (key2055, 2), (key2229, 2), (key2055, 2), (key2056, -1), (key2026, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2056, -1)]

def rawRow17159 : Integer.Sparse Key := [(key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2134, 2), (key2019, 2), (key2019, 2), (key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2), (key2134, -1), (key2134, -1), (key2047, -1), (key2047, -1), (key2019, -1), (key2019, -1), (key2229, 2), (key2055, 2), (key2055, 2), (key2145, -1), (key2145, -1), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1)]

def rawRow17160 : Integer.Sparse Key := [(key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2013, 2), (key2013, 2), (key2127, 2), (key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2), (key2013, -1), (key2042, -1), (key2013, -1), (key2127, -1), (key2042, -1), (key2127, -1), (key2056, 2), (key2056, 2), (key2228, 2), (key2026, -1), (key2055, -1), (key2026, -1), (key2144, -1), (key2055, -1), (key2144, -1)]

def rawRow17161 : Integer.Sparse Key := [(key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2013, 2), (key2127, 2), (key2013, 2), (key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2042, -1), (key2013, -1), (key2127, -1), (key2013, -1), (key2127, -1), (key2042, -1), (key2056, 2), (key2228, 2), (key2056, 2), (key2055, -1), (key2026, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2055, -1)]

def rawRow17162 : Integer.Sparse Key := [(key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2127, 2), (key2013, 2), (key2013, 2), (key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2), (key2127, -1), (key2127, -1), (key2042, -1), (key2042, -1), (key2013, -1), (key2013, -1), (key2228, 2), (key2056, 2), (key2056, 2), (key2144, -1), (key2144, -1), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1)]

def rawRow17163 : Integer.Sparse Key := [(key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2055, 2), (key2055, 2), (key2229, 2), (key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2), (key2026, -1), (key2056, -1), (key2026, -1), (key2145, -1), (key2056, -1), (key2145, -1), (key2019, 2), (key2019, 2), (key2134, 2), (key2019, -1), (key2047, -1), (key2019, -1), (key2134, -1), (key2047, -1), (key2134, -1)]

def rawRow17164 : Integer.Sparse Key := [(key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2055, 2), (key2229, 2), (key2055, 2), (key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2056, -1), (key2026, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2056, -1), (key2019, 2), (key2134, 2), (key2019, 2), (key2047, -1), (key2019, -1), (key2134, -1), (key2019, -1), (key2134, -1), (key2047, -1)]

def rawRow17165 : Integer.Sparse Key := [(key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2229, 2), (key2055, 2), (key2055, 2), (key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2), (key2145, -1), (key2145, -1), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2134, 2), (key2019, 2), (key2019, 2), (key2134, -1), (key2134, -1), (key2047, -1), (key2047, -1), (key2019, -1), (key2019, -1)]

def rawRow17166 : Integer.Sparse Key := [(key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2042, 2), (key2042, 2), (key2042, 2), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2047, 2), (key2047, 2), (key2047, 2), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1)]

def rawRow17167 : Integer.Sparse Key := [(key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2056, 2), (key2056, 2), (key2228, 2), (key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2), (key2026, -1), (key2055, -1), (key2026, -1), (key2144, -1), (key2055, -1), (key2144, -1), (key2013, 2), (key2013, 2), (key2127, 2), (key2013, -1), (key2042, -1), (key2013, -1), (key2127, -1), (key2042, -1), (key2127, -1)]

def rawRow17168 : Integer.Sparse Key := [(key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2056, 2), (key2228, 2), (key2056, 2), (key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2055, -1), (key2026, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2055, -1), (key2013, 2), (key2127, 2), (key2013, 2), (key2042, -1), (key2013, -1), (key2127, -1), (key2013, -1), (key2127, -1), (key2042, -1)]

def rawRow17169 : Integer.Sparse Key := [(key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2228, 2), (key2056, 2), (key2056, 2), (key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2), (key2144, -1), (key2144, -1), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2127, 2), (key2013, 2), (key2013, 2), (key2127, -1), (key2127, -1), (key2042, -1), (key2042, -1), (key2013, -1), (key2013, -1)]

def rawRow17170 : Integer.Sparse Key := [(key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2047, 2), (key2047, 2), (key2047, 2), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2042, 2), (key2042, 2), (key2042, 2), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1)]

def rawRow17171 : Integer.Sparse Key := [(key2103, 4), (key2108, 4), (key2109, 4), (key2108, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2131, 12)]

def rawRow17172 : Integer.Sparse Key := [(key2103, 4), (key2109, 4), (key2108, 4), (key2109, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2131, 12)]

def rawRow17173 : Integer.Sparse Key := [(key2108, 4), (key2103, 4), (key2109, 4), (key2108, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2131, 12)]

def rawRow17174 : Integer.Sparse Key := [(key2108, 4), (key2109, 4), (key2103, 4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, 12)]

def rawRow17175 : Integer.Sparse Key := [(key2109, 4), (key2103, 4), (key2108, 4), (key2109, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2131, 12)]

def rawRow17176 : Integer.Sparse Key := [(key2109, 4), (key2108, 4), (key2103, 4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, 12)]

def rawRow17177 : Integer.Sparse Key := [(key2108, 4), (key2108, 4), (key2131, 4), (key2103, -4), (key2109, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2131, -4), (key2109, 12)]

def rawRow17178 : Integer.Sparse Key := [(key2108, 4), (key2131, 4), (key2108, 4), (key2109, -4), (key2103, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2131, -4), (key2109, 12)]

def rawRow17179 : Integer.Sparse Key := [(key2131, 4), (key2108, 4), (key2108, 4), (key2109, -4), (key2109, -4), (key2103, -4), (key2131, -4), (key2131, -4), (key2108, -4), (key2109, 12)]

def rawRow17180 : Integer.Sparse Key := [(key2109, 4), (key2109, 4), (key2131, 4), (key2103, -4), (key2108, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2131, -4), (key2108, 12)]

def rawRow17181 : Integer.Sparse Key := [(key2109, 4), (key2131, 4), (key2109, 4), (key2108, -4), (key2103, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2131, -4), (key2108, 12)]

def rawRow17182 : Integer.Sparse Key := [(key2131, 4), (key2109, 4), (key2109, 4), (key2108, -4), (key2108, -4), (key2103, -4), (key2131, -4), (key2131, -4), (key2109, -4), (key2108, 12)]

def rawRow17183 : Integer.Sparse Key := [(key2108, 4), (key2108, 4), (key2131, 4), (key2108, -4), (key2131, -4), (key2131, -4), (key2103, -4), (key2109, -4), (key2109, -4), (key2109, 12)]

def rawRow17184 : Integer.Sparse Key := [(key2108, 4), (key2131, 4), (key2108, 4), (key2131, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2103, -4), (key2109, -4), (key2109, 12)]

def rawRow17185 : Integer.Sparse Key := [(key2131, 4), (key2108, 4), (key2108, 4), (key2131, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2109, -4), (key2103, -4), (key2109, 12)]

def rawRow17186 : Integer.Sparse Key := [(key2131, 4), (key2131, 4), (key2131, 4), (key2108, -4), (key2108, -4), (key2108, -4), (key2109, -4), (key2109, -4), (key2109, -4), (key2103, 12)]

def rawRow17187 : Integer.Sparse Key := [(key2109, 4), (key2109, 4), (key2131, 4), (key2109, -4), (key2131, -4), (key2131, -4), (key2103, -4), (key2108, -4), (key2108, -4), (key2108, 12)]

def rawRow17188 : Integer.Sparse Key := [(key2109, 4), (key2131, 4), (key2109, 4), (key2131, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2103, -4), (key2108, -4), (key2108, 12)]

def rawRow17189 : Integer.Sparse Key := [(key2131, 4), (key2109, 4), (key2109, 4), (key2131, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2108, -4), (key2103, -4), (key2108, 12)]

def rawRow17190 : Integer.Sparse Key := [(key2131, 4), (key2131, 4), (key2131, 4), (key2109, -4), (key2109, -4), (key2109, -4), (key2108, -4), (key2108, -4), (key2108, -4), (key2103, 12)]

def rawRow17191 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, -2), (key1982, 6), (key1974, -2), (key1977, -2), (key1982, -2), (key1974, 2), (key1977, 2), (key2210, 2), (key2214, 2), (key2219, 2), (key2223, 2), (key1982, -2), (key2219, -2), (key2223, -2), (key1982, 6), (key1982, -2), (key2219, -2), (key2223, -2)]

def rawRow17192 : Integer.Sparse Key := [(key1977, -2), (key1974, -2), (key1982, -2), (key1982, 6), (key1977, -2), (key1974, -2), (key1982, -2), (key1977, 2), (key1974, 2), (key2214, 2), (key2210, 2), (key2223, 2), (key2219, 2), (key1982, -2), (key2223, -2), (key2219, -2), (key1982, 6), (key1982, -2), (key2223, -2), (key2219, -2)]

def rawRow17193 : Integer.Sparse Key := [(key1974, -2), (key1982, -2), (key1977, -2), (key1982, 6), (key1974, -2), (key1982, -2), (key1977, -2), (key2210, 2), (key2219, 2), (key1974, 2), (key2223, 2), (key1977, 2), (key2214, 2), (key2219, -2), (key1982, -2), (key2223, -2), (key1982, 6), (key2219, -2), (key1982, -2), (key2223, -2)]

def rawRow17194 : Integer.Sparse Key := [(key1982, -2), (key1974, -2), (key1977, -2), (key1982, 6), (key1982, -2), (key1974, -2), (key1977, -2), (key2219, 2), (key2210, 2), (key2223, 2), (key1974, 2), (key2214, 2), (key1977, 2), (key2219, -2), (key2223, -2), (key1982, -2), (key1982, 6), (key2219, -2), (key2223, -2), (key1982, -2)]

def rawRow17195 : Integer.Sparse Key := [(key1977, -2), (key1982, -2), (key1974, -2), (key1982, 6), (key1977, -2), (key1982, -2), (key1974, -2), (key2214, 2), (key2223, 2), (key1977, 2), (key2219, 2), (key1974, 2), (key2210, 2), (key2223, -2), (key1982, -2), (key2219, -2), (key1982, 6), (key2223, -2), (key1982, -2), (key2219, -2)]

def rawRow17196 : Integer.Sparse Key := [(key1982, -2), (key1977, -2), (key1974, -2), (key1982, 6), (key1982, -2), (key1977, -2), (key1974, -2), (key2223, 2), (key2214, 2), (key2219, 2), (key1977, 2), (key2210, 2), (key1974, 2), (key2223, -2), (key2219, -2), (key1982, -2), (key1982, 6), (key2223, -2), (key2219, -2), (key1982, -2)]

def rawRow17197 : Integer.Sparse Key := [(key1974, -2), (key1982, -2), (key1982, -2), (key1977, 6), (key2210, -2), (key2219, -2), (key2219, -2), (key1974, 2), (key1982, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key2223, 2), (key1977, -2), (key1977, -2), (key2214, -2), (key2219, 6), (key1982, -2), (key1982, -2), (key2223, -2)]

def rawRow17198 : Integer.Sparse Key := [(key1982, -2), (key1974, -2), (key1982, -2), (key1977, 6), (key2219, -2), (key2210, -2), (key2219, -2), (key1982, 2), (key1974, 2), (key2223, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key1977, -2), (key2214, -2), (key1977, -2), (key2219, 6), (key1982, -2), (key2223, -2), (key1982, -2)]

def rawRow17199 : Integer.Sparse Key := [(key1982, -2), (key1982, -2), (key1974, -2), (key1977, 6), (key2219, -2), (key2219, -2), (key2210, -2), (key2223, 2), (key2223, 2), (key1982, 2), (key1982, 2), (key1974, 2), (key1974, 2), (key2214, -2), (key1977, -2), (key1977, -2), (key2219, 6), (key2223, -2), (key1982, -2), (key1982, -2)]

def rawRow17200 : Integer.Sparse Key := [(key1977, -2), (key1982, -2), (key1982, -2), (key1974, 6), (key2214, -2), (key2223, -2), (key2223, -2), (key1977, 2), (key1982, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key2219, 2), (key1974, -2), (key1974, -2), (key2210, -2), (key2223, 6), (key1982, -2), (key1982, -2), (key2219, -2)]

def rawRow17201 : Integer.Sparse Key := [(key1982, -2), (key1977, -2), (key1982, -2), (key1974, 6), (key2223, -2), (key2214, -2), (key2223, -2), (key1982, 2), (key1977, 2), (key2219, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key1974, -2), (key2210, -2), (key1974, -2), (key2223, 6), (key1982, -2), (key2219, -2), (key1982, -2)]

def rawRow17202 : Integer.Sparse Key := [(key1982, -2), (key1982, -2), (key1977, -2), (key1974, 6), (key2223, -2), (key2223, -2), (key2214, -2), (key2219, 2), (key2219, 2), (key1982, 2), (key1982, 2), (key1977, 2), (key1977, 2), (key2210, -2), (key1974, -2), (key1974, -2), (key2223, 6), (key2219, -2), (key1982, -2), (key1982, -2)]

def rawRow17203 : Integer.Sparse Key := [(key2210, -2), (key2219, -2), (key2219, -2), (key2219, 6), (key1974, -2), (key1982, -2), (key1982, -2), (key1974, 2), (key1982, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key2223, 2), (key1982, -2), (key1982, -2), (key2223, -2), (key1977, 6), (key1977, -2), (key1977, -2), (key2214, -2)]

def rawRow17204 : Integer.Sparse Key := [(key2219, -2), (key2210, -2), (key2219, -2), (key2219, 6), (key1982, -2), (key1974, -2), (key1982, -2), (key1982, 2), (key1974, 2), (key2223, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key1982, -2), (key2223, -2), (key1982, -2), (key1977, 6), (key1977, -2), (key2214, -2), (key1977, -2)]

def rawRow17205 : Integer.Sparse Key := [(key2219, -2), (key2219, -2), (key2210, -2), (key2219, 6), (key1982, -2), (key1982, -2), (key1974, -2), (key2223, 2), (key2223, 2), (key1982, 2), (key1982, 2), (key1974, 2), (key1974, 2), (key2223, -2), (key1982, -2), (key1982, -2), (key1977, 6), (key2214, -2), (key1977, -2), (key1977, -2)]

def rawRow17206 : Integer.Sparse Key := [(key2219, -2), (key2219, -2), (key2219, -2), (key2210, 6), (key2223, -2), (key2223, -2), (key2223, -2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1974, -2), (key1974, -2), (key1974, -2), (key2214, 6), (key1977, -2), (key1977, -2), (key1977, -2)]

def rawRow17207 : Integer.Sparse Key := [(key2214, -2), (key2223, -2), (key2223, -2), (key2223, 6), (key1977, -2), (key1982, -2), (key1982, -2), (key1977, 2), (key1982, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key2219, 2), (key1982, -2), (key1982, -2), (key2219, -2), (key1974, 6), (key1974, -2), (key1974, -2), (key2210, -2)]

def rawRow17208 : Integer.Sparse Key := [(key2223, -2), (key2214, -2), (key2223, -2), (key2223, 6), (key1982, -2), (key1977, -2), (key1982, -2), (key1982, 2), (key1977, 2), (key2219, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key1982, -2), (key2219, -2), (key1982, -2), (key1974, 6), (key1974, -2), (key2210, -2), (key1974, -2)]

def rawRow17209 : Integer.Sparse Key := [(key2223, -2), (key2223, -2), (key2214, -2), (key2223, 6), (key1982, -2), (key1982, -2), (key1977, -2), (key2219, 2), (key2219, 2), (key1982, 2), (key1982, 2), (key1977, 2), (key1977, 2), (key2219, -2), (key1982, -2), (key1982, -2), (key1974, 6), (key2210, -2), (key1974, -2), (key1974, -2)]

def rawRow17210 : Integer.Sparse Key := [(key2223, -2), (key2223, -2), (key2223, -2), (key2214, 6), (key2219, -2), (key2219, -2), (key2219, -2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1977, -2), (key1977, -2), (key1977, -2), (key2210, 6), (key1974, -2), (key1974, -2), (key1974, -2)]

def rawRow17211 : Integer.Sparse Key := [(key758, 4), (key762, 4), (key764, 4), (key762, -4), (key764, -4), (key789, -4), (key762, -4), (key764, -4), (key789, -4), (key789, 12)]

def rawRow17212 : Integer.Sparse Key := [(key758, 4), (key764, 4), (key762, 4), (key764, -4), (key762, -4), (key789, -4), (key764, -4), (key762, -4), (key789, -4), (key789, 12)]

def rawRow17213 : Integer.Sparse Key := [(key762, 4), (key758, 4), (key764, 4), (key762, -4), (key789, -4), (key764, -4), (key762, -4), (key789, -4), (key764, -4), (key789, 12)]

def rawRow17214 : Integer.Sparse Key := [(key762, 4), (key764, 4), (key758, 4), (key789, -4), (key762, -4), (key764, -4), (key789, -4), (key762, -4), (key764, -4), (key789, 12)]

def rawRow17215 : Integer.Sparse Key := [(key764, 4), (key758, 4), (key762, 4), (key764, -4), (key789, -4), (key762, -4), (key764, -4), (key789, -4), (key762, -4), (key789, 12)]

def rawRow17216 : Integer.Sparse Key := [(key764, 4), (key762, 4), (key758, 4), (key789, -4), (key764, -4), (key762, -4), (key789, -4), (key764, -4), (key762, -4), (key789, 12)]

def rawRow17217 : Integer.Sparse Key := [(key762, 4), (key762, 4), (key789, 4), (key758, -4), (key764, -4), (key764, -4), (key762, -4), (key789, -4), (key789, -4), (key764, 12)]

def rawRow17218 : Integer.Sparse Key := [(key762, 4), (key789, 4), (key762, 4), (key764, -4), (key758, -4), (key764, -4), (key789, -4), (key762, -4), (key789, -4), (key764, 12)]

def rawRow17219 : Integer.Sparse Key := [(key789, 4), (key762, 4), (key762, 4), (key764, -4), (key764, -4), (key758, -4), (key789, -4), (key789, -4), (key762, -4), (key764, 12)]

def rawRow17220 : Integer.Sparse Key := [(key764, 4), (key764, 4), (key789, 4), (key758, -4), (key762, -4), (key762, -4), (key764, -4), (key789, -4), (key789, -4), (key762, 12)]

def rawRow17221 : Integer.Sparse Key := [(key764, 4), (key789, 4), (key764, 4), (key762, -4), (key758, -4), (key762, -4), (key789, -4), (key764, -4), (key789, -4), (key762, 12)]

def rawRow17222 : Integer.Sparse Key := [(key789, 4), (key764, 4), (key764, 4), (key762, -4), (key762, -4), (key758, -4), (key789, -4), (key789, -4), (key764, -4), (key762, 12)]

def rawRow17223 : Integer.Sparse Key := [(key762, 4), (key762, 4), (key789, 4), (key762, -4), (key789, -4), (key789, -4), (key758, -4), (key764, -4), (key764, -4), (key764, 12)]

def rawRow17224 : Integer.Sparse Key := [(key762, 4), (key789, 4), (key762, 4), (key789, -4), (key762, -4), (key789, -4), (key764, -4), (key758, -4), (key764, -4), (key764, 12)]

def rawRow17225 : Integer.Sparse Key := [(key789, 4), (key762, 4), (key762, 4), (key789, -4), (key789, -4), (key762, -4), (key764, -4), (key764, -4), (key758, -4), (key764, 12)]

def rawRow17226 : Integer.Sparse Key := [(key789, 4), (key789, 4), (key789, 4), (key762, -4), (key762, -4), (key762, -4), (key764, -4), (key764, -4), (key764, -4), (key758, 12)]

def rawRow17227 : Integer.Sparse Key := [(key764, 4), (key764, 4), (key789, 4), (key764, -4), (key789, -4), (key789, -4), (key758, -4), (key762, -4), (key762, -4), (key762, 12)]

def rawRow17228 : Integer.Sparse Key := [(key764, 4), (key789, 4), (key764, 4), (key789, -4), (key764, -4), (key789, -4), (key762, -4), (key758, -4), (key762, -4), (key762, 12)]

def rawRow17229 : Integer.Sparse Key := [(key789, 4), (key764, 4), (key764, 4), (key789, -4), (key789, -4), (key764, -4), (key762, -4), (key762, -4), (key758, -4), (key762, 12)]

def rawRow17230 : Integer.Sparse Key := [(key789, 4), (key789, 4), (key789, 4), (key764, -4), (key764, -4), (key764, -4), (key762, -4), (key762, -4), (key762, -4), (key758, 12)]

def rawRow17231 : Integer.Sparse Key := [(key2014, -1), (key2018, -1), (key2128, -1), (key2133, -1), (key2138, -1), (key2141, -1), (key2023, 2), (key2138, 2), (key2141, 2), (key2014, -1), (key2018, -1), (key2128, -1), (key2133, -1), (key2138, -1), (key2141, -1), (key2043, 2), (key2046, 2), (key2128, 2), (key2133, 2), (key2221, 2), (key2222, 2), (key2051, -1), (key2052, -1), (key2138, -1), (key2141, -1), (key2221, -1), (key2222, -1), (key2023, 2), (key2138, 2), (key2141, 2), (key2051, -1), (key2052, -1), (key2138, -1), (key2141, -1), (key2221, -1), (key2222, -1)]

def rawRow17232 : Integer.Sparse Key := [(key2018, -1), (key2014, -1), (key2133, -1), (key2128, -1), (key2141, -1), (key2138, -1), (key2023, 2), (key2141, 2), (key2138, 2), (key2018, -1), (key2014, -1), (key2133, -1), (key2128, -1), (key2141, -1), (key2138, -1), (key2046, 2), (key2043, 2), (key2133, 2), (key2128, 2), (key2222, 2), (key2221, 2), (key2052, -1), (key2051, -1), (key2141, -1), (key2138, -1), (key2222, -1), (key2221, -1), (key2023, 2), (key2141, 2), (key2138, 2), (key2052, -1), (key2051, -1), (key2141, -1), (key2138, -1), (key2222, -1), (key2221, -1)]

def rawRow17233 : Integer.Sparse Key := [(key2128, -1), (key2138, -1), (key2014, -1), (key2141, -1), (key2018, -1), (key2133, -1), (key2138, 2), (key2023, 2), (key2141, 2), (key2128, -1), (key2138, -1), (key2014, -1), (key2141, -1), (key2018, -1), (key2133, -1), (key2128, 2), (key2221, 2), (key2043, 2), (key2222, 2), (key2046, 2), (key2133, 2), (key2138, -1), (key2221, -1), (key2051, -1), (key2222, -1), (key2052, -1), (key2141, -1), (key2138, 2), (key2023, 2), (key2141, 2), (key2138, -1), (key2221, -1), (key2051, -1), (key2222, -1), (key2052, -1), (key2141, -1)]

def rawRow17234 : Integer.Sparse Key := [(key2138, -1), (key2128, -1), (key2141, -1), (key2014, -1), (key2133, -1), (key2018, -1), (key2138, 2), (key2141, 2), (key2023, 2), (key2138, -1), (key2128, -1), (key2141, -1), (key2014, -1), (key2133, -1), (key2018, -1), (key2221, 2), (key2128, 2), (key2222, 2), (key2043, 2), (key2133, 2), (key2046, 2), (key2221, -1), (key2138, -1), (key2222, -1), (key2051, -1), (key2141, -1), (key2052, -1), (key2138, 2), (key2141, 2), (key2023, 2), (key2221, -1), (key2138, -1), (key2222, -1), (key2051, -1), (key2141, -1), (key2052, -1)]

def rawRow17235 : Integer.Sparse Key := [(key2133, -1), (key2141, -1), (key2018, -1), (key2138, -1), (key2014, -1), (key2128, -1), (key2141, 2), (key2023, 2), (key2138, 2), (key2133, -1), (key2141, -1), (key2018, -1), (key2138, -1), (key2014, -1), (key2128, -1), (key2133, 2), (key2222, 2), (key2046, 2), (key2221, 2), (key2043, 2), (key2128, 2), (key2141, -1), (key2222, -1), (key2052, -1), (key2221, -1), (key2051, -1), (key2138, -1), (key2141, 2), (key2023, 2), (key2138, 2), (key2141, -1), (key2222, -1), (key2052, -1), (key2221, -1), (key2051, -1), (key2138, -1)]

def rawRow17236 : Integer.Sparse Key := [(key2141, -1), (key2133, -1), (key2138, -1), (key2018, -1), (key2128, -1), (key2014, -1), (key2141, 2), (key2138, 2), (key2023, 2), (key2141, -1), (key2133, -1), (key2138, -1), (key2018, -1), (key2128, -1), (key2014, -1), (key2222, 2), (key2133, 2), (key2221, 2), (key2046, 2), (key2128, 2), (key2043, 2), (key2222, -1), (key2141, -1), (key2221, -1), (key2052, -1), (key2138, -1), (key2051, -1), (key2141, 2), (key2138, 2), (key2023, 2), (key2222, -1), (key2141, -1), (key2221, -1), (key2052, -1), (key2138, -1), (key2051, -1)]

def rawRow17237 : Integer.Sparse Key := [(key2014, -1), (key2023, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2018, 2), (key2018, 2), (key2133, 2), (key2043, -1), (key2051, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2222, -1), (key2014, 2), (key2052, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2141, 2), (key2018, -1), (key2046, -1), (key2018, -1), (key2133, -1), (key2046, -1), (key2133, -1), (key2051, 2), (key2051, 2), (key2222, 2), (key2023, -1), (key2052, -1), (key2023, -1), (key2141, -1), (key2052, -1), (key2141, -1)]

def rawRow17238 : Integer.Sparse Key := [(key2023, -1), (key2014, -1), (key2141, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2018, 2), (key2133, 2), (key2018, 2), (key2051, -1), (key2043, -1), (key2222, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2052, 2), (key2014, 2), (key2141, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2046, -1), (key2018, -1), (key2133, -1), (key2018, -1), (key2133, -1), (key2046, -1), (key2051, 2), (key2222, 2), (key2051, 2), (key2052, -1), (key2023, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2052, -1)]

def rawRow17239 : Integer.Sparse Key := [(key2141, -1), (key2141, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2133, 2), (key2018, 2), (key2018, 2), (key2222, -1), (key2222, -1), (key2051, -1), (key2051, -1), (key2043, -1), (key2043, -1), (key2141, 2), (key2141, 2), (key2052, 2), (key2052, 2), (key2014, 2), (key2014, 2), (key2133, -1), (key2133, -1), (key2046, -1), (key2046, -1), (key2018, -1), (key2018, -1), (key2222, 2), (key2051, 2), (key2051, 2), (key2141, -1), (key2141, -1), (key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1)]

def rawRow17240 : Integer.Sparse Key := [(key2018, -1), (key2023, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2014, 2), (key2014, 2), (key2128, 2), (key2046, -1), (key2052, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2221, -1), (key2018, 2), (key2051, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2138, 2), (key2014, -1), (key2043, -1), (key2014, -1), (key2128, -1), (key2043, -1), (key2128, -1), (key2052, 2), (key2052, 2), (key2221, 2), (key2023, -1), (key2051, -1), (key2023, -1), (key2138, -1), (key2051, -1), (key2138, -1)]

def rawRow17241 : Integer.Sparse Key := [(key2023, -1), (key2018, -1), (key2138, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2014, 2), (key2128, 2), (key2014, 2), (key2052, -1), (key2046, -1), (key2221, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2051, 2), (key2018, 2), (key2138, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2043, -1), (key2014, -1), (key2128, -1), (key2014, -1), (key2128, -1), (key2043, -1), (key2052, 2), (key2221, 2), (key2052, 2), (key2051, -1), (key2023, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2051, -1)]

def rawRow17242 : Integer.Sparse Key := [(key2138, -1), (key2138, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2128, 2), (key2014, 2), (key2014, 2), (key2221, -1), (key2221, -1), (key2052, -1), (key2052, -1), (key2046, -1), (key2046, -1), (key2138, 2), (key2138, 2), (key2051, 2), (key2051, 2), (key2018, 2), (key2018, 2), (key2128, -1), (key2128, -1), (key2043, -1), (key2043, -1), (key2014, -1), (key2014, -1), (key2221, 2), (key2052, 2), (key2052, 2), (key2138, -1), (key2138, -1), (key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1)]

def rawRow17243 : Integer.Sparse Key := [(key2043, -1), (key2051, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2222, -1), (key2051, 2), (key2051, 2), (key2222, 2), (key2014, -1), (key2023, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2014, 2), (key2052, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2141, 2), (key2023, -1), (key2052, -1), (key2023, -1), (key2141, -1), (key2052, -1), (key2141, -1), (key2018, 2), (key2018, 2), (key2133, 2), (key2018, -1), (key2046, -1), (key2018, -1), (key2133, -1), (key2046, -1), (key2133, -1)]

def rawRow17244 : Integer.Sparse Key := [(key2051, -1), (key2043, -1), (key2222, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2051, 2), (key2222, 2), (key2051, 2), (key2023, -1), (key2014, -1), (key2141, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2052, 2), (key2014, 2), (key2141, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2052, -1), (key2023, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2052, -1), (key2018, 2), (key2133, 2), (key2018, 2), (key2046, -1), (key2018, -1), (key2133, -1), (key2018, -1), (key2133, -1), (key2046, -1)]

def rawRow17245 : Integer.Sparse Key := [(key2222, -1), (key2222, -1), (key2051, -1), (key2051, -1), (key2043, -1), (key2043, -1), (key2222, 2), (key2051, 2), (key2051, 2), (key2141, -1), (key2141, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2141, 2), (key2141, 2), (key2052, 2), (key2052, 2), (key2014, 2), (key2014, 2), (key2141, -1), (key2141, -1), (key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1), (key2133, 2), (key2018, 2), (key2018, 2), (key2133, -1), (key2133, -1), (key2046, -1), (key2046, -1), (key2018, -1), (key2018, -1)]

def rawRow17246 : Integer.Sparse Key := [(key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2043, 2), (key2043, 2), (key2043, 2), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2046, 2), (key2046, 2), (key2046, 2), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1)]

def rawRow17247 : Integer.Sparse Key := [(key2046, -1), (key2052, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2221, -1), (key2052, 2), (key2052, 2), (key2221, 2), (key2018, -1), (key2023, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2018, 2), (key2051, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2138, 2), (key2023, -1), (key2051, -1), (key2023, -1), (key2138, -1), (key2051, -1), (key2138, -1), (key2014, 2), (key2014, 2), (key2128, 2), (key2014, -1), (key2043, -1), (key2014, -1), (key2128, -1), (key2043, -1), (key2128, -1)]

def rawRow17248 : Integer.Sparse Key := [(key2052, -1), (key2046, -1), (key2221, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2052, 2), (key2221, 2), (key2052, 2), (key2023, -1), (key2018, -1), (key2138, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2051, 2), (key2018, 2), (key2138, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2051, -1), (key2023, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2051, -1), (key2014, 2), (key2128, 2), (key2014, 2), (key2043, -1), (key2014, -1), (key2128, -1), (key2014, -1), (key2128, -1), (key2043, -1)]

def rawRow17249 : Integer.Sparse Key := [(key2221, -1), (key2221, -1), (key2052, -1), (key2052, -1), (key2046, -1), (key2046, -1), (key2221, 2), (key2052, 2), (key2052, 2), (key2138, -1), (key2138, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2138, 2), (key2138, 2), (key2051, 2), (key2051, 2), (key2018, 2), (key2018, 2), (key2138, -1), (key2138, -1), (key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1), (key2128, 2), (key2014, 2), (key2014, 2), (key2128, -1), (key2128, -1), (key2043, -1), (key2043, -1), (key2014, -1), (key2014, -1)]

def rawRow17250 : Integer.Sparse Key := [(key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2046, 2), (key2046, 2), (key2046, 2), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2043, 2), (key2043, 2), (key2043, 2), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1)]

def rawRow17251 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, -2), (key365, 6), (key357, -2), (key359, -2), (key365, -2), (key357, 2), (key359, 2), (key527, 2), (key674, 2), (key535, 2), (key675, 2), (key365, -2), (key535, -2), (key675, -2), (key365, 6), (key365, -2), (key535, -2), (key675, -2)]

def rawRow17252 : Integer.Sparse Key := [(key359, -2), (key357, -2), (key365, -2), (key365, 6), (key359, -2), (key357, -2), (key365, -2), (key359, 2), (key357, 2), (key674, 2), (key527, 2), (key675, 2), (key535, 2), (key365, -2), (key675, -2), (key535, -2), (key365, 6), (key365, -2), (key675, -2), (key535, -2)]

def rawRow17253 : Integer.Sparse Key := [(key357, -2), (key365, -2), (key359, -2), (key365, 6), (key357, -2), (key365, -2), (key359, -2), (key527, 2), (key535, 2), (key357, 2), (key675, 2), (key359, 2), (key674, 2), (key535, -2), (key365, -2), (key675, -2), (key365, 6), (key535, -2), (key365, -2), (key675, -2)]

def rawRow17254 : Integer.Sparse Key := [(key365, -2), (key357, -2), (key359, -2), (key365, 6), (key365, -2), (key357, -2), (key359, -2), (key535, 2), (key527, 2), (key675, 2), (key357, 2), (key674, 2), (key359, 2), (key535, -2), (key675, -2), (key365, -2), (key365, 6), (key535, -2), (key675, -2), (key365, -2)]

def rawRow17255 : Integer.Sparse Key := [(key359, -2), (key365, -2), (key357, -2), (key365, 6), (key359, -2), (key365, -2), (key357, -2), (key674, 2), (key675, 2), (key359, 2), (key535, 2), (key357, 2), (key527, 2), (key675, -2), (key365, -2), (key535, -2), (key365, 6), (key675, -2), (key365, -2), (key535, -2)]

def rawRow17256 : Integer.Sparse Key := [(key365, -2), (key359, -2), (key357, -2), (key365, 6), (key365, -2), (key359, -2), (key357, -2), (key675, 2), (key674, 2), (key535, 2), (key359, 2), (key527, 2), (key357, 2), (key675, -2), (key535, -2), (key365, -2), (key365, 6), (key675, -2), (key535, -2), (key365, -2)]

def rawRow17257 : Integer.Sparse Key := [(key357, -2), (key365, -2), (key365, -2), (key359, 6), (key527, -2), (key535, -2), (key535, -2), (key357, 2), (key365, 2), (key357, 2), (key675, 2), (key365, 2), (key675, 2), (key359, -2), (key359, -2), (key674, -2), (key535, 6), (key365, -2), (key365, -2), (key675, -2)]

def rawRow17258 : Integer.Sparse Key := [(key365, -2), (key357, -2), (key365, -2), (key359, 6), (key535, -2), (key527, -2), (key535, -2), (key365, 2), (key357, 2), (key675, 2), (key357, 2), (key675, 2), (key365, 2), (key359, -2), (key674, -2), (key359, -2), (key535, 6), (key365, -2), (key675, -2), (key365, -2)]

def rawRow17259 : Integer.Sparse Key := [(key365, -2), (key365, -2), (key357, -2), (key359, 6), (key535, -2), (key535, -2), (key527, -2), (key675, 2), (key675, 2), (key365, 2), (key365, 2), (key357, 2), (key357, 2), (key674, -2), (key359, -2), (key359, -2), (key535, 6), (key675, -2), (key365, -2), (key365, -2)]

def rawRow17260 : Integer.Sparse Key := [(key359, -2), (key365, -2), (key365, -2), (key357, 6), (key674, -2), (key675, -2), (key675, -2), (key359, 2), (key365, 2), (key359, 2), (key535, 2), (key365, 2), (key535, 2), (key357, -2), (key357, -2), (key527, -2), (key675, 6), (key365, -2), (key365, -2), (key535, -2)]

def rawRow17261 : Integer.Sparse Key := [(key365, -2), (key359, -2), (key365, -2), (key357, 6), (key675, -2), (key674, -2), (key675, -2), (key365, 2), (key359, 2), (key535, 2), (key359, 2), (key535, 2), (key365, 2), (key357, -2), (key527, -2), (key357, -2), (key675, 6), (key365, -2), (key535, -2), (key365, -2)]

def rawRow17262 : Integer.Sparse Key := [(key365, -2), (key365, -2), (key359, -2), (key357, 6), (key675, -2), (key675, -2), (key674, -2), (key535, 2), (key535, 2), (key365, 2), (key365, 2), (key359, 2), (key359, 2), (key527, -2), (key357, -2), (key357, -2), (key675, 6), (key535, -2), (key365, -2), (key365, -2)]

def rawRow17263 : Integer.Sparse Key := [(key527, -2), (key535, -2), (key535, -2), (key535, 6), (key357, -2), (key365, -2), (key365, -2), (key357, 2), (key365, 2), (key357, 2), (key675, 2), (key365, 2), (key675, 2), (key365, -2), (key365, -2), (key675, -2), (key359, 6), (key359, -2), (key359, -2), (key674, -2)]

def rawRow17264 : Integer.Sparse Key := [(key535, -2), (key527, -2), (key535, -2), (key535, 6), (key365, -2), (key357, -2), (key365, -2), (key365, 2), (key357, 2), (key675, 2), (key357, 2), (key675, 2), (key365, 2), (key365, -2), (key675, -2), (key365, -2), (key359, 6), (key359, -2), (key674, -2), (key359, -2)]

def rawRow17265 : Integer.Sparse Key := [(key535, -2), (key535, -2), (key527, -2), (key535, 6), (key365, -2), (key365, -2), (key357, -2), (key675, 2), (key675, 2), (key365, 2), (key365, 2), (key357, 2), (key357, 2), (key675, -2), (key365, -2), (key365, -2), (key359, 6), (key674, -2), (key359, -2), (key359, -2)]

def rawRow17266 : Integer.Sparse Key := [(key535, -2), (key535, -2), (key535, -2), (key527, 6), (key675, -2), (key675, -2), (key675, -2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key357, -2), (key357, -2), (key357, -2), (key674, 6), (key359, -2), (key359, -2), (key359, -2)]

def rawRow17267 : Integer.Sparse Key := [(key674, -2), (key675, -2), (key675, -2), (key675, 6), (key359, -2), (key365, -2), (key365, -2), (key359, 2), (key365, 2), (key359, 2), (key535, 2), (key365, 2), (key535, 2), (key365, -2), (key365, -2), (key535, -2), (key357, 6), (key357, -2), (key357, -2), (key527, -2)]

def rawRow17268 : Integer.Sparse Key := [(key675, -2), (key674, -2), (key675, -2), (key675, 6), (key365, -2), (key359, -2), (key365, -2), (key365, 2), (key359, 2), (key535, 2), (key359, 2), (key535, 2), (key365, 2), (key365, -2), (key535, -2), (key365, -2), (key357, 6), (key357, -2), (key527, -2), (key357, -2)]

def rawRow17269 : Integer.Sparse Key := [(key675, -2), (key675, -2), (key674, -2), (key675, 6), (key365, -2), (key365, -2), (key359, -2), (key535, 2), (key535, 2), (key365, 2), (key365, 2), (key359, 2), (key359, 2), (key535, -2), (key365, -2), (key365, -2), (key357, 6), (key527, -2), (key357, -2), (key357, -2)]

def rawRow17270 : Integer.Sparse Key := [(key675, -2), (key675, -2), (key675, -2), (key674, 6), (key535, -2), (key535, -2), (key535, -2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key359, -2), (key359, -2), (key359, -2), (key527, 6), (key357, -2), (key357, -2), (key357, -2)]

def rawRow17271 : Integer.Sparse Key := [(key1976, 2), (key1981, 2), (key1983, 2), (key1981, -2), (key1983, -2), (key1997, -2), (key1976, 2), (key1981, 2), (key1983, 2), (key1981, -1), (key1983, -1), (key2218, -1), (key2224, -1), (key2262, -1), (key2266, -1), (key1981, -2), (key1983, -2), (key1997, -2), (key1981, -1), (key1983, -1), (key2218, -1), (key2224, -1), (key2262, -1), (key2266, -1), (key1997, 4), (key2262, 4), (key2266, 4)]

def rawRow17272 : Integer.Sparse Key := [(key1976, 2), (key1983, 2), (key1981, 2), (key1983, -2), (key1981, -2), (key1997, -2), (key1976, 2), (key1983, 2), (key1981, 2), (key1983, -1), (key1981, -1), (key2224, -1), (key2218, -1), (key2266, -1), (key2262, -1), (key1983, -2), (key1981, -2), (key1997, -2), (key1983, -1), (key1981, -1), (key2224, -1), (key2218, -1), (key2266, -1), (key2262, -1), (key1997, 4), (key2266, 4), (key2262, 4)]

def rawRow17273 : Integer.Sparse Key := [(key1981, 2), (key1976, 2), (key1983, 2), (key1981, -2), (key1997, -2), (key1983, -2), (key1981, 2), (key1976, 2), (key1983, 2), (key2218, -1), (key2262, -1), (key1981, -1), (key2266, -1), (key1983, -1), (key2224, -1), (key1981, -2), (key1997, -2), (key1983, -2), (key2218, -1), (key2262, -1), (key1981, -1), (key2266, -1), (key1983, -1), (key2224, -1), (key2262, 4), (key1997, 4), (key2266, 4)]

def rawRow17274 : Integer.Sparse Key := [(key1981, 2), (key1983, 2), (key1976, 2), (key1997, -2), (key1981, -2), (key1983, -2), (key1981, 2), (key1983, 2), (key1976, 2), (key2262, -1), (key2218, -1), (key2266, -1), (key1981, -1), (key2224, -1), (key1983, -1), (key1997, -2), (key1981, -2), (key1983, -2), (key2262, -1), (key2218, -1), (key2266, -1), (key1981, -1), (key2224, -1), (key1983, -1), (key2262, 4), (key2266, 4), (key1997, 4)]

def rawRow17275 : Integer.Sparse Key := [(key1983, 2), (key1976, 2), (key1981, 2), (key1983, -2), (key1997, -2), (key1981, -2), (key1983, 2), (key1976, 2), (key1981, 2), (key2224, -1), (key2266, -1), (key1983, -1), (key2262, -1), (key1981, -1), (key2218, -1), (key1983, -2), (key1997, -2), (key1981, -2), (key2224, -1), (key2266, -1), (key1983, -1), (key2262, -1), (key1981, -1), (key2218, -1), (key2266, 4), (key1997, 4), (key2262, 4)]

def rawRow17276 : Integer.Sparse Key := [(key1983, 2), (key1981, 2), (key1976, 2), (key1997, -2), (key1983, -2), (key1981, -2), (key1983, 2), (key1981, 2), (key1976, 2), (key2266, -1), (key2224, -1), (key2262, -1), (key1983, -1), (key2218, -1), (key1981, -1), (key1997, -2), (key1983, -2), (key1981, -2), (key2266, -1), (key2224, -1), (key2262, -1), (key1983, -1), (key2218, -1), (key1981, -1), (key2266, 4), (key2262, 4), (key1997, 4)]

def rawRow17277 : Integer.Sparse Key := [(key1981, 2), (key1981, 2), (key1997, 2), (key1976, -2), (key1983, -2), (key1983, -2), (key2218, 2), (key2218, 2), (key2262, 2), (key1976, -1), (key1983, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key2224, -1), (key2218, -2), (key2262, -2), (key2262, -2), (key1981, -1), (key1997, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key2266, -1), (key1983, 4), (key1983, 4), (key2224, 4)]

def rawRow17278 : Integer.Sparse Key := [(key1981, 2), (key1997, 2), (key1981, 2), (key1983, -2), (key1976, -2), (key1983, -2), (key2218, 2), (key2262, 2), (key2218, 2), (key1983, -1), (key1976, -1), (key2224, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key2262, -2), (key2218, -2), (key2262, -2), (key1997, -1), (key1981, -1), (key2266, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key1983, 4), (key2224, 4), (key1983, 4)]

def rawRow17279 : Integer.Sparse Key := [(key1997, 2), (key1981, 2), (key1981, 2), (key1983, -2), (key1983, -2), (key1976, -2), (key2262, 2), (key2218, 2), (key2218, 2), (key2224, -1), (key2224, -1), (key1983, -1), (key1983, -1), (key1976, -1), (key1976, -1), (key2262, -2), (key2262, -2), (key2218, -2), (key2266, -1), (key2266, -1), (key1997, -1), (key1997, -1), (key1981, -1), (key1981, -1), (key2224, 4), (key1983, 4), (key1983, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17280 : Integer.Sparse Key := [(key1983, 2), (key1983, 2), (key1997, 2), (key1976, -2), (key1981, -2), (key1981, -2), (key2224, 2), (key2224, 2), (key2266, 2), (key1976, -1), (key1981, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key2218, -1), (key2224, -2), (key2266, -2), (key2266, -2), (key1983, -1), (key1997, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key2262, -1), (key1981, 4), (key1981, 4), (key2218, 4)]

def rawRow17281 : Integer.Sparse Key := [(key1983, 2), (key1997, 2), (key1983, 2), (key1981, -2), (key1976, -2), (key1981, -2), (key2224, 2), (key2266, 2), (key2224, 2), (key1981, -1), (key1976, -1), (key2218, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key2266, -2), (key2224, -2), (key2266, -2), (key1997, -1), (key1983, -1), (key2262, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key1981, 4), (key2218, 4), (key1981, 4)]

def rawRow17282 : Integer.Sparse Key := [(key1997, 2), (key1983, 2), (key1983, 2), (key1981, -2), (key1981, -2), (key1976, -2), (key2266, 2), (key2224, 2), (key2224, 2), (key2218, -1), (key2218, -1), (key1981, -1), (key1981, -1), (key1976, -1), (key1976, -1), (key2266, -2), (key2266, -2), (key2224, -2), (key2262, -1), (key2262, -1), (key1997, -1), (key1997, -1), (key1983, -1), (key1983, -1), (key2218, 4), (key1981, 4), (key1981, 4)]

def rawRow17283 : Integer.Sparse Key := [(key2218, 2), (key2218, 2), (key2262, 2), (key2218, -2), (key2262, -2), (key2262, -2), (key1981, 2), (key1981, 2), (key1997, 2), (key1981, -1), (key1997, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key2266, -1), (key1976, -2), (key1983, -2), (key1983, -2), (key1976, -1), (key1983, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key2224, -1), (key1983, 4), (key1983, 4), (key2224, 4)]

def rawRow17284 : Integer.Sparse Key := [(key2218, 2), (key2262, 2), (key2218, 2), (key2262, -2), (key2218, -2), (key2262, -2), (key1981, 2), (key1997, 2), (key1981, 2), (key1997, -1), (key1981, -1), (key2266, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key1983, -2), (key1976, -2), (key1983, -2), (key1983, -1), (key1976, -1), (key2224, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key1983, 4), (key2224, 4), (key1983, 4)]

def rawRow17285 : Integer.Sparse Key := [(key2262, 2), (key2218, 2), (key2218, 2), (key2262, -2), (key2262, -2), (key2218, -2), (key1997, 2), (key1981, 2), (key1981, 2), (key2266, -1), (key2266, -1), (key1997, -1), (key1997, -1), (key1981, -1), (key1981, -1), (key1983, -2), (key1983, -2), (key1976, -2), (key2224, -1), (key2224, -1), (key1983, -1), (key1983, -1), (key1976, -1), (key1976, -1), (key2224, 4), (key1983, 4), (key1983, 4)]

def rawRow17286 : Integer.Sparse Key := [(key2262, 2), (key2262, 2), (key2262, 2), (key2218, -2), (key2218, -2), (key2218, -2), (key2266, 2), (key2266, 2), (key2266, 2), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key2224, -2), (key2224, -2), (key2224, -2), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1976, 4), (key1976, 4), (key1976, 4)]

def rawRow17287 : Integer.Sparse Key := [(key2224, 2), (key2224, 2), (key2266, 2), (key2224, -2), (key2266, -2), (key2266, -2), (key1983, 2), (key1983, 2), (key1997, 2), (key1983, -1), (key1997, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key2262, -1), (key1976, -2), (key1981, -2), (key1981, -2), (key1976, -1), (key1981, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key2218, -1), (key1981, 4), (key1981, 4), (key2218, 4)]

def rawRow17288 : Integer.Sparse Key := [(key2224, 2), (key2266, 2), (key2224, 2), (key2266, -2), (key2224, -2), (key2266, -2), (key1983, 2), (key1997, 2), (key1983, 2), (key1997, -1), (key1983, -1), (key2262, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key1981, -2), (key1976, -2), (key1981, -2), (key1981, -1), (key1976, -1), (key2218, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key1981, 4), (key2218, 4), (key1981, 4)]

def rawRow17289 : Integer.Sparse Key := [(key2266, 2), (key2224, 2), (key2224, 2), (key2266, -2), (key2266, -2), (key2224, -2), (key1997, 2), (key1983, 2), (key1983, 2), (key2262, -1), (key2262, -1), (key1997, -1), (key1997, -1), (key1983, -1), (key1983, -1), (key1981, -2), (key1981, -2), (key1976, -2), (key2218, -1), (key2218, -1), (key1981, -1), (key1981, -1), (key1976, -1), (key1976, -1), (key2218, 4), (key1981, 4), (key1981, 4)]

def rawRow17290 : Integer.Sparse Key := [(key2266, 2), (key2266, 2), (key2266, 2), (key2224, -2), (key2224, -2), (key2224, -2), (key2262, 2), (key2262, 2), (key2262, 2), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key2218, -2), (key2218, -2), (key2218, -2), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1976, 4), (key1976, 4), (key1976, 4)]

def rawRow17291 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, 2), (key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2013, 2), (key2019, 2), (key2026, 2), (key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2042, 2), (key2047, 2), (key2127, 2), (key2134, 2), (key2228, 2), (key2229, 2)]

def rawRow17292 : Integer.Sparse Key := [(key2019, 2), (key2013, 2), (key2026, 2), (key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2019, 2), (key2013, 2), (key2026, 2), (key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2047, 2), (key2042, 2), (key2134, 2), (key2127, 2), (key2229, 2), (key2228, 2)]

def rawRow17293 : Integer.Sparse Key := [(key2013, 2), (key2026, 2), (key2019, 2), (key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2013, 2), (key2026, 2), (key2019, 2), (key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2127, 2), (key2228, 2), (key2042, 2), (key2229, 2), (key2047, 2), (key2134, 2)]

def rawRow17294 : Integer.Sparse Key := [(key2026, 2), (key2013, 2), (key2019, 2), (key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2026, 2), (key2013, 2), (key2019, 2), (key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2228, 2), (key2127, 2), (key2229, 2), (key2042, 2), (key2134, 2), (key2047, 2)]

def rawRow17295 : Integer.Sparse Key := [(key2019, 2), (key2026, 2), (key2013, 2), (key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2019, 2), (key2026, 2), (key2013, 2), (key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2134, 2), (key2229, 2), (key2047, 2), (key2228, 2), (key2042, 2), (key2127, 2)]

def rawRow17296 : Integer.Sparse Key := [(key2026, 2), (key2019, 2), (key2013, 2), (key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2026, 2), (key2019, 2), (key2013, 2), (key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2229, 2), (key2134, 2), (key2228, 2), (key2047, 2), (key2127, 2), (key2042, 2)]

def rawRow17297 : Integer.Sparse Key := [(key2042, 2), (key2055, 2), (key2055, 2), (key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2127, 2), (key2144, 2), (key2144, 2), (key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2)]

def rawRow17298 : Integer.Sparse Key := [(key2055, 2), (key2042, 2), (key2055, 2), (key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2144, 2), (key2127, 2), (key2144, 2), (key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2)]

def rawRow17299 : Integer.Sparse Key := [(key2055, 2), (key2055, 2), (key2042, 2), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2144, 2), (key2144, 2), (key2127, 2), (key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2)]

def rawRow17300 : Integer.Sparse Key := [(key2047, 2), (key2056, 2), (key2056, 2), (key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2134, 2), (key2145, 2), (key2145, 2), (key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2)]

def rawRow17301 : Integer.Sparse Key := [(key2056, 2), (key2047, 2), (key2056, 2), (key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2145, 2), (key2134, 2), (key2145, 2), (key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2)]

def rawRow17302 : Integer.Sparse Key := [(key2056, 2), (key2056, 2), (key2047, 2), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2145, 2), (key2145, 2), (key2134, 2), (key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2)]

def rawRow17303 : Integer.Sparse Key := [(key2127, 2), (key2144, 2), (key2144, 2), (key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2042, 2), (key2055, 2), (key2055, 2), (key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2)]

def rawRow17304 : Integer.Sparse Key := [(key2144, 2), (key2127, 2), (key2144, 2), (key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2055, 2), (key2042, 2), (key2055, 2), (key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2)]

def rawRow17305 : Integer.Sparse Key := [(key2144, 2), (key2144, 2), (key2127, 2), (key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2055, 2), (key2055, 2), (key2042, 2), (key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2)]

def rawRow17306 : Integer.Sparse Key := [(key2228, 2), (key2228, 2), (key2228, 2), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2229, 2), (key2229, 2), (key2229, 2), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2)]

def rawRow17307 : Integer.Sparse Key := [(key2134, 2), (key2145, 2), (key2145, 2), (key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2047, 2), (key2056, 2), (key2056, 2), (key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2)]

def rawRow17308 : Integer.Sparse Key := [(key2145, 2), (key2134, 2), (key2145, 2), (key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2056, 2), (key2047, 2), (key2056, 2), (key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2)]

def rawRow17309 : Integer.Sparse Key := [(key2145, 2), (key2145, 2), (key2134, 2), (key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2056, 2), (key2056, 2), (key2047, 2), (key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2)]

def rawRow17310 : Integer.Sparse Key := [(key2229, 2), (key2229, 2), (key2229, 2), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2228, 2), (key2228, 2), (key2228, 2), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2)]

def rawRow17311 : Integer.Sparse Key := [(key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2026, 2), (key2055, 2), (key2056, 2), (key2013, 1), (key2019, 1), (key2127, 1), (key2134, 1), (key2144, 1), (key2145, 1), (key2026, -2), (key2144, -2), (key2145, -2), (key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2013, 1), (key2019, 1), (key2127, 1), (key2134, 1), (key2144, 1), (key2145, 1), (key2026, 2), (key2055, 2), (key2056, 2), (key2026, -2), (key2144, -2), (key2145, -2)]

def rawRow17312 : Integer.Sparse Key := [(key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2026, 2), (key2056, 2), (key2055, 2), (key2019, 1), (key2013, 1), (key2134, 1), (key2127, 1), (key2145, 1), (key2144, 1), (key2026, -2), (key2145, -2), (key2144, -2), (key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2019, 1), (key2013, 1), (key2134, 1), (key2127, 1), (key2145, 1), (key2144, 1), (key2026, 2), (key2056, 2), (key2055, 2), (key2026, -2), (key2145, -2), (key2144, -2)]

def rawRow17313 : Integer.Sparse Key := [(key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2055, 2), (key2026, 2), (key2056, 2), (key2127, 1), (key2144, 1), (key2013, 1), (key2145, 1), (key2019, 1), (key2134, 1), (key2144, -2), (key2026, -2), (key2145, -2), (key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2127, 1), (key2144, 1), (key2013, 1), (key2145, 1), (key2019, 1), (key2134, 1), (key2055, 2), (key2026, 2), (key2056, 2), (key2144, -2), (key2026, -2), (key2145, -2)]

def rawRow17314 : Integer.Sparse Key := [(key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2055, 2), (key2056, 2), (key2026, 2), (key2144, 1), (key2127, 1), (key2145, 1), (key2013, 1), (key2134, 1), (key2019, 1), (key2144, -2), (key2145, -2), (key2026, -2), (key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2144, 1), (key2127, 1), (key2145, 1), (key2013, 1), (key2134, 1), (key2019, 1), (key2055, 2), (key2056, 2), (key2026, 2), (key2144, -2), (key2145, -2), (key2026, -2)]

def rawRow17315 : Integer.Sparse Key := [(key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2056, 2), (key2026, 2), (key2055, 2), (key2134, 1), (key2145, 1), (key2019, 1), (key2144, 1), (key2013, 1), (key2127, 1), (key2145, -2), (key2026, -2), (key2144, -2), (key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2134, 1), (key2145, 1), (key2019, 1), (key2144, 1), (key2013, 1), (key2127, 1), (key2056, 2), (key2026, 2), (key2055, 2), (key2145, -2), (key2026, -2), (key2144, -2)]

def rawRow17316 : Integer.Sparse Key := [(key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2056, 2), (key2055, 2), (key2026, 2), (key2145, 1), (key2134, 1), (key2144, 1), (key2019, 1), (key2127, 1), (key2013, 1), (key2145, -2), (key2144, -2), (key2026, -2), (key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2145, 1), (key2134, 1), (key2144, 1), (key2019, 1), (key2127, 1), (key2013, 1), (key2056, 2), (key2055, 2), (key2026, 2), (key2145, -2), (key2144, -2), (key2026, -2)]

def rawRow17317 : Integer.Sparse Key := [(key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2019, 2), (key2019, 2), (key2047, 2), (key2013, 1), (key2026, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2145, 1), (key2019, -2), (key2019, -2), (key2134, -2), (key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2042, 1), (key2055, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2229, 1), (key2144, 2), (key2144, 2), (key2228, 2), (key2055, -2), (key2055, -2), (key2229, -2)]

def rawRow17318 : Integer.Sparse Key := [(key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2019, 2), (key2047, 2), (key2019, 2), (key2026, 1), (key2013, 1), (key2145, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2019, -2), (key2134, -2), (key2019, -2), (key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2055, 1), (key2042, 1), (key2229, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2144, 2), (key2228, 2), (key2144, 2), (key2055, -2), (key2229, -2), (key2055, -2)]

def rawRow17319 : Integer.Sparse Key := [(key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2047, 2), (key2019, 2), (key2019, 2), (key2145, 1), (key2145, 1), (key2026, 1), (key2026, 1), (key2013, 1), (key2013, 1), (key2134, -2), (key2019, -2), (key2019, -2), (key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2229, 1), (key2229, 1), (key2055, 1), (key2055, 1), (key2042, 1), (key2042, 1), (key2228, 2), (key2144, 2), (key2144, 2), (key2229, -2), (key2055, -2), (key2055, -2)]

def rawRow17320 : Integer.Sparse Key := [(key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2013, 2), (key2013, 2), (key2042, 2), (key2019, 1), (key2026, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2144, 1), (key2013, -2), (key2013, -2), (key2127, -2), (key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2047, 1), (key2056, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2228, 1), (key2145, 2), (key2145, 2), (key2229, 2), (key2056, -2), (key2056, -2), (key2228, -2)]

def rawRow17321 : Integer.Sparse Key := [(key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2013, 2), (key2042, 2), (key2013, 2), (key2026, 1), (key2019, 1), (key2144, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2013, -2), (key2127, -2), (key2013, -2), (key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2056, 1), (key2047, 1), (key2228, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2145, 2), (key2229, 2), (key2145, 2), (key2056, -2), (key2228, -2), (key2056, -2)]

def rawRow17322 : Integer.Sparse Key := [(key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2042, 2), (key2013, 2), (key2013, 2), (key2144, 1), (key2144, 1), (key2026, 1), (key2026, 1), (key2019, 1), (key2019, 1), (key2127, -2), (key2013, -2), (key2013, -2), (key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2228, 1), (key2228, 1), (key2056, 1), (key2056, 1), (key2047, 1), (key2047, 1), (key2229, 2), (key2145, 2), (key2145, 2), (key2228, -2), (key2056, -2), (key2056, -2)]

def rawRow17323 : Integer.Sparse Key := [(key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2144, 2), (key2144, 2), (key2228, 2), (key2042, 1), (key2055, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2229, 1), (key2055, -2), (key2055, -2), (key2229, -2), (key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2013, 1), (key2026, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2145, 1), (key2019, 2), (key2019, 2), (key2047, 2), (key2019, -2), (key2019, -2), (key2134, -2)]

def rawRow17324 : Integer.Sparse Key := [(key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2144, 2), (key2228, 2), (key2144, 2), (key2055, 1), (key2042, 1), (key2229, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2055, -2), (key2229, -2), (key2055, -2), (key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2026, 1), (key2013, 1), (key2145, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2019, 2), (key2047, 2), (key2019, 2), (key2019, -2), (key2134, -2), (key2019, -2)]

def rawRow17325 : Integer.Sparse Key := [(key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2228, 2), (key2144, 2), (key2144, 2), (key2229, 1), (key2229, 1), (key2055, 1), (key2055, 1), (key2042, 1), (key2042, 1), (key2229, -2), (key2055, -2), (key2055, -2), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, 1), (key2145, 1), (key2026, 1), (key2026, 1), (key2013, 1), (key2013, 1), (key2047, 2), (key2019, 2), (key2019, 2), (key2134, -2), (key2019, -2), (key2019, -2)]

def rawRow17326 : Integer.Sparse Key := [(key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2127, 2), (key2127, 2), (key2127, 2), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2042, -2), (key2042, -2), (key2042, -2), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2134, 2), (key2134, 2), (key2134, 2), (key2047, -2), (key2047, -2), (key2047, -2)]

def rawRow17327 : Integer.Sparse Key := [(key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2145, 2), (key2145, 2), (key2229, 2), (key2047, 1), (key2056, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2228, 1), (key2056, -2), (key2056, -2), (key2228, -2), (key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2019, 1), (key2026, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2144, 1), (key2013, 2), (key2013, 2), (key2042, 2), (key2013, -2), (key2013, -2), (key2127, -2)]

def rawRow17328 : Integer.Sparse Key := [(key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2145, 2), (key2229, 2), (key2145, 2), (key2056, 1), (key2047, 1), (key2228, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2056, -2), (key2228, -2), (key2056, -2), (key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2026, 1), (key2019, 1), (key2144, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2013, 2), (key2042, 2), (key2013, 2), (key2013, -2), (key2127, -2), (key2013, -2)]

def rawRow17329 : Integer.Sparse Key := [(key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2229, 2), (key2145, 2), (key2145, 2), (key2228, 1), (key2228, 1), (key2056, 1), (key2056, 1), (key2047, 1), (key2047, 1), (key2228, -2), (key2056, -2), (key2056, -2), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, 1), (key2144, 1), (key2026, 1), (key2026, 1), (key2019, 1), (key2019, 1), (key2042, 2), (key2013, 2), (key2013, 2), (key2127, -2), (key2013, -2), (key2013, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18455 : Integer.Sparse Key := [(key83, 24), (key0, 24), (key83, 24), (key83, 24), (key83, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1689 : Integer.Sparse Key := [(key1668, -2), (key1655, -2), (key1660, -2), (key1597, 1), (key1573, 1), (key1668, 1), (key1546, 1), (key1660, 1), (key1560, 1), (key1826, 2), (key1813, 2), (key1818, 2), (key1448, -1), (key1424, -1), (key1826, -1), (key1316, -1), (key1818, -1), (key1330, -1), (key1799, -1), (key1788, -1), (key1845, -1), (key1772, -1), (key1842, -1), (key1781, -1), (key1467, 1), (key1455, 1), (key1845, 1), (key1337, 1), (key1842, 1), (key1346, 1)]

def rawRow1690 : Integer.Sparse Key := [(key1660, -2), (key1668, -2), (key1655, -2), (key1660, 1), (key1668, 1), (key1560, 1), (key1597, 1), (key1546, 1), (key1573, 1), (key1818, 2), (key1826, 2), (key1813, 2), (key1818, -1), (key1826, -1), (key1330, -1), (key1448, -1), (key1316, -1), (key1424, -1), (key1842, -1), (key1845, -1), (key1781, -1), (key1799, -1), (key1772, -1), (key1788, -1), (key1842, 1), (key1845, 1), (key1346, 1), (key1467, 1), (key1337, 1), (key1455, 1)]

def rawRow1691 : Integer.Sparse Key := [(key1668, -2), (key1660, -2), (key1655, -2), (key1668, 1), (key1660, 1), (key1597, 1), (key1560, 1), (key1573, 1), (key1546, 1), (key1826, 2), (key1818, 2), (key1813, 2), (key1826, -1), (key1818, -1), (key1448, -1), (key1330, -1), (key1424, -1), (key1316, -1), (key1845, -1), (key1842, -1), (key1799, -1), (key1781, -1), (key1788, -1), (key1772, -1), (key1845, 1), (key1842, 1), (key1467, 1), (key1346, 1), (key1455, 1), (key1337, 1)]

def rawRow1692 : Integer.Sparse Key := [(key1772, -2), (key1775, -2), (key1781, -2), (key1788, 1), (key1791, 1), (key1813, 1), (key1840, 1), (key1818, 1), (key1842, 1), (key1337, 2), (key1340, 2), (key1346, 2), (key1455, -1), (key1458, -1), (key1655, -1), (key1840, -1), (key1660, -1), (key1842, -1), (key1296, -1), (key1303, -1), (key1316, -1), (key1340, -1), (key1330, -1), (key1346, -1), (key1391, 1), (key1398, 1), (key1546, 1), (key1775, 1), (key1560, 1), (key1781, 1)]

def rawRow1693 : Integer.Sparse Key := [(key1775, -2), (key1772, -2), (key1781, -2), (key1791, 1), (key1788, 1), (key1840, 1), (key1813, 1), (key1842, 1), (key1818, 1), (key1340, 2), (key1337, 2), (key1346, 2), (key1458, -1), (key1455, -1), (key1840, -1), (key1655, -1), (key1842, -1), (key1660, -1), (key1303, -1), (key1296, -1), (key1340, -1), (key1316, -1), (key1346, -1), (key1330, -1), (key1398, 1), (key1391, 1), (key1775, 1), (key1546, 1), (key1781, 1), (key1560, 1)]

def rawRow1694 : Integer.Sparse Key := [(key1772, -2), (key1781, -2), (key1775, -2), (key1813, 1), (key1818, 1), (key1788, 1), (key1842, 1), (key1791, 1), (key1840, 1), (key1337, 2), (key1346, 2), (key1340, 2), (key1655, -1), (key1660, -1), (key1455, -1), (key1842, -1), (key1458, -1), (key1840, -1), (key1316, -1), (key1330, -1), (key1296, -1), (key1346, -1), (key1303, -1), (key1340, -1), (key1546, 1), (key1560, 1), (key1391, 1), (key1781, 1), (key1398, 1), (key1775, 1)]

def rawRow1695 : Integer.Sparse Key := [(key1781, -2), (key1772, -2), (key1775, -2), (key1818, 1), (key1813, 1), (key1842, 1), (key1788, 1), (key1840, 1), (key1791, 1), (key1346, 2), (key1337, 2), (key1340, 2), (key1660, -1), (key1655, -1), (key1842, -1), (key1455, -1), (key1840, -1), (key1458, -1), (key1330, -1), (key1316, -1), (key1346, -1), (key1296, -1), (key1340, -1), (key1303, -1), (key1560, 1), (key1546, 1), (key1781, 1), (key1391, 1), (key1775, 1), (key1398, 1)]

def rawRow1696 : Integer.Sparse Key := [(key1775, -2), (key1781, -2), (key1772, -2), (key1840, 1), (key1842, 1), (key1791, 1), (key1818, 1), (key1788, 1), (key1813, 1), (key1340, 2), (key1346, 2), (key1337, 2), (key1840, -1), (key1842, -1), (key1458, -1), (key1660, -1), (key1455, -1), (key1655, -1), (key1340, -1), (key1346, -1), (key1303, -1), (key1330, -1), (key1296, -1), (key1316, -1), (key1775, 1), (key1781, 1), (key1398, 1), (key1560, 1), (key1391, 1), (key1546, 1)]

def rawRow1697 : Integer.Sparse Key := [(key1781, -2), (key1775, -2), (key1772, -2), (key1842, 1), (key1840, 1), (key1818, 1), (key1791, 1), (key1813, 1), (key1788, 1), (key1346, 2), (key1340, 2), (key1337, 2), (key1842, -1), (key1840, -1), (key1660, -1), (key1458, -1), (key1655, -1), (key1455, -1), (key1346, -1), (key1340, -1), (key1330, -1), (key1303, -1), (key1316, -1), (key1296, -1), (key1781, 1), (key1775, 1), (key1560, 1), (key1398, 1), (key1546, 1), (key1391, 1)]

def rawRow1698 : Integer.Sparse Key := [(key1813, -2), (key1818, -2), (key1826, -2), (key1772, 1), (key1781, 1), (key1788, 1), (key1842, 1), (key1799, 1), (key1845, 1), (key1655, 2), (key1660, 2), (key1668, 2), (key1337, -1), (key1346, -1), (key1455, -1), (key1842, -1), (key1467, -1), (key1845, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1660, -1), (key1597, -1), (key1668, -1), (key1316, 1), (key1330, 1), (key1424, 1), (key1818, 1), (key1448, 1), (key1826, 1)]

def rawRow1699 : Integer.Sparse Key := [(key1818, -2), (key1813, -2), (key1826, -2), (key1781, 1), (key1772, 1), (key1842, 1), (key1788, 1), (key1845, 1), (key1799, 1), (key1660, 2), (key1655, 2), (key1668, 2), (key1346, -1), (key1337, -1), (key1842, -1), (key1455, -1), (key1845, -1), (key1467, -1), (key1560, -1), (key1546, -1), (key1660, -1), (key1573, -1), (key1668, -1), (key1597, -1), (key1330, 1), (key1316, 1), (key1818, 1), (key1424, 1), (key1826, 1), (key1448, 1)]

def rawRow1700 : Integer.Sparse Key := [(key1813, -2), (key1826, -2), (key1818, -2), (key1788, 1), (key1799, 1), (key1772, 1), (key1845, 1), (key1781, 1), (key1842, 1), (key1655, 2), (key1668, 2), (key1660, 2), (key1455, -1), (key1467, -1), (key1337, -1), (key1845, -1), (key1346, -1), (key1842, -1), (key1573, -1), (key1597, -1), (key1546, -1), (key1668, -1), (key1560, -1), (key1660, -1), (key1424, 1), (key1448, 1), (key1316, 1), (key1826, 1), (key1330, 1), (key1818, 1)]

def rawRow1701 : Integer.Sparse Key := [(key1826, -2), (key1813, -2), (key1818, -2), (key1799, 1), (key1788, 1), (key1845, 1), (key1772, 1), (key1842, 1), (key1781, 1), (key1668, 2), (key1655, 2), (key1660, 2), (key1467, -1), (key1455, -1), (key1845, -1), (key1337, -1), (key1842, -1), (key1346, -1), (key1597, -1), (key1573, -1), (key1668, -1), (key1546, -1), (key1660, -1), (key1560, -1), (key1448, 1), (key1424, 1), (key1826, 1), (key1316, 1), (key1818, 1), (key1330, 1)]

def rawRow1702 : Integer.Sparse Key := [(key1818, -2), (key1826, -2), (key1813, -2), (key1842, 1), (key1845, 1), (key1781, 1), (key1799, 1), (key1772, 1), (key1788, 1), (key1660, 2), (key1668, 2), (key1655, 2), (key1842, -1), (key1845, -1), (key1346, -1), (key1467, -1), (key1337, -1), (key1455, -1), (key1660, -1), (key1668, -1), (key1560, -1), (key1597, -1), (key1546, -1), (key1573, -1), (key1818, 1), (key1826, 1), (key1330, 1), (key1448, 1), (key1316, 1), (key1424, 1)]

def rawRow1703 : Integer.Sparse Key := [(key1826, -2), (key1818, -2), (key1813, -2), (key1845, 1), (key1842, 1), (key1799, 1), (key1781, 1), (key1788, 1), (key1772, 1), (key1668, 2), (key1660, 2), (key1655, 2), (key1845, -1), (key1842, -1), (key1467, -1), (key1346, -1), (key1455, -1), (key1337, -1), (key1668, -1), (key1660, -1), (key1597, -1), (key1560, -1), (key1573, -1), (key1546, -1), (key1826, 1), (key1818, 1), (key1448, 1), (key1330, 1), (key1424, 1), (key1316, 1)]

def rawRow1704 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1018, -2), (key1005, 6), (key1111, 2), (key1111, 2), (key1126, 2), (key1040, -2), (key1192, -2), (key1192, -2), (key1154, -6), (key1075, 2), (key1211, 2), (key1211, 2)]

def rawRow1705 : Integer.Sparse Key := [(key998, -2), (key1018, -2), (key998, -2), (key1005, 6), (key1111, 2), (key1126, 2), (key1111, 2), (key1192, -2), (key1040, -2), (key1192, -2), (key1154, -6), (key1211, 2), (key1075, 2), (key1211, 2)]

def rawRow1706 : Integer.Sparse Key := [(key1018, -2), (key998, -2), (key998, -2), (key1005, 6), (key1126, 2), (key1111, 2), (key1111, 2), (key1192, -2), (key1192, -2), (key1040, -2), (key1154, -6), (key1211, 2), (key1211, 2), (key1075, 2)]

def rawRow1707 : Integer.Sparse Key := [(key998, -2), (key1005, -2), (key1018, -2), (key998, 6), (key1190, 2), (key1192, 2), (key1198, 2), (key1033, -2), (key1111, -2), (key1190, -2), (key1211, -6), (key1075, 2), (key1154, 2), (key1211, 2)]

def rawRow1708 : Integer.Sparse Key := [(key1005, -2), (key998, -2), (key1018, -2), (key998, 6), (key1192, 2), (key1190, 2), (key1198, 2), (key1033, -2), (key1190, -2), (key1111, -2), (key1211, -6), (key1075, 2), (key1211, 2), (key1154, 2)]

def rawRow1709 : Integer.Sparse Key := [(key998, -2), (key1018, -2), (key1005, -2), (key998, 6), (key1190, 2), (key1198, 2), (key1192, 2), (key1111, -2), (key1033, -2), (key1190, -2), (key1211, -6), (key1154, 2), (key1075, 2), (key1211, 2)]

def rawRow1710 : Integer.Sparse Key := [(key1018, -2), (key998, -2), (key1005, -2), (key998, 6), (key1198, 2), (key1190, 2), (key1192, 2), (key1111, -2), (key1190, -2), (key1033, -2), (key1211, -6), (key1154, 2), (key1211, 2), (key1075, 2)]

def rawRow1711 : Integer.Sparse Key := [(key1005, -2), (key1018, -2), (key998, -2), (key998, 6), (key1192, 2), (key1198, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key1111, -2), (key1211, -6), (key1211, 2), (key1075, 2), (key1154, 2)]

def rawRow1712 : Integer.Sparse Key := [(key1018, -2), (key1005, -2), (key998, -2), (key998, 6), (key1198, 2), (key1192, 2), (key1190, 2), (key1190, -2), (key1111, -2), (key1033, -2), (key1211, -6), (key1211, 2), (key1154, 2), (key1075, 2)]

def rawRow1713 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1126, -2), (key1154, 6), (key998, 2), (key998, 2), (key1018, 2), (key1075, -2), (key1211, -2), (key1211, -2), (key1005, -6), (key1040, 2), (key1192, 2), (key1192, 2)]

def rawRow1714 : Integer.Sparse Key := [(key1111, -2), (key1126, -2), (key1111, -2), (key1154, 6), (key998, 2), (key1018, 2), (key998, 2), (key1211, -2), (key1075, -2), (key1211, -2), (key1005, -6), (key1192, 2), (key1040, 2), (key1192, 2)]

def rawRow1715 : Integer.Sparse Key := [(key1126, -2), (key1111, -2), (key1111, -2), (key1154, 6), (key1018, 2), (key998, 2), (key998, 2), (key1211, -2), (key1211, -2), (key1075, -2), (key1005, -6), (key1192, 2), (key1192, 2), (key1040, 2)]

def rawRow1716 : Integer.Sparse Key := [(key1111, -2), (key1126, -2), (key1154, -2), (key1111, 6), (key1190, 2), (key1198, 2), (key1211, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1192, -6), (key1005, 2), (key1040, 2), (key1192, 2)]

def rawRow1717 : Integer.Sparse Key := [(key1126, -2), (key1111, -2), (key1154, -2), (key1111, 6), (key1198, 2), (key1190, 2), (key1211, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1192, -6), (key1005, 2), (key1192, 2), (key1040, 2)]

def rawRow1718 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1126, -2), (key1111, 6), (key1190, 2), (key1211, 2), (key1198, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1192, -6), (key1040, 2), (key1005, 2), (key1192, 2)]

def rawRow1719 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1126, -2), (key1111, 6), (key1211, 2), (key1190, 2), (key1198, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1192, -6), (key1040, 2), (key1192, 2), (key1005, 2)]

def rawRow1720 : Integer.Sparse Key := [(key1126, -2), (key1154, -2), (key1111, -2), (key1111, 6), (key1198, 2), (key1211, 2), (key1190, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1192, -6), (key1192, 2), (key1005, 2), (key1040, 2)]

def rawRow1721 : Integer.Sparse Key := [(key1154, -2), (key1126, -2), (key1111, -2), (key1111, 6), (key1211, 2), (key1198, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1192, -6), (key1192, 2), (key1040, 2), (key1005, 2)]

def rawRow1722 : Integer.Sparse Key := [(key1190, -2), (key1192, -2), (key1198, -2), (key1211, 6), (key998, 2), (key1005, 2), (key1018, 2), (key1075, -2), (key1154, -2), (key1211, -2), (key998, -6), (key1033, 2), (key1111, 2), (key1190, 2)]

def rawRow1723 : Integer.Sparse Key := [(key1192, -2), (key1190, -2), (key1198, -2), (key1211, 6), (key1005, 2), (key998, 2), (key1018, 2), (key1075, -2), (key1211, -2), (key1154, -2), (key998, -6), (key1033, 2), (key1190, 2), (key1111, 2)]

def rawRow1724 : Integer.Sparse Key := [(key1190, -2), (key1198, -2), (key1192, -2), (key1211, 6), (key998, 2), (key1018, 2), (key1005, 2), (key1154, -2), (key1075, -2), (key1211, -2), (key998, -6), (key1111, 2), (key1033, 2), (key1190, 2)]

def rawRow1725 : Integer.Sparse Key := [(key1198, -2), (key1190, -2), (key1192, -2), (key1211, 6), (key1018, 2), (key998, 2), (key1005, 2), (key1154, -2), (key1211, -2), (key1075, -2), (key998, -6), (key1111, 2), (key1190, 2), (key1033, 2)]

def rawRow1726 : Integer.Sparse Key := [(key1192, -2), (key1198, -2), (key1190, -2), (key1211, 6), (key1005, 2), (key1018, 2), (key998, 2), (key1211, -2), (key1075, -2), (key1154, -2), (key998, -6), (key1190, 2), (key1033, 2), (key1111, 2)]

def rawRow1727 : Integer.Sparse Key := [(key1198, -2), (key1192, -2), (key1190, -2), (key1211, 6), (key1018, 2), (key1005, 2), (key998, 2), (key1211, -2), (key1154, -2), (key1075, -2), (key998, -6), (key1190, 2), (key1111, 2), (key1033, 2)]

def rawRow1728 : Integer.Sparse Key := [(key1190, -2), (key1198, -2), (key1211, -2), (key1192, 6), (key1111, 2), (key1126, 2), (key1154, 2), (key1005, -2), (key1040, -2), (key1192, -2), (key1111, -6), (key998, 2), (key1033, 2), (key1190, 2)]

def rawRow1729 : Integer.Sparse Key := [(key1198, -2), (key1190, -2), (key1211, -2), (key1192, 6), (key1126, 2), (key1111, 2), (key1154, 2), (key1005, -2), (key1192, -2), (key1040, -2), (key1111, -6), (key998, 2), (key1190, 2), (key1033, 2)]

def rawRow1730 : Integer.Sparse Key := [(key1190, -2), (key1211, -2), (key1198, -2), (key1192, 6), (key1111, 2), (key1154, 2), (key1126, 2), (key1040, -2), (key1005, -2), (key1192, -2), (key1111, -6), (key1033, 2), (key998, 2), (key1190, 2)]

def rawRow1731 : Integer.Sparse Key := [(key1211, -2), (key1190, -2), (key1198, -2), (key1192, 6), (key1154, 2), (key1111, 2), (key1126, 2), (key1040, -2), (key1192, -2), (key1005, -2), (key1111, -6), (key1033, 2), (key1190, 2), (key998, 2)]

def rawRow1732 : Integer.Sparse Key := [(key1198, -2), (key1211, -2), (key1190, -2), (key1192, 6), (key1126, 2), (key1154, 2), (key1111, 2), (key1192, -2), (key1005, -2), (key1040, -2), (key1111, -6), (key1190, 2), (key998, 2), (key1033, 2)]

def rawRow1733 : Integer.Sparse Key := [(key1211, -2), (key1198, -2), (key1190, -2), (key1192, 6), (key1154, 2), (key1126, 2), (key1111, 2), (key1192, -2), (key1040, -2), (key1005, -2), (key1111, -6), (key1190, 2), (key1033, 2), (key998, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def targetCombined2_part4 : Sparse := [([1, 0, -1, 0, 2, -1, 0], 36), ([1, 0, -1, 0, 2, 0, -1], 36)]

end MUB6.TaoCertificate

end OAI
end


