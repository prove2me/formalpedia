-- Prove2me | Definitions.Def_OAIQ106D178
-- name    : OAIQ106D178
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:41:06.72973+00:00
-- url     : https://prove2.me/theorems/1f2b3d2e-d7ba-4b8b-8a69-ac3449e1b189
-- title:
--   Definitions bundle OAIQ106D178 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 90 declarations of OpenAI's Lean: 90 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow6723`, `OAI.MUB6.Certificate.GramRows.rawRow6724`, `OAI.MUB6.Certificate.GramRows.rawRow6725`, `OAI.MUB6.Certificate.GramRows.rawRow6726`, `OAI.MUB6.Certificate.GramRows.rawRow6727`, `OAI.MUB6.Certificate.GramRows.rawRow6728`, `OAI.MUB6.Certificate.GramRows.rawRow6729`, `OAI.MUB6.Certificate.GramRows.rawRow6730`, `OAI.MUB6.Certificate.GramRows.rawRow6731`, `OAI.MUB6.Certificate.GramRows.rawRow6732`, `OAI.MUB6.Certificate.GramRows.rawRow6733`, `OAI.MUB6.Certificate.GramRows.rawRow6734`, `OAI.MUB6.Certificate.GramRows.rawRow6735`, `OAI.MUB6.Certificate.GramRows.rawRow6736`, `OAI.MUB6.Certificate.GramRows.rawRow6737`, `OAI.MUB6.Certificate.GramRows.rawRow6738`, `OAI.MUB6.Certificate.GramRows.rawRow6739`, `OAI.MUB6.Certificate.GramRows.rawRow6740`, `OAI.MUB6.Certificate.GramRows.rawRow6741`, `OAI.MUB6.Certificate.GramRows.rawRow6742`, `OAI.MUB6.Certificate.GramRows.rawRow6743`, `OAI.MUB6.Certificate.GramRows.rawRow6744`, `OAI.MUB6.Certificate.GramRows.rawRow6745`, `OAI.MUB6.Certificate.GramRows.rawRow6746`, `OAI.MUB6.Certificate.GramRows.rawRow6747`, `OAI.MUB6.Certificate.GramRows.rawRow6748`, `OAI.MUB6.Certificate.GramRows.rawRow6749`, `OAI.MUB6.Certificate.GramRows.rawRow6750`, `OAI.MUB6.Certificate.GramRows.rawRow6751`, `OAI.MUB6.Certificate.GramRows.rawRow6752`, `OAI.MUB6.Certificate.GramRows.rawRow6753`, `OAI.MUB6.Certificate.GramRows.rawRow6754`, `OAI.MUB6.Certificate.GramRows.rawRow6755`, `OAI.MUB6.Certificate.GramRows.rawRow6756`, `OAI.MUB6.Certificate.GramRows.rawRow6757`, `OAI.MUB6.Certificate.GramRows.rawRow6758`, `OAI.MUB6.Certificate.GramRows.rawRow6759`, `OAI.MUB6.Certificate.GramRows.rawRow6760`, `OAI.MUB6.Certificate.GramRows.rawRow6761`, `OAI.MUB6.Certificate.GramRows.rawRow6762` and 50 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block18.lean), [`MutuallyUnbiased_GramRows_Block76`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block76.lean), [`MutuallyUnbiased_GramRows_Block77`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block77.lean), [`MutuallyUnbiased_GramRows_Block81`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block81.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D087`, `OAIQ106D089`, `OAIQ106D090`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_2` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow68 : Integer.Sparse Key := [(key1655, -1), (key1659, -1), (key1667, 2), (key1546, 1), (key1559, 1), (key1596, -1), (key1667, -1), (key1546, -2), (key1573, 1), (key1655, 1), (key1813, 1), (key1817, 1), (key1825, -2), (key1316, -1), (key1329, -1), (key1447, 1), (key1825, 1), (key1316, 2), (key1424, -1), (key1813, -1), (key1772, -1), (key1780, -1), (key1798, 1), (key1844, 1), (key1337, 1), (key1345, 1), (key1466, -1), (key1844, -1), (key1296, -1), (key1337, -1), (key1391, 1), (key1772, 1), (key1774, 2), (key1790, -1), (key1839, -1), (key1339, -2), (key1457, 1), (key1839, 1), (key1302, 1), (key1339, 1), (key1397, -1), (key1774, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow680 : Integer.Sparse Key := [(key314, -6), (key314, 2), (key300, 2), (key314, 2), (key404, 6), (key404, -2), (key234, -2), (key404, -2), (key433, -2), (key314, -2), (key433, -2), (key433, 2), (key246, 2), (key433, 2)]

def rawRow681 : Integer.Sparse Key := [(key314, -6), (key314, 2), (key314, 2), (key300, 2), (key404, 6), (key404, -2), (key404, -2), (key234, -2), (key433, -2), (key433, -2), (key314, -2), (key433, 2), (key433, 2), (key246, 2)]

def rawRow682 : Integer.Sparse Key := [(key383, -6), (key404, 2), (key433, 2), (key433, 2), (key246, 6), (key314, -2), (key433, -2), (key433, -2), (key234, -2), (key246, -2), (key246, -2), (key300, 2), (key314, 2), (key314, 2)]

def rawRow683 : Integer.Sparse Key := [(key383, -6), (key433, 2), (key404, 2), (key433, 2), (key246, 6), (key433, -2), (key314, -2), (key433, -2), (key246, -2), (key234, -2), (key246, -2), (key314, 2), (key300, 2), (key314, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6723 : Integer.Sparse Key := [(key2061, -1), (key2093, -1), (key2066, 2), (key2061, -1), (key2093, -1), (key2031, 2), (key2096, 2), (key2036, -1), (key2071, -1), (key2066, 2), (key2036, -1), (key2071, -1), (key2150, 1), (key2195, 1), (key2155, -2), (key2150, 1), (key2195, 1), (key2031, -2), (key2201, -2), (key2036, 1), (key2168, 1), (key2155, -2), (key2036, 1), (key2168, 1), (key2150, -1), (key2306, -1), (key2155, 1), (key2248, 1), (key2061, 1), (key2311, 1), (key2066, -1), (key2255, -1), (key2150, -1), (key2306, -1), (key2061, 1), (key2311, 1), (key2155, 1), (key2248, 1), (key2066, -1), (key2255, -1)]

def rawRow6724 : Integer.Sparse Key := [(key2093, -1), (key2061, -1), (key2066, 2), (key2093, -1), (key2061, -1), (key2096, 2), (key2031, 2), (key2071, -1), (key2036, -1), (key2066, 2), (key2071, -1), (key2036, -1), (key2195, 1), (key2150, 1), (key2155, -2), (key2195, 1), (key2150, 1), (key2201, -2), (key2031, -2), (key2168, 1), (key2036, 1), (key2155, -2), (key2168, 1), (key2036, 1), (key2306, -1), (key2150, -1), (key2248, 1), (key2155, 1), (key2311, 1), (key2061, 1), (key2255, -1), (key2066, -1), (key2306, -1), (key2150, -1), (key2311, 1), (key2061, 1), (key2248, 1), (key2155, 1), (key2255, -1), (key2066, -1)]

def rawRow6725 : Integer.Sparse Key := [(key2066, -1), (key2093, -1), (key2061, 2), (key2071, -1), (key2096, -1), (key2036, 2), (key2093, 2), (key2031, -1), (key2061, -1), (key2071, 2), (key2036, -1), (key2066, -1), (key2155, 1), (key2195, 1), (key2150, -2), (key2168, 1), (key2201, 1), (key2036, -2), (key2195, -2), (key2031, 1), (key2150, 1), (key2168, -2), (key2036, 1), (key2155, 1), (key2155, -1), (key2304, -1), (key2150, 1), (key2243, 1), (key2066, 1), (key2304, 1), (key2061, -1), (key2243, -1), (key2168, -1), (key2311, -1), (key2071, 1), (key2306, 1), (key2168, 1), (key2255, 1), (key2071, -1), (key2248, -1)]

def rawRow6726 : Integer.Sparse Key := [(key2093, -1), (key2066, -1), (key2061, 2), (key2096, -1), (key2071, -1), (key2093, 2), (key2036, 2), (key2061, -1), (key2031, -1), (key2071, 2), (key2066, -1), (key2036, -1), (key2195, 1), (key2155, 1), (key2150, -2), (key2201, 1), (key2168, 1), (key2195, -2), (key2036, -2), (key2150, 1), (key2031, 1), (key2168, -2), (key2155, 1), (key2036, 1), (key2304, -1), (key2155, -1), (key2243, 1), (key2150, 1), (key2304, 1), (key2066, 1), (key2243, -1), (key2061, -1), (key2311, -1), (key2168, -1), (key2306, 1), (key2071, 1), (key2255, 1), (key2168, 1), (key2248, -1), (key2071, -1)]

def rawRow6727 : Integer.Sparse Key := [(key2071, -1), (key2071, -1), (key2096, 2), (key2036, -1), (key2036, -1), (key2066, 2), (key2066, 2), (key2093, -1), (key2093, -1), (key2031, 2), (key2061, -1), (key2061, -1), (key2168, 1), (key2168, 1), (key2201, -2), (key2036, 1), (key2036, 1), (key2155, -2), (key2155, -2), (key2195, 1), (key2195, 1), (key2031, -2), (key2150, 1), (key2150, 1), (key2255, -1), (key2255, -1), (key2311, 1), (key2311, 1), (key2248, 1), (key2248, 1), (key2306, -1), (key2306, -1), (key2066, -1), (key2066, -1), (key2155, 1), (key2155, 1), (key2061, 1), (key2061, 1), (key2150, -1), (key2150, -1)]

def rawRow6728 : Integer.Sparse Key := [(key2071, -1), (key2096, -1), (key2071, 2), (key2066, -1), (key2093, -1), (key2036, 2), (key2093, 2), (key2036, -1), (key2066, -1), (key2061, 2), (key2031, -1), (key2061, -1), (key2168, 1), (key2201, 1), (key2168, -2), (key2155, 1), (key2195, 1), (key2036, -2), (key2195, -2), (key2036, 1), (key2155, 1), (key2150, -2), (key2031, 1), (key2150, 1), (key2168, -1), (key2311, -1), (key2168, 1), (key2255, 1), (key2071, 1), (key2306, 1), (key2071, -1), (key2248, -1), (key2155, -1), (key2304, -1), (key2066, 1), (key2304, 1), (key2150, 1), (key2243, 1), (key2061, -1), (key2243, -1)]

def rawRow6729 : Integer.Sparse Key := [(key2096, -1), (key2071, -1), (key2071, 2), (key2093, -1), (key2066, -1), (key2093, 2), (key2036, 2), (key2066, -1), (key2036, -1), (key2061, 2), (key2061, -1), (key2031, -1), (key2201, 1), (key2168, 1), (key2168, -2), (key2195, 1), (key2155, 1), (key2195, -2), (key2036, -2), (key2155, 1), (key2036, 1), (key2150, -2), (key2150, 1), (key2031, 1), (key2311, -1), (key2168, -1), (key2255, 1), (key2168, 1), (key2306, 1), (key2071, 1), (key2248, -1), (key2071, -1), (key2304, -1), (key2155, -1), (key2304, 1), (key2066, 1), (key2243, 1), (key2150, 1), (key2243, -1), (key2061, -1)]

def rawRow6730 : Integer.Sparse Key := [(key2150, -1), (key2155, -1), (key2195, 2), (key2150, -1), (key2155, -1), (key2243, 2), (key2248, 2), (key2304, -1), (key2306, -1), (key2195, 2), (key2304, -1), (key2306, -1), (key2061, 1), (key2066, 1), (key2093, -2), (key2061, 1), (key2066, 1), (key2243, -2), (key2255, -2), (key2304, 1), (key2311, 1), (key2093, -2), (key2304, 1), (key2311, 1), (key2061, -1), (key2071, -1), (key2093, 1), (key2096, 1), (key2150, 1), (key2168, 1), (key2195, -1), (key2201, -1), (key2061, -1), (key2071, -1), (key2150, 1), (key2168, 1), (key2093, 1), (key2096, 1), (key2195, -1), (key2201, -1)]

def rawRow6731 : Integer.Sparse Key := [(key2155, -1), (key2150, -1), (key2195, 2), (key2155, -1), (key2150, -1), (key2248, 2), (key2243, 2), (key2306, -1), (key2304, -1), (key2195, 2), (key2306, -1), (key2304, -1), (key2066, 1), (key2061, 1), (key2093, -2), (key2066, 1), (key2061, 1), (key2255, -2), (key2243, -2), (key2311, 1), (key2304, 1), (key2093, -2), (key2311, 1), (key2304, 1), (key2071, -1), (key2061, -1), (key2096, 1), (key2093, 1), (key2168, 1), (key2150, 1), (key2201, -1), (key2195, -1), (key2071, -1), (key2061, -1), (key2168, 1), (key2150, 1), (key2096, 1), (key2093, 1), (key2201, -1), (key2195, -1)]

def rawRow6732 : Integer.Sparse Key := [(key2150, -1), (key2195, -1), (key2155, 2), (key2243, -1), (key2304, -1), (key2150, 2), (key2306, 2), (key2155, -1), (key2248, -1), (key2304, 2), (key2195, -1), (key2306, -1), (key2061, 1), (key2093, 1), (key2066, -2), (key2243, 1), (key2304, 1), (key2061, -2), (key2311, -2), (key2066, 1), (key2255, 1), (key2304, -2), (key2093, 1), (key2311, 1), (key2031, -1), (key2096, -1), (key2036, 1), (key2071, 1), (key2031, 1), (key2201, 1), (key2036, -1), (key2168, -1), (key2150, -1), (key2306, -1), (key2061, 1), (key2311, 1), (key2195, 1), (key2306, 1), (key2093, -1), (key2311, -1)]

def rawRow6733 : Integer.Sparse Key := [(key2195, -1), (key2150, -1), (key2155, 2), (key2304, -1), (key2243, -1), (key2306, 2), (key2150, 2), (key2248, -1), (key2155, -1), (key2304, 2), (key2306, -1), (key2195, -1), (key2093, 1), (key2061, 1), (key2066, -2), (key2304, 1), (key2243, 1), (key2311, -2), (key2061, -2), (key2255, 1), (key2066, 1), (key2304, -2), (key2311, 1), (key2093, 1), (key2096, -1), (key2031, -1), (key2071, 1), (key2036, 1), (key2201, 1), (key2031, 1), (key2168, -1), (key2036, -1), (key2306, -1), (key2150, -1), (key2311, 1), (key2061, 1), (key2306, 1), (key2195, 1), (key2311, -1), (key2093, -1)]

def rawRow6734 : Integer.Sparse Key := [(key2155, -1), (key2195, -1), (key2150, 2), (key2248, -1), (key2306, -1), (key2155, 2), (key2304, 2), (key2150, -1), (key2243, -1), (key2306, 2), (key2195, -1), (key2304, -1), (key2066, 1), (key2093, 1), (key2061, -2), (key2255, 1), (key2311, 1), (key2066, -2), (key2304, -2), (key2061, 1), (key2243, 1), (key2311, -2), (key2093, 1), (key2304, 1), (key2036, -1), (key2093, -1), (key2031, 1), (key2061, 1), (key2036, 1), (key2195, 1), (key2031, -1), (key2150, -1), (key2168, -1), (key2311, -1), (key2071, 1), (key2306, 1), (key2201, 1), (key2311, 1), (key2096, -1), (key2306, -1)]

def rawRow6735 : Integer.Sparse Key := [(key2195, -1), (key2155, -1), (key2150, 2), (key2306, -1), (key2248, -1), (key2304, 2), (key2155, 2), (key2243, -1), (key2150, -1), (key2306, 2), (key2304, -1), (key2195, -1), (key2093, 1), (key2066, 1), (key2061, -2), (key2311, 1), (key2255, 1), (key2304, -2), (key2066, -2), (key2243, 1), (key2061, 1), (key2311, -2), (key2304, 1), (key2093, 1), (key2093, -1), (key2036, -1), (key2061, 1), (key2031, 1), (key2195, 1), (key2036, 1), (key2150, -1), (key2031, -1), (key2311, -1), (key2168, -1), (key2306, 1), (key2071, 1), (key2311, 1), (key2201, 1), (key2306, -1), (key2096, -1)]

def rawRow6736 : Integer.Sparse Key := [(key2243, -1), (key2304, -1), (key2304, 2), (key2150, -1), (key2195, -1), (key2150, 2), (key2306, 2), (key2195, -1), (key2306, -1), (key2155, 2), (key2155, -1), (key2248, -1), (key2243, 1), (key2304, 1), (key2304, -2), (key2061, 1), (key2093, 1), (key2061, -2), (key2311, -2), (key2093, 1), (key2311, 1), (key2066, -2), (key2066, 1), (key2255, 1), (key2150, -1), (key2306, -1), (key2195, 1), (key2306, 1), (key2061, 1), (key2311, 1), (key2093, -1), (key2311, -1), (key2031, -1), (key2096, -1), (key2031, 1), (key2201, 1), (key2036, 1), (key2071, 1), (key2036, -1), (key2168, -1)]

def rawRow6737 : Integer.Sparse Key := [(key2304, -1), (key2243, -1), (key2304, 2), (key2195, -1), (key2150, -1), (key2306, 2), (key2150, 2), (key2306, -1), (key2195, -1), (key2155, 2), (key2248, -1), (key2155, -1), (key2304, 1), (key2243, 1), (key2304, -2), (key2093, 1), (key2061, 1), (key2311, -2), (key2061, -2), (key2311, 1), (key2093, 1), (key2066, -2), (key2255, 1), (key2066, 1), (key2306, -1), (key2150, -1), (key2306, 1), (key2195, 1), (key2311, 1), (key2061, 1), (key2311, -1), (key2093, -1), (key2096, -1), (key2031, -1), (key2201, 1), (key2031, 1), (key2071, 1), (key2036, 1), (key2168, -1), (key2036, -1)]

def rawRow6738 : Integer.Sparse Key := [(key2304, -1), (key2304, -1), (key2243, 2), (key2306, -1), (key2306, -1), (key2195, 2), (key2195, 2), (key2150, -1), (key2150, -1), (key2248, 2), (key2155, -1), (key2155, -1), (key2304, 1), (key2304, 1), (key2243, -2), (key2311, 1), (key2311, 1), (key2093, -2), (key2093, -2), (key2061, 1), (key2061, 1), (key2255, -2), (key2066, 1), (key2066, 1), (key2195, -1), (key2195, -1), (key2150, 1), (key2150, 1), (key2093, 1), (key2093, 1), (key2061, -1), (key2061, -1), (key2201, -1), (key2201, -1), (key2096, 1), (key2096, 1), (key2168, 1), (key2168, 1), (key2071, -1), (key2071, -1)]

def rawRow6739 : Integer.Sparse Key := [(key2248, -1), (key2306, -1), (key2306, 2), (key2155, -1), (key2195, -1), (key2155, 2), (key2304, 2), (key2195, -1), (key2304, -1), (key2150, 2), (key2150, -1), (key2243, -1), (key2255, 1), (key2311, 1), (key2311, -2), (key2066, 1), (key2093, 1), (key2066, -2), (key2304, -2), (key2093, 1), (key2304, 1), (key2061, -2), (key2061, 1), (key2243, 1), (key2168, -1), (key2311, -1), (key2201, 1), (key2311, 1), (key2071, 1), (key2306, 1), (key2096, -1), (key2306, -1), (key2036, -1), (key2093, -1), (key2036, 1), (key2195, 1), (key2031, 1), (key2061, 1), (key2031, -1), (key2150, -1)]

def rawRow6740 : Integer.Sparse Key := [(key2306, -1), (key2248, -1), (key2306, 2), (key2195, -1), (key2155, -1), (key2304, 2), (key2155, 2), (key2304, -1), (key2195, -1), (key2150, 2), (key2243, -1), (key2150, -1), (key2311, 1), (key2255, 1), (key2311, -2), (key2093, 1), (key2066, 1), (key2304, -2), (key2066, -2), (key2304, 1), (key2093, 1), (key2061, -2), (key2243, 1), (key2061, 1), (key2311, -1), (key2168, -1), (key2311, 1), (key2201, 1), (key2306, 1), (key2071, 1), (key2306, -1), (key2096, -1), (key2093, -1), (key2036, -1), (key2195, 1), (key2036, 1), (key2061, 1), (key2031, 1), (key2150, -1), (key2031, -1)]

def rawRow6741 : Integer.Sparse Key := [(key2306, -1), (key2306, -1), (key2248, 2), (key2304, -1), (key2304, -1), (key2195, 2), (key2195, 2), (key2155, -1), (key2155, -1), (key2243, 2), (key2150, -1), (key2150, -1), (key2311, 1), (key2311, 1), (key2255, -2), (key2304, 1), (key2304, 1), (key2093, -2), (key2093, -2), (key2066, 1), (key2066, 1), (key2243, -2), (key2061, 1), (key2061, 1), (key2201, -1), (key2201, -1), (key2168, 1), (key2168, 1), (key2096, 1), (key2096, 1), (key2071, -1), (key2071, -1), (key2195, -1), (key2195, -1), (key2093, 1), (key2093, 1), (key2150, 1), (key2150, 1), (key2061, -1), (key2061, -1)]

def rawRow6742 : Integer.Sparse Key := [(key2168, -1), (key2168, -1), (key2201, 2), (key2168, -1), (key2168, -1), (key2255, 2), (key2255, 2), (key2311, -1), (key2311, -1), (key2201, 2), (key2311, -1), (key2311, -1), (key2071, 1), (key2071, 1), (key2096, -2), (key2071, 1), (key2071, 1), (key2248, -2), (key2248, -2), (key2306, 1), (key2306, 1), (key2096, -2), (key2306, 1), (key2306, 1), (key2066, -1), (key2066, -1), (key2093, 1), (key2093, 1), (key2155, 1), (key2155, 1), (key2195, -1), (key2195, -1), (key2066, -1), (key2066, -1), (key2155, 1), (key2155, 1), (key2093, 1), (key2093, 1), (key2195, -1), (key2195, -1)]

def rawRow6743 : Integer.Sparse Key := [(key2168, -1), (key2201, -1), (key2168, 2), (key2255, -1), (key2311, -1), (key2168, 2), (key2311, 2), (key2168, -1), (key2255, -1), (key2311, 2), (key2201, -1), (key2311, -1), (key2071, 1), (key2096, 1), (key2071, -2), (key2248, 1), (key2306, 1), (key2071, -2), (key2306, -2), (key2071, 1), (key2248, 1), (key2306, -2), (key2096, 1), (key2306, 1), (key2036, -1), (key2093, -1), (key2036, 1), (key2066, 1), (key2036, 1), (key2195, 1), (key2036, -1), (key2155, -1), (key2155, -1), (key2304, -1), (key2066, 1), (key2304, 1), (key2195, 1), (key2304, 1), (key2093, -1), (key2304, -1)]

def rawRow6744 : Integer.Sparse Key := [(key2201, -1), (key2168, -1), (key2168, 2), (key2311, -1), (key2255, -1), (key2311, 2), (key2168, 2), (key2255, -1), (key2168, -1), (key2311, 2), (key2311, -1), (key2201, -1), (key2096, 1), (key2071, 1), (key2071, -2), (key2306, 1), (key2248, 1), (key2306, -2), (key2071, -2), (key2248, 1), (key2071, 1), (key2306, -2), (key2306, 1), (key2096, 1), (key2093, -1), (key2036, -1), (key2066, 1), (key2036, 1), (key2195, 1), (key2036, 1), (key2155, -1), (key2036, -1), (key2304, -1), (key2155, -1), (key2304, 1), (key2066, 1), (key2304, 1), (key2195, 1), (key2304, -1), (key2093, -1)]

def rawRow6745 : Integer.Sparse Key := [(key2255, -1), (key2311, -1), (key2311, 2), (key2168, -1), (key2201, -1), (key2168, 2), (key2311, 2), (key2201, -1), (key2311, -1), (key2168, 2), (key2168, -1), (key2255, -1), (key2248, 1), (key2306, 1), (key2306, -2), (key2071, 1), (key2096, 1), (key2071, -2), (key2306, -2), (key2096, 1), (key2306, 1), (key2071, -2), (key2071, 1), (key2248, 1), (key2155, -1), (key2304, -1), (key2195, 1), (key2304, 1), (key2066, 1), (key2304, 1), (key2093, -1), (key2304, -1), (key2036, -1), (key2093, -1), (key2036, 1), (key2195, 1), (key2036, 1), (key2066, 1), (key2036, -1), (key2155, -1)]

def rawRow6746 : Integer.Sparse Key := [(key2311, -1), (key2255, -1), (key2311, 2), (key2201, -1), (key2168, -1), (key2311, 2), (key2168, 2), (key2311, -1), (key2201, -1), (key2168, 2), (key2255, -1), (key2168, -1), (key2306, 1), (key2248, 1), (key2306, -2), (key2096, 1), (key2071, 1), (key2306, -2), (key2071, -2), (key2306, 1), (key2096, 1), (key2071, -2), (key2248, 1), (key2071, 1), (key2304, -1), (key2155, -1), (key2304, 1), (key2195, 1), (key2304, 1), (key2066, 1), (key2304, -1), (key2093, -1), (key2093, -1), (key2036, -1), (key2195, 1), (key2036, 1), (key2066, 1), (key2036, 1), (key2155, -1), (key2036, -1)]

def rawRow6747 : Integer.Sparse Key := [(key2311, -1), (key2311, -1), (key2255, 2), (key2311, -1), (key2311, -1), (key2201, 2), (key2201, 2), (key2168, -1), (key2168, -1), (key2255, 2), (key2168, -1), (key2168, -1), (key2306, 1), (key2306, 1), (key2248, -2), (key2306, 1), (key2306, 1), (key2096, -2), (key2096, -2), (key2071, 1), (key2071, 1), (key2248, -2), (key2071, 1), (key2071, 1), (key2195, -1), (key2195, -1), (key2155, 1), (key2155, 1), (key2093, 1), (key2093, 1), (key2066, -1), (key2066, -1), (key2195, -1), (key2195, -1), (key2093, 1), (key2093, 1), (key2155, 1), (key2155, 1), (key2066, -1), (key2066, -1)]

def rawRow6748 : Integer.Sparse Key := [(key312, -1), (key313, -1), (key313, 2), (key324, -1), (key325, -1), (key324, 2), (key339, 2), (key325, -1), (key339, -1), (key329, 2), (key329, -1), (key341, -1), (key312, 1), (key313, 1), (key313, -2), (key794, 1), (key796, 1), (key794, -2), (key815, -2), (key796, 1), (key815, 1), (key832, -2), (key832, 1), (key841, 1), (key728, -1), (key736, -1), (key730, 1), (key736, 1), (key794, 1), (key815, 1), (key796, -1), (key815, -1), (key864, -1), (key870, -1), (key864, 1), (key880, 1), (key926, 1), (key929, 1), (key926, -1), (key936, -1)]

def rawRow6749 : Integer.Sparse Key := [(key313, -1), (key312, -1), (key313, 2), (key325, -1), (key324, -1), (key339, 2), (key324, 2), (key339, -1), (key325, -1), (key329, 2), (key341, -1), (key329, -1), (key313, 1), (key312, 1), (key313, -2), (key796, 1), (key794, 1), (key815, -2), (key794, -2), (key815, 1), (key796, 1), (key832, -2), (key841, 1), (key832, 1), (key736, -1), (key728, -1), (key736, 1), (key730, 1), (key815, 1), (key794, 1), (key815, -1), (key796, -1), (key870, -1), (key864, -1), (key880, 1), (key864, 1), (key929, 1), (key926, 1), (key936, -1), (key926, -1)]

def rawRow6750 : Integer.Sparse Key := [(key313, -1), (key313, -1), (key312, 2), (key339, -1), (key339, -1), (key325, 2), (key325, 2), (key324, -1), (key324, -1), (key341, 2), (key329, -1), (key329, -1), (key313, 1), (key313, 1), (key312, -2), (key815, 1), (key815, 1), (key796, -2), (key796, -2), (key794, 1), (key794, 1), (key841, -2), (key832, 1), (key832, 1), (key730, -1), (key730, -1), (key728, 1), (key728, 1), (key796, 1), (key796, 1), (key794, -1), (key794, -1), (key880, -1), (key880, -1), (key870, 1), (key870, 1), (key936, 1), (key936, 1), (key929, -1), (key929, -1)]

def rawRow6751 : Integer.Sparse Key := [(key324, -1), (key325, -1), (key329, 2), (key312, -1), (key313, -1), (key324, 2), (key339, 2), (key329, -1), (key341, -1), (key313, 2), (key325, -1), (key339, -1), (key414, 1), (key415, 1), (key419, -2), (key312, 1), (key313, 1), (key794, -2), (key815, -2), (key832, 1), (key841, 1), (key727, -2), (key796, 1), (key815, 1), (key864, -1), (key870, -1), (key926, 1), (key929, 1), (key864, 1), (key880, 1), (key926, -1), (key936, -1), (key728, -1), (key736, -1), (key794, 1), (key815, 1), (key730, 1), (key736, 1), (key796, -1), (key815, -1)]

def rawRow6752 : Integer.Sparse Key := [(key325, -1), (key324, -1), (key329, 2), (key313, -1), (key312, -1), (key339, 2), (key324, 2), (key341, -1), (key329, -1), (key313, 2), (key339, -1), (key325, -1), (key415, 1), (key414, 1), (key419, -2), (key313, 1), (key312, 1), (key815, -2), (key794, -2), (key841, 1), (key832, 1), (key727, -2), (key815, 1), (key796, 1), (key870, -1), (key864, -1), (key929, 1), (key926, 1), (key880, 1), (key864, 1), (key936, -1), (key926, -1), (key736, -1), (key728, -1), (key815, 1), (key794, 1), (key736, 1), (key730, 1), (key815, -1), (key796, -1)]

def rawRow6753 : Integer.Sparse Key := [(key324, -1), (key329, -1), (key325, 2), (key324, -1), (key329, -1), (key312, 2), (key341, 2), (key313, -1), (key339, -1), (key325, 2), (key313, -1), (key339, -1), (key414, 1), (key419, 1), (key415, -2), (key414, 1), (key419, 1), (key312, -2), (key841, -2), (key727, 1), (key815, 1), (key796, -2), (key727, 1), (key815, 1), (key794, -1), (key929, -1), (key796, 1), (key870, 1), (key728, 1), (key936, 1), (key730, -1), (key880, -1), (key794, -1), (key929, -1), (key728, 1), (key936, 1), (key796, 1), (key870, 1), (key730, -1), (key880, -1)]

def rawRow6754 : Integer.Sparse Key := [(key329, -1), (key324, -1), (key325, 2), (key329, -1), (key324, -1), (key341, 2), (key312, 2), (key339, -1), (key313, -1), (key325, 2), (key339, -1), (key313, -1), (key419, 1), (key414, 1), (key415, -2), (key419, 1), (key414, 1), (key584, -2), (key725, -2), (key815, 1), (key727, 1), (key796, -2), (key815, 1), (key727, 1), (key929, -1), (key794, -1), (key870, 1), (key796, 1), (key936, 1), (key728, 1), (key880, -1), (key730, -1), (key929, -1), (key794, -1), (key936, 1), (key728, 1), (key870, 1), (key796, 1), (key880, -1), (key730, -1)]

def rawRow6755 : Integer.Sparse Key := [(key325, -1), (key329, -1), (key324, 2), (key339, -1), (key341, -1), (key313, 2), (key329, 2), (key312, -1), (key324, -1), (key339, 2), (key313, -1), (key325, -1), (key415, 1), (key419, 1), (key414, -2), (key582, 1), (key584, 1), (key313, -2), (key419, -2), (key725, 1), (key794, 1), (key815, -2), (key727, 1), (key796, 1), (key796, -1), (key926, -1), (key794, 1), (key864, 1), (key730, 1), (key926, 1), (key728, -1), (key864, -1), (key815, -1), (key936, -1), (key736, 1), (key929, 1), (key815, 1), (key880, 1), (key736, -1), (key870, -1)]

def rawRow6756 : Integer.Sparse Key := [(key329, -1), (key325, -1), (key324, 2), (key341, -1), (key339, -1), (key329, 2), (key313, 2), (key324, -1), (key312, -1), (key339, 2), (key325, -1), (key313, -1), (key419, 1), (key415, 1), (key414, -2), (key584, 1), (key582, 1), (key419, -2), (key313, -2), (key794, 1), (key725, 1), (key815, -2), (key796, 1), (key727, 1), (key926, -1), (key796, -1), (key864, 1), (key794, 1), (key926, 1), (key730, 1), (key864, -1), (key728, -1), (key936, -1), (key815, -1), (key929, 1), (key736, 1), (key880, 1), (key815, 1), (key870, -1), (key736, -1)]

def rawRow6757 : Integer.Sparse Key := [(key339, -1), (key339, -1), (key341, 2), (key313, -1), (key313, -1), (key325, 2), (key325, 2), (key329, -1), (key329, -1), (key312, 2), (key324, -1), (key324, -1), (key582, 1), (key582, 1), (key584, -2), (key313, 1), (key313, 1), (key415, -2), (key415, -2), (key419, 1), (key419, 1), (key725, -2), (key794, 1), (key794, 1), (key880, -1), (key880, -1), (key936, 1), (key936, 1), (key870, 1), (key870, 1), (key929, -1), (key929, -1), (key730, -1), (key730, -1), (key796, 1), (key796, 1), (key728, 1), (key728, 1), (key794, -1), (key794, -1)]

def rawRow6758 : Integer.Sparse Key := [(key339, -1), (key341, -1), (key339, 2), (key325, -1), (key329, -1), (key313, 2), (key329, 2), (key313, -1), (key325, -1), (key324, 2), (key312, -1), (key324, -1), (key582, 1), (key584, 1), (key582, -2), (key415, 1), (key419, 1), (key313, -2), (key419, -2), (key313, 1), (key415, 1), (key794, -2), (key725, 1), (key794, 1), (key815, -1), (key936, -1), (key815, 1), (key880, 1), (key736, 1), (key929, 1), (key736, -1), (key870, -1), (key796, -1), (key926, -1), (key730, 1), (key926, 1), (key794, 1), (key864, 1), (key728, -1), (key864, -1)]

def rawRow6759 : Integer.Sparse Key := [(key341, -1), (key339, -1), (key339, 2), (key329, -1), (key325, -1), (key329, 2), (key313, 2), (key325, -1), (key313, -1), (key324, 2), (key324, -1), (key312, -1), (key584, 1), (key582, 1), (key582, -2), (key419, 1), (key415, 1), (key419, -2), (key313, -2), (key415, 1), (key313, 1), (key794, -2), (key794, 1), (key725, 1), (key936, -1), (key815, -1), (key880, 1), (key815, 1), (key929, 1), (key736, 1), (key870, -1), (key736, -1), (key926, -1), (key796, -1), (key926, 1), (key730, 1), (key864, 1), (key794, 1), (key864, -1), (key728, -1)]

def rawRow6760 : Integer.Sparse Key := [(key414, -1), (key415, -1), (key419, 2), (key414, -1), (key415, -1), (key447, 2), (key474, 2), (key451, -1), (key476, -1), (key419, 2), (key451, -1), (key476, -1), (key324, 1), (key325, 1), (key329, -2), (key324, 1), (key325, 1), (key447, -2), (key600, -2), (key451, 1), (key602, 1), (key329, -2), (key451, 1), (key602, 1), (key324, -1), (key339, -1), (key329, 1), (key341, 1), (key794, 1), (key815, 1), (key832, -1), (key841, -1), (key728, -1), (key736, -1), (key794, 1), (key815, 1), (key748, 1), (key752, 1), (key832, -1), (key841, -1)]

def rawRow6761 : Integer.Sparse Key := [(key415, -1), (key414, -1), (key419, 2), (key415, -1), (key414, -1), (key474, 2), (key447, 2), (key476, -1), (key451, -1), (key419, 2), (key476, -1), (key451, -1), (key325, 1), (key324, 1), (key329, -2), (key325, 1), (key324, 1), (key600, -2), (key447, -2), (key602, 1), (key451, 1), (key329, -2), (key602, 1), (key451, 1), (key339, -1), (key324, -1), (key341, 1), (key329, 1), (key815, 1), (key794, 1), (key841, -1), (key832, -1), (key736, -1), (key728, -1), (key815, 1), (key794, 1), (key752, 1), (key748, 1), (key841, -1), (key832, -1)]

def rawRow6762 : Integer.Sparse Key := [(key414, -1), (key419, -1), (key415, 2), (key447, -1), (key451, -1), (key414, 2), (key476, 2), (key415, -1), (key474, -1), (key451, 2), (key419, -1), (key476, -1), (key324, 1), (key329, 1), (key325, -2), (key447, 1), (key451, 1), (key324, -2), (key602, -2), (key325, 1), (key600, 1), (key451, -2), (key329, 1), (key602, 1), (key312, -1), (key341, -1), (key313, 1), (key339, 1), (key312, 1), (key841, 1), (key727, -1), (key815, -1), (key794, -1), (key929, -1), (key728, 1), (key936, 1), (key832, 1), (key929, 1), (key748, -1), (key936, -1)]

def rawRow6763 : Integer.Sparse Key := [(key419, -1), (key414, -1), (key415, 2), (key451, -1), (key447, -1), (key476, 2), (key414, 2), (key474, -1), (key415, -1), (key451, 2), (key476, -1), (key419, -1), (key329, 1), (key324, 1), (key325, -2), (key451, 1), (key447, 1), (key602, -2), (key324, -2), (key600, 1), (key325, 1), (key451, -2), (key602, 1), (key329, 1), (key341, -1), (key312, -1), (key339, 1), (key313, 1), (key584, 1), (key725, 1), (key815, -1), (key727, -1), (key929, -1), (key794, -1), (key936, 1), (key728, 1), (key929, 1), (key832, 1), (key936, -1), (key748, -1)]

def rawRow6764 : Integer.Sparse Key := [(key415, -1), (key419, -1), (key414, 2), (key474, -1), (key476, -1), (key415, 2), (key451, 2), (key414, -1), (key447, -1), (key476, 2), (key419, -1), (key451, -1), (key325, 1), (key329, 1), (key324, -2), (key600, 1), (key602, 1), (key325, -2), (key451, -2), (key324, 1), (key447, 1), (key602, -2), (key329, 1), (key451, 1), (key313, -1), (key329, -1), (key312, 1), (key324, 1), (key313, 1), (key419, 1), (key725, -1), (key794, -1), (key815, -1), (key936, -1), (key736, 1), (key929, 1), (key841, 1), (key936, 1), (key752, -1), (key929, -1)]

def rawRow6765 : Integer.Sparse Key := [(key419, -1), (key415, -1), (key414, 2), (key476, -1), (key474, -1), (key451, 2), (key415, 2), (key447, -1), (key414, -1), (key476, 2), (key451, -1), (key419, -1), (key329, 1), (key325, 1), (key324, -2), (key602, 1), (key600, 1), (key451, -2), (key325, -2), (key447, 1), (key324, 1), (key602, -2), (key451, 1), (key329, 1), (key329, -1), (key313, -1), (key324, 1), (key312, 1), (key419, 1), (key313, 1), (key794, -1), (key725, -1), (key936, -1), (key815, -1), (key929, 1), (key736, 1), (key936, 1), (key841, 1), (key929, -1), (key752, -1)]

def rawRow6766 : Integer.Sparse Key := [(key447, -1), (key451, -1), (key451, 2), (key414, -1), (key419, -1), (key414, 2), (key476, 2), (key419, -1), (key476, -1), (key415, 2), (key415, -1), (key474, -1), (key447, 1), (key451, 1), (key451, -2), (key324, 1), (key329, 1), (key324, -2), (key602, -2), (key329, 1), (key602, 1), (key325, -2), (key325, 1), (key600, 1), (key414, -1), (key476, -1), (key419, 1), (key476, 1), (key324, 1), (key602, 1), (key329, -1), (key602, -1), (key312, -1), (key341, -1), (key312, 1), (key841, 1), (key727, 1), (key736, 1), (key727, -1), (key815, -1)]

def rawRow6767 : Integer.Sparse Key := [(key451, -1), (key447, -1), (key451, 2), (key419, -1), (key414, -1), (key476, 2), (key414, 2), (key476, -1), (key419, -1), (key415, 2), (key474, -1), (key415, -1), (key451, 1), (key447, 1), (key451, -2), (key329, 1), (key324, 1), (key602, -2), (key324, -2), (key602, 1), (key329, 1), (key325, -2), (key600, 1), (key325, 1), (key476, -1), (key414, -1), (key476, 1), (key419, 1), (key602, 1), (key324, 1), (key602, -1), (key329, -1), (key341, -1), (key312, -1), (key584, 1), (key725, 1), (key736, 1), (key727, 1), (key815, -1), (key727, -1)]

def rawRow6768 : Integer.Sparse Key := [(key451, -1), (key451, -1), (key447, 2), (key476, -1), (key476, -1), (key419, 2), (key419, 2), (key414, -1), (key414, -1), (key474, 2), (key415, -1), (key415, -1), (key451, 1), (key451, 1), (key447, -2), (key602, 1), (key602, 1), (key329, -2), (key329, -2), (key324, 1), (key324, 1), (key600, -2), (key325, 1), (key325, 1), (key419, -1), (key419, -1), (key414, 1), (key414, 1), (key329, 1), (key329, 1), (key324, -1), (key324, -1), (key584, -1), (key584, -1), (key341, 1), (key341, 1), (key815, 1), (key815, 1), (key736, -1), (key736, -1)]

def rawRow6769 : Integer.Sparse Key := [(key474, -1), (key476, -1), (key476, 2), (key415, -1), (key419, -1), (key415, 2), (key451, 2), (key419, -1), (key451, -1), (key414, 2), (key414, -1), (key447, -1), (key600, 1), (key602, 1), (key602, -2), (key325, 1), (key329, 1), (key325, -2), (key451, -2), (key329, 1), (key451, 1), (key324, -2), (key324, 1), (key447, 1), (key582, -1), (key602, -1), (key584, 1), (key602, 1), (key339, 1), (key476, 1), (key341, -1), (key476, -1), (key313, -1), (key329, -1), (key313, 1), (key419, 1), (key725, 1), (key728, 1), (key725, -1), (key794, -1)]

def rawRow6770 : Integer.Sparse Key := [(key476, -1), (key474, -1), (key476, 2), (key419, -1), (key415, -1), (key451, 2), (key415, 2), (key451, -1), (key419, -1), (key414, 2), (key447, -1), (key414, -1), (key602, 1), (key600, 1), (key602, -2), (key329, 1), (key325, 1), (key451, -2), (key325, -2), (key451, 1), (key329, 1), (key324, -2), (key447, 1), (key324, 1), (key602, -1), (key582, -1), (key602, 1), (key584, 1), (key476, 1), (key339, 1), (key476, -1), (key341, -1), (key329, -1), (key313, -1), (key419, 1), (key313, 1), (key728, 1), (key725, 1), (key794, -1), (key725, -1)]

def rawRow6771 : Integer.Sparse Key := [(key476, -1), (key476, -1), (key474, 2), (key451, -1), (key451, -1), (key419, 2), (key419, 2), (key415, -1), (key415, -1), (key447, 2), (key414, -1), (key414, -1), (key602, 1), (key602, 1), (key600, -2), (key451, 1), (key451, 1), (key329, -2), (key329, -2), (key325, 1), (key325, 1), (key447, -2), (key324, 1), (key324, 1), (key584, -1), (key584, -1), (key582, 1), (key582, 1), (key341, 1), (key341, 1), (key339, -1), (key339, -1), (key419, -1), (key419, -1), (key329, 1), (key329, 1), (key794, 1), (key794, 1), (key728, -1), (key728, -1)]

def rawRow6772 : Integer.Sparse Key := [(key582, -1), (key582, -1), (key584, 2), (key582, -1), (key582, -1), (key600, 2), (key600, 2), (key602, -1), (key602, -1), (key584, 2), (key602, -1), (key602, -1), (key339, 1), (key339, 1), (key341, -2), (key339, 1), (key339, 1), (key474, -2), (key474, -2), (key476, 1), (key476, 1), (key341, -2), (key476, 1), (key476, 1), (key325, -1), (key325, -1), (key329, 1), (key329, 1), (key415, 1), (key415, 1), (key419, -1), (key419, -1), (key325, -1), (key325, -1), (key415, 1), (key415, 1), (key329, 1), (key329, 1), (key419, -1), (key419, -1)]

def rawRow6773 : Integer.Sparse Key := [(key582, -1), (key584, -1), (key582, 2), (key600, -1), (key602, -1), (key582, 2), (key602, 2), (key582, -1), (key600, -1), (key602, 2), (key584, -1), (key602, -1), (key339, 1), (key341, 1), (key339, -2), (key474, 1), (key476, 1), (key339, -2), (key476, -2), (key339, 1), (key474, 1), (key476, -2), (key341, 1), (key476, 1), (key313, -1), (key329, -1), (key313, 1), (key325, 1), (key313, 1), (key419, 1), (key313, -1), (key415, -1), (key415, -1), (key451, -1), (key325, 1), (key451, 1), (key419, 1), (key451, 1), (key329, -1), (key451, -1)]

def rawRow6774 : Integer.Sparse Key := [(key584, -1), (key582, -1), (key582, 2), (key602, -1), (key600, -1), (key602, 2), (key582, 2), (key600, -1), (key582, -1), (key602, 2), (key602, -1), (key584, -1), (key341, 1), (key339, 1), (key339, -2), (key476, 1), (key474, 1), (key476, -2), (key339, -2), (key474, 1), (key339, 1), (key476, -2), (key476, 1), (key341, 1), (key329, -1), (key313, -1), (key325, 1), (key313, 1), (key419, 1), (key313, 1), (key415, -1), (key313, -1), (key451, -1), (key415, -1), (key451, 1), (key325, 1), (key451, 1), (key419, 1), (key451, -1), (key329, -1)]

def rawRow6775 : Integer.Sparse Key := [(key600, -1), (key602, -1), (key602, 2), (key582, -1), (key584, -1), (key582, 2), (key602, 2), (key584, -1), (key602, -1), (key582, 2), (key582, -1), (key600, -1), (key474, 1), (key476, 1), (key476, -2), (key339, 1), (key341, 1), (key339, -2), (key476, -2), (key341, 1), (key476, 1), (key339, -2), (key339, 1), (key474, 1), (key415, -1), (key451, -1), (key419, 1), (key451, 1), (key325, 1), (key451, 1), (key329, -1), (key451, -1), (key313, -1), (key329, -1), (key313, 1), (key419, 1), (key313, 1), (key325, 1), (key313, -1), (key415, -1)]

def rawRow6776 : Integer.Sparse Key := [(key602, -1), (key600, -1), (key602, 2), (key584, -1), (key582, -1), (key602, 2), (key582, 2), (key602, -1), (key584, -1), (key582, 2), (key600, -1), (key582, -1), (key476, 1), (key474, 1), (key476, -2), (key341, 1), (key339, 1), (key476, -2), (key339, -2), (key476, 1), (key341, 1), (key339, -2), (key474, 1), (key339, 1), (key451, -1), (key415, -1), (key451, 1), (key419, 1), (key451, 1), (key325, 1), (key451, -1), (key329, -1), (key329, -1), (key313, -1), (key419, 1), (key313, 1), (key325, 1), (key313, 1), (key415, -1), (key313, -1)]

def rawRow6777 : Integer.Sparse Key := [(key602, -1), (key602, -1), (key600, 2), (key602, -1), (key602, -1), (key584, 2), (key584, 2), (key582, -1), (key582, -1), (key600, 2), (key582, -1), (key582, -1), (key476, 1), (key476, 1), (key474, -2), (key476, 1), (key476, 1), (key341, -2), (key341, -2), (key339, 1), (key339, 1), (key474, -2), (key339, 1), (key339, 1), (key419, -1), (key419, -1), (key415, 1), (key415, 1), (key329, 1), (key329, 1), (key325, -1), (key325, -1), (key419, -1), (key419, -1), (key329, 1), (key329, 1), (key415, 1), (key415, 1), (key325, -1), (key325, -1)]

def rawRow6778 : Integer.Sparse Key := [(key2031, -1), (key2034, -1), (key2034, 2), (key2061, -1), (key2064, -1), (key2061, 2), (key2070, 2), (key2064, -1), (key2070, -1), (key2080, 2), (key2080, -1), (key2086, -1), (key2031, 1), (key2034, 1), (key2034, -2), (key2150, 1), (key2153, 1), (key2150, -2), (key2167, -2), (key2153, 1), (key2167, 1), (key2177, -2), (key2177, 1), (key2188, 1), (key2061, -1), (key2070, -1), (key2064, 1), (key2070, 1), (key2150, 1), (key2167, 1), (key2153, -1), (key2167, -1), (key2243, -1), (key2247, -1), (key2243, 1), (key2254, 1), (key2277, 1), (key2280, 1), (key2277, -1), (key2288, -1)]

def rawRow6779 : Integer.Sparse Key := [(key2034, -1), (key2031, -1), (key2034, 2), (key2064, -1), (key2061, -1), (key2070, 2), (key2061, 2), (key2070, -1), (key2064, -1), (key2080, 2), (key2086, -1), (key2080, -1), (key2034, 1), (key2031, 1), (key2034, -2), (key2153, 1), (key2150, 1), (key2167, -2), (key2150, -2), (key2167, 1), (key2153, 1), (key2177, -2), (key2188, 1), (key2177, 1), (key2070, -1), (key2061, -1), (key2070, 1), (key2064, 1), (key2167, 1), (key2150, 1), (key2167, -1), (key2153, -1), (key2247, -1), (key2243, -1), (key2254, 1), (key2243, 1), (key2280, 1), (key2277, 1), (key2288, -1), (key2277, -1)]

def rawRow6780 : Integer.Sparse Key := [(key2034, -1), (key2034, -1), (key2031, 2), (key2070, -1), (key2070, -1), (key2064, 2), (key2064, 2), (key2061, -1), (key2061, -1), (key2086, 2), (key2080, -1), (key2080, -1), (key2034, 1), (key2034, 1), (key2031, -2), (key2167, 1), (key2167, 1), (key2153, -2), (key2153, -2), (key2150, 1), (key2150, 1), (key2188, -2), (key2177, 1), (key2177, 1), (key2064, -1), (key2064, -1), (key2061, 1), (key2061, 1), (key2153, 1), (key2153, 1), (key2150, -1), (key2150, -1), (key2254, -1), (key2254, -1), (key2247, 1), (key2247, 1), (key2288, 1), (key2288, 1), (key2280, -1), (key2280, -1)]

def rawRow6781 : Integer.Sparse Key := [(key2061, -1), (key2064, -1), (key2080, 2), (key2031, -1), (key2034, -1), (key2061, 2), (key2070, 2), (key2080, -1), (key2086, -1), (key2034, 2), (key2064, -1), (key2070, -1), (key2150, 1), (key2153, 1), (key2177, -2), (key2031, 1), (key2034, 1), (key2150, -2), (key2167, -2), (key2177, 1), (key2188, 1), (key2034, -2), (key2153, 1), (key2167, 1), (key2243, -1), (key2247, -1), (key2277, 1), (key2280, 1), (key2243, 1), (key2254, 1), (key2277, -1), (key2288, -1), (key2061, -1), (key2070, -1), (key2150, 1), (key2167, 1), (key2064, 1), (key2070, 1), (key2153, -1), (key2167, -1)]

def rawRow6782 : Integer.Sparse Key := [(key2064, -1), (key2061, -1), (key2080, 2), (key2034, -1), (key2031, -1), (key2070, 2), (key2061, 2), (key2086, -1), (key2080, -1), (key2034, 2), (key2070, -1), (key2064, -1), (key2153, 1), (key2150, 1), (key2177, -2), (key2034, 1), (key2031, 1), (key2167, -2), (key2150, -2), (key2188, 1), (key2177, 1), (key2034, -2), (key2167, 1), (key2153, 1), (key2247, -1), (key2243, -1), (key2280, 1), (key2277, 1), (key2254, 1), (key2243, 1), (key2288, -1), (key2277, -1), (key2070, -1), (key2061, -1), (key2167, 1), (key2150, 1), (key2070, 1), (key2064, 1), (key2167, -1), (key2153, -1)]

def rawRow6783 : Integer.Sparse Key := [(key2061, -1), (key2080, -1), (key2064, 2), (key2061, -1), (key2080, -1), (key2031, 2), (key2086, 2), (key2034, -1), (key2070, -1), (key2064, 2), (key2034, -1), (key2070, -1), (key2150, 1), (key2177, 1), (key2153, -2), (key2150, 1), (key2177, 1), (key2031, -2), (key2188, -2), (key2034, 1), (key2167, 1), (key2153, -2), (key2034, 1), (key2167, 1), (key2150, -1), (key2280, -1), (key2153, 1), (key2247, 1), (key2061, 1), (key2288, 1), (key2064, -1), (key2254, -1), (key2150, -1), (key2280, -1), (key2061, 1), (key2288, 1), (key2153, 1), (key2247, 1), (key2064, -1), (key2254, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6784 : Integer.Sparse Key := [(key2080, -1), (key2061, -1), (key2064, 2), (key2080, -1), (key2061, -1), (key2086, 2), (key2031, 2), (key2070, -1), (key2034, -1), (key2064, 2), (key2070, -1), (key2034, -1), (key2177, 1), (key2150, 1), (key2153, -2), (key2177, 1), (key2150, 1), (key2188, -2), (key2031, -2), (key2167, 1), (key2034, 1), (key2153, -2), (key2167, 1), (key2034, 1), (key2280, -1), (key2150, -1), (key2247, 1), (key2153, 1), (key2288, 1), (key2061, 1), (key2254, -1), (key2064, -1), (key2280, -1), (key2150, -1), (key2288, 1), (key2061, 1), (key2247, 1), (key2153, 1), (key2254, -1), (key2064, -1)]

def rawRow6785 : Integer.Sparse Key := [(key2064, -1), (key2080, -1), (key2061, 2), (key2070, -1), (key2086, -1), (key2034, 2), (key2080, 2), (key2031, -1), (key2061, -1), (key2070, 2), (key2034, -1), (key2064, -1), (key2153, 1), (key2177, 1), (key2150, -2), (key2167, 1), (key2188, 1), (key2034, -2), (key2177, -2), (key2031, 1), (key2150, 1), (key2167, -2), (key2034, 1), (key2153, 1), (key2153, -1), (key2277, -1), (key2150, 1), (key2243, 1), (key2064, 1), (key2277, 1), (key2061, -1), (key2243, -1), (key2167, -1), (key2288, -1), (key2070, 1), (key2280, 1), (key2167, 1), (key2254, 1), (key2070, -1), (key2247, -1)]

def rawRow6786 : Integer.Sparse Key := [(key2080, -1), (key2064, -1), (key2061, 2), (key2086, -1), (key2070, -1), (key2080, 2), (key2034, 2), (key2061, -1), (key2031, -1), (key2070, 2), (key2064, -1), (key2034, -1), (key2177, 1), (key2153, 1), (key2150, -2), (key2188, 1), (key2167, 1), (key2177, -2), (key2034, -2), (key2150, 1), (key2031, 1), (key2167, -2), (key2153, 1), (key2034, 1), (key2277, -1), (key2153, -1), (key2243, 1), (key2150, 1), (key2277, 1), (key2064, 1), (key2243, -1), (key2061, -1), (key2288, -1), (key2167, -1), (key2280, 1), (key2070, 1), (key2254, 1), (key2167, 1), (key2247, -1), (key2070, -1)]

def rawRow6787 : Integer.Sparse Key := [(key2070, -1), (key2070, -1), (key2086, 2), (key2034, -1), (key2034, -1), (key2064, 2), (key2064, 2), (key2080, -1), (key2080, -1), (key2031, 2), (key2061, -1), (key2061, -1), (key2167, 1), (key2167, 1), (key2188, -2), (key2034, 1), (key2034, 1), (key2153, -2), (key2153, -2), (key2177, 1), (key2177, 1), (key2031, -2), (key2150, 1), (key2150, 1), (key2254, -1), (key2254, -1), (key2288, 1), (key2288, 1), (key2247, 1), (key2247, 1), (key2280, -1), (key2280, -1), (key2064, -1), (key2064, -1), (key2153, 1), (key2153, 1), (key2061, 1), (key2061, 1), (key2150, -1), (key2150, -1)]

def rawRow6788 : Integer.Sparse Key := [(key2070, -1), (key2086, -1), (key2070, 2), (key2064, -1), (key2080, -1), (key2034, 2), (key2080, 2), (key2034, -1), (key2064, -1), (key2061, 2), (key2031, -1), (key2061, -1), (key2167, 1), (key2188, 1), (key2167, -2), (key2153, 1), (key2177, 1), (key2034, -2), (key2177, -2), (key2034, 1), (key2153, 1), (key2150, -2), (key2031, 1), (key2150, 1), (key2167, -1), (key2288, -1), (key2167, 1), (key2254, 1), (key2070, 1), (key2280, 1), (key2070, -1), (key2247, -1), (key2153, -1), (key2277, -1), (key2064, 1), (key2277, 1), (key2150, 1), (key2243, 1), (key2061, -1), (key2243, -1)]

def rawRow6789 : Integer.Sparse Key := [(key2086, -1), (key2070, -1), (key2070, 2), (key2080, -1), (key2064, -1), (key2080, 2), (key2034, 2), (key2064, -1), (key2034, -1), (key2061, 2), (key2061, -1), (key2031, -1), (key2188, 1), (key2167, 1), (key2167, -2), (key2177, 1), (key2153, 1), (key2177, -2), (key2034, -2), (key2153, 1), (key2034, 1), (key2150, -2), (key2150, 1), (key2031, 1), (key2288, -1), (key2167, -1), (key2254, 1), (key2167, 1), (key2280, 1), (key2070, 1), (key2247, -1), (key2070, -1), (key2277, -1), (key2153, -1), (key2277, 1), (key2064, 1), (key2243, 1), (key2150, 1), (key2243, -1), (key2061, -1)]

def rawRow6790 : Integer.Sparse Key := [(key2150, -1), (key2153, -1), (key2177, 2), (key2150, -1), (key2153, -1), (key2243, 2), (key2247, 2), (key2277, -1), (key2280, -1), (key2177, 2), (key2277, -1), (key2280, -1), (key2061, 1), (key2064, 1), (key2080, -2), (key2061, 1), (key2064, 1), (key2243, -2), (key2254, -2), (key2277, 1), (key2288, 1), (key2080, -2), (key2277, 1), (key2288, 1), (key2061, -1), (key2070, -1), (key2080, 1), (key2086, 1), (key2150, 1), (key2167, 1), (key2177, -1), (key2188, -1), (key2061, -1), (key2070, -1), (key2150, 1), (key2167, 1), (key2080, 1), (key2086, 1), (key2177, -1), (key2188, -1)]

def rawRow6791 : Integer.Sparse Key := [(key2153, -1), (key2150, -1), (key2177, 2), (key2153, -1), (key2150, -1), (key2247, 2), (key2243, 2), (key2280, -1), (key2277, -1), (key2177, 2), (key2280, -1), (key2277, -1), (key2064, 1), (key2061, 1), (key2080, -2), (key2064, 1), (key2061, 1), (key2254, -2), (key2243, -2), (key2288, 1), (key2277, 1), (key2080, -2), (key2288, 1), (key2277, 1), (key2070, -1), (key2061, -1), (key2086, 1), (key2080, 1), (key2167, 1), (key2150, 1), (key2188, -1), (key2177, -1), (key2070, -1), (key2061, -1), (key2167, 1), (key2150, 1), (key2086, 1), (key2080, 1), (key2188, -1), (key2177, -1)]

def rawRow6792 : Integer.Sparse Key := [(key2150, -1), (key2177, -1), (key2153, 2), (key2243, -1), (key2277, -1), (key2150, 2), (key2280, 2), (key2153, -1), (key2247, -1), (key2277, 2), (key2177, -1), (key2280, -1), (key2061, 1), (key2080, 1), (key2064, -2), (key2243, 1), (key2277, 1), (key2061, -2), (key2288, -2), (key2064, 1), (key2254, 1), (key2277, -2), (key2080, 1), (key2288, 1), (key2031, -1), (key2086, -1), (key2034, 1), (key2070, 1), (key2031, 1), (key2188, 1), (key2034, -1), (key2167, -1), (key2150, -1), (key2280, -1), (key2061, 1), (key2288, 1), (key2177, 1), (key2280, 1), (key2080, -1), (key2288, -1)]

def rawRow6793 : Integer.Sparse Key := [(key2177, -1), (key2150, -1), (key2153, 2), (key2277, -1), (key2243, -1), (key2280, 2), (key2150, 2), (key2247, -1), (key2153, -1), (key2277, 2), (key2280, -1), (key2177, -1), (key2080, 1), (key2061, 1), (key2064, -2), (key2277, 1), (key2243, 1), (key2288, -2), (key2061, -2), (key2254, 1), (key2064, 1), (key2277, -2), (key2288, 1), (key2080, 1), (key2086, -1), (key2031, -1), (key2070, 1), (key2034, 1), (key2188, 1), (key2031, 1), (key2167, -1), (key2034, -1), (key2280, -1), (key2150, -1), (key2288, 1), (key2061, 1), (key2280, 1), (key2177, 1), (key2288, -1), (key2080, -1)]

def rawRow6794 : Integer.Sparse Key := [(key2153, -1), (key2177, -1), (key2150, 2), (key2247, -1), (key2280, -1), (key2153, 2), (key2277, 2), (key2150, -1), (key2243, -1), (key2280, 2), (key2177, -1), (key2277, -1), (key2064, 1), (key2080, 1), (key2061, -2), (key2254, 1), (key2288, 1), (key2064, -2), (key2277, -2), (key2061, 1), (key2243, 1), (key2288, -2), (key2080, 1), (key2277, 1), (key2034, -1), (key2080, -1), (key2031, 1), (key2061, 1), (key2034, 1), (key2177, 1), (key2031, -1), (key2150, -1), (key2167, -1), (key2288, -1), (key2070, 1), (key2280, 1), (key2188, 1), (key2288, 1), (key2086, -1), (key2280, -1)]

def rawRow6795 : Integer.Sparse Key := [(key2177, -1), (key2153, -1), (key2150, 2), (key2280, -1), (key2247, -1), (key2277, 2), (key2153, 2), (key2243, -1), (key2150, -1), (key2280, 2), (key2277, -1), (key2177, -1), (key2080, 1), (key2064, 1), (key2061, -2), (key2288, 1), (key2254, 1), (key2277, -2), (key2064, -2), (key2243, 1), (key2061, 1), (key2288, -2), (key2277, 1), (key2080, 1), (key2080, -1), (key2034, -1), (key2061, 1), (key2031, 1), (key2177, 1), (key2034, 1), (key2150, -1), (key2031, -1), (key2288, -1), (key2167, -1), (key2280, 1), (key2070, 1), (key2288, 1), (key2188, 1), (key2280, -1), (key2086, -1)]

def rawRow6796 : Integer.Sparse Key := [(key2243, -1), (key2277, -1), (key2277, 2), (key2150, -1), (key2177, -1), (key2150, 2), (key2280, 2), (key2177, -1), (key2280, -1), (key2153, 2), (key2153, -1), (key2247, -1), (key2243, 1), (key2277, 1), (key2277, -2), (key2061, 1), (key2080, 1), (key2061, -2), (key2288, -2), (key2080, 1), (key2288, 1), (key2064, -2), (key2064, 1), (key2254, 1), (key2150, -1), (key2280, -1), (key2177, 1), (key2280, 1), (key2061, 1), (key2288, 1), (key2080, -1), (key2288, -1), (key2031, -1), (key2086, -1), (key2031, 1), (key2188, 1), (key2034, 1), (key2070, 1), (key2034, -1), (key2167, -1)]

def rawRow6797 : Integer.Sparse Key := [(key2277, -1), (key2243, -1), (key2277, 2), (key2177, -1), (key2150, -1), (key2280, 2), (key2150, 2), (key2280, -1), (key2177, -1), (key2153, 2), (key2247, -1), (key2153, -1), (key2277, 1), (key2243, 1), (key2277, -2), (key2080, 1), (key2061, 1), (key2288, -2), (key2061, -2), (key2288, 1), (key2080, 1), (key2064, -2), (key2254, 1), (key2064, 1), (key2280, -1), (key2150, -1), (key2280, 1), (key2177, 1), (key2288, 1), (key2061, 1), (key2288, -1), (key2080, -1), (key2086, -1), (key2031, -1), (key2188, 1), (key2031, 1), (key2070, 1), (key2034, 1), (key2167, -1), (key2034, -1)]

def rawRow6798 : Integer.Sparse Key := [(key2277, -1), (key2277, -1), (key2243, 2), (key2280, -1), (key2280, -1), (key2177, 2), (key2177, 2), (key2150, -1), (key2150, -1), (key2247, 2), (key2153, -1), (key2153, -1), (key2277, 1), (key2277, 1), (key2243, -2), (key2288, 1), (key2288, 1), (key2080, -2), (key2080, -2), (key2061, 1), (key2061, 1), (key2254, -2), (key2064, 1), (key2064, 1), (key2177, -1), (key2177, -1), (key2150, 1), (key2150, 1), (key2080, 1), (key2080, 1), (key2061, -1), (key2061, -1), (key2188, -1), (key2188, -1), (key2086, 1), (key2086, 1), (key2167, 1), (key2167, 1), (key2070, -1), (key2070, -1)]

def rawRow6799 : Integer.Sparse Key := [(key2247, -1), (key2280, -1), (key2280, 2), (key2153, -1), (key2177, -1), (key2153, 2), (key2277, 2), (key2177, -1), (key2277, -1), (key2150, 2), (key2150, -1), (key2243, -1), (key2254, 1), (key2288, 1), (key2288, -2), (key2064, 1), (key2080, 1), (key2064, -2), (key2277, -2), (key2080, 1), (key2277, 1), (key2061, -2), (key2061, 1), (key2243, 1), (key2167, -1), (key2288, -1), (key2188, 1), (key2288, 1), (key2070, 1), (key2280, 1), (key2086, -1), (key2280, -1), (key2034, -1), (key2080, -1), (key2034, 1), (key2177, 1), (key2031, 1), (key2061, 1), (key2031, -1), (key2150, -1)]

def rawRow6800 : Integer.Sparse Key := [(key2280, -1), (key2247, -1), (key2280, 2), (key2177, -1), (key2153, -1), (key2277, 2), (key2153, 2), (key2277, -1), (key2177, -1), (key2150, 2), (key2243, -1), (key2150, -1), (key2288, 1), (key2254, 1), (key2288, -2), (key2080, 1), (key2064, 1), (key2277, -2), (key2064, -2), (key2277, 1), (key2080, 1), (key2061, -2), (key2243, 1), (key2061, 1), (key2288, -1), (key2167, -1), (key2288, 1), (key2188, 1), (key2280, 1), (key2070, 1), (key2280, -1), (key2086, -1), (key2080, -1), (key2034, -1), (key2177, 1), (key2034, 1), (key2061, 1), (key2031, 1), (key2150, -1), (key2031, -1)]

def rawRow6801 : Integer.Sparse Key := [(key2280, -1), (key2280, -1), (key2247, 2), (key2277, -1), (key2277, -1), (key2177, 2), (key2177, 2), (key2153, -1), (key2153, -1), (key2243, 2), (key2150, -1), (key2150, -1), (key2288, 1), (key2288, 1), (key2254, -2), (key2277, 1), (key2277, 1), (key2080, -2), (key2080, -2), (key2064, 1), (key2064, 1), (key2243, -2), (key2061, 1), (key2061, 1), (key2188, -1), (key2188, -1), (key2167, 1), (key2167, 1), (key2086, 1), (key2086, 1), (key2070, -1), (key2070, -1), (key2177, -1), (key2177, -1), (key2080, 1), (key2080, 1), (key2150, 1), (key2150, 1), (key2061, -1), (key2061, -1)]

def rawRow6802 : Integer.Sparse Key := [(key2167, -1), (key2167, -1), (key2188, 2), (key2167, -1), (key2167, -1), (key2254, 2), (key2254, 2), (key2288, -1), (key2288, -1), (key2188, 2), (key2288, -1), (key2288, -1), (key2070, 1), (key2070, 1), (key2086, -2), (key2070, 1), (key2070, 1), (key2247, -2), (key2247, -2), (key2280, 1), (key2280, 1), (key2086, -2), (key2280, 1), (key2280, 1), (key2064, -1), (key2064, -1), (key2080, 1), (key2080, 1), (key2153, 1), (key2153, 1), (key2177, -1), (key2177, -1), (key2064, -1), (key2064, -1), (key2153, 1), (key2153, 1), (key2080, 1), (key2080, 1), (key2177, -1), (key2177, -1)]

def rawRow6803 : Integer.Sparse Key := [(key2167, -1), (key2188, -1), (key2167, 2), (key2254, -1), (key2288, -1), (key2167, 2), (key2288, 2), (key2167, -1), (key2254, -1), (key2288, 2), (key2188, -1), (key2288, -1), (key2070, 1), (key2086, 1), (key2070, -2), (key2247, 1), (key2280, 1), (key2070, -2), (key2280, -2), (key2070, 1), (key2247, 1), (key2280, -2), (key2086, 1), (key2280, 1), (key2034, -1), (key2080, -1), (key2034, 1), (key2064, 1), (key2034, 1), (key2177, 1), (key2034, -1), (key2153, -1), (key2153, -1), (key2277, -1), (key2064, 1), (key2277, 1), (key2177, 1), (key2277, 1), (key2080, -1), (key2277, -1)]

def rawRow6804 : Integer.Sparse Key := [(key2188, -1), (key2167, -1), (key2167, 2), (key2288, -1), (key2254, -1), (key2288, 2), (key2167, 2), (key2254, -1), (key2167, -1), (key2288, 2), (key2288, -1), (key2188, -1), (key2086, 1), (key2070, 1), (key2070, -2), (key2280, 1), (key2247, 1), (key2280, -2), (key2070, -2), (key2247, 1), (key2070, 1), (key2280, -2), (key2280, 1), (key2086, 1), (key2080, -1), (key2034, -1), (key2064, 1), (key2034, 1), (key2177, 1), (key2034, 1), (key2153, -1), (key2034, -1), (key2277, -1), (key2153, -1), (key2277, 1), (key2064, 1), (key2277, 1), (key2177, 1), (key2277, -1), (key2080, -1)]

def rawRow6805 : Integer.Sparse Key := [(key2254, -1), (key2288, -1), (key2288, 2), (key2167, -1), (key2188, -1), (key2167, 2), (key2288, 2), (key2188, -1), (key2288, -1), (key2167, 2), (key2167, -1), (key2254, -1), (key2247, 1), (key2280, 1), (key2280, -2), (key2070, 1), (key2086, 1), (key2070, -2), (key2280, -2), (key2086, 1), (key2280, 1), (key2070, -2), (key2070, 1), (key2247, 1), (key2153, -1), (key2277, -1), (key2177, 1), (key2277, 1), (key2064, 1), (key2277, 1), (key2080, -1), (key2277, -1), (key2034, -1), (key2080, -1), (key2034, 1), (key2177, 1), (key2034, 1), (key2064, 1), (key2034, -1), (key2153, -1)]

def rawRow6806 : Integer.Sparse Key := [(key2288, -1), (key2254, -1), (key2288, 2), (key2188, -1), (key2167, -1), (key2288, 2), (key2167, 2), (key2288, -1), (key2188, -1), (key2167, 2), (key2254, -1), (key2167, -1), (key2280, 1), (key2247, 1), (key2280, -2), (key2086, 1), (key2070, 1), (key2280, -2), (key2070, -2), (key2280, 1), (key2086, 1), (key2070, -2), (key2247, 1), (key2070, 1), (key2277, -1), (key2153, -1), (key2277, 1), (key2177, 1), (key2277, 1), (key2064, 1), (key2277, -1), (key2080, -1), (key2080, -1), (key2034, -1), (key2177, 1), (key2034, 1), (key2064, 1), (key2034, 1), (key2153, -1), (key2034, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7377 : Integer.Sparse Key := [(key0, -24), (key83, 6), (key83, 6), (key83, 6), (key83, 6)]

end MUB6.Certificate.GramRows

end OAI
end


