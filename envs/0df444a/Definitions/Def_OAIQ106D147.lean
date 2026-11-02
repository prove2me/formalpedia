-- Prove2me | Definitions.Def_OAIQ106D147
-- name    : OAIQ106D147
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:48:52.987899+00:00
-- url     : https://prove2.me/theorems/aea02d47-bdb7-46d9-94e2-4c9be032fe6f
-- title:
--   Definitions bundle OAIQ106D147 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 285 declarations of OpenAI's Lean: 285 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.entry10_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_7`, `OAI.MUB6.Certificate.GramFunctions.Block2.terms9`, `OAI.MUB6.Certificate.GramRows.row6711`, `OAI.MUB6.Certificate.GramRows.row6712`, `OAI.MUB6.Certificate.GramRows.row6713`, `OAI.MUB6.Certificate.GramRows.row6714`, `OAI.MUB6.Certificate.GramRows.row6715`, `OAI.MUB6.Certificate.GramRows.row6716`, `OAI.MUB6.Certificate.GramRows.row6717`, `OAI.MUB6.Certificate.GramRows.row6718`, `OAI.MUB6.Certificate.GramRows.row6719`, `OAI.MUB6.Certificate.GramRows.row6720`, `OAI.MUB6.Certificate.GramRows.row6721`, `OAI.MUB6.Certificate.GramRows.row6722`, `OAI.MUB6.Certificate.GramRows.row6723`, `OAI.MUB6.Certificate.GramRows.row6724`, `OAI.MUB6.Certificate.GramRows.row6725`, `OAI.MUB6.Certificate.GramRows.row6726`, `OAI.MUB6.Certificate.GramRows.row6727`, `OAI.MUB6.Certificate.GramRows.row6728`, `OAI.MUB6.Certificate.GramRows.row6729`, `OAI.MUB6.Certificate.GramRows.row6730`, `OAI.MUB6.Certificate.GramRows.row6731`, `OAI.MUB6.Certificate.GramRows.row6732`, `OAI.MUB6.Certificate.GramRows.row6733`, `OAI.MUB6.Certificate.GramRows.row6734`, `OAI.MUB6.Certificate.GramRows.row6735`, `OAI.MUB6.Certificate.GramRows.row6736`, `OAI.MUB6.Certificate.GramRows.row6737`, `OAI.MUB6.Certificate.GramRows.row6738`, `OAI.MUB6.Certificate.GramRows.row6739`, `OAI.MUB6.Certificate.GramRows.row6740`, `OAI.MUB6.Certificate.GramRows.row6741`, `OAI.MUB6.Certificate.GramRows.row6742`, `OAI.MUB6.Certificate.GramRows.row6743`, `OAI.MUB6.Certificate.GramRows.row6744`, `OAI.MUB6.Certificate.GramRows.row6745`, `OAI.MUB6.Certificate.GramRows.row6746` and 245 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block3Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Data.lean), [`MutuallyUnbiased_GramEntries_Block4Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block4Data.lean), [`MutuallyUnbiased_GramFunctions_Block2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Block2.lean), [`MutuallyUnbiased_GramRows_Block76`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block76.lean), [`MutuallyUnbiased_GramRows_Block77`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block77.lean), [`MutuallyUnbiased_GramRows_Block78`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block78.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D087`, `OAIQ106D088`, `OAIQ106D089` and `OAIQ106D090` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D198` and `OAIQ106D199`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D081
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D088
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization

def entry10_0 : Integer.Sparse Key := [(key1254, -192), (key1263, 192), (key1529, -48), (key1607, -240), (key1646, 288), (key1763, 48), (key1804, -288), (key1835, 240)]

def entry10_1 : Integer.Sparse Key := [(key16, 72), (key41, 648), (key98, -480), (key205, -72), (key374, 72), (key425, -240)]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization

def entry10_7 : Integer.Sparse Key := [(key2678, -288), (key2687, 288), (key2709, 288), (key2713, -288)]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block2

def terms9 : Array TaggedTerm := #[
  ⟨0, ![1, -1, -1, 0, 0, 1], 1⟩,
  ⟨0, ![1, -1, -1, 0, 1, 0], 1⟩,
  ⟨0, ![1, -1, -1, 1, 0, 0], -2⟩,
  ⟨0, ![1, -1, 0, -1, 0, 1], 1⟩,
  ⟨0, ![1, -1, 0, -1, 1, 0], 1⟩,
  ⟨0, ![1, -1, 0, 0, -1, 1], -2⟩,
  ⟨0, ![1, -1, 0, 0, 1, -1], -2⟩,
  ⟨0, ![1, -1, 0, 1, -1, 0], 1⟩,
  ⟨0, ![1, -1, 0, 1, 0, -1], 1⟩,
  ⟨0, ![1, -1, 1, -1, 0, 0], -2⟩,
  ⟨0, ![1, -1, 1, 0, -1, 0], 1⟩,
  ⟨0, ![1, -1, 1, 0, 0, -1], 1⟩,
  ⟨0, ![1, 0, -1, -1, 0, 1], -2⟩,
  ⟨0, ![1, 0, -1, -1, 1, 0], -2⟩,
  ⟨0, ![1, 0, -1, 0, -1, 1], 1⟩,
  ⟨0, ![1, 0, -1, 0, 1, -1], 1⟩,
  ⟨0, ![1, 0, -1, 1, -1, 0], 1⟩,
  ⟨0, ![1, 0, -1, 1, 0, -1], 1⟩,
  ⟨0, ![1, 0, 0, -1, -1, 1], 1⟩,
  ⟨0, ![1, 0, 0, -1, 1, -1], 1⟩,
  ⟨0, ![1, 0, 0, 1, -1, -1], -2⟩,
  ⟨0, ![1, 0, 1, -1, -1, 0], 1⟩,
  ⟨0, ![1, 0, 1, -1, 0, -1], 1⟩,
  ⟨0, ![1, 0, 1, 0, -1, -1], -2⟩,
  ⟨0, ![1, 1, -1, -1, 0, 0], 4⟩,
  ⟨0, ![1, 1, -1, 0, -1, 0], -2⟩,
  ⟨0, ![1, 1, -1, 0, 0, -1], -2⟩,
  ⟨0, ![1, 1, 0, -1, -1, 0], -2⟩,
  ⟨0, ![1, 1, 0, -1, 0, -1], -2⟩,
  ⟨0, ![1, 1, 0, 0, -1, -1], 4⟩
]

end MUB6.Certificate.GramFunctions.Block2

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

def row6711 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2749, -1), (key2751, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6712 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6713 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6714 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6715 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6716 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 1), (key2952, -1), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6717 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 1), (key2952, -1), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6718 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6719 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6720 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6721 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6722 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6723 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6724 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6725 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6726 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6727 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6728 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6729 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6730 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6731 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6732 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6733 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6734 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6735 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6736 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6737 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6738 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6739 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6740 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

def row6741 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6742 : Integer.Sparse Key := [(key2066, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2155, 4), (key2168, -4), (key2195, -4), (key2201, 4), (key2248, -4), (key2255, 4), (key2306, 4), (key2311, -4)]

def row6743 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6744 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6745 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6746 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

def row6747 : Integer.Sparse Key := [(key2066, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2155, 4), (key2168, -4), (key2195, -4), (key2201, 4), (key2248, -4), (key2255, 4), (key2306, 4), (key2311, -4)]

def row6748 : Integer.Sparse Key := [(key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key728, -1), (key730, 1), (key796, 1), (key815, -1), (key832, -1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6749 : Integer.Sparse Key := [(key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key728, -1), (key730, 1), (key796, 1), (key815, -1), (key832, -1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6750 : Integer.Sparse Key := [(key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key728, 2), (key730, -2), (key796, -2), (key815, 2), (key832, 2), (key841, -2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

def row6751 : Integer.Sparse Key := [(key313, 2), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key727, -2), (key728, -1), (key730, 1), (key794, -1), (key815, -1), (key832, 1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6752 : Integer.Sparse Key := [(key313, 2), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key727, -2), (key728, -1), (key730, 1), (key794, -1), (key815, -1), (key832, 1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6753 : Integer.Sparse Key := [(key313, -2), (key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key414, 2), (key415, -2), (key419, 2), (key727, 2), (key728, 2), (key730, -2), (key794, -2), (key815, 2), (key841, -2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

def row6754 : Integer.Sparse Key := [(key312, 2), (key313, -2), (key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key414, 2), (key415, -2), (key419, 2), (key584, -2), (key725, -2), (key727, 2), (key728, 2), (key730, -2), (key794, -2), (key815, 2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

def row6755 : Integer.Sparse Key := [(key312, -1), (key313, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, -2), (key415, 1), (key419, -1), (key582, 1), (key584, 1), (key725, 1), (key727, 1), (key728, -1), (key730, 1), (key794, 2), (key815, -2), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6756 : Integer.Sparse Key := [(key312, -1), (key313, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, -2), (key415, 1), (key419, -1), (key582, 1), (key584, 1), (key725, 1), (key727, 1), (key728, -1), (key730, 1), (key794, 2), (key815, -2), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6757 : Integer.Sparse Key := [(key312, 2), (key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key415, -4), (key419, 2), (key582, 2), (key584, -2), (key725, -2), (key728, 2), (key730, -2), (key796, 2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

def row6758 : Integer.Sparse Key := [(key312, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key415, 2), (key419, -1), (key582, -1), (key584, 1), (key725, 1), (key728, -1), (key730, 1), (key796, -1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6759 : Integer.Sparse Key := [(key312, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key415, 2), (key419, -1), (key582, -1), (key584, 1), (key725, 1), (key728, -1), (key730, 1), (key796, -1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

def row6760 : Integer.Sparse Key := [(key324, 1), (key325, 2), (key329, -3), (key339, -1), (key341, 1), (key414, -2), (key415, -2), (key419, 4), (key474, 2), (key476, -2), (key600, -2), (key602, 2), (key728, -1), (key736, -1), (key748, 1), (key752, 1), (key794, 2), (key815, 2), (key832, -2), (key841, -2)]

def row6761 : Integer.Sparse Key := [(key324, 1), (key325, 2), (key329, -3), (key339, -1), (key341, 1), (key414, -2), (key415, -2), (key419, 4), (key474, 2), (key476, -2), (key600, -2), (key602, 2), (key728, -1), (key736, -1), (key748, 1), (key752, 1), (key794, 2), (key815, 2), (key832, -2), (key841, -2)]

def row6762 : Integer.Sparse Key := [(key313, 1), (key324, -1), (key325, -1), (key329, 2), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key727, -1), (key728, 1), (key748, -1), (key794, -1), (key815, -1), (key832, 1), (key841, 1)]

def row6763 : Integer.Sparse Key := [(key312, -1), (key313, 1), (key324, -1), (key325, -1), (key329, 2), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key474, -1), (key476, 1), (key584, 1), (key600, 1), (key602, -1), (key725, 1), (key727, -1), (key728, 1), (key748, -1), (key794, -1), (key815, -1), (key832, 1)]

def row6764 : Integer.Sparse Key := [(key312, 1), (key325, -1), (key329, 1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key725, -1), (key736, 1), (key752, -1), (key794, -1), (key815, -1), (key841, 1)]

def row6765 : Integer.Sparse Key := [(key312, 1), (key325, -1), (key329, 1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key725, -1), (key736, 1), (key752, -1), (key794, -1), (key815, -1), (key841, 1)]

def row6766 : Integer.Sparse Key := [(key325, -1), (key329, 1), (key341, -1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key736, 1), (key815, -1), (key841, 1)]

def row6767 : Integer.Sparse Key := [(key312, -1), (key325, -1), (key329, 1), (key341, -1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key584, 1), (key600, 1), (key602, -1), (key725, 1), (key736, 1), (key815, -1)]

def row6768 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key584, -2), (key600, -2), (key602, 2), (key736, -2), (key815, 2)]

def row6769 : Integer.Sparse Key := [(key324, -1), (key325, -1), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key582, -1), (key584, 1), (key600, 1), (key602, -1), (key728, 1), (key794, -1)]

def row6770 : Integer.Sparse Key := [(key324, -1), (key325, -1), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key582, -1), (key584, 1), (key600, 1), (key602, -1), (key728, 1), (key794, -1)]

def row6771 : Integer.Sparse Key := [(key324, 2), (key325, 2), (key329, -2), (key339, -2), (key341, 2), (key414, -2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2), (key728, -2), (key794, 2)]

def row6772 : Integer.Sparse Key := [(key325, -4), (key329, 4), (key339, 4), (key341, -4), (key415, 4), (key419, -4), (key474, -4), (key476, 4), (key582, -4), (key584, 4), (key600, 4), (key602, -4)]

def row6773 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

def row6774 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

def row6775 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

def row6776 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

def row6777 : Integer.Sparse Key := [(key325, -4), (key329, 4), (key339, 4), (key341, -4), (key415, 4), (key419, -4), (key474, -4), (key476, 4), (key582, -4), (key584, 4), (key600, 4), (key602, -4)]

def row6778 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6779 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6780 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6781 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6782 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6783 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

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

def row6784 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6785 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6786 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6787 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6788 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6789 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6790 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6791 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6792 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6793 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6794 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6795 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6796 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6797 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6798 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6799 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6800 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

def row6801 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6802 : Integer.Sparse Key := [(key2064, -4), (key2070, 4), (key2080, 4), (key2086, -4), (key2153, 4), (key2167, -4), (key2177, -4), (key2188, 4), (key2247, -4), (key2254, 4), (key2280, 4), (key2288, -4)]

def row6803 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6804 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6805 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6806 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

def row6807 : Integer.Sparse Key := [(key2064, -4), (key2070, 4), (key2080, 4), (key2086, -4), (key2153, 4), (key2167, -4), (key2177, -4), (key2188, 4), (key2247, -4), (key2254, 4), (key2280, 4), (key2288, -4)]

def row6808 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6809 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6810 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

def row6811 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6812 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6813 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

def row6814 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

def row6815 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6816 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6817 : Integer.Sparse Key := [(key66, 4), (key67, -4), (key78, -4), (key80, 4), (key708, -2), (key711, 2), (key717, 2), (key719, -2), (key862, -2), (key887, 2), (key894, 2), (key896, 2), (key917, -4), (key949, -2), (key956, 2)]

def row6818 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6819 : Integer.Sparse Key := [(key66, -2), (key67, 2), (key78, 2), (key80, -2), (key708, 1), (key711, -1), (key717, -1), (key719, 1), (key862, 1), (key887, -1), (key894, -1), (key896, -1), (key917, 2), (key949, 1), (key956, -1)]

def row6820 : Integer.Sparse Key := [(key66, 2), (key78, -1), (key80, -1), (key131, -4), (key141, 4), (key143, 4), (key160, -4), (key711, -2), (key717, -1), (key719, 3), (key862, 2), (key887, 2), (key894, -2), (key896, -2), (key917, -4), (key949, 2), (key956, 2)]

def row6821 : Integer.Sparse Key := [(key66, 2), (key78, -1), (key80, -1), (key131, -4), (key141, 4), (key143, 4), (key160, -4), (key711, -2), (key717, -1), (key719, 3), (key862, 2), (key887, 2), (key894, -2), (key896, -2), (key917, -4), (key949, 2), (key956, 2)]

def row6822 : Integer.Sparse Key := [(key66, -1), (key78, 2), (key80, -1), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, -1), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

def row6823 : Integer.Sparse Key := [(key66, -1), (key78, 2), (key80, -1), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, -1), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

def row6824 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 2), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, 2), (key719, -3), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

def row6825 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 2), (key131, 2), (key141, -2), (key143, -2), (key160, 2), (key711, 1), (key717, 2), (key719, -3), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 2), (key949, -1), (key956, -1)]

def row6826 : Integer.Sparse Key := [(key78, 2), (key131, 2), (key141, -1), (key143, -2), (key160, 1), (key708, -1), (key711, 1), (key717, -1), (key719, -1), (key862, -1), (key887, -1), (key896, 1), (key917, 2), (key956, -1)]

def row6827 : Integer.Sparse Key := [(key78, 2), (key131, 2), (key141, -1), (key143, -2), (key160, 1), (key708, -1), (key711, 1), (key717, -1), (key719, -1), (key862, -1), (key887, -1), (key896, 1), (key917, 2), (key956, -1)]

def row6828 : Integer.Sparse Key := [(key78, -1), (key131, -4), (key141, 2), (key143, 4), (key160, -2), (key191, 2), (key708, 2), (key711, -2), (key717, -1), (key719, 2), (key862, 2), (key887, 2), (key896, -2), (key917, -4)]

def row6829 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 1), (key131, 2), (key141, -2), (key143, -2), (key160, 1), (key183, 1), (key191, -1), (key711, 1), (key717, 2), (key719, -2), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 1)]

def row6830 : Integer.Sparse Key := [(key66, -1), (key78, -1), (key80, 1), (key131, 2), (key141, -2), (key143, -2), (key160, 1), (key183, 1), (key191, -1), (key711, 1), (key717, 2), (key719, -2), (key862, -1), (key887, -1), (key894, 1), (key896, 1), (key917, 1)]

def row6831 : Integer.Sparse Key := [(key78, -1), (key80, -2), (key131, -4), (key141, 2), (key143, 4), (key160, -2), (key183, -2), (key191, 2), (key708, 2), (key711, -2), (key717, -1), (key719, 4), (key862, 2), (key887, 2), (key896, -2), (key917, -2)]

def row6832 : Integer.Sparse Key := [(key66, -2), (key67, 4), (key78, 2), (key80, -4), (key143, -4), (key160, 4), (key178, -4), (key183, 8), (key191, -4), (key708, -2), (key717, 2), (key862, 4), (key894, -4)]

def row6833 : Integer.Sparse Key := [(key66, 1), (key67, -2), (key78, -1), (key80, 2), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 1), (key717, -1), (key862, -2), (key894, 2)]

def row6834 : Integer.Sparse Key := [(key66, 1), (key67, -2), (key78, -1), (key80, 2), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 1), (key717, -1), (key862, -2), (key894, 2)]

def row6835 : Integer.Sparse Key := [(key66, -1), (key67, -2), (key78, -1), (key80, 2), (key131, -1), (key141, 1), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 3), (key717, -1), (key862, -1), (key894, 1)]

def row6836 : Integer.Sparse Key := [(key66, -1), (key67, -2), (key78, -1), (key80, 2), (key131, -1), (key141, 1), (key143, 2), (key160, -2), (key178, 2), (key183, -4), (key191, 2), (key708, 3), (key717, -1), (key862, -1), (key894, 1)]

def row6837 : Integer.Sparse Key := [(key67, 4), (key78, 2), (key80, -4), (key131, 2), (key141, -4), (key143, -4), (key160, 4), (key178, -4), (key183, 8), (key191, -4), (key708, -4), (key717, 2), (key862, 2)]

def row6839 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6840 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6841 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6842 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6843 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6844 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6845 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6846 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6847 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6848 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6849 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6850 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6851 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6852 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6853 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6854 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6855 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6856 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6857 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6858 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6859 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6860 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

def row6861 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6862 : Integer.Sparse Key := [(key1992, -4), (key1995, 4), (key2002, 4), (key2004, -4), (key2237, 4), (key2260, -4), (key2271, -4), (key2273, -4), (key2295, 8), (key2325, 4), (key2337, -4)]

def row6863 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6864 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6865 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6866 : Integer.Sparse Key := [(key1992, 2), (key1995, -2), (key2002, -2), (key2004, 2), (key2237, -2), (key2260, 2), (key2271, 2), (key2273, 2), (key2295, -4), (key2325, -2), (key2337, 2)]

def row6867 : Integer.Sparse Key := [(key1992, -4), (key1995, 4), (key2002, 4), (key2004, -4), (key2237, 4), (key2260, -4), (key2271, -4), (key2273, -4), (key2295, 8), (key2325, 4), (key2337, -4)]

def row6868 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6869 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6870 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6871 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6872 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6873 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6874 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6875 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6876 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6877 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6878 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6879 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6880 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6881 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6882 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6883 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6884 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6885 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6886 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6887 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6888 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6889 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6890 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2065, 1), (key2073, -1), (key2083, -1), (key2088, 1), (key2178, 1), (key2180, -1), (key2278, -1), (key2282, 1), (key2329, 1), (key2331, -1)]

def row6891 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6892 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, 4), (key2073, -4), (key2083, -4), (key2088, 4), (key2178, 4), (key2180, -4), (key2278, -4), (key2282, 4), (key2329, 4), (key2331, -4)]

def row6893 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6894 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6895 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6896 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2065, -2), (key2073, 2), (key2083, 2), (key2088, -2), (key2178, -2), (key2180, 2), (key2278, 2), (key2282, -2), (key2329, -2), (key2331, 2)]

def row6897 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2065, 4), (key2073, -4), (key2083, -4), (key2088, 4), (key2178, 4), (key2180, -4), (key2278, -4), (key2282, 4), (key2329, 4), (key2331, -4)]

def row6898 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6899 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6900 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6901 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6902 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6903 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6904 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6905 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6906 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6907 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6908 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6909 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6910 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6911 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6912 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6913 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6914 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6915 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6916 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6917 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6918 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6919 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6920 : Integer.Sparse Key := [(key729, -1), (key735, 1), (key739, 1), (key744, -1), (key795, 1), (key813, -1), (key819, -1), (key826, 1), (key869, -1), (key878, 1), (key903, 1), (key909, -1)]

def row6921 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6922 : Integer.Sparse Key := [(key729, -4), (key735, 4), (key739, 4), (key744, -4), (key795, 4), (key813, -4), (key819, -4), (key826, 4), (key869, -4), (key878, 4), (key903, 4), (key909, -4)]

def row6923 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6924 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6925 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6926 : Integer.Sparse Key := [(key729, 2), (key735, -2), (key739, -2), (key744, 2), (key795, -2), (key813, 2), (key819, 2), (key826, -2), (key869, 2), (key878, -2), (key903, -2), (key909, 2)]

def row6927 : Integer.Sparse Key := [(key729, -4), (key735, 4), (key739, 4), (key744, -4), (key795, 4), (key813, -4), (key819, -4), (key826, 4), (key869, -4), (key878, 4), (key903, 4), (key909, -4)]

def row6928 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6929 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6930 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6931 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6932 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6933 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6934 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6935 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6936 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6937 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6938 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6939 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6940 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6941 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6942 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6943 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6944 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6945 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6946 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6947 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6948 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6949 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6950 : Integer.Sparse Key := [(key2031, 1), (key2036, -1), (key2061, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2150, -1), (key2155, 1), (key2243, 1), (key2248, -1), (key2304, -1), (key2306, 1)]

def row6951 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6952 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2150, -4), (key2155, 4), (key2243, 4), (key2248, -4), (key2304, -4), (key2306, 4)]

def row6953 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6954 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6955 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6956 : Integer.Sparse Key := [(key2031, -2), (key2036, 2), (key2061, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2150, 2), (key2155, -2), (key2243, -2), (key2248, 2), (key2304, 2), (key2306, -2)]

def row6957 : Integer.Sparse Key := [(key2031, 4), (key2036, -4), (key2061, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2150, -4), (key2155, 4), (key2243, 4), (key2248, -4), (key2304, -4), (key2306, 4)]

def row6958 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6959 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6960 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6961 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6962 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6963 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6964 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6965 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6966 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6967 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6968 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6969 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6970 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6971 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6972 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6973 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6974 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6975 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6976 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6977 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6978 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6979 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6980 : Integer.Sparse Key := [(key2035, -1), (key2038, 1), (key2081, 1), (key2083, -1), (key2154, 1), (key2170, -1), (key2180, -1), (key2190, 1), (key2278, -1), (key2290, 1), (key2329, 1), (key2334, -1)]

def row6981 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6982 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2081, 4), (key2083, -4), (key2154, 4), (key2170, -4), (key2180, -4), (key2190, 4), (key2278, -4), (key2290, 4), (key2329, 4), (key2334, -4)]

def row6983 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6984 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6985 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6986 : Integer.Sparse Key := [(key2035, 2), (key2038, -2), (key2081, -2), (key2083, 2), (key2154, -2), (key2170, 2), (key2180, 2), (key2190, -2), (key2278, 2), (key2290, -2), (key2329, -2), (key2334, 2)]

def row6987 : Integer.Sparse Key := [(key2035, -4), (key2038, 4), (key2081, 4), (key2083, -4), (key2154, 4), (key2170, -4), (key2180, -4), (key2190, 4), (key2278, -4), (key2290, 4), (key2329, 4), (key2334, -4)]

def row6988 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6989 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, 1), (key822, 1), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6990 : Integer.Sparse Key := [(key781, -2), (key784, 2), (key806, 4), (key809, -2), (key814, -2), (key822, -2), (key827, 2), (key875, -2), (key879, 2), (key906, 2), (key910, -2)]

def row6991 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

def row6992 : Integer.Sparse Key := [(key781, 1), (key784, -1), (key806, -2), (key809, 1), (key814, -1), (key822, 3), (key827, -1), (key875, 1), (key879, -1), (key906, -1), (key910, 1)]

end MUB6.Certificate.GramRows

end OAI
end


