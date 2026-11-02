-- Prove2me | Definitions.Def_OAIQ106D149
-- name    : OAIQ106D149
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:57:29.400665+00:00
-- url     : https://prove2.me/theorems/f2b1a48b-e56f-4aa9-8f4e-63cd2a2ea64d
-- title:
--   Definitions bundle OAIQ106D149 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1700 declarations of OpenAI's Lean: 1700 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block5.entry10_9`, `OAI.MUB6.Certificate.GramFunctions.Block3.terms2`, `OAI.MUB6.Certificate.GramFunctions.Block3.terms22`, `OAI.MUB6.Certificate.GramFunctions.Block3.terms23`, `OAI.MUB6.Certificate.GramFunctions.Block3.terms24`, `OAI.MUB6.Certificate.GramFunctions.Block3.terms25`, `OAI.MUB6.Certificate.GramFunctions.Block3.terms26`, `OAI.MUB6.Certificate.GramFunctions.Block3.terms3`, `OAI.MUB6.Certificate.GramFunctions.Block3.terms4`, `OAI.MUB6.Certificate.GramFunctions.Block3.terms5`, `OAI.MUB6.Certificate.GramRows.row10808`, `OAI.MUB6.Certificate.GramRows.row10809`, `OAI.MUB6.Certificate.GramRows.row10810`, `OAI.MUB6.Certificate.GramRows.row10811`, `OAI.MUB6.Certificate.GramRows.row10812`, `OAI.MUB6.Certificate.GramRows.row10813`, `OAI.MUB6.Certificate.GramRows.row10814`, `OAI.MUB6.Certificate.GramRows.row10815`, `OAI.MUB6.Certificate.GramRows.row10816`, `OAI.MUB6.Certificate.GramRows.row10817`, `OAI.MUB6.Certificate.GramRows.row10818`, `OAI.MUB6.Certificate.GramRows.row10819`, `OAI.MUB6.Certificate.GramRows.row10820`, `OAI.MUB6.Certificate.GramRows.row10821`, `OAI.MUB6.Certificate.GramRows.row10822`, `OAI.MUB6.Certificate.GramRows.row10823`, `OAI.MUB6.Certificate.GramRows.row10824`, `OAI.MUB6.Certificate.GramRows.row10825`, `OAI.MUB6.Certificate.GramRows.row10826`, `OAI.MUB6.Certificate.GramRows.row10827`, `OAI.MUB6.Certificate.GramRows.row10828`, `OAI.MUB6.Certificate.GramRows.row10829`, `OAI.MUB6.Certificate.GramRows.row10830`, `OAI.MUB6.Certificate.GramRows.row10831`, `OAI.MUB6.Certificate.GramRows.row10832`, `OAI.MUB6.Certificate.GramRows.row10833`, `OAI.MUB6.Certificate.GramRows.row10834`, `OAI.MUB6.Certificate.GramRows.row10835`, `OAI.MUB6.Certificate.GramRows.row10836`, `OAI.MUB6.Certificate.GramRows.row10837` and 1660 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block5Data`, `MutuallyUnbiased_GramFunctions_Block3`, `MutuallyUnbiased_GramRows_Block108`, `MutuallyUnbiased_GramRows_Block109`, `MutuallyUnbiased_GramRows_Block113`, `MutuallyUnbiased_GramRows_Block114`, `MutuallyUnbiased_GramRows_Block115`, `MutuallyUnbiased_GramRows_Block116`, `MutuallyUnbiased_GramRows_Block117`, `MutuallyUnbiased_GramRows_Block118`, `MutuallyUnbiased_GramRows_Block119`, `MutuallyUnbiased_GramRows_Block120`, `MutuallyUnbiased_GramRows_Block121`, `MutuallyUnbiased_GramRows_Block122`, `MutuallyUnbiased_GramRows_Block123`, `MutuallyUnbiased_GramRows_Block124`, `MutuallyUnbiased_GramRows_Block125`, `MutuallyUnbiased_GramRows_Block126`, `MutuallyUnbiased_GramRows_Block127`, `MutuallyUnbiased_GramRows_Block81`, `MutuallyUnbiased_GramRows_Block82`, `MutuallyUnbiased_GramRows_Block83`, `MutuallyUnbiased_GramRows_Block84`.
--
--   **Imports.** It imports the bundles `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D088`, `OAIQ106D089`, `OAIQ106D090`, `OAIQ106D091` and `OAIQ106D092` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D199`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D081
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D088
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D092

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization

def entry10_9 : Integer.Sparse Key := [(key1501, 4320), (key1506, 4320), (key1733, 1440), (key1735, 4320)]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block3

def terms2 : Array TaggedTerm := #[
  ⟨0, ![1, -3, 0, 0, 0, 2], -6⟩,
  ⟨0, ![1, -3, 0, 0, 2, 0], -6⟩,
  ⟨0, ![1, -3, 0, 2, 0, 0], -6⟩,
  ⟨0, ![1, -3, 2, 0, 0, 0], -6⟩,
  ⟨0, ![1, 0, -3, 0, 0, 2], 2⟩,
  ⟨0, ![1, 0, -3, 0, 2, 0], 2⟩,
  ⟨0, ![1, 0, -3, 2, 0, 0], 2⟩,
  ⟨0, ![1, 0, 0, -3, 0, 2], 2⟩,
  ⟨0, ![1, 0, 0, -3, 2, 0], 2⟩,
  ⟨0, ![1, 0, 0, 0, -3, 2], 2⟩,
  ⟨0, ![1, 0, 0, 0, 2, -3], 2⟩,
  ⟨0, ![1, 0, 0, 2, -3, 0], 2⟩,
  ⟨0, ![1, 0, 0, 2, 0, -3], 2⟩,
  ⟨0, ![1, 0, 2, -3, 0, 0], 2⟩,
  ⟨0, ![1, 0, 2, 0, -3, 0], 2⟩,
  ⟨0, ![1, 0, 2, 0, 0, -3], 2⟩
]

def terms3 : Array TaggedTerm := #[
  ⟨1, ![3, -1, -2, 0, 0, 0], -6⟩,
  ⟨1, ![3, -1, 0, -2, 0, 0], -6⟩,
  ⟨1, ![3, -1, 0, 0, -2, 0], -6⟩,
  ⟨1, ![3, -1, 0, 0, 0, -2], -6⟩,
  ⟨1, ![3, 0, -2, -1, 0, 0], 2⟩,
  ⟨1, ![3, 0, -2, 0, -1, 0], 2⟩,
  ⟨1, ![3, 0, -2, 0, 0, -1], 2⟩,
  ⟨1, ![3, 0, -1, -2, 0, 0], 2⟩,
  ⟨1, ![3, 0, -1, 0, -2, 0], 2⟩,
  ⟨1, ![3, 0, -1, 0, 0, -2], 2⟩,
  ⟨1, ![3, 0, 0, -2, -1, 0], 2⟩,
  ⟨1, ![3, 0, 0, -2, 0, -1], 2⟩,
  ⟨1, ![3, 0, 0, -1, -2, 0], 2⟩,
  ⟨1, ![3, 0, 0, -1, 0, -2], 2⟩,
  ⟨1, ![3, 0, 0, 0, -2, -1], 2⟩,
  ⟨1, ![3, 0, 0, 0, -1, -2], 2⟩
]

def terms4 : Array TaggedTerm := #[
  ⟨1, ![1, -3, 0, 0, 0, 2], -6⟩,
  ⟨1, ![1, -3, 0, 0, 2, 0], -6⟩,
  ⟨1, ![1, -3, 0, 2, 0, 0], -6⟩,
  ⟨1, ![1, -3, 2, 0, 0, 0], -6⟩,
  ⟨1, ![1, 0, -3, 0, 0, 2], 2⟩,
  ⟨1, ![1, 0, -3, 0, 2, 0], 2⟩,
  ⟨1, ![1, 0, -3, 2, 0, 0], 2⟩,
  ⟨1, ![1, 0, 0, -3, 0, 2], 2⟩,
  ⟨1, ![1, 0, 0, -3, 2, 0], 2⟩,
  ⟨1, ![1, 0, 0, 0, -3, 2], 2⟩,
  ⟨1, ![1, 0, 0, 0, 2, -3], 2⟩,
  ⟨1, ![1, 0, 0, 2, -3, 0], 2⟩,
  ⟨1, ![1, 0, 0, 2, 0, -3], 2⟩,
  ⟨1, ![1, 0, 2, -3, 0, 0], 2⟩,
  ⟨1, ![1, 0, 2, 0, -3, 0], 2⟩,
  ⟨1, ![1, 0, 2, 0, 0, -3], 2⟩
]

def terms5 : Array TaggedTerm := #[
  ⟨1, ![1, -1, -2, 0, 0, 2], -2⟩,
  ⟨1, ![1, -1, -2, 0, 2, 0], -2⟩,
  ⟨1, ![1, -1, -2, 2, 0, 0], -2⟩,
  ⟨1, ![1, -1, 0, -2, 0, 2], -2⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], -2⟩,
  ⟨1, ![1, -1, 0, 0, -2, 2], -2⟩,
  ⟨1, ![1, -1, 0, 0, 2, -2], -2⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], -2⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], -2⟩,
  ⟨1, ![1, -1, 2, -2, 0, 0], -2⟩,
  ⟨1, ![1, -1, 2, 0, -2, 0], -2⟩,
  ⟨1, ![1, -1, 2, 0, 0, -2], -2⟩,
  ⟨1, ![1, 0, -2, -1, 0, 2], 1⟩,
  ⟨1, ![1, 0, -2, -1, 2, 0], 1⟩,
  ⟨1, ![1, 0, -2, 0, -1, 2], 1⟩,
  ⟨1, ![1, 0, -2, 0, 2, -1], 1⟩,
  ⟨1, ![1, 0, -2, 2, -1, 0], 1⟩,
  ⟨1, ![1, 0, -2, 2, 0, -1], 1⟩,
  ⟨1, ![1, 0, -1, -2, 0, 2], 1⟩,
  ⟨1, ![1, 0, -1, -2, 2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨1, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨1, ![1, 0, -1, 2, -2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 2, 0, -2], 1⟩,
  ⟨1, ![1, 0, 0, -2, -1, 2], 1⟩,
  ⟨1, ![1, 0, 0, -2, 2, -1], 1⟩,
  ⟨1, ![1, 0, 0, -1, -2, 2], 1⟩,
  ⟨1, ![1, 0, 0, -1, 2, -2], 1⟩,
  ⟨1, ![1, 0, 0, 2, -2, -1], 1⟩,
  ⟨1, ![1, 0, 0, 2, -1, -2], 1⟩,
  ⟨1, ![1, 0, 2, -2, -1, 0], 1⟩,
  ⟨1, ![1, 0, 2, -2, 0, -1], 1⟩,
  ⟨1, ![1, 0, 2, -1, -2, 0], 1⟩,
  ⟨1, ![1, 0, 2, -1, 0, -2], 1⟩,
  ⟨1, ![1, 0, 2, 0, -2, -1], 1⟩,
  ⟨1, ![1, 0, 2, 0, -1, -2], 1⟩
]

def terms22 : Array TaggedTerm := #[
  ⟨1, ![2, -1, -2, 0, 0, 1], -2⟩,
  ⟨1, ![2, -1, -2, 0, 1, 0], -2⟩,
  ⟨1, ![2, -1, -2, 1, 0, 0], -2⟩,
  ⟨1, ![2, -1, 0, -2, 0, 1], -2⟩,
  ⟨1, ![2, -1, 0, -2, 1, 0], -2⟩,
  ⟨1, ![2, -1, 0, 0, -2, 1], -2⟩,
  ⟨1, ![2, -1, 0, 0, 1, -2], -2⟩,
  ⟨1, ![2, -1, 0, 1, -2, 0], -2⟩,
  ⟨1, ![2, -1, 0, 1, 0, -2], -2⟩,
  ⟨1, ![2, -1, 1, -2, 0, 0], -2⟩,
  ⟨1, ![2, -1, 1, 0, -2, 0], -2⟩,
  ⟨1, ![2, -1, 1, 0, 0, -2], -2⟩,
  ⟨1, ![2, 0, -2, -1, 0, 1], 1⟩,
  ⟨1, ![2, 0, -2, -1, 1, 0], 1⟩,
  ⟨1, ![2, 0, -2, 0, -1, 1], 1⟩,
  ⟨1, ![2, 0, -2, 0, 1, -1], 1⟩,
  ⟨1, ![2, 0, -2, 1, -1, 0], 1⟩,
  ⟨1, ![2, 0, -2, 1, 0, -1], 1⟩,
  ⟨1, ![2, 0, -1, -2, 0, 1], 1⟩,
  ⟨1, ![2, 0, -1, -2, 1, 0], 1⟩,
  ⟨1, ![2, 0, -1, 0, -2, 1], 1⟩,
  ⟨1, ![2, 0, -1, 0, 1, -2], 1⟩,
  ⟨1, ![2, 0, -1, 1, -2, 0], 1⟩,
  ⟨1, ![2, 0, -1, 1, 0, -2], 1⟩,
  ⟨1, ![2, 0, 0, -2, -1, 1], 1⟩,
  ⟨1, ![2, 0, 0, -2, 1, -1], 1⟩,
  ⟨1, ![2, 0, 0, -1, -2, 1], 1⟩,
  ⟨1, ![2, 0, 0, -1, 1, -2], 1⟩,
  ⟨1, ![2, 0, 0, 1, -2, -1], 1⟩,
  ⟨1, ![2, 0, 0, 1, -1, -2], 1⟩,
  ⟨1, ![2, 0, 1, -2, -1, 0], 1⟩,
  ⟨1, ![2, 0, 1, -2, 0, -1], 1⟩,
  ⟨1, ![2, 0, 1, -1, -2, 0], 1⟩,
  ⟨1, ![2, 0, 1, -1, 0, -2], 1⟩,
  ⟨1, ![2, 0, 1, 0, -2, -1], 1⟩,
  ⟨1, ![2, 0, 1, 0, -1, -2], 1⟩
]

def terms23 : Array TaggedTerm := #[
  ⟨1, ![1, -3, 0, 0, 1, 1], -4⟩,
  ⟨1, ![1, -3, 0, 1, 0, 1], -4⟩,
  ⟨1, ![1, -3, 0, 1, 1, 0], -4⟩,
  ⟨1, ![1, -3, 1, 0, 0, 1], -4⟩,
  ⟨1, ![1, -3, 1, 0, 1, 0], -4⟩,
  ⟨1, ![1, -3, 1, 1, 0, 0], -4⟩,
  ⟨1, ![1, 0, -3, 0, 1, 1], 2⟩,
  ⟨1, ![1, 0, -3, 1, 0, 1], 2⟩,
  ⟨1, ![1, 0, -3, 1, 1, 0], 2⟩,
  ⟨1, ![1, 0, 0, -3, 1, 1], 2⟩,
  ⟨1, ![1, 0, 0, 1, -3, 1], 2⟩,
  ⟨1, ![1, 0, 0, 1, 1, -3], 2⟩,
  ⟨1, ![1, 0, 1, -3, 0, 1], 2⟩,
  ⟨1, ![1, 0, 1, -3, 1, 0], 2⟩,
  ⟨1, ![1, 0, 1, 0, -3, 1], 2⟩,
  ⟨1, ![1, 0, 1, 0, 1, -3], 2⟩,
  ⟨1, ![1, 0, 1, 1, -3, 0], 2⟩,
  ⟨1, ![1, 0, 1, 1, 0, -3], 2⟩
]

def terms24 : Array TaggedTerm := #[
  ⟨0, ![2, -2, 0, 0, 0, 0], -24⟩,
  ⟨0, ![2, 0, -2, 0, 0, 0], 6⟩,
  ⟨0, ![2, 0, 0, -2, 0, 0], 6⟩,
  ⟨0, ![2, 0, 0, 0, -2, 0], 6⟩,
  ⟨0, ![2, 0, 0, 0, 0, -2], 6⟩
]

def terms25 : Array TaggedTerm := #[
  ⟨1, ![2, 0, -1, -1, -1, 1], 6⟩,
  ⟨1, ![2, 0, -1, -1, 1, -1], 6⟩,
  ⟨1, ![2, 0, -1, 1, -1, -1], 6⟩,
  ⟨1, ![2, 0, 1, -1, -1, -1], 6⟩,
  ⟨1, ![2, 1, -1, -1, -1, 0], -6⟩,
  ⟨1, ![2, 1, -1, -1, 0, -1], -6⟩,
  ⟨1, ![2, 1, -1, 0, -1, -1], -6⟩,
  ⟨1, ![2, 1, 0, -1, -1, -1], -6⟩
]

def terms26 : Array TaggedTerm := #[
  ⟨0, ![0, 0, -2, 0, 1, 1], 2⟩,
  ⟨0, ![0, 0, -2, 1, 0, 1], 2⟩,
  ⟨0, ![0, 0, -2, 1, 1, 0], 2⟩,
  ⟨0, ![0, 0, 0, -2, 1, 1], 2⟩,
  ⟨0, ![0, 0, 0, 1, -2, 1], 2⟩,
  ⟨0, ![0, 0, 0, 1, 1, -2], 2⟩,
  ⟨0, ![0, 0, 1, -2, 0, 1], 2⟩,
  ⟨0, ![0, 0, 1, -2, 1, 0], 2⟩,
  ⟨0, ![0, 0, 1, 0, -2, 1], 2⟩,
  ⟨0, ![0, 0, 1, 0, 1, -2], 2⟩,
  ⟨0, ![0, 0, 1, 1, -2, 0], 2⟩,
  ⟨0, ![0, 0, 1, 1, 0, -2], 2⟩,
  ⟨0, ![0, 1, -2, 0, 0, 1], -2⟩,
  ⟨0, ![0, 1, -2, 0, 1, 0], -2⟩,
  ⟨0, ![0, 1, -2, 1, 0, 0], -2⟩,
  ⟨0, ![0, 1, 0, -2, 0, 1], -2⟩,
  ⟨0, ![0, 1, 0, -2, 1, 0], -2⟩,
  ⟨0, ![0, 1, 0, 0, -2, 1], -2⟩,
  ⟨0, ![0, 1, 0, 0, 1, -2], -2⟩,
  ⟨0, ![0, 1, 0, 1, -2, 0], -2⟩,
  ⟨0, ![0, 1, 0, 1, 0, -2], -2⟩,
  ⟨0, ![0, 1, 1, -2, 0, 0], -2⟩,
  ⟨0, ![0, 1, 1, 0, -2, 0], -2⟩,
  ⟨0, ![0, 1, 1, 0, 0, -2], -2⟩
]

end MUB6.Certificate.GramFunctions.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10808 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10809 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10810 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10811 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10812 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10813 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10814 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10815 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10816 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10817 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10818 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10819 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10820 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10821 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10822 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10823 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10824 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10825 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10826 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10827 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10828 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10829 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10830 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10831 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10832 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10833 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10834 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10835 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10836 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10837 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10838 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10839 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10840 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10841 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10842 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10843 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10844 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10845 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10846 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10847 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10848 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10849 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10850 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10851 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10852 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10853 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10854 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10855 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10856 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10857 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10858 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10859 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10860 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10861 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10862 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10863 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10864 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10865 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10866 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10867 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10868 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10869 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10870 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10871 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10872 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10873 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10910 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10911 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10912 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10913 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10914 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10915 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10916 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10917 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10918 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10919 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10920 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10921 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10922 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10923 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10924 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10925 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10926 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10927 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10928 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10929 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10930 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10931 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10932 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10933 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10934 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10935 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10936 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10937 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10938 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10939 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10940 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10941 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10942 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10943 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10944 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10945 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11498 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11499 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11500 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11501 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11502 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11503 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11504 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11505 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11506 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11507 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11508 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11509 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11510 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11511 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11512 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11513 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11514 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11515 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11516 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11517 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11518 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11519 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11520 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11521 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11522 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11523 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11524 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11525 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11526 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11527 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11528 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11529 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11530 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11531 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11532 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11533 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11534 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11535 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11536 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11537 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11538 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11539 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11540 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11541 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11542 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11543 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11544 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11545 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11558 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11559 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11560 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11561 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11562 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11563 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11564 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11565 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11566 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11567 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11568 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11569 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11606 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11607 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11608 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11609 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11610 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11611 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11612 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11613 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11614 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11615 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11616 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11617 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11642 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11643 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11644 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11645 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11646 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11647 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11648 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11649 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11650 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11651 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11652 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11653 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11666 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11667 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11668 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11669 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11670 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11671 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11672 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11673 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11674 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11675 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11676 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11677 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11702 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11703 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11704 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11705 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11706 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11707 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11708 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11709 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11710 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11711 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11712 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11713 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11714 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11715 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11716 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11717 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11718 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11719 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11720 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11721 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11722 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11723 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11724 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11725 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11726 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11727 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11728 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11729 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11730 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11731 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11732 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11733 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11734 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11735 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11736 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11737 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11792 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11793 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11794 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11795 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11796 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11797 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11798 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11799 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11800 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11801 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11802 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11803 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11804 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11805 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11806 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11807 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11808 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11809 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11810 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11811 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11812 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11813 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11814 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11815 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11816 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11817 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11818 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11819 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11820 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11821 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11822 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11823 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11824 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11825 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11826 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11827 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11828 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11829 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11830 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11831 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11832 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11833 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11834 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11835 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11836 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11837 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11838 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11839 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11840 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11841 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11842 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11843 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11844 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11845 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11846 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2366, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11847 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -6), (key2366, -6), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11848 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -6), (key2366, -6), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11849 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11850 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11851 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11852 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -12), (key2456, 4), (key2458, -6), (key2517, 4), (key2519, -6), (key2523, 4), (key2567, 2), (key2579, 4)]

def row11853 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -12), (key2456, 4), (key2458, -6), (key2517, 4), (key2519, -6), (key2523, 4), (key2567, 2), (key2579, 4)]

def row11854 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -12), (key2456, 4), (key2458, -6), (key2517, 4), (key2519, -6), (key2523, 4), (key2567, 2), (key2579, 4)]

def row11855 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -8), (key2458, -6), (key2517, 4), (key2519, -4), (key2523, 4), (key2579, 4)]

def row11856 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -8), (key2458, -6), (key2517, 2), (key2519, -4), (key2523, 4), (key2528, 2), (key2560, 4)]

def row11857 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -8), (key2458, -6), (key2517, 2), (key2519, -4), (key2523, 4), (key2528, 2), (key2560, 4)]

def row11858 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11859 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11860 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11861 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11862 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11863 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11882 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11883 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11884 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11885 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11886 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11887 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11888 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11889 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11890 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11891 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11892 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11893 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11894 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11895 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11896 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11897 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11898 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11899 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11954 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11955 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11956 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11957 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11958 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11959 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11960 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11961 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11962 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11963 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11964 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11965 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11966 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11967 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11968 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11969 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11970 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11971 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11990 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2567, -12), (key2579, -12)]

def row11991 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2567, -12), (key2579, -12)]

def row11992 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2567, -12), (key2579, -12)]

def row11993 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2567, -12), (key2579, -12)]

def row11994 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2567, -12), (key2579, -12)]

def row11995 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2567, -12), (key2579, -12)]

def row11996 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row11997 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row11998 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row11999 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12000 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12001 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12002 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12003 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12004 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12005 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12006 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12007 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12008 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12009 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12010 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12011 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12012 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12013 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12014 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12015 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12016 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12017 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12018 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12019 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12020 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12021 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12022 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12023 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12024 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12025 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12044 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12045 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12046 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12047 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12048 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12049 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12050 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12051 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12052 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12053 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12054 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12055 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12056 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12057 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12058 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12059 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12060 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12061 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12098 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12099 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12100 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12101 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12102 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12103 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12104 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12105 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12106 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12107 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12108 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12109 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12110 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12111 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12112 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12113 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12114 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12115 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12116 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12117 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12118 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12119 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12120 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12121 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12122 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12123 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12124 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12125 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12126 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12127 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12128 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12129 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12130 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12131 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12132 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12133 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12134 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12135 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12136 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12137 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12138 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12139 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12140 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12141 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12142 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12143 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12144 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12145 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12146 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12147 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12148 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12149 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12150 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12151 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12188 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12189 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12190 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12191 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12192 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12193 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12194 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12195 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12196 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12197 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2525, -4), (key2562, 4), (key2564, 4)]

def row12198 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2525, -4), (key2562, 4), (key2564, 4)]

def row12199 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2525, -4), (key2562, 4), (key2564, 4)]

def row12200 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12201 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12202 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -2), (key2525, -4), (key2532, 2), (key2562, 4), (key2564, 4)]

def row12203 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -2), (key2525, -4), (key2532, 2), (key2562, 4), (key2564, 4)]

def row12204 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12205 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12206 : Integer.Sparse Key := [(key1700, 24), (key1851, -24)]

def row12207 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

def row12208 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

def row12209 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

def row12210 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

def row12211 : Integer.Sparse Key := [(key219, -24), (key491, 24)]

def row12212 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

def row12213 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

def row12214 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

def row12215 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

def row12216 : Integer.Sparse Key := [(key30, -24), (key110, 24)]

def row12217 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

def row12218 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

def row12219 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

def row12220 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

def row12221 : Integer.Sparse Key := [(key1483, -24), (key1709, 24)]

def row12222 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

def row12223 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

def row12224 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

def row12225 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

def row12226 : Integer.Sparse Key := [(key1274, -24), (key1697, 24)]

def row12227 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

def row12228 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

def row12229 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

def row12230 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

def row12231 : Integer.Sparse Key := [(key1485, -24), (key1711, 24)]

def row12232 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

def row12233 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

def row12234 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

def row12235 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

def row12236 : Integer.Sparse Key := [(key1272, -24), (key1695, 24)]

def row12237 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

def row12238 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

def row12239 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

def row12240 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

def row12241 : Integer.Sparse Key := [(key1359, -24), (key1485, 24)]

def row12242 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

def row12243 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

def row12244 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

def row12245 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

def row12246 : Integer.Sparse Key := [(key395, -24), (key440, 24)]

def row12247 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

def row12248 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

def row12249 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

def row12250 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

def row12251 : Integer.Sparse Key := [(key1711, 24), (key1936, -24)]

def row12252 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

def row12253 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

def row12254 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

def row12255 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

def row12256 : Integer.Sparse Key := [(key348, -24), (key505, 24)]

def row12257 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

def row12258 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

def row12259 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

def row12260 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

def row12261 : Integer.Sparse Key := [(key1273, 24), (key1850, -24)]

def row12262 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

def row12263 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

def row12264 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

def row12265 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

def row12266 : Integer.Sparse Key := [(key1274, 24), (key1932, -24)]

def row12267 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

def row12268 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

def row12269 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

def row12270 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

def row12271 : Integer.Sparse Key := [(key750, -24), (key927, 24)]

def row12272 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

def row12273 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

def row12274 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

def row12275 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

def row12276 : Integer.Sparse Key := [(key30, 24), (key146, -24)]

def row12277 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

def row12278 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

def row12279 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

def row12280 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

def row12281 : Integer.Sparse Key := [(key1273, -24), (key1696, 24)]

def row12282 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

def row12283 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

def row12284 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

def row12285 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

def row12286 : Integer.Sparse Key := [(key1357, -24), (key1483, 24)]

def row12287 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12288 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

def row12289 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

def row12290 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

def row12291 : Integer.Sparse Key := [(key1489, -24), (key1715, 24)]

def row12292 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

def row12293 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

def row12294 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

def row12295 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

def row12296 : Integer.Sparse Key := [(key118, 24), (key155, -24)]

def row12297 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

def row12298 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

def row12299 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

def row12300 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

def row12301 : Integer.Sparse Key := [(key1498, -24), (key1730, 24)]

def row12302 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

def row12303 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

def row12304 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

def row12305 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

def row12306 : Integer.Sparse Key := [(key670, 24), (key680, -24)]

def row12307 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

def row12308 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

def row12309 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

def row12310 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

def row12311 : Integer.Sparse Key := [(key1710, 24), (key1859, -24)]

def row12312 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

def row12313 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

def row12314 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

def row12315 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

def row12316 : Integer.Sparse Key := [(key1484, -24), (key1710, 24)]

def row12317 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

def row12318 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

def row12319 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

def row12320 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

def row12321 : Integer.Sparse Key := [(key1277, -24), (key1700, 24)]

def row12322 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

def row12323 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

def row12324 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

def row12325 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

def row12326 : Integer.Sparse Key := [(key288, -24), (key513, 24)]

def row12327 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

def row12328 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

def row12329 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

def row12330 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

def row12331 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

def row12332 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

def row12333 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

def row12334 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

def row12335 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

def row12336 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

def row12337 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

def row12338 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

def row12339 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

def row12340 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

def row12341 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

def row12342 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

def row12343 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

def row12344 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

def row12345 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

def row12346 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

def row12347 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

def row12348 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

def row12349 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

def row12350 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

def row12351 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

def row12352 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

def row12353 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

def row12354 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

def row12355 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

def row12356 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

def row12357 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

def row12358 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

def row12359 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

def row12360 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

def row12361 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

def row12362 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

def row12363 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

def row12364 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

def row12365 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

def row12366 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

def row12367 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

def row12368 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

def row12369 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

def row12370 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

def row12371 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

def row12372 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

def row12373 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

def row12374 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

def row12375 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

def row12376 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

def row12377 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

def row12378 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

def row12379 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

def row12380 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

def row12381 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

def row12382 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

def row12383 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

def row12384 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

def row12385 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

def row12386 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

def row12387 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

def row12388 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

def row12389 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

def row12390 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

def row12391 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

def row12392 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

def row12393 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

def row12394 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

def row12395 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

def row12396 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

def row12397 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

def row12398 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

def row12399 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

def row12400 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

def row12401 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

def row12402 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

def row12403 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

def row12404 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

def row12405 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

def row12406 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

def row12407 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

def row12408 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

def row12409 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

def row12410 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

def row12411 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

def row12412 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

def row12413 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

def row12414 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

def row12415 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12416 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

def row12417 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

def row12418 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

def row12419 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

def row12420 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

def row12421 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

def row12422 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

def row12423 : Integer.Sparse Key := [(key2414, -6), (key2546, 6), (key2548, 18), (key3033, -12), (key3120, -6)]

def row12424 : Integer.Sparse Key := [(key2414, -6), (key2546, 6), (key2548, 18), (key3033, -12), (key3120, -6)]

def row12425 : Integer.Sparse Key := [(key2414, -6), (key2546, 6), (key2548, 18), (key3033, -12), (key3120, -6)]

def row12426 : Integer.Sparse Key := [(key2414, -6), (key2487, -6), (key2546, 6), (key2548, 18), (key3033, -12)]

def row12427 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

def row12428 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

def row12429 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

def row12430 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

def row12431 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

def row12432 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

def row12433 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

def row12434 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

def row12435 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

def row12436 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

def row12437 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

def row12438 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

def row12439 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

def row12440 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

def row12441 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

def row12442 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

def row12443 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

def row12444 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

def row12445 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

def row12446 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

def row12447 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

def row12448 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

def row12449 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

def row12450 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

def row12451 : Integer.Sparse Key := [(key2414, 2), (key2424, 4), (key2487, -6), (key2492, -18), (key3033, 4), (key3039, 8), (key3138, 6)]

def row12452 : Integer.Sparse Key := [(key2414, 2), (key2424, 4), (key2487, -6), (key2492, -18), (key3033, 4), (key3039, 8), (key3138, 6)]

def row12453 : Integer.Sparse Key := [(key2414, 2), (key2424, 4), (key2487, -6), (key2492, -18), (key3033, 4), (key3039, 8), (key3138, 6)]

def row12454 : Integer.Sparse Key := [(key2414, 2), (key2424, 12), (key2487, -6), (key2492, -18), (key2548, 6), (key3033, 4)]

def row12455 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

def row12456 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

def row12457 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

def row12458 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

def row12459 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

def row12460 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

def row12461 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

def row12462 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

def row12463 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

def row12464 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

def row12465 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

def row12466 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

def row12467 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

def row12468 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

def row12469 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

def row12470 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

def row12471 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

def row12472 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

def row12473 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

def row12474 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

def row12475 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

def row12476 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

def row12477 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

def row12478 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

def row12479 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

def row12480 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

def row12481 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

def row12482 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

def row12483 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

def row12484 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

def row12485 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

def row12486 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

def row12487 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

def row12488 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

def row12489 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

def row12490 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

def row12491 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

def row12492 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

def row12493 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

def row12494 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

def row12495 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

def row12496 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

def row12497 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

def row12498 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

def row12499 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2742, 2), (key3047, 3), (key3050, -12), (key3054, 3), (key3066, -6), (key3072, 4), (key3103, -6), (key3110, 6)]

def row12500 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2742, 2), (key3047, 3), (key3050, -12), (key3054, 3), (key3066, -6), (key3072, 4), (key3103, -6), (key3110, 6)]

def row12501 : Integer.Sparse Key := [(key2679, 3), (key2689, 4), (key2742, 2), (key2955, 2), (key3047, 3), (key3050, -12), (key3054, 2), (key3066, -6), (key3072, 4), (key3103, -6), (key3110, 4)]

def row12502 : Integer.Sparse Key := [(key2679, 3), (key2689, 6), (key2742, 6), (key2955, 6), (key3047, 3), (key3050, -12), (key3066, -6), (key3103, -6)]

def row12503 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -2), (key2715, 6), (key2818, 6), (key3047, -6), (key3061, -4), (key3096, -6)]

def row12504 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -2), (key2715, 6), (key2818, 6), (key3047, -6), (key3061, -4), (key3096, -6)]

def row12505 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -2), (key2715, 6), (key2813, -2), (key2818, 6), (key3047, -6), (key3061, -4), (key3096, -4)]

def row12506 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -6), (key2715, 6), (key2813, -6), (key2818, 6), (key3047, -6)]

def row12507 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2710, -6), (key2715, -12), (key2742, 2), (key2979, -6), (key3047, 3), (key3054, 3), (key3072, 4), (key3110, 6)]

def row12508 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2710, -6), (key2715, -12), (key2742, 2), (key2979, -6), (key3047, 3), (key3054, 3), (key3072, 4), (key3110, 6)]

def row12509 : Integer.Sparse Key := [(key2679, 3), (key2689, 4), (key2710, -6), (key2715, -12), (key2742, 2), (key2955, 2), (key2979, -6), (key3047, 3), (key3054, 2), (key3072, 4), (key3110, 4)]

def row12510 : Integer.Sparse Key := [(key2679, 3), (key2689, 6), (key2710, -6), (key2715, -12), (key2742, 6), (key2955, 6), (key2979, -6), (key3047, 3)]

def row12511 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

def row12512 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

def row12513 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

def row12514 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

def row12515 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

def row12516 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

def row12517 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

def row12518 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

def row12519 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

def row12520 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

def row12521 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

def row12522 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

def row12523 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

def row12524 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

def row12525 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

def row12526 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

def row12527 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

def row12528 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

def row12529 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

def row12530 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

def row12531 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

def row12532 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

def row12533 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

def row12534 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

def row12535 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

def row12536 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

def row12537 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

def row12538 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

def row12539 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12540 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12541 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12542 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12543 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12544 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12545 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12546 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12547 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12548 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12549 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12550 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12551 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12552 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12553 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12554 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12555 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12556 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12557 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12558 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12559 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12560 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12561 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12562 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12563 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12564 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12565 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12566 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12567 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12568 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12569 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12570 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12571 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12572 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12573 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12574 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12575 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12576 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12577 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12578 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12579 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12580 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12581 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12582 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12583 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12584 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12585 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12586 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12587 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12588 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12589 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12590 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12591 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12592 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12593 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12594 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12595 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12596 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12597 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12598 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12599 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12600 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12601 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12602 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12603 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12604 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12605 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12606 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12607 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12608 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12609 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12610 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12611 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12612 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12613 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12614 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12615 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12616 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12617 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12618 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12619 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12620 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12621 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12622 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12623 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12624 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12625 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12626 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12627 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12628 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12629 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12630 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12631 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12632 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12633 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12634 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12635 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12636 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12637 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12638 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12639 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12640 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12641 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12642 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12643 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12644 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12645 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12646 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12647 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12648 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12649 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12650 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12651 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12652 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12653 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12654 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12655 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12656 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12657 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12658 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12659 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12660 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12661 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12662 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12663 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12664 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12665 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12666 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12667 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12668 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12669 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12670 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12671 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12672 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12673 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12674 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12675 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12676 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12677 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12678 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12679 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12680 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12681 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12682 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12683 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12684 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12685 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12686 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12687 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12688 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12689 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12690 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12691 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12692 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12693 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12694 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12695 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12696 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12697 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12698 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12699 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12700 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12701 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12702 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12703 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12704 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12705 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12706 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12707 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12708 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12709 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12710 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12711 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12712 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12713 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12714 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12715 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12716 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12717 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12718 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12719 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12720 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12721 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12722 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12723 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12724 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12725 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12726 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12727 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12728 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12729 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12730 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12731 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12732 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12733 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12734 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12735 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12736 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12737 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12738 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12739 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12740 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12741 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12742 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12743 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12744 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12745 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12746 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12747 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12748 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12749 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12750 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12751 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12752 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12753 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12754 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12755 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12756 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12757 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12758 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12759 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12760 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12761 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12762 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12763 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12764 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12765 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12766 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12767 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12768 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12769 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12770 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12771 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12772 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12773 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12774 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12775 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12776 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12777 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12778 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12779 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12780 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12781 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12782 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12783 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12784 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12785 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12786 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12787 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12788 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12789 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12790 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12791 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12792 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12793 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12794 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12795 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12796 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12797 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12798 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12799 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12800 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12801 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12802 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12803 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12804 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12805 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12806 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12807 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12808 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12809 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12810 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12811 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12812 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12813 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12814 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12815 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12816 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12817 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12818 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12819 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12820 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12821 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12822 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12823 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12824 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12825 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12826 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12827 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12828 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12829 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12830 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12831 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12832 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12833 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12834 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12835 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12836 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12837 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12838 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12839 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12840 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12841 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12842 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12843 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12844 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12845 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12846 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12847 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12848 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12849 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12850 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12851 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12852 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12853 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12854 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12855 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12856 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12857 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12858 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12859 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12860 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12861 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12862 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12863 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12864 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12865 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12866 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12867 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12868 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12869 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12870 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12871 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12872 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12873 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12874 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12875 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12876 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12877 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12878 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12879 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12880 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12881 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12882 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12883 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12884 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12885 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12886 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12887 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12888 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12889 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12890 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12891 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12892 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12893 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12894 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12895 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12896 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12897 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12898 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12899 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12900 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12901 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12902 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12903 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12904 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12905 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12906 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12907 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12908 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12909 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12910 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12911 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12912 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12913 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12914 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12915 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12916 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12917 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12918 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12919 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12920 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12921 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12922 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12923 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12924 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12925 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12926 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12927 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12928 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12929 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12930 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12931 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12932 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12933 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12934 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12935 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12936 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12937 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12938 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12939 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12940 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12941 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12942 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12943 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12944 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12945 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12946 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12947 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12948 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12949 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12950 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12951 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12952 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12953 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12954 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12955 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12956 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12957 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12958 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12959 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12960 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12961 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12962 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12963 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12964 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12965 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12966 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12967 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12968 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12969 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12970 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12971 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12972 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12973 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12974 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12975 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12976 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12977 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12978 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12979 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12980 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12981 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12982 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12983 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12984 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12985 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12986 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12987 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12988 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12989 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12990 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12991 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12992 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12993 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12994 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12995 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row12996 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row12997 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row12998 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row12999 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13000 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13001 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13002 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13003 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13004 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13005 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13006 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13007 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13008 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13009 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13010 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13011 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13012 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13013 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13014 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13015 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13016 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13017 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13018 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13019 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13020 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13021 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13022 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13023 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13024 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13025 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13026 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13027 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13028 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13029 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13030 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13031 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13032 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13033 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13034 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13035 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13036 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13037 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13038 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13039 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13040 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13041 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13042 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13043 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13044 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13045 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13046 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13047 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13048 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13049 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13050 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13051 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13052 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13053 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13054 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13055 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13056 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13057 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13058 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13059 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13060 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13061 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13062 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13063 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13064 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13065 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13066 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13067 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13068 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13069 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13070 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13071 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13072 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13073 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13074 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13075 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13076 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13077 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13078 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13079 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13080 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13081 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13082 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13083 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13084 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13085 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13086 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13087 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13088 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13089 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13090 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13091 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13092 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13093 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13094 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13095 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13096 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13097 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13098 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13099 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13100 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13101 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13102 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13103 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13104 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13105 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13106 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13107 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13108 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13109 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13110 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13111 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13112 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13113 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13114 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13115 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13116 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13117 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13118 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13119 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13120 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13121 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13122 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13123 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13124 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13125 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13126 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13127 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13128 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13129 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13130 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13131 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13132 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13133 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13134 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13135 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13136 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13137 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13138 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13139 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13140 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13141 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13142 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13143 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13144 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13145 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13146 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13147 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13148 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13149 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13150 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13151 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13152 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13153 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13154 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13155 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13156 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13157 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13158 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13159 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13160 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13161 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13162 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13163 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13164 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13165 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13166 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 4), (key561, -4), (key632, -2), (key647, 4)]

def row13167 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 4), (key561, -4), (key632, -2), (key647, 4)]

def row13168 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 4), (key561, -4), (key632, -2), (key647, 4)]

def row13169 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13170 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13171 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 2), (key561, -4), (key631, 2), (key632, -2), (key647, 4)]

def row13172 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 2), (key561, -4), (key631, 2), (key632, -2), (key647, 4)]

def row13173 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13174 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13175 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

def row13176 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

def row13177 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

def row13178 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

def row13179 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

def row13180 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -4), (key561, 4), (key632, 2), (key647, -2), (key650, 4)]

def row13181 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -4), (key561, 4), (key632, 2), (key647, -2), (key650, 4)]

def row13182 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

def row13183 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13184 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

def row13185 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

def row13186 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

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

def row7386 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7387 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7388 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7389 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7390 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7391 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7392 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7393 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7394 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7395 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7396 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7397 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7402 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7403 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7404 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7405 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7406 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7407 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7408 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7409 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7410 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7411 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7412 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7413 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7418 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7419 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7420 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7421 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

def row7422 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

def row7423 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, 2), (key202, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7424 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, 2), (key202, 2)]

def row7425 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

def row7426 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

def row7427 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7428 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7429 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7434 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7435 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7436 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7437 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7438 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7439 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7440 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7441 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7442 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7443 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7444 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7445 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7450 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7451 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7452 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7453 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7454 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7455 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7456 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7457 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7458 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7459 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7460 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7461 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7466 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7467 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7468 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7469 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7470 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7471 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7472 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7473 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7474 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7475 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7476 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7477 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7482 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7483 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7484 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7485 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, 2), (key2799, 4), (key2849, -8)]

def row7486 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, 2), (key2799, 4), (key2849, -8)]

def row7487 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, 2), (key2799, 4), (key2849, -8)]

def row7488 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7489 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7490 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2776, 2), (key2799, 4), (key2849, -8)]

def row7491 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2776, 2), (key2799, 4), (key2849, -8)]

def row7492 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7493 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7498 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2458, -4), (key2519, -2), (key2528, 4), (key2560, 2)]

def row7499 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2458, -4), (key2519, -2), (key2528, 4), (key2560, 2)]

def row7500 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2458, -4), (key2519, -2), (key2528, 4), (key2560, 2)]

def row7501 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 2), (key2519, -2), (key2523, 2), (key2528, 2), (key2530, -2), (key2560, 2)]

def row7502 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 2), (key2519, -2), (key2523, 2), (key2528, 2), (key2530, -2), (key2560, 2)]

def row7503 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2560, 2)]

def row7504 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2560, 2)]

def row7505 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2579, 2)]

def row7506 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2579, 2)]

def row7507 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2452, -4), (key2456, 4), (key2458, -4), (key2517, 4), (key2519, -4), (key2523, 4), (key2530, -4), (key2560, -2), (key2567, 2), (key2579, 4)]

def row7508 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2452, -4), (key2456, 4), (key2458, -4), (key2517, 4), (key2519, -4), (key2523, 4), (key2530, -4), (key2560, -2), (key2567, 2), (key2579, 4)]

def row7509 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2452, -4), (key2456, 4), (key2458, -4), (key2517, 4), (key2519, -4), (key2523, 4), (key2530, -4), (key2560, -2), (key2567, 2), (key2579, 4)]

def row7514 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7515 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7516 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7517 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7518 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7519 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7520 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7521 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7522 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7523 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7524 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7525 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7530 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7531 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7532 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7533 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7534 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7535 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7536 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7537 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7538 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7539 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7540 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7541 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7546 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7547 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7548 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7549 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7550 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7551 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7552 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7553 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7554 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7555 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7556 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7557 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7562 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7563 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7564 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7565 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

def row7566 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

def row7567 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, 2), (key2578, 2)]

def row7568 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, 2), (key2578, 2)]

def row7569 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

def row7570 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

def row7571 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7572 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7573 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7610 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7611 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7612 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7613 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7614 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7615 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7616 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7617 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7618 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7619 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7620 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7621 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7622 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7623 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7624 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7625 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7626 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7627 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7628 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7629 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7630 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7631 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7632 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7633 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7634 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7635 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7636 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7637 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7638 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7639 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7640 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7641 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7642 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7643 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7644 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7645 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7646 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7647 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7648 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7649 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7650 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7651 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7652 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7653 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7654 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7655 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7656 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7657 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7658 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7659 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7660 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7661 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7662 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7663 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7664 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7665 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7666 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7667 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7668 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7669 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7670 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7671 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7672 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7673 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7674 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7675 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7676 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7677 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7678 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7679 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7680 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7681 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7682 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7683 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7684 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7685 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7686 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7687 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7688 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7689 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7690 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7691 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7692 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7693 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7694 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7695 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7696 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7697 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7698 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7699 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7700 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7701 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7702 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7703 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7704 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7705 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7790 : Integer.Sparse Key := [(key2455, 24), (key2516, -24)]

end MUB6.Certificate.GramRows

end OAI
end


