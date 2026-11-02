-- Prove2me | Definitions.Def_OAIQ106D151
-- name    : OAIQ106D151
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:56:30.561885+00:00
-- url     : https://prove2.me/theorems/c88971d4-b546-4a21-8059-7db4b66981d6
-- title:
--   Definitions bundle OAIQ106D151 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1078 declarations of OpenAI's Lean: 1078 definitions. The definitions and types are `OAI.MUB6.Certificate.GramFunctions.Block4.terms13`, `OAI.MUB6.Certificate.GramFunctions.Block4.terms14`, `OAI.MUB6.Certificate.GramFunctions.Block4.terms15`, `OAI.MUB6.Certificate.GramFunctions.Block4.terms16`, `OAI.MUB6.Certificate.GramFunctions.Block4.terms17`, `OAI.MUB6.Certificate.GramRows.row13629`, `OAI.MUB6.Certificate.GramRows.row13630`, `OAI.MUB6.Certificate.GramRows.row13631`, `OAI.MUB6.Certificate.GramRows.row13632`, `OAI.MUB6.Certificate.GramRows.row13633`, `OAI.MUB6.Certificate.GramRows.row13634`, `OAI.MUB6.Certificate.GramRows.row13635`, `OAI.MUB6.Certificate.GramRows.row13636`, `OAI.MUB6.Certificate.GramRows.row13637`, `OAI.MUB6.Certificate.GramRows.row13638`, `OAI.MUB6.Certificate.GramRows.row13639`, `OAI.MUB6.Certificate.GramRows.row13640`, `OAI.MUB6.Certificate.GramRows.row13641`, `OAI.MUB6.Certificate.GramRows.row13642`, `OAI.MUB6.Certificate.GramRows.row13643`, `OAI.MUB6.Certificate.GramRows.row13644`, `OAI.MUB6.Certificate.GramRows.row13645`, `OAI.MUB6.Certificate.GramRows.row13646`, `OAI.MUB6.Certificate.GramRows.row13647`, `OAI.MUB6.Certificate.GramRows.row13648`, `OAI.MUB6.Certificate.GramRows.row13649`, `OAI.MUB6.Certificate.GramRows.row13656`, `OAI.MUB6.Certificate.GramRows.row13657`, `OAI.MUB6.Certificate.GramRows.row13658`, `OAI.MUB6.Certificate.GramRows.row13665`, `OAI.MUB6.Certificate.GramRows.row13666`, `OAI.MUB6.Certificate.GramRows.row13667`, `OAI.MUB6.Certificate.GramRows.row13668`, `OAI.MUB6.Certificate.GramRows.row13669`, `OAI.MUB6.Certificate.GramRows.row13670`, `OAI.MUB6.Certificate.GramRows.row13671`, `OAI.MUB6.Certificate.GramRows.row13672`, `OAI.MUB6.Certificate.GramRows.row13673`, `OAI.MUB6.Certificate.GramRows.row13674`, `OAI.MUB6.Certificate.GramRows.row13675` and 1038 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramFunctions_Block4`, `MutuallyUnbiased_GramRows_Block130`, `MutuallyUnbiased_GramRows_Block131`, `MutuallyUnbiased_GramRows_Block140`, `MutuallyUnbiased_GramRows_Block141`, `MutuallyUnbiased_GramRows_Block142`, `MutuallyUnbiased_GramRows_Block143`, `MutuallyUnbiased_GramRows_Block144`, `MutuallyUnbiased_GramRows_Block145`, `MutuallyUnbiased_GramRows_Block146`, `MutuallyUnbiased_GramRows_Block147`, `MutuallyUnbiased_GramRows_Block148`, `MutuallyUnbiased_GramRows_Block150`, `MutuallyUnbiased_GramRows_Block151`, `MutuallyUnbiased_GramRows_Block152`, `MutuallyUnbiased_GramRows_Block153`, `MutuallyUnbiased_GramRows_Block154`, `MutuallyUnbiased_GramRows_Block155`, `MutuallyUnbiased_GramRows_Block156`, `MutuallyUnbiased_GramRows_Block157`.
--
--   **Imports.** It imports the bundles `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092`, `OAIQ106D093` and `OAIQ106D094` of this split.
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
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D093
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block4

def terms13 : Array TaggedTerm := #[
  ⟨1, ![1, -2, -1, 0, 0, 2], 2⟩,
  ⟨1, ![1, -2, -1, 0, 2, 0], 2⟩,
  ⟨1, ![1, -2, -1, 2, 0, 0], 2⟩,
  ⟨1, ![1, -2, 0, -1, 0, 2], -1⟩,
  ⟨1, ![1, -2, 0, -1, 2, 0], -1⟩,
  ⟨1, ![1, -2, 0, 0, -1, 2], -1⟩,
  ⟨1, ![1, -2, 0, 0, 2, -1], -1⟩,
  ⟨1, ![1, -2, 0, 2, -1, 0], -1⟩,
  ⟨1, ![1, -2, 0, 2, 0, -1], -1⟩,
  ⟨1, ![1, -1, -2, 0, 0, 2], 2⟩,
  ⟨1, ![1, -1, -2, 0, 2, 0], 2⟩,
  ⟨1, ![1, -1, -2, 2, 0, 0], 2⟩,
  ⟨1, ![1, -1, 0, -2, 0, 2], -1⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], -1⟩,
  ⟨1, ![1, -1, 0, 0, -2, 2], -1⟩,
  ⟨1, ![1, -1, 0, 0, 2, -2], -1⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], -1⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], -1⟩,
  ⟨1, ![1, 0, -2, -1, 0, 2], -1⟩,
  ⟨1, ![1, 0, -2, -1, 2, 0], -1⟩,
  ⟨1, ![1, 0, -2, 0, -1, 2], -1⟩,
  ⟨1, ![1, 0, -2, 0, 2, -1], -1⟩,
  ⟨1, ![1, 0, -2, 2, -1, 0], -1⟩,
  ⟨1, ![1, 0, -2, 2, 0, -1], -1⟩,
  ⟨1, ![1, 0, -1, -2, 0, 2], -1⟩,
  ⟨1, ![1, 0, -1, -2, 2, 0], -1⟩,
  ⟨1, ![1, 0, -1, 0, -2, 2], -1⟩,
  ⟨1, ![1, 0, -1, 0, 2, -2], -1⟩,
  ⟨1, ![1, 0, -1, 2, -2, 0], -1⟩,
  ⟨1, ![1, 0, -1, 2, 0, -2], -1⟩,
  ⟨1, ![1, 0, 0, -2, -1, 2], 2⟩,
  ⟨1, ![1, 0, 0, -2, 2, -1], 2⟩,
  ⟨1, ![1, 0, 0, -1, -2, 2], 2⟩,
  ⟨1, ![1, 0, 0, -1, 2, -2], 2⟩,
  ⟨1, ![1, 0, 0, 2, -2, -1], 2⟩,
  ⟨1, ![1, 0, 0, 2, -1, -2], 2⟩
]

def terms14 : Array TaggedTerm := #[
  ⟨1, ![1, -2, 0, -1, 0, 2], -1⟩,
  ⟨1, ![1, -2, 0, -1, 2, 0], -1⟩,
  ⟨1, ![1, -2, 0, 0, -1, 2], -1⟩,
  ⟨1, ![1, -2, 0, 0, 2, -1], -1⟩,
  ⟨1, ![1, -2, 0, 2, -1, 0], -1⟩,
  ⟨1, ![1, -2, 0, 2, 0, -1], -1⟩,
  ⟨1, ![1, -2, 2, -1, 0, 0], 2⟩,
  ⟨1, ![1, -2, 2, 0, -1, 0], 2⟩,
  ⟨1, ![1, -2, 2, 0, 0, -1], 2⟩,
  ⟨1, ![1, -1, 0, -2, 0, 2], 1⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], 1⟩,
  ⟨1, ![1, -1, 0, 0, -2, 2], 1⟩,
  ⟨1, ![1, -1, 0, 0, 2, -2], 1⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], 1⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], 1⟩,
  ⟨1, ![1, -1, 2, -2, 0, 0], -2⟩,
  ⟨1, ![1, -1, 2, 0, -2, 0], -2⟩,
  ⟨1, ![1, -1, 2, 0, 0, -2], -2⟩,
  ⟨1, ![1, 0, -2, -1, 0, 2], -1⟩,
  ⟨1, ![1, 0, -2, -1, 2, 0], -1⟩,
  ⟨1, ![1, 0, -2, 0, -1, 2], -1⟩,
  ⟨1, ![1, 0, -2, 0, 2, -1], -1⟩,
  ⟨1, ![1, 0, -2, 2, -1, 0], -1⟩,
  ⟨1, ![1, 0, -2, 2, 0, -1], -1⟩,
  ⟨1, ![1, 0, -1, -2, 0, 2], 1⟩,
  ⟨1, ![1, 0, -1, -2, 2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨1, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨1, ![1, 0, -1, 2, -2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 2, 0, -2], 1⟩,
  ⟨1, ![1, 2, -2, -1, 0, 0], 2⟩,
  ⟨1, ![1, 2, -2, 0, -1, 0], 2⟩,
  ⟨1, ![1, 2, -2, 0, 0, -1], 2⟩,
  ⟨1, ![1, 2, -1, -2, 0, 0], -2⟩,
  ⟨1, ![1, 2, -1, 0, -2, 0], -2⟩,
  ⟨1, ![1, 2, -1, 0, 0, -2], -2⟩
]

def terms15 : Array TaggedTerm := #[
  ⟨1, ![2, -2, 0, -1, 0, 1], -1⟩,
  ⟨1, ![2, -2, 0, -1, 1, 0], -1⟩,
  ⟨1, ![2, -2, 0, 0, -1, 1], -1⟩,
  ⟨1, ![2, -2, 0, 0, 1, -1], -1⟩,
  ⟨1, ![2, -2, 0, 1, -1, 0], -1⟩,
  ⟨1, ![2, -2, 0, 1, 0, -1], -1⟩,
  ⟨1, ![2, -2, 1, -1, 0, 0], 2⟩,
  ⟨1, ![2, -2, 1, 0, -1, 0], 2⟩,
  ⟨1, ![2, -2, 1, 0, 0, -1], 2⟩,
  ⟨1, ![2, -1, 0, -2, 0, 1], 1⟩,
  ⟨1, ![2, -1, 0, -2, 1, 0], 1⟩,
  ⟨1, ![2, -1, 0, 0, -2, 1], 1⟩,
  ⟨1, ![2, -1, 0, 0, 1, -2], 1⟩,
  ⟨1, ![2, -1, 0, 1, -2, 0], 1⟩,
  ⟨1, ![2, -1, 0, 1, 0, -2], 1⟩,
  ⟨1, ![2, -1, 1, -2, 0, 0], -2⟩,
  ⟨1, ![2, -1, 1, 0, -2, 0], -2⟩,
  ⟨1, ![2, -1, 1, 0, 0, -2], -2⟩,
  ⟨1, ![2, 0, -2, -1, 0, 1], -1⟩,
  ⟨1, ![2, 0, -2, -1, 1, 0], -1⟩,
  ⟨1, ![2, 0, -2, 0, -1, 1], -1⟩,
  ⟨1, ![2, 0, -2, 0, 1, -1], -1⟩,
  ⟨1, ![2, 0, -2, 1, -1, 0], -1⟩,
  ⟨1, ![2, 0, -2, 1, 0, -1], -1⟩,
  ⟨1, ![2, 0, -1, -2, 0, 1], 1⟩,
  ⟨1, ![2, 0, -1, -2, 1, 0], 1⟩,
  ⟨1, ![2, 0, -1, 0, -2, 1], 1⟩,
  ⟨1, ![2, 0, -1, 0, 1, -2], 1⟩,
  ⟨1, ![2, 0, -1, 1, -2, 0], 1⟩,
  ⟨1, ![2, 0, -1, 1, 0, -2], 1⟩,
  ⟨1, ![2, 1, -2, -1, 0, 0], 2⟩,
  ⟨1, ![2, 1, -2, 0, -1, 0], 2⟩,
  ⟨1, ![2, 1, -2, 0, 0, -1], 2⟩,
  ⟨1, ![2, 1, -1, -2, 0, 0], -2⟩,
  ⟨1, ![2, 1, -1, 0, -2, 0], -2⟩,
  ⟨1, ![2, 1, -1, 0, 0, -2], -2⟩
]

def terms16 : Array TaggedTerm := #[
  ⟨1, ![1, -1, 0, -2, 1, 1], 2⟩,
  ⟨1, ![1, -1, 0, 1, -2, 1], 2⟩,
  ⟨1, ![1, -1, 0, 1, 1, -2], 2⟩,
  ⟨1, ![1, -1, 1, -2, 0, 1], -1⟩,
  ⟨1, ![1, -1, 1, -2, 1, 0], -1⟩,
  ⟨1, ![1, -1, 1, 0, -2, 1], -1⟩,
  ⟨1, ![1, -1, 1, 0, 1, -2], -1⟩,
  ⟨1, ![1, -1, 1, 1, -2, 0], -1⟩,
  ⟨1, ![1, -1, 1, 1, 0, -2], -1⟩,
  ⟨1, ![1, 0, -1, -2, 1, 1], 2⟩,
  ⟨1, ![1, 0, -1, 1, -2, 1], 2⟩,
  ⟨1, ![1, 0, -1, 1, 1, -2], 2⟩,
  ⟨1, ![1, 0, 1, -2, -1, 1], -1⟩,
  ⟨1, ![1, 0, 1, -2, 1, -1], -1⟩,
  ⟨1, ![1, 0, 1, -1, -2, 1], -1⟩,
  ⟨1, ![1, 0, 1, -1, 1, -2], -1⟩,
  ⟨1, ![1, 0, 1, 1, -2, -1], -1⟩,
  ⟨1, ![1, 0, 1, 1, -1, -2], -1⟩,
  ⟨1, ![1, 1, -1, -2, 0, 1], -1⟩,
  ⟨1, ![1, 1, -1, -2, 1, 0], -1⟩,
  ⟨1, ![1, 1, -1, 0, -2, 1], -1⟩,
  ⟨1, ![1, 1, -1, 0, 1, -2], -1⟩,
  ⟨1, ![1, 1, -1, 1, -2, 0], -1⟩,
  ⟨1, ![1, 1, -1, 1, 0, -2], -1⟩,
  ⟨1, ![1, 1, 0, -2, -1, 1], -1⟩,
  ⟨1, ![1, 1, 0, -2, 1, -1], -1⟩,
  ⟨1, ![1, 1, 0, -1, -2, 1], -1⟩,
  ⟨1, ![1, 1, 0, -1, 1, -2], -1⟩,
  ⟨1, ![1, 1, 0, 1, -2, -1], -1⟩,
  ⟨1, ![1, 1, 0, 1, -1, -2], -1⟩,
  ⟨1, ![1, 1, 1, -2, -1, 0], 2⟩,
  ⟨1, ![1, 1, 1, -2, 0, -1], 2⟩,
  ⟨1, ![1, 1, 1, -1, -2, 0], 2⟩,
  ⟨1, ![1, 1, 1, -1, 0, -2], 2⟩,
  ⟨1, ![1, 1, 1, 0, -2, -1], 2⟩,
  ⟨1, ![1, 1, 1, 0, -1, -2], 2⟩
]

def terms17 : Array TaggedTerm := #[
  ⟨0, ![0, -1, -1, 0, 0, 2], 4⟩,
  ⟨0, ![0, -1, -1, 0, 2, 0], 4⟩,
  ⟨0, ![0, -1, -1, 2, 0, 0], 4⟩,
  ⟨0, ![0, -1, 0, -1, 0, 2], -2⟩,
  ⟨0, ![0, -1, 0, -1, 2, 0], -2⟩,
  ⟨0, ![0, -1, 0, 0, -1, 2], -2⟩,
  ⟨0, ![0, -1, 0, 0, 2, -1], -2⟩,
  ⟨0, ![0, -1, 0, 2, -1, 0], -2⟩,
  ⟨0, ![0, -1, 0, 2, 0, -1], -2⟩,
  ⟨0, ![0, 0, -1, -1, 0, 2], -2⟩,
  ⟨0, ![0, 0, -1, -1, 2, 0], -2⟩,
  ⟨0, ![0, 0, -1, 0, -1, 2], -2⟩,
  ⟨0, ![0, 0, -1, 0, 2, -1], -2⟩,
  ⟨0, ![0, 0, -1, 2, -1, 0], -2⟩,
  ⟨0, ![0, 0, -1, 2, 0, -1], -2⟩,
  ⟨0, ![0, 0, 0, -1, -1, 2], 4⟩,
  ⟨0, ![0, 0, 0, -1, 2, -1], 4⟩,
  ⟨0, ![0, 0, 0, 2, -1, -1], 4⟩
]

end MUB6.Certificate.GramFunctions.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13629 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13630 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13631 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13632 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13633 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13634 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13635 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13636 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13637 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13638 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13639 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13640 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13641 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13642 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13643 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1114, -4), (key1123, 4), (key1235, -2), (key1242, 2)]

def row13644 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13645 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13646 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13647 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13648 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13649 : Integer.Sparse Key := [(key993, 2), (key1001, -4), (key1015, 2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -4), (key1114, 12), (key1123, -4), (key1150, -4), (key1232, -4), (key1235, 2), (key1242, 2)]

def row13656 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13657 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13658 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, -4), (key1150, 4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row13665 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13666 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13667 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13668 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13669 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13670 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2583, 2), (key2604, -2), (key2845, -4), (key2916, 4), (key2925, -2), (key3028, 2)]

def row13671 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2589, 4), (key2604, -2), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, -4), (key2925, 6), (key3019, 4), (key3028, -2)]

def row13672 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2589, 4), (key2604, -2), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, -4), (key2925, 6), (key3019, 4), (key3028, -2)]

def row13673 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2589, 4), (key2604, -2), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, -4), (key2925, 6), (key3019, 4), (key3028, -2)]

def row13674 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13675 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13676 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13677 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13678 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13679 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2583, 2), (key2604, -2), (key2768, 6), (key2839, 2), (key2845, -2), (key2916, -2), (key2925, -2), (key3019, 2), (key3028, 2)]

def row13680 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2589, -4), (key2762, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3005, 2), (key3028, 2)]

def row13681 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2589, -4), (key2762, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3005, 2), (key3028, 2)]

def row13682 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, -4), (key2604, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3028, 2)]

def row13683 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, -4), (key2604, 2), (key2768, -4), (key2845, 6), (key2876, -4), (key2925, 2), (key3028, 2)]

def row13684 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2589, -4), (key2762, 2), (key2768, -4), (key2845, 6), (key2876, -4)]

def row13685 : Integer.Sparse Key := [(key2388, 2), (key2398, 2), (key2435, 2), (key2464, -4), (key2470, 6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2583, 2), (key2589, -4), (key2768, -4), (key2845, 6), (key2876, -4)]

def row13692 : Integer.Sparse Key := [(key2376, 4), (key2388, -2), (key2398, 6), (key2404, -4), (key2435, -2), (key2470, 4), (key2478, -4), (key2501, 4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, -2), (key2839, -4)]

def row13693 : Integer.Sparse Key := [(key2376, 4), (key2388, -2), (key2398, 6), (key2404, -4), (key2435, -2), (key2470, 4), (key2478, -4), (key2501, 4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, -2), (key2839, -4)]

def row13694 : Integer.Sparse Key := [(key2376, 4), (key2388, -2), (key2398, 6), (key2404, -4), (key2435, -2), (key2470, 4), (key2478, -4), (key2501, 4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, -2), (key2839, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13701 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13702 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13703 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13704 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13705 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13706 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13707 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13708 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13709 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13710 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13711 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13712 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13713 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13714 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13715 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, -2), (key2721, 2), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, -4)]

def row13716 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13717 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13718 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13719 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13720 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13721 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, -4), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, -4), (key2824, 2), (key2853, 12), (key2855, -4), (key2865, -4)]

def row13728 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13729 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13730 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2780, -4), (key2789, 6), (key2803, -4), (key2824, 6), (key2853, 4), (key2855, -4), (key2865, -4)]

def row13737 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13738 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13739 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13740 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13741 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13742 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13743 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13744 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13745 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13746 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13747 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13748 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13749 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13750 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13751 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1113, -4), (key1122, 4), (key1234, -2), (key1241, 2)]

def row13752 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13753 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13754 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13755 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13756 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13757 : Integer.Sparse Key := [(key994, 2), (key1000, -4), (key1014, 2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -4), (key1113, 12), (key1122, -4), (key1149, -4), (key1231, -4), (key1234, 2), (key1241, 2)]

def row13764 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13765 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13766 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, -4), (key1149, 4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row13773 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13774 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13775 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13776 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13777 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13778 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13779 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13780 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13781 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13782 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13783 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13784 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13785 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13786 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13787 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row13788 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13789 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13790 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13791 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13792 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13793 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row13800 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13801 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

def row13802 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1116, -4), (key1125, 8), (key1130, -4), (key1152, -4), (key1159, 8), (key1174, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14963 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14964 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14965 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14966 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14967 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14968 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14969 : Integer.Sparse Key := [(key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, 4), (key1186, -4), (key1222, -4), (key1224, 4)]

def row14970 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14971 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14972 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14973 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14974 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14975 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14976 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14977 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14978 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row14979 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14980 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14981 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14982 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14983 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14984 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row14985 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1171, -8), (key1175, 8)]

def row14986 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1171, -8), (key1175, 8)]

def row14987 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1171, -8), (key1175, 8)]

def row15015 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15016 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15017 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15018 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15019 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15020 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15021 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15022 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15023 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

def row15024 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15025 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15026 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15027 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15028 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15029 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15030 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15031 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15032 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

def row15033 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15034 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15035 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15036 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15037 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15038 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

def row15039 : Integer.Sparse Key := [(key2420, 12), (key2427, -16), (key2438, 4), (key2495, -8), (key2504, 8)]

def row15040 : Integer.Sparse Key := [(key2420, 12), (key2427, -16), (key2438, 4), (key2495, -8), (key2504, 8)]

def row15041 : Integer.Sparse Key := [(key2420, 12), (key2427, -16), (key2438, 4), (key2495, -8), (key2504, 8)]

def row15042 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15043 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15044 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15045 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15046 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15047 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15048 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15049 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15050 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

def row15051 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15052 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15053 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15054 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15055 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15056 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15057 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15058 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15059 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

def row15060 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15061 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15062 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15063 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15064 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15065 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

def row15066 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, -8), (key2459, 4), (key2517, 12), (key2520, -8), (key2531, 4), (key2561, -4)]

def row15067 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, -8), (key2459, 4), (key2517, 12), (key2520, -8), (key2531, 4), (key2561, -4)]

def row15068 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, -8), (key2459, 4), (key2517, 12), (key2520, -8), (key2531, 4), (key2561, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15195 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15196 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15197 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15198 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15199 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15200 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15201 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15202 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15203 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15204 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15205 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15206 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

def row15207 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15208 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15209 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15210 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15211 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15212 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

def row15213 : Integer.Sparse Key := [(key2370, -2), (key2376, -4), (key2388, 6), (key2762, -2), (key2768, -4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3005, 6), (key3019, -4), (key3028, -2)]

def row15214 : Integer.Sparse Key := [(key2370, -2), (key2376, -4), (key2388, 6), (key2762, -2), (key2768, -4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3005, 6), (key3019, -4), (key3028, -2)]

def row15215 : Integer.Sparse Key := [(key2370, -2), (key2376, -4), (key2388, 6), (key2762, -2), (key2768, -4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3005, 6), (key3019, -4), (key3028, -2)]

def row15216 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15217 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15218 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15219 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15220 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15221 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

def row15222 : Integer.Sparse Key := [(key2398, -2), (key2404, -4), (key2435, 6), (key2583, -2), (key2589, -4), (key2604, 6), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3019, -4), (key3028, -2)]

def row15223 : Integer.Sparse Key := [(key2398, -2), (key2404, -4), (key2435, 6), (key2583, -2), (key2589, -4), (key2604, 6), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3019, -4), (key3028, -2)]

def row15224 : Integer.Sparse Key := [(key2398, -2), (key2404, -4), (key2435, 6), (key2583, -2), (key2589, -4), (key2604, 6), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3019, -4), (key3028, -2)]

def row15225 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15226 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15227 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15228 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15229 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15230 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

def row15231 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15232 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row15233 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row15234 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15235 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15236 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15237 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15238 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15239 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15240 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row15241 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row15242 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row15243 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15244 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15245 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15246 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15247 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15248 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

def row15249 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15250 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15251 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15252 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15253 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15254 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15255 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15256 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15257 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15258 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15259 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15260 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

def row15261 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15262 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15263 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15264 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15265 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15266 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

def row15267 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15268 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15269 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15270 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15271 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15272 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15273 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15274 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15275 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15276 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15277 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15278 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

def row15279 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15280 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15281 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15282 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15283 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15284 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

def row15303 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15304 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15305 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15306 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15307 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15308 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15309 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15310 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15311 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15312 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15313 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15314 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

def row15315 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15316 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15317 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15318 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15319 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15320 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15321 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15322 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15323 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15324 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15325 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15326 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15327 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15328 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15329 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15330 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15331 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15332 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

def row15333 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15334 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15335 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15336 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15337 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15338 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

def row15339 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15340 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15341 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15342 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15343 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15344 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15345 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15346 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15347 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15348 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15349 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15350 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

def row15351 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15352 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15353 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15354 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15355 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15356 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15357 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15358 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15359 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15360 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15361 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15362 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15363 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15364 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15365 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15366 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15367 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15368 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

def row15369 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15370 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15371 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15372 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15373 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15374 : Integer.Sparse Key := [(key2584, 2), (key2588, -4), (key2599, 2), (key2763, 2), (key2767, -4), (key2840, -4), (key2844, 12), (key2875, -4), (key2888, -4), (key2909, 2), (key2930, 2), (key2967, -4), (key2988, 2)]

def row15375 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15376 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15377 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15378 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15379 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15380 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15381 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15382 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15383 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15384 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15385 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15386 : Integer.Sparse Key := [(key2012, 8), (key2025, 4), (key2041, -4), (key2054, -8), (key2126, -4), (key2143, -8), (key2227, 12)]

def row15387 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15388 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15389 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15390 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15391 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15392 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15393 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15394 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15395 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15396 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15397 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15398 : Integer.Sparse Key := [(key2025, -4), (key2041, 4), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15399 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15400 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15401 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15402 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15403 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15404 : Integer.Sparse Key := [(key2025, -4), (key2041, -4), (key2054, 8), (key2126, 4), (key2227, -4)]

def row15405 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15406 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15407 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15408 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15409 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15410 : Integer.Sparse Key := [(key2012, -8), (key2025, 12), (key2041, 4), (key2054, -8), (key2126, 4), (key2143, -8), (key2227, 4)]

def row15447 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15448 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15449 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15450 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15451 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15452 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15453 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15454 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15455 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15456 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15457 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15458 : Integer.Sparse Key := [(key1358, -2), (key1364, -4), (key1374, 6), (key1484, -2), (key1490, -4), (key1513, 6), (key1710, 4), (key1716, 4), (key1723, -4), (key1741, -4), (key1937, 4), (key1940, -2), (key1949, -2)]

def row15459 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15460 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15461 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15462 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15463 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15464 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15465 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15466 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15467 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15468 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15469 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15470 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1940, 2), (key1949, -2)]

def row15471 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15472 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15473 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15474 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15475 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15476 : Integer.Sparse Key := [(key1358, 2), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1940, -2), (key1949, 2)]

def row15477 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15478 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15479 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15480 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15481 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

def row15482 : Integer.Sparse Key := [(key1358, 2), (key1364, -4), (key1374, 2), (key1484, 2), (key1490, -4), (key1513, 2), (key1710, -4), (key1716, 12), (key1723, -4), (key1741, -4), (key1937, -4), (key1940, 2), (key1949, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15561 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15562 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15563 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15564 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15565 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15566 : Integer.Sparse Key := [(key993, 6), (key1001, -4), (key1015, -2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, -4), (key1114, 4), (key1123, 4), (key1150, -4), (key1232, -4), (key1235, -2), (key1242, 6)]

def row15567 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2762, -2), (key2768, 4), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, 4), (key2925, -2), (key3005, -2), (key3019, -4), (key3028, 6)]

def row15568 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2762, -2), (key2768, 4), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, 4), (key2925, -2), (key3005, -2), (key3019, -4), (key3028, 6)]

def row15569 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2762, -2), (key2768, 4), (key2839, -4), (key2845, 4), (key2876, -4), (key2916, 4), (key2925, -2), (key3005, -2), (key3019, -4), (key3028, 6)]

def row15570 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2404, 4), (key2435, -2), (key2470, 4), (key2478, 4), (key2501, -4), (key2568, -4), (key2570, -2), (key2575, 6), (key2762, -2), (key2839, -4)]

def row15571 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2404, 4), (key2435, -2), (key2470, 4), (key2478, 4), (key2501, -4), (key2568, -4), (key2570, -2), (key2575, 6), (key2762, -2), (key2839, -4)]

def row15572 : Integer.Sparse Key := [(key2370, 6), (key2376, -4), (key2388, -2), (key2404, 4), (key2435, -2), (key2470, 4), (key2478, 4), (key2501, -4), (key2568, -4), (key2570, -2), (key2575, 6), (key2762, -2), (key2839, -4)]

def row15573 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15574 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15575 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15576 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15577 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15578 : Integer.Sparse Key := [(key2610, -2), (key2626, -4), (key2635, 6), (key2665, -2), (key2700, -4), (key2721, 6), (key2780, 4), (key2789, -2), (key2803, 4), (key2824, -2), (key2853, 4), (key2855, -4), (key2865, -4)]

def row15579 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15580 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15581 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15582 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15583 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15584 : Integer.Sparse Key := [(key994, 6), (key1000, -4), (key1014, -2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, -4), (key1113, 4), (key1122, 4), (key1149, -4), (key1231, -4), (key1234, -2), (key1241, 6)]

def row15585 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15586 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15587 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15588 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15589 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15590 : Integer.Sparse Key := [(key1038, -4), (key1044, 4), (key1073, 4), (key1080, -4), (key1116, -4), (key1125, -4), (key1130, 8), (key1152, 8), (key1159, -4), (key1174, -4)]

def row15597 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15598 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15599 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15600 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15601 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15602 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15603 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15604 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15605 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, -4), (key2714, 8), (key2815, 12), (key2817, -8), (key2863, -4)]

def row15606 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15607 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15608 : Integer.Sparse Key := [(key2681, -8), (key2688, 4), (key2712, 12), (key2714, -8), (key2815, -4), (key2817, 8), (key2863, -4)]

def row15609 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

def row15610 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

def row15611 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

def row15612 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15613 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15614 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15615 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15616 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

def row15617 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

def row15618 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15619 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15620 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

def row15621 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15622 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15623 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15624 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15625 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15626 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15627 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15628 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15629 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

def row15630 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15631 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15632 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

def row15645 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15646 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15647 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15648 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15649 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15650 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15651 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15652 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15653 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

def row15654 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15655 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15656 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

def row15735 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15736 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15737 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15738 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15739 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15740 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15741 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row15742 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row15743 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15744 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15745 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15746 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15747 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15748 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15749 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

def row15750 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row15751 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row15752 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row15753 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15754 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15755 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15756 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15757 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15758 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15759 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15760 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15761 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15762 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15763 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15764 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15765 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15766 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15767 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2399, 2), (key2434, -2), (key2469, -4), (key2500, 4), (key2541, 2), (key2552, -2)]

def row15768 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15769 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15770 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, -4), (key2469, 4), (key2477, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row15771 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15772 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15773 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15774 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15775 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15776 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15777 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15778 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15779 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15780 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15781 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15782 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15783 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15784 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15785 : Integer.Sparse Key := [(key2607, -2), (key2623, 4), (key2634, -2), (key2662, -2), (key2697, 4), (key2720, -2), (key2788, 2), (key2823, 2), (key2850, -4)]

def row15786 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15787 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15788 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, -2), (key2697, -4), (key2720, 6), (key2777, 4), (key2788, -2), (key2800, 4), (key2823, -2), (key2850, 4), (key2854, -4), (key2864, -4)]

def row15789 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15790 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15791 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15792 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15793 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15794 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15795 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15796 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15797 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15798 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15799 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15800 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15801 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15802 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15803 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 2), (key1068, -2), (key1110, -4), (key1147, 4), (key1196, 2), (key1209, -2)]

def row15804 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15805 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15806 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row15807 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15808 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15809 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15810 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15811 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15812 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15813 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15814 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15815 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15816 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15817 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15818 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15819 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15820 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15821 : Integer.Sparse Key := [(key1038, 2), (key1042, -2), (key1073, -2), (key1077, 2), (key1116, -2), (key1125, 4), (key1128, -2), (key1152, -2), (key1156, 4), (key1172, -2), (key1194, -2), (key1200, 2), (key1213, 2), (key1223, -2)]

def row15822 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15823 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15824 : Integer.Sparse Key := [(key1038, -4), (key1042, 4), (key1073, 4), (key1077, -4), (key1116, -4), (key1125, -4), (key1128, 8), (key1152, 8), (key1156, -4), (key1172, -4)]

def row15843 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15844 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15845 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15846 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15847 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15848 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15849 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15850 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15851 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15852 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15853 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15854 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15855 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15856 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15857 : Integer.Sparse Key := [(key2687, -4), (key2709, 4), (key2812, -4), (key2816, 8), (key2862, -4)]

def row15858 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15859 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15860 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, -4), (key2713, 8), (key2812, 12), (key2816, -8), (key2862, -4)]

def row15861 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15862 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15863 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15864 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15865 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15866 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2762, 2), (key2842, -4), (key2908, 2), (key2928, -2), (key2965, 4), (key2987, -2)]

def row15867 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2765, 4), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, 4), (key2908, -2), (key2928, -2), (key2965, -4), (key2987, 6)]

def row15868 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2765, 4), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, 4), (key2908, -2), (key2928, -2), (key2965, -4), (key2987, 6)]

def row15869 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2765, 4), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, 4), (key2908, -2), (key2928, -2), (key2965, -4), (key2987, 6)]

def row15870 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row15871 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15872 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row15873 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row15874 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row15875 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2586, 6), (key2762, 2), (key2839, 2), (key2842, -2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2)]

def row15876 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2401, 4), (key2433, -2), (key2467, 4), (key2476, 4), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, -2), (key2839, -4)]

def row15877 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2401, 4), (key2433, -2), (key2467, 4), (key2476, 4), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, -2), (key2839, -4)]

def row15878 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2401, 4), (key2433, -2), (key2467, 4), (key2476, 4), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, -2), (key2839, -4)]

def row15879 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15880 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15881 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15882 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15883 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15884 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15885 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15886 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15887 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15888 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15889 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15890 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15891 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15892 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15893 : Integer.Sparse Key := [(key2020, -4), (key2040, 4), (key2125, -4), (key2135, 8), (key2220, -4)]

def row15894 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15895 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15896 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, -4), (key2048, 8), (key2125, 12), (key2135, -8), (key2220, -4)]

def row15915 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15916 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15917 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15918 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15919 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15920 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15921 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15922 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15923 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15924 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15925 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15926 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15927 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15928 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15929 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15930 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15931 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15932 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15933 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15934 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15935 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15936 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15937 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15938 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 2), (key1513, -2), (key1716, -4), (key1741, 4), (key1867, 2), (key1877, -2)]

def row15939 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15940 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15941 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15942 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15943 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15944 : Integer.Sparse Key := [(key1359, 2), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1716, -4), (key1723, 4), (key1867, -2), (key1877, 2)]

def row15945 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15946 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15947 : Integer.Sparse Key := [(key1359, 6), (key1364, -4), (key1374, -2), (key1485, -2), (key1490, 4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1861, -4), (key1867, -2), (key1877, 6)]

def row15948 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15949 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

def row15950 : Integer.Sparse Key := [(key1359, -2), (key1364, 4), (key1374, -2), (key1485, 6), (key1490, -4), (key1513, -2), (key1711, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1861, -4), (key1867, 6), (key1877, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16131 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16132 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16133 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16134 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16135 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16136 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16137 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16138 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16139 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16140 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16141 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16142 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, -4), (key1127, 6), (key1155, -2), (key1190, 4), (key1193, -4), (key1199, -4), (key1212, 4)]

def row16143 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16144 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16145 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16146 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16147 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16148 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16149 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16150 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16151 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16152 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16153 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16154 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -2), (key1076, -2), (key1127, -2), (key1155, 2), (key1190, -4), (key1199, 4)]

def row16155 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16156 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16157 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16158 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16159 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16160 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1190, -4), (key1193, 4)]

def row16161 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16162 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16163 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16164 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16165 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16166 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, -4), (key1041, 2), (key1076, 2), (key1111, -4), (key1127, 2), (key1155, 2), (key1190, 12), (key1193, -4), (key1199, -4), (key1212, -4)]

def row16203 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16204 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16205 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16206 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16207 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16208 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16209 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16210 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16211 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16212 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16213 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16214 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, -2), (key2705, -2), (key2725, 4), (key2785, 6), (key2793, -4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 4)]

def row16215 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16216 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16217 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16218 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16219 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16220 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16221 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16222 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16223 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16224 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16225 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16226 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, -2), (key2705, 2), (key2785, -2), (key2793, 4), (key2808, -2), (key2828, 4), (key2879, -4)]

def row16227 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16228 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16229 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16230 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16231 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16232 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, 2), (key2705, -2), (key2785, -2), (key2808, -2), (key2859, 4), (key2869, 4), (key2879, -4)]

def row16233 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16234 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16235 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16236 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16237 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16238 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, 2), (key2705, 2), (key2725, -4), (key2785, 2), (key2793, -4), (key2808, 2), (key2828, -4), (key2859, -4), (key2869, -4), (key2879, 12)]

def row16239 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16240 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16241 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16242 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16243 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16244 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16245 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16246 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16247 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16248 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16249 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16250 : Integer.Sparse Key := [(key998, 4), (key1005, -2), (key1018, -2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, -4), (key1126, 6), (key1154, -2), (key1190, 4), (key1192, -4), (key1198, -4), (key1211, 4)]

def row16251 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16252 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16253 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16254 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16255 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16256 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16257 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16258 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16259 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16260 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16261 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16262 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

def row16263 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16264 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16265 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16266 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16267 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16268 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

def row16269 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16270 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16271 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16272 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16273 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16274 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

def row16275 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16276 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16277 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16278 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16279 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16280 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16281 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16282 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16283 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16284 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16285 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16286 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

def row16287 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16288 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16289 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16290 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16291 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16292 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16293 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16294 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16295 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16296 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16297 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16298 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row16299 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16300 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16301 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16302 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16303 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16304 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row16305 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16306 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16307 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16308 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16309 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16310 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

def row16347 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16348 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16349 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16350 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16351 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16352 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16353 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16354 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16355 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16356 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16357 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16358 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

def row16359 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16360 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16361 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16362 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16363 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16364 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16365 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16366 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16367 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16368 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16369 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16370 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

def row16371 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16372 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16373 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16374 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16375 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16376 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

def row16377 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16378 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16379 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16380 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16381 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

def row16382 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16419 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16420 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16421 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16422 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16423 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16424 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16425 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16426 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16427 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16428 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16429 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16430 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

def row16431 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16432 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16433 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16434 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16435 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16436 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16437 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16438 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16439 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16440 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16441 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16442 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

def row16443 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16444 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16445 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16446 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16447 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16448 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

def row16449 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16450 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16451 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16452 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16453 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16454 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

def row16491 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16492 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16493 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16494 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16495 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16496 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16497 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16498 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16499 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16500 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16501 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16502 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

def row16503 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16504 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16505 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16506 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16507 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16508 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16509 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16510 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16511 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16512 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16513 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16514 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

def row16515 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16516 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16517 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16518 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16519 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16520 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

def row16521 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16522 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16523 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16524 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16525 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

def row16526 : Integer.Sparse Key := [(key1363, -4), (key1369, 2), (key1378, 2), (key1489, -4), (key1495, 2), (key1518, 2), (key1715, -4), (key1727, 2), (key1746, 2), (key1860, 12), (key1864, -4), (key1869, -4), (key1879, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16671 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2906, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, -2)]

def row16672 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2906, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, -2)]

def row16673 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2906, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, -2)]

def row16674 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16675 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16676 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2899, 1), (key2906, 2), (key2915, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16677 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2899, 1), (key2906, 2), (key2915, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16678 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16679 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

def row16680 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -4), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2978, -2), (key2985, 4), (key2994, -4), (key3004, -2)]

def row16681 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -4), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2978, -2), (key2985, 4), (key2994, -4), (key3004, -2)]

def row16682 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -4), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2978, -2), (key2985, 4), (key2994, -4), (key3004, -2)]

def row16683 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16684 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16685 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16686 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16687 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16688 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

def row16689 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16690 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16691 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16692 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16693 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16694 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

def row16695 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16696 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16697 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2751, -2), (key2797, 2), (key2833, 2), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16698 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2751, -2), (key2797, 2), (key2833, 2), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16699 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16700 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

def row16701 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16702 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16703 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 4), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16704 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 4), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16705 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16706 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

def row16707 : Integer.Sparse Key := [(key2234, 8), (key2259, 4), (key2268, -8), (key2272, -8), (key2294, -8), (key2324, 8), (key2336, 4)]

def row16708 : Integer.Sparse Key := [(key2234, 8), (key2259, 4), (key2268, -8), (key2272, -8), (key2294, -8), (key2324, 8), (key2336, 4)]

def row16709 : Integer.Sparse Key := [(key2234, 8), (key2259, 4), (key2268, -8), (key2272, -8), (key2294, -8), (key2324, 8), (key2336, 4)]

def row16710 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16711 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16712 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16713 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16714 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16715 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16716 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16717 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16718 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16719 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16720 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16721 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

def row16722 : Integer.Sparse Key := [(key1989, -8), (key1994, 8), (key1999, 8), (key2003, -8), (key2259, 4), (key2294, -8), (key2336, 4)]

def row16723 : Integer.Sparse Key := [(key1989, -8), (key1994, 8), (key1999, 8), (key2003, -8), (key2259, 4), (key2294, -8), (key2336, 4)]

def row16724 : Integer.Sparse Key := [(key1989, -8), (key1994, 8), (key1999, 8), (key2003, -8), (key2259, 4), (key2294, -8), (key2336, 4)]

def row16725 : Integer.Sparse Key := [(key702, -4), (key706, -8), (key722, 12), (key856, 4), (key860, 4), (key883, 4), (key922, -8), (key939, -4)]

def row16726 : Integer.Sparse Key := [(key702, -4), (key706, -8), (key722, 12), (key856, 4), (key860, 4), (key883, 4), (key922, -8), (key939, -4)]

def row16727 : Integer.Sparse Key := [(key702, -4), (key706, -8), (key722, 12), (key856, 4), (key860, 4), (key883, 4), (key922, -8), (key939, -4)]

def row16728 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16729 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16730 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16731 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16732 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16733 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16734 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16735 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16736 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16737 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16738 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16739 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

def row16740 : Integer.Sparse Key := [(key702, 4), (key706, -8), (key722, 4), (key856, -4), (key860, 12), (key883, -4), (key922, -8), (key939, 4)]

def row16741 : Integer.Sparse Key := [(key702, 4), (key706, -8), (key722, 4), (key856, -4), (key860, 12), (key883, -4), (key922, -8), (key939, 4)]

def row16742 : Integer.Sparse Key := [(key702, 4), (key706, -8), (key722, 4), (key856, -4), (key860, 12), (key883, -4), (key922, -8), (key939, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16887 : Integer.Sparse Key := [(key2147, -4), (key2152, -4), (key2166, -4), (key2176, 8), (key2187, 4), (key2240, 4), (key2246, 4), (key2253, 4), (key2276, -4), (key2279, -4), (key2287, -4)]

def row16888 : Integer.Sparse Key := [(key2147, -4), (key2152, -4), (key2166, -4), (key2176, 8), (key2187, 4), (key2240, 4), (key2246, 4), (key2253, 4), (key2276, -4), (key2279, -4), (key2287, -4)]

def row16889 : Integer.Sparse Key := [(key2147, -4), (key2152, -4), (key2166, -4), (key2176, 8), (key2187, 4), (key2240, 4), (key2246, 4), (key2253, 4), (key2276, -4), (key2279, -4), (key2287, -4)]

def row16890 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16891 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16892 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16893 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16894 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16895 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

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

def row16896 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16897 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16898 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16899 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16900 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16901 : Integer.Sparse Key := [(key2028, -1), (key2033, 1), (key2058, 1), (key2063, -2), (key2069, 1), (key2079, 1), (key2085, -1), (key2147, 1), (key2152, 1), (key2166, 2), (key2176, -2), (key2187, -2), (key2240, -1), (key2246, -1), (key2253, -2), (key2276, 1), (key2279, 1), (key2287, 2)]

def row16902 : Integer.Sparse Key := [(key2028, 4), (key2033, -4), (key2058, -4), (key2063, 8), (key2069, -4), (key2079, -4), (key2085, 4), (key2166, -4), (key2187, 4), (key2253, 4), (key2287, -4)]

def row16903 : Integer.Sparse Key := [(key2028, 4), (key2033, -4), (key2058, -4), (key2063, 8), (key2069, -4), (key2079, -4), (key2085, 4), (key2166, -4), (key2187, 4), (key2253, 4), (key2287, -4)]

def row16904 : Integer.Sparse Key := [(key2028, 4), (key2033, -4), (key2058, -4), (key2063, 8), (key2069, -4), (key2079, -4), (key2085, 4), (key2166, -4), (key2187, 4), (key2253, 4), (key2287, -4)]

def row16905 : Integer.Sparse Key := [(key360, -2), (key362, -4), (key366, 6), (key731, -2), (key733, -4), (key750, 6), (key865, 4), (key867, 4), (key881, 4), (key927, -8), (key938, -4)]

def row16906 : Integer.Sparse Key := [(key360, -2), (key362, -4), (key366, 6), (key731, -2), (key733, -4), (key750, 6), (key865, 4), (key867, 4), (key881, 4), (key927, -8), (key938, -4)]

def row16907 : Integer.Sparse Key := [(key360, -2), (key362, -4), (key366, 6), (key731, -2), (key733, -4), (key750, 6), (key865, 4), (key867, 4), (key881, 4), (key927, -8), (key938, -4)]

def row16908 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16909 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16910 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16911 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16912 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16913 : Integer.Sparse Key := [(key360, -2), (key362, 4), (key366, -2), (key731, 2), (key750, -2), (key867, -4), (key927, 4)]

def row16914 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16915 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16916 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16917 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16918 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16919 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key529, -2), (key531, -2), (key537, 4), (key731, 2), (key733, 6), (key750, -2), (key865, 2), (key867, -2)]

def row16920 : Integer.Sparse Key := [(key360, 2), (key366, 2), (key529, -4), (key531, 6), (key537, -8), (key731, 2), (key733, -8), (key750, 2), (key867, 6), (key881, -4), (key938, 4)]

def row16921 : Integer.Sparse Key := [(key360, 2), (key366, 2), (key529, -4), (key531, 6), (key537, -8), (key731, 2), (key733, -8), (key750, 2), (key867, 6), (key881, -4), (key938, 4)]

def row16922 : Integer.Sparse Key := [(key360, 2), (key366, 4), (key529, -4), (key531, 6), (key537, -8), (key676, 4), (key731, 2), (key733, -8), (key867, 6), (key881, -4)]

def row16923 : Integer.Sparse Key := [(key1989, 8), (key1994, 4), (key1999, -4), (key2003, -8), (key2268, -4), (key2272, -4), (key2294, -4), (key2324, 8), (key2336, 4)]

def row16924 : Integer.Sparse Key := [(key1989, 8), (key1994, 4), (key1999, -4), (key2003, -8), (key2268, -4), (key2272, -4), (key2294, -4), (key2324, 8), (key2336, 4)]

def row16925 : Integer.Sparse Key := [(key1989, 8), (key1994, 4), (key1999, -4), (key2003, -8), (key2268, -4), (key2272, -4), (key2294, -4), (key2324, 8), (key2336, 4)]

def row16926 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16927 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16928 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16929 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16930 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16931 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16932 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16933 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16934 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16935 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16936 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16937 : Integer.Sparse Key := [(key1989, -1), (key1994, -3), (key1999, 1), (key2003, 3), (key2234, 1), (key2259, -1), (key2268, -1), (key2272, 3), (key2294, 2), (key2324, -3), (key2336, -1)]

def row16938 : Integer.Sparse Key := [(key1989, -4), (key1994, 8), (key2003, -4), (key2234, -4), (key2259, 4), (key2268, 8), (key2272, -8), (key2294, -4), (key2324, 4)]

def row16939 : Integer.Sparse Key := [(key1989, -4), (key1994, 8), (key2003, -4), (key2234, -4), (key2259, 4), (key2268, 8), (key2272, -8), (key2294, -4), (key2324, 4)]

def row16940 : Integer.Sparse Key := [(key1989, -4), (key1994, 8), (key2003, -4), (key2234, -4), (key2259, 4), (key2268, 8), (key2272, -8), (key2294, -4), (key2324, 4)]

def row16941 : Integer.Sparse Key := [(key2027, 4), (key2033, 8), (key2057, -4), (key2063, -4), (key2069, -4), (key2146, -4), (key2152, -4), (key2166, -4), (key2239, 4), (key2246, 4), (key2253, 4)]

def row16942 : Integer.Sparse Key := [(key2027, 4), (key2033, 8), (key2057, -4), (key2063, -4), (key2069, -4), (key2146, -4), (key2152, -4), (key2166, -4), (key2239, 4), (key2246, 4), (key2253, 4)]

def row16943 : Integer.Sparse Key := [(key2027, 4), (key2033, 8), (key2057, -4), (key2063, -4), (key2069, -4), (key2146, -4), (key2152, -4), (key2166, -4), (key2239, 4), (key2246, 4), (key2253, 4)]

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

def row17024 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

end MUB6.Certificate.GramRows

end OAI
end


