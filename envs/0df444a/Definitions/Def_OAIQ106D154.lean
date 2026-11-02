-- Prove2me | Definitions.Def_OAIQ106D154
-- name    : OAIQ106D154
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:02:22.97219+00:00
-- url     : https://prove2.me/theorems/8807d1d5-b825-49f4-827f-a0e449c10907
-- title:
--   Definitions bundle OAIQ106D154 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1284 declarations of OpenAI's Lean: 1284 definitions. The definitions and types are `OAI.MUB6.Certificate.GramFunctions.Block5.terms1`, `OAI.MUB6.Certificate.GramFunctions.Block5.terms2`, `OAI.MUB6.Certificate.GramFunctions.Block5.terms3`, `OAI.MUB6.Certificate.GramFunctions.Block5.terms4`, `OAI.MUB6.Certificate.GramFunctions.Block5.terms5`, `OAI.MUB6.Certificate.GramFunctions.Block5.terms6`, `OAI.MUB6.Certificate.GramFunctions.Block5.terms7`, `OAI.MUB6.Certificate.GramFunctions.Block5.terms8`, `OAI.MUB6.Certificate.GramFunctions.Block5.terms9`, `OAI.MUB6.Certificate.GramRows.rawRow0`, `OAI.MUB6.Certificate.GramRows.rawRow1`, `OAI.MUB6.Certificate.GramRows.rawRow10`, `OAI.MUB6.Certificate.GramRows.rawRow1000`, `OAI.MUB6.Certificate.GramRows.rawRow1001`, `OAI.MUB6.Certificate.GramRows.row18449`, `OAI.MUB6.Certificate.GramRows.row18450`, `OAI.MUB6.Certificate.GramRows.row18451`, `OAI.MUB6.Certificate.GramRows.row18452`, `OAI.MUB6.Certificate.GramRows.row18453`, `OAI.MUB6.Certificate.GramRows.row18454`, `OAI.MUB6.Certificate.GramRows.row18455`, `OAI.MUB6.Certificate.GramRows.row18456`, `OAI.MUB6.Certificate.GramRows.row18457`, `OAI.MUB6.Certificate.GramRows.row18458`, `OAI.MUB6.Certificate.GramRows.row18459`, `OAI.MUB6.Certificate.GramRows.row18460`, `OAI.MUB6.Certificate.GramRows.row18461`, `OAI.MUB6.Certificate.GramRows.row18462`, `OAI.MUB6.Certificate.GramRows.row18463`, `OAI.MUB6.Certificate.GramRows.row18464`, `OAI.MUB6.Certificate.GramRows.row18465`, `OAI.MUB6.Certificate.GramRows.row18466`, `OAI.MUB6.Certificate.GramRows.row18467`, `OAI.MUB6.Certificate.GramRows.row18468`, `OAI.MUB6.Certificate.GramRows.row18469`, `OAI.MUB6.Certificate.GramRows.row18470`, `OAI.MUB6.Certificate.GramRows.row18471`, `OAI.MUB6.Certificate.GramRows.row18472`, `OAI.MUB6.Certificate.GramRows.row18473`, `OAI.MUB6.Certificate.GramRows.row18474` and 1244 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramFunctions_Block5`, `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block168`, `MutuallyUnbiased_GramRows_Block169`, `MutuallyUnbiased_GramRows_Block170`, `MutuallyUnbiased_GramRows_Block171`, `MutuallyUnbiased_GramRows_Block172`, `MutuallyUnbiased_GramRows_Block173`, `MutuallyUnbiased_GramRows_Block174`, `MutuallyUnbiased_GramRows_Block175`, `MutuallyUnbiased_GramRows_Block178`, `MutuallyUnbiased_GramRows_Block179`, `MutuallyUnbiased_GramRows_Block180`, `MutuallyUnbiased_GramRows_Block181`, `MutuallyUnbiased_GramRows_Block182`, `MutuallyUnbiased_GramRows_Block28`.
--
--   **Imports.** It imports the bundles `OAIQ106D080`, `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D199` and `OAIQ106D200`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D080
import Definitions.Def_OAIQ106D081
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block5

def terms1 : Array TaggedTerm := #[
  ⟨0, ![3, -3, 0, 0, 0, 0], 24⟩,
  ⟨0, ![3, 0, -3, 0, 0, 0], 24⟩,
  ⟨0, ![3, 0, 0, -3, 0, 0], 24⟩,
  ⟨0, ![3, 0, 0, 0, -3, 0], 24⟩,
  ⟨0, ![3, 0, 0, 0, 0, -3], 24⟩
]

def terms2 : Array TaggedTerm := #[
  ⟨1, ![1, -2, -1, 0, 0, 2], 2⟩,
  ⟨1, ![1, -2, -1, 0, 2, 0], 2⟩,
  ⟨1, ![1, -2, -1, 2, 0, 0], 2⟩,
  ⟨1, ![1, -2, 0, -1, 0, 2], 2⟩,
  ⟨1, ![1, -2, 0, -1, 2, 0], 2⟩,
  ⟨1, ![1, -2, 0, 0, -1, 2], 2⟩,
  ⟨1, ![1, -2, 0, 0, 2, -1], 2⟩,
  ⟨1, ![1, -2, 0, 2, -1, 0], 2⟩,
  ⟨1, ![1, -2, 0, 2, 0, -1], 2⟩,
  ⟨1, ![1, -2, 2, -1, 0, 0], 2⟩,
  ⟨1, ![1, -2, 2, 0, -1, 0], 2⟩,
  ⟨1, ![1, -2, 2, 0, 0, -1], 2⟩,
  ⟨1, ![1, -1, -2, 0, 0, 2], 2⟩,
  ⟨1, ![1, -1, -2, 0, 2, 0], 2⟩,
  ⟨1, ![1, -1, -2, 2, 0, 0], 2⟩,
  ⟨1, ![1, -1, 0, -2, 0, 2], 2⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], 2⟩,
  ⟨1, ![1, -1, 0, 0, -2, 2], 2⟩,
  ⟨1, ![1, -1, 0, 0, 2, -2], 2⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], 2⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], 2⟩,
  ⟨1, ![1, -1, 2, -2, 0, 0], 2⟩,
  ⟨1, ![1, -1, 2, 0, -2, 0], 2⟩,
  ⟨1, ![1, -1, 2, 0, 0, -2], 2⟩,
  ⟨1, ![1, 0, -2, -1, 0, 2], 2⟩,
  ⟨1, ![1, 0, -2, -1, 2, 0], 2⟩,
  ⟨1, ![1, 0, -2, 0, -1, 2], 2⟩,
  ⟨1, ![1, 0, -2, 0, 2, -1], 2⟩,
  ⟨1, ![1, 0, -2, 2, -1, 0], 2⟩,
  ⟨1, ![1, 0, -2, 2, 0, -1], 2⟩,
  ⟨1, ![1, 0, -1, -2, 0, 2], 2⟩,
  ⟨1, ![1, 0, -1, -2, 2, 0], 2⟩,
  ⟨1, ![1, 0, -1, 0, -2, 2], 2⟩,
  ⟨1, ![1, 0, -1, 0, 2, -2], 2⟩,
  ⟨1, ![1, 0, -1, 2, -2, 0], 2⟩,
  ⟨1, ![1, 0, -1, 2, 0, -2], 2⟩,
  ⟨1, ![1, 0, 0, -2, -1, 2], 2⟩,
  ⟨1, ![1, 0, 0, -2, 2, -1], 2⟩,
  ⟨1, ![1, 0, 0, -1, -2, 2], 2⟩,
  ⟨1, ![1, 0, 0, -1, 2, -2], 2⟩,
  ⟨1, ![1, 0, 0, 2, -2, -1], 2⟩,
  ⟨1, ![1, 0, 0, 2, -1, -2], 2⟩,
  ⟨1, ![1, 0, 2, -2, -1, 0], 2⟩,
  ⟨1, ![1, 0, 2, -2, 0, -1], 2⟩,
  ⟨1, ![1, 0, 2, -1, -2, 0], 2⟩,
  ⟨1, ![1, 0, 2, -1, 0, -2], 2⟩,
  ⟨1, ![1, 0, 2, 0, -2, -1], 2⟩,
  ⟨1, ![1, 0, 2, 0, -1, -2], 2⟩,
  ⟨1, ![1, 2, -2, -1, 0, 0], 2⟩,
  ⟨1, ![1, 2, -2, 0, -1, 0], 2⟩,
  ⟨1, ![1, 2, -2, 0, 0, -1], 2⟩,
  ⟨1, ![1, 2, -1, -2, 0, 0], 2⟩,
  ⟨1, ![1, 2, -1, 0, -2, 0], 2⟩,
  ⟨1, ![1, 2, -1, 0, 0, -2], 2⟩,
  ⟨1, ![1, 2, 0, -2, -1, 0], 2⟩,
  ⟨1, ![1, 2, 0, -2, 0, -1], 2⟩,
  ⟨1, ![1, 2, 0, -1, -2, 0], 2⟩,
  ⟨1, ![1, 2, 0, -1, 0, -2], 2⟩,
  ⟨1, ![1, 2, 0, 0, -2, -1], 2⟩,
  ⟨1, ![1, 2, 0, 0, -1, -2], 2⟩
]

def terms3 : Array TaggedTerm := #[
  ⟨1, ![3, -3, 0, 0, 0, 0], 24⟩,
  ⟨1, ![3, 0, -3, 0, 0, 0], 24⟩,
  ⟨1, ![3, 0, 0, -3, 0, 0], 24⟩,
  ⟨1, ![3, 0, 0, 0, -3, 0], 24⟩,
  ⟨1, ![3, 0, 0, 0, 0, -3], 24⟩
]

def terms4 : Array TaggedTerm := #[
  ⟨0, ![1, -3, 0, 0, 0, 2], 6⟩,
  ⟨0, ![1, -3, 0, 0, 2, 0], 6⟩,
  ⟨0, ![1, -3, 0, 2, 0, 0], 6⟩,
  ⟨0, ![1, -3, 2, 0, 0, 0], 6⟩,
  ⟨0, ![1, 0, -3, 0, 0, 2], 6⟩,
  ⟨0, ![1, 0, -3, 0, 2, 0], 6⟩,
  ⟨0, ![1, 0, -3, 2, 0, 0], 6⟩,
  ⟨0, ![1, 0, 0, -3, 0, 2], 6⟩,
  ⟨0, ![1, 0, 0, -3, 2, 0], 6⟩,
  ⟨0, ![1, 0, 0, 0, -3, 2], 6⟩,
  ⟨0, ![1, 0, 0, 0, 2, -3], 6⟩,
  ⟨0, ![1, 0, 0, 2, -3, 0], 6⟩,
  ⟨0, ![1, 0, 0, 2, 0, -3], 6⟩,
  ⟨0, ![1, 0, 2, -3, 0, 0], 6⟩,
  ⟨0, ![1, 0, 2, 0, -3, 0], 6⟩,
  ⟨0, ![1, 0, 2, 0, 0, -3], 6⟩,
  ⟨0, ![1, 2, -3, 0, 0, 0], 6⟩,
  ⟨0, ![1, 2, 0, -3, 0, 0], 6⟩,
  ⟨0, ![1, 2, 0, 0, -3, 0], 6⟩,
  ⟨0, ![1, 2, 0, 0, 0, -3], 6⟩
]

def terms5 : Array TaggedTerm := #[
  ⟨1, ![1, -3, 0, 0, 1, 1], 4⟩,
  ⟨1, ![1, -3, 0, 1, 0, 1], 4⟩,
  ⟨1, ![1, -3, 0, 1, 1, 0], 4⟩,
  ⟨1, ![1, -3, 1, 0, 0, 1], 4⟩,
  ⟨1, ![1, -3, 1, 0, 1, 0], 4⟩,
  ⟨1, ![1, -3, 1, 1, 0, 0], 4⟩,
  ⟨1, ![1, 0, -3, 0, 1, 1], 4⟩,
  ⟨1, ![1, 0, -3, 1, 0, 1], 4⟩,
  ⟨1, ![1, 0, -3, 1, 1, 0], 4⟩,
  ⟨1, ![1, 0, 0, -3, 1, 1], 4⟩,
  ⟨1, ![1, 0, 0, 1, -3, 1], 4⟩,
  ⟨1, ![1, 0, 0, 1, 1, -3], 4⟩,
  ⟨1, ![1, 0, 1, -3, 0, 1], 4⟩,
  ⟨1, ![1, 0, 1, -3, 1, 0], 4⟩,
  ⟨1, ![1, 0, 1, 0, -3, 1], 4⟩,
  ⟨1, ![1, 0, 1, 0, 1, -3], 4⟩,
  ⟨1, ![1, 0, 1, 1, -3, 0], 4⟩,
  ⟨1, ![1, 0, 1, 1, 0, -3], 4⟩,
  ⟨1, ![1, 1, -3, 0, 0, 1], 4⟩,
  ⟨1, ![1, 1, -3, 0, 1, 0], 4⟩,
  ⟨1, ![1, 1, -3, 1, 0, 0], 4⟩,
  ⟨1, ![1, 1, 0, -3, 0, 1], 4⟩,
  ⟨1, ![1, 1, 0, -3, 1, 0], 4⟩,
  ⟨1, ![1, 1, 0, 0, -3, 1], 4⟩,
  ⟨1, ![1, 1, 0, 0, 1, -3], 4⟩,
  ⟨1, ![1, 1, 0, 1, -3, 0], 4⟩,
  ⟨1, ![1, 1, 0, 1, 0, -3], 4⟩,
  ⟨1, ![1, 1, 1, -3, 0, 0], 4⟩,
  ⟨1, ![1, 1, 1, 0, -3, 0], 4⟩,
  ⟨1, ![1, 1, 1, 0, 0, -3], 4⟩
]

def terms6 : Array TaggedTerm := #[
  ⟨1, ![2, -3, 0, 0, 0, 1], 6⟩,
  ⟨1, ![2, -3, 0, 0, 1, 0], 6⟩,
  ⟨1, ![2, -3, 0, 1, 0, 0], 6⟩,
  ⟨1, ![2, -3, 1, 0, 0, 0], 6⟩,
  ⟨1, ![2, 0, -3, 0, 0, 1], 6⟩,
  ⟨1, ![2, 0, -3, 0, 1, 0], 6⟩,
  ⟨1, ![2, 0, -3, 1, 0, 0], 6⟩,
  ⟨1, ![2, 0, 0, -3, 0, 1], 6⟩,
  ⟨1, ![2, 0, 0, -3, 1, 0], 6⟩,
  ⟨1, ![2, 0, 0, 0, -3, 1], 6⟩,
  ⟨1, ![2, 0, 0, 0, 1, -3], 6⟩,
  ⟨1, ![2, 0, 0, 1, -3, 0], 6⟩,
  ⟨1, ![2, 0, 0, 1, 0, -3], 6⟩,
  ⟨1, ![2, 0, 1, -3, 0, 0], 6⟩,
  ⟨1, ![2, 0, 1, 0, -3, 0], 6⟩,
  ⟨1, ![2, 0, 1, 0, 0, -3], 6⟩,
  ⟨1, ![2, 1, -3, 0, 0, 0], 6⟩,
  ⟨1, ![2, 1, 0, -3, 0, 0], 6⟩,
  ⟨1, ![2, 1, 0, 0, -3, 0], 6⟩,
  ⟨1, ![2, 1, 0, 0, 0, -3], 6⟩
]

def terms7 : Array TaggedTerm := #[
  ⟨1, ![3, -2, -1, 0, 0, 0], 6⟩,
  ⟨1, ![3, -2, 0, -1, 0, 0], 6⟩,
  ⟨1, ![3, -2, 0, 0, -1, 0], 6⟩,
  ⟨1, ![3, -2, 0, 0, 0, -1], 6⟩,
  ⟨1, ![3, -1, -2, 0, 0, 0], 6⟩,
  ⟨1, ![3, -1, 0, -2, 0, 0], 6⟩,
  ⟨1, ![3, -1, 0, 0, -2, 0], 6⟩,
  ⟨1, ![3, -1, 0, 0, 0, -2], 6⟩,
  ⟨1, ![3, 0, -2, -1, 0, 0], 6⟩,
  ⟨1, ![3, 0, -2, 0, -1, 0], 6⟩,
  ⟨1, ![3, 0, -2, 0, 0, -1], 6⟩,
  ⟨1, ![3, 0, -1, -2, 0, 0], 6⟩,
  ⟨1, ![3, 0, -1, 0, -2, 0], 6⟩,
  ⟨1, ![3, 0, -1, 0, 0, -2], 6⟩,
  ⟨1, ![3, 0, 0, -2, -1, 0], 6⟩,
  ⟨1, ![3, 0, 0, -2, 0, -1], 6⟩,
  ⟨1, ![3, 0, 0, -1, -2, 0], 6⟩,
  ⟨1, ![3, 0, 0, -1, 0, -2], 6⟩,
  ⟨1, ![3, 0, 0, 0, -2, -1], 6⟩,
  ⟨1, ![3, 0, 0, 0, -1, -2], 6⟩
]

def terms8 : Array TaggedTerm := #[
  ⟨0, ![-2, 0, 0, 0, 0, 2], 24⟩,
  ⟨0, ![-2, 0, 0, 0, 2, 0], 24⟩,
  ⟨0, ![-2, 0, 0, 2, 0, 0], 24⟩,
  ⟨0, ![-2, 0, 2, 0, 0, 0], 24⟩,
  ⟨0, ![-2, 2, 0, 0, 0, 0], 24⟩
]

def terms9 : Array TaggedTerm := #[
  ⟨1, ![3, -1, -1, -1, 0, 0], 12⟩,
  ⟨1, ![3, -1, -1, 0, -1, 0], 12⟩,
  ⟨1, ![3, -1, -1, 0, 0, -1], 12⟩,
  ⟨1, ![3, -1, 0, -1, -1, 0], 12⟩,
  ⟨1, ![3, -1, 0, -1, 0, -1], 12⟩,
  ⟨1, ![3, -1, 0, 0, -1, -1], 12⟩,
  ⟨1, ![3, 0, -1, -1, -1, 0], 12⟩,
  ⟨1, ![3, 0, -1, -1, 0, -1], 12⟩,
  ⟨1, ![3, 0, -1, 0, -1, -1], 12⟩,
  ⟨1, ![3, 0, 0, -1, -1, -1], 12⟩
]

end MUB6.Certificate.GramFunctions.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow0 : Integer.Sparse Key := [(key236, -1), (key239, -1), (key239, 2), (key248, 1), (key251, 1), (key251, -1), (key260, -1), (key267, -2), (key267, 1), (key271, 1), (key302, 1), (key305, 1), (key305, -2), (key316, -1), (key319, -1), (key319, 1), (key328, 1), (key335, 2), (key335, -1), (key340, -1), (key385, -1), (key388, -1), (key388, 1), (key397, 1), (key406, 1), (key409, 1), (key409, -1), (key418, -1), (key467, -1), (key469, -1), (key467, 1), (key475, 1), (key568, 2), (key568, -1), (key572, -1), (key578, -2), (key578, 1), (key583, 1), (key593, 1), (key595, 1), (key593, -1), (key601, -1)]

def rawRow1 : Integer.Sparse Key := [(key239, -1), (key236, -1), (key239, 2), (key251, 1), (key248, 1), (key260, -1), (key251, -1), (key267, -2), (key271, 1), (key267, 1), (key305, 1), (key302, 1), (key305, -2), (key319, -1), (key316, -1), (key328, 1), (key319, 1), (key335, 2), (key340, -1), (key335, -1), (key388, -1), (key385, -1), (key397, 1), (key388, 1), (key409, 1), (key406, 1), (key418, -1), (key409, -1), (key469, -1), (key467, -1), (key475, 1), (key467, 1), (key568, 2), (key572, -1), (key568, -1), (key578, -2), (key583, 1), (key578, 1), (key595, 1), (key593, 1), (key601, -1), (key593, -1)]

def rawRow10 : Integer.Sparse Key := [(key302, -1), (key305, -1), (key305, 2), (key316, 1), (key319, 1), (key319, -1), (key335, -1), (key328, -2), (key328, 1), (key340, 1), (key236, 1), (key239, 1), (key239, -2), (key406, -1), (key409, -1), (key409, 1), (key418, 1), (key578, 2), (key578, -1), (key583, -1), (key248, -1), (key251, -1), (key251, 1), (key260, 1), (key316, 1), (key319, 1), (key319, -1), (key328, -1), (key593, -1), (key595, -1), (key593, 1), (key601, 1), (key267, 2), (key267, -1), (key271, -1), (key335, -2), (key335, 1), (key340, 1), (key467, 1), (key469, 1), (key467, -1), (key475, -1)]

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

def row18449 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

def row18450 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

def row18451 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

def row18452 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

def row18453 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

def row18454 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

def row18455 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

def row18456 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

def row18457 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

def row18458 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

def row18459 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18460 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18461 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18462 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18463 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18464 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18465 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18466 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18467 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18468 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18469 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18470 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18471 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18472 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18473 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18474 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18475 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18476 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18477 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18478 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18479 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18480 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18481 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18482 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18483 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18484 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18485 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18486 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18487 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18488 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18489 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18490 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18491 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18492 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18493 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18494 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18495 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2589, 12), (key2762, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3005, 6), (key3028, 6)]

def row18496 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2589, 12), (key2762, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3005, 6), (key3028, 6)]

def row18497 : Integer.Sparse Key := [(key2398, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3028, 6)]

def row18498 : Integer.Sparse Key := [(key2398, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3028, 6)]

def row18499 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2570, 6), (key2575, 6), (key2589, 12), (key2762, 6), (key2768, 12), (key2845, 6), (key2876, 12)]

def row18500 : Integer.Sparse Key := [(key2388, 6), (key2398, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 12), (key2768, 12), (key2845, 6), (key2876, 12)]

def row18501 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2589, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

def row18502 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2589, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

def row18503 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

def row18504 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

def row18505 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2589, 6), (key2762, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

def row18506 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

def row18507 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 12)]

def row18508 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 12)]

def row18509 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 12)]

def row18510 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 12)]

def row18511 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 12)]

def row18512 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 12)]

def row18513 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 6)]

def row18514 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 6)]

def row18515 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 6)]

def row18516 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 6)]

def row18517 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2464, 12), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6)]

def row18518 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2464, 12), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6)]

def row18519 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18520 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18521 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18522 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18523 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18524 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18525 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18526 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18527 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18528 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18529 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18530 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18531 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18532 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18533 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18534 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18535 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18536 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18537 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18538 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18539 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18540 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18541 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18542 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18543 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18544 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18545 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18546 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18547 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18548 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18549 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18550 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18551 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18552 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18553 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18554 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18555 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18556 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18557 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18558 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18559 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18560 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18561 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18562 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18563 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18564 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18565 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18566 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18567 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18568 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18569 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18570 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18571 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18572 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18573 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18574 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18575 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18576 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18577 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18578 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18639 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

def row18640 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

def row18641 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

def row18642 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

def row18643 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

def row18644 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

def row18645 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

def row18646 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

def row18647 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

def row18648 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

def row18649 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

def row18650 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

def row18651 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

def row18652 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

def row18653 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

def row18654 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

def row18655 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

def row18656 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

def row18657 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

def row18658 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

def row18659 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18660 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18661 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18662 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18663 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18664 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18665 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18666 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18667 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18668 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18669 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18670 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18671 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18672 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18673 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18674 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18675 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18676 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18677 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18678 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18679 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18680 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18681 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18682 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18683 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18684 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18685 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18686 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18687 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18688 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18689 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18690 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18691 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18692 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18693 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18694 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18695 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18696 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18697 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18698 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18699 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18700 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18701 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18702 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18703 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18704 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18705 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18706 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18707 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18708 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18709 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18710 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18711 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18712 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18713 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18714 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18715 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18716 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18717 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18718 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18719 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18720 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18721 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18722 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18723 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18724 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18725 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18726 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18727 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18728 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18729 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18730 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18731 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18732 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18733 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18734 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18735 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18736 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18737 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18738 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18739 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18740 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18741 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18742 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18743 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18744 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18745 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18746 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

def row18747 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

def row18748 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 36), (key202, 6)]

def row18749 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 36), (key202, 6)]

def row18750 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

def row18751 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

def row18752 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18753 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18754 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18755 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18756 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18757 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18758 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18759 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18760 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18761 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18762 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18763 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18764 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18765 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 12), (key2456, 12), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 6), (key2523, 24), (key2567, 6), (key2579, 12)]

def row18766 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 12), (key2456, 12), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 6), (key2523, 24), (key2567, 6), (key2579, 12)]

def row18767 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 12), (key2456, 12), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 6), (key2523, 24), (key2567, 6), (key2579, 12)]

def row18768 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 24), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 12), (key2523, 24), (key2579, 12)]

def row18769 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 24), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 24), (key2528, 6), (key2560, 12)]

def row18770 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 24), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 24), (key2528, 6), (key2560, 12)]

def row18771 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18772 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18773 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18774 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18775 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18776 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18777 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18778 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18779 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18780 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18781 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18782 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18783 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18784 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18785 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18786 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18787 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18788 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18789 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18790 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18791 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18792 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18793 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18794 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18795 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18796 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18797 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18798 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18799 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18800 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18801 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18802 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18803 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18804 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18805 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18806 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18807 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18808 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18809 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18810 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18811 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18812 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18813 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18814 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18815 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18816 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18817 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18818 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18849 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18850 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18851 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18852 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18853 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18854 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18855 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18856 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18857 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18858 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18859 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18860 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18861 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18862 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18863 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18864 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18865 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18866 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18867 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18868 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18869 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18870 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18871 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18872 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18873 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18874 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18875 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18876 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18877 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18878 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18879 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18880 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18881 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18882 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18883 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18884 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18885 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18886 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18887 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18888 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18889 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18890 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18891 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18892 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18893 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18894 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18895 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18896 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18897 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18898 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18899 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18900 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18901 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18902 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18903 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18904 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18905 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18906 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18907 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18908 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18909 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18910 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18911 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18912 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18913 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18914 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18915 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18916 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18917 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18918 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 32), (key2525, 12), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18919 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 32), (key2525, 12), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18920 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 32), (key2525, 12), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18921 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18922 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18923 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 28), (key2525, 12), (key2532, 4), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18924 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 28), (key2525, 12), (key2532, 4), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18925 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18926 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18927 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18928 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18929 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18930 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18931 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18932 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 8), (key2532, 8), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18933 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 8), (key2532, 8), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18934 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18935 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18936 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18937 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18938 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18939 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18940 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18941 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18942 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18943 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18944 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18945 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18946 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18947 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18948 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18949 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18950 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18951 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18952 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18953 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18954 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18955 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18956 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18957 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18958 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18959 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18960 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18961 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18962 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18963 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18964 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18965 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18966 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18967 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18968 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18969 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18970 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18971 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18972 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18973 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18974 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18975 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18976 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18977 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18978 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18979 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18980 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18981 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18982 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18983 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18984 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18985 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18986 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18987 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18988 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18989 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18990 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18991 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18992 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18993 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18994 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18995 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18996 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18997 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18998 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18999 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19000 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19001 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19002 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19003 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19004 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19005 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19006 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19007 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19008 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19009 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19010 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19011 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19012 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19013 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19014 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19015 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19016 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19017 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19018 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19019 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19020 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19021 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19022 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19023 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19024 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19025 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19026 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19027 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19028 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19029 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19030 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19031 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19032 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19033 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19034 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19035 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19036 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19037 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19038 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19039 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19040 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19041 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19042 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19043 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19044 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19045 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19046 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19047 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19048 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19049 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19050 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19051 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19052 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19053 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19054 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19055 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19056 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19057 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19058 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19059 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19060 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19061 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19062 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19063 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19064 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19065 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19066 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

def row19067 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

def row19068 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 36), (key2558, 6)]

def row19069 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 36), (key2558, 6)]

def row19070 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

def row19071 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19072 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19073 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19074 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19075 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19076 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19077 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19078 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19079 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19080 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19081 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19082 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19083 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19084 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19085 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19086 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19087 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19088 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19089 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19090 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19091 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19092 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19093 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19094 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19095 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19096 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19097 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19098 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19099 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19100 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19101 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19102 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19103 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19104 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19105 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19106 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19107 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19108 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19109 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19110 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19111 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19112 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19113 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19114 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19115 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19116 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19117 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19118 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19119 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19120 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19121 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19122 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19123 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19124 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19125 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19126 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19127 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19128 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19129 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19130 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19131 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19132 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19133 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19134 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19135 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19136 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19137 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19138 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19139 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

def row19140 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

def row19141 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

def row19142 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

def row19143 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

def row19144 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

def row19145 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

def row19146 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

def row19147 : Integer.Sparse Key := [(key2368, 24), (key2462, 24), (key2760, 24), (key2837, 48)]

def row19148 : Integer.Sparse Key := [(key2368, 24), (key2462, 24), (key2760, 24), (key2837, 48)]

def row19149 : Integer.Sparse Key := [(key2368, 24), (key2462, 24), (key2760, 24), (key2837, 48)]

def row19150 : Integer.Sparse Key := [(key2396, 24), (key2462, 24), (key2581, 24), (key2837, 48)]

def row19151 : Integer.Sparse Key := [(key2396, 24), (key2462, 24), (key2581, 24), (key2837, 48)]

def row19152 : Integer.Sparse Key := [(key2396, 24), (key2462, 24), (key2581, 24), (key2837, 48)]

def row19153 : Integer.Sparse Key := [(key2368, 24), (key2462, 48), (key2760, 24), (key2837, 24)]

def row19154 : Integer.Sparse Key := [(key2368, 24), (key2462, 48), (key2760, 24), (key2837, 24)]

def row19155 : Integer.Sparse Key := [(key2396, 24), (key2462, 48), (key2581, 24), (key2837, 24)]

def row19156 : Integer.Sparse Key := [(key2396, 24), (key2462, 48), (key2581, 24), (key2837, 24)]

def row19157 : Integer.Sparse Key := [(key2368, 24), (key2462, 72), (key2760, 24)]

def row19158 : Integer.Sparse Key := [(key2396, 24), (key2462, 72), (key2581, 24)]

def row19159 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19160 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19161 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19162 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19163 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19164 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19165 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19166 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19167 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19168 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19169 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19170 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19171 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19172 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19173 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19174 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19175 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19176 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19177 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19178 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19179 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19180 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19181 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19182 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19183 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19184 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19185 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19186 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19187 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19188 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19189 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19190 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19191 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19192 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19193 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19194 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19195 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19196 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19197 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19198 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19199 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19200 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19201 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19202 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19203 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19204 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19205 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19206 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19207 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19208 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19209 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19210 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19211 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19212 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19213 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19214 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19215 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19216 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19217 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19218 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19219 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19220 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19221 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19222 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19223 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

def row19224 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

def row19225 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

def row19226 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

def row19227 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19228 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19229 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19230 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 30), (key2776, 6), (key2799, 18), (key2849, 36)]

def row19231 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 30), (key2776, 6), (key2799, 18), (key2849, 36)]

def row19232 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 30), (key2776, 6), (key2799, 18), (key2849, 36)]

def row19233 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19234 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19235 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 24), (key2776, 12), (key2799, 18), (key2849, 36)]

def row19236 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 24), (key2776, 12), (key2799, 18), (key2849, 36)]

def row19237 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19238 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19239 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

def row19240 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

def row19241 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

def row19242 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

def row19243 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

def row19244 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

def row19245 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

def row19246 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

def row19247 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

def row19248 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

def row19249 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

def row19250 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

def row19251 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

def row19252 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

def row19253 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

def row19254 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

def row19255 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

def row19256 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

def row19257 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

def row19258 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

def row19259 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

def row19260 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

def row19261 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

def row19262 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

def row19263 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

def row19264 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

def row19265 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

def row19266 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

def row19267 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

def row19268 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

def row19269 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

def row19270 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

def row19271 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

def row19272 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

def row19273 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

def row19274 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

def row19275 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

def row19276 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

def row19277 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

def row19278 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

def row19279 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

def row19280 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

def row19281 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

def row19282 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

def row19283 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

def row19284 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19285 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19286 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19287 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19288 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19289 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19290 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19291 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19292 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19293 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19294 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19295 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19296 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19297 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19298 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19299 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19300 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19301 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19302 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19303 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19304 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19305 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19306 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19307 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19308 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19309 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19310 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19311 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19312 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19313 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19314 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19315 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19316 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19317 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19318 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19319 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19320 : Integer.Sparse Key := [(key2412, 24), (key2485, 24), (key3031, 48), (key3118, 24)]

def row19321 : Integer.Sparse Key := [(key2412, 24), (key2485, 24), (key3031, 48), (key3118, 24)]

def row19322 : Integer.Sparse Key := [(key2412, 24), (key2485, 24), (key3031, 48), (key3118, 24)]

def row19323 : Integer.Sparse Key := [(key2412, 24), (key2485, 48), (key3031, 48)]

def row19324 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19325 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19326 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19327 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19328 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19329 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19330 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19331 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19332 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19333 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19334 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19335 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19336 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19337 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19338 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19339 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19340 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19341 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19342 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19343 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19344 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19345 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19346 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19347 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19348 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19349 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19350 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19351 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19352 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19353 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19354 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key3045, 18), (key3059, 24), (key3094, 36), (key3122, 12)]

def row19355 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key3045, 18), (key3059, 24), (key3094, 36), (key3122, 12)]

def row19356 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key3045, 18), (key3059, 24), (key3094, 36), (key3122, 12)]

def row19357 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key2811, 6), (key3045, 18), (key3059, 24), (key3094, 30), (key3122, 12)]

def row19358 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key2811, 6), (key3045, 18), (key3059, 24), (key3094, 30), (key3122, 12)]

def row19359 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key2811, 12), (key3045, 18), (key3059, 24), (key3094, 24), (key3122, 12)]

def row19360 : Integer.Sparse Key := [(key2677, 18), (key2708, 24), (key2811, 18), (key2861, 12), (key3045, 18), (key3059, 12), (key3094, 18)]

def row19361 : Integer.Sparse Key := [(key2677, 18), (key2708, 24), (key2811, 18), (key2861, 12), (key3045, 18), (key3059, 12), (key3094, 18)]

def row19362 : Integer.Sparse Key := [(key2677, 18), (key2708, 24), (key2811, 24), (key2861, 12), (key3045, 18), (key3059, 12), (key3094, 12)]

def row19363 : Integer.Sparse Key := [(key2677, 18), (key2708, 36), (key2811, 36), (key2861, 12), (key3045, 18)]

def row19364 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19365 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19366 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19367 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19368 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19369 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19370 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19371 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19372 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19373 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19374 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19375 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19376 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19377 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19378 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19379 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19380 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19381 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19382 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19383 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19724 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19725 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19726 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19727 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19728 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19729 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19730 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19731 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19732 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19733 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19734 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19735 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19736 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19737 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19738 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19739 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19740 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19741 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19742 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19743 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19744 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19745 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19746 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19747 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19748 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19749 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19750 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19751 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19752 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19753 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19754 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19755 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19756 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19757 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19758 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19759 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19760 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19761 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19762 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19763 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19764 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19765 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19766 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19767 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19768 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19769 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19770 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19771 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19772 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19773 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19774 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19775 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19776 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19777 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19778 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19779 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19780 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19781 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19782 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19783 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19788 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19789 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19790 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19791 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19792 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19793 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19794 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19795 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19796 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19797 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19798 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19799 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19800 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19801 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19802 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19803 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19804 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19805 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19806 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19807 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19808 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19809 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19810 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19811 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19812 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19813 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19814 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19815 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19816 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19817 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19818 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19819 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19820 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19821 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19822 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19823 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19824 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19825 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19826 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19827 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19828 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19829 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19830 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19831 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19832 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19833 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19834 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19835 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19836 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19837 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19838 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19839 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19840 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19841 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19842 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19843 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19844 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19845 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19846 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19847 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19848 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19849 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19850 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19851 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19852 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19853 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19854 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19855 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19856 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19857 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19858 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19859 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19860 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19861 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19862 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19863 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19864 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19865 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19866 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19867 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19868 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19869 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19870 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19871 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19872 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19873 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19874 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19875 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19876 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19877 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19878 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19879 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19880 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key212, 12), (key375, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key654, 6), (key663, 6)]

def row19881 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key212, 12), (key375, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key654, 6), (key663, 6)]

def row19882 : Integer.Sparse Key := [(key43, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key206, 6), (key212, 12), (key218, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key663, 6)]

def row19883 : Integer.Sparse Key := [(key43, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key206, 6), (key212, 12), (key218, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key663, 6)]

def row19884 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key196, 6), (key200, 6), (key212, 12), (key375, 6), (key381, 12), (key432, 6), (key460, 12)]

def row19885 : Integer.Sparse Key := [(key35, 6), (key43, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key196, 6), (key200, 6), (key206, 6), (key212, 12), (key381, 12), (key432, 6), (key460, 12)]

def row19886 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key212, 6), (key375, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

def row19887 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key212, 6), (key375, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

def row19888 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key206, 6), (key212, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

def row19889 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key206, 6), (key212, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

def row19890 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key48, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key212, 6), (key375, 6), (key381, 6), (key432, 6), (key460, 6)]

def row19891 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key43, 6), (key48, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key206, 6), (key212, 6), (key381, 6), (key432, 6), (key460, 6)]

def row19892 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 12)]

def row19893 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 12)]

def row19894 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 12)]

def row19895 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 12)]

def row19896 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 12)]

def row19897 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 12)]

def row19898 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 6)]

def row19899 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 6)]

def row19900 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 6)]

def row19901 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 6)]

def row19902 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key100, 12), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6)]

def row19903 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key100, 12), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6)]

def row19964 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19965 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19966 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19967 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19968 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19969 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19970 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19971 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19972 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19973 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19974 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19975 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19976 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19977 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19978 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19979 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19980 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19981 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19982 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19983 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19984 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19985 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19986 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19987 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19988 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19989 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19990 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19991 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19992 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19993 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19994 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19995 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19996 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19997 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19998 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19999 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20000 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20001 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20002 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20003 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20004 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20005 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20006 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20007 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20008 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20009 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20010 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20011 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20012 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20013 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20014 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20015 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20016 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20017 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20018 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20019 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20020 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20021 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20022 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20023 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20024 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20025 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20026 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20027 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20028 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20029 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20030 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20031 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20032 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20033 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20034 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20035 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20036 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20037 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20038 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20039 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20040 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20041 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20042 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20043 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20044 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20045 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20046 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20047 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20048 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20049 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20050 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20051 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20052 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20053 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20054 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20055 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20056 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20057 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20058 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20059 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20060 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20061 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20062 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20063 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20064 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20065 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20066 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20067 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20068 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20069 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20070 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20071 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20072 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20073 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20074 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20075 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20076 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20077 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20078 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20079 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20080 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20081 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20082 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20083 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20084 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20085 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20086 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20087 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20088 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20089 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20090 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20091 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20092 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20093 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20094 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20095 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row20096 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20097 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20098 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20099 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20100 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20101 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20102 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20103 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20104 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20105 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20106 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20107 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20108 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20109 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20110 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20111 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20112 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20113 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20114 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20115 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20116 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20117 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20118 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20119 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20120 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20121 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20122 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20123 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20124 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20125 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20126 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20127 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20128 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20129 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20130 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20131 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20132 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20133 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20134 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20135 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20136 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20137 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20138 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20139 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20140 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20141 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20142 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20143 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20144 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20145 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20146 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20147 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20148 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20149 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20150 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20151 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20152 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20153 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20154 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20155 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20156 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20157 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20158 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20159 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20160 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20161 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20162 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20163 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20164 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20165 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20166 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20167 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20168 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20169 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20170 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20171 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20172 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20173 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20174 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20175 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20176 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20177 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20178 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20179 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20180 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20181 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20182 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20183 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20184 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20185 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20186 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20187 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20188 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20189 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20190 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20191 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20192 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20193 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20194 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20195 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20196 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20197 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20198 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20199 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20200 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20201 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20202 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20203 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row20315 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20316 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20317 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20318 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20319 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20320 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20321 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20322 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20323 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1000 : Integer.Sparse Key := [(key48, -2), (key48, -2), (key74, -2), (key43, 6), (key460, 2), (key460, 2), (key663, 2), (key206, -2), (key426, -2), (key426, -2), (key490, -6), (key218, 2), (key486, 2), (key486, 2)]

def rawRow1001 : Integer.Sparse Key := [(key48, -2), (key74, -2), (key48, -2), (key43, 6), (key460, 2), (key663, 2), (key460, 2), (key426, -2), (key206, -2), (key426, -2), (key490, -6), (key486, 2), (key218, 2), (key486, 2)]

end MUB6.Certificate.GramRows

end OAI
end


