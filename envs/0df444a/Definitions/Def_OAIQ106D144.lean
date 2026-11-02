-- Prove2me | Definitions.Def_OAIQ106D144
-- name    : OAIQ106D144
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:45:25.1051+00:00
-- url     : https://prove2.me/theorems/8f766e4f-2ee1-4d08-b1dd-d456642c973c
-- title:
--   Definitions bundle OAIQ106D144 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 505 declarations of OpenAI's Lean: 505 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.entry10_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_7`, `OAI.MUB6.Certificate.GramFunctions.Block2.terms1`, `OAI.MUB6.Certificate.GramFunctions.Block2.terms2`, `OAI.MUB6.Certificate.GramFunctions.Block2.terms3`, `OAI.MUB6.Certificate.GramFunctions.Block2.terms4`, `OAI.MUB6.Certificate.GramFunctions.Block2.terms5`, `OAI.MUB6.Certificate.GramFunctions.Block2.terms6`, `OAI.MUB6.Certificate.GramRows.row10499`, `OAI.MUB6.Certificate.GramRows.row5188`, `OAI.MUB6.Certificate.GramRows.row5189`, `OAI.MUB6.Certificate.GramRows.row5190`, `OAI.MUB6.Certificate.GramRows.row5191`, `OAI.MUB6.Certificate.GramRows.row5192`, `OAI.MUB6.Certificate.GramRows.row5193`, `OAI.MUB6.Certificate.GramRows.row5194`, `OAI.MUB6.Certificate.GramRows.row5195`, `OAI.MUB6.Certificate.GramRows.row5196`, `OAI.MUB6.Certificate.GramRows.row5197`, `OAI.MUB6.Certificate.GramRows.row5198`, `OAI.MUB6.Certificate.GramRows.row5199`, `OAI.MUB6.Certificate.GramRows.row5200`, `OAI.MUB6.Certificate.GramRows.row5201`, `OAI.MUB6.Certificate.GramRows.row5202`, `OAI.MUB6.Certificate.GramRows.row5203`, `OAI.MUB6.Certificate.GramRows.row5204`, `OAI.MUB6.Certificate.GramRows.row5205`, `OAI.MUB6.Certificate.GramRows.row5206`, `OAI.MUB6.Certificate.GramRows.row5207`, `OAI.MUB6.Certificate.GramRows.row5208`, `OAI.MUB6.Certificate.GramRows.row5209`, `OAI.MUB6.Certificate.GramRows.row5210`, `OAI.MUB6.Certificate.GramRows.row5211`, `OAI.MUB6.Certificate.GramRows.row5212`, `OAI.MUB6.Certificate.GramRows.row5213`, `OAI.MUB6.Certificate.GramRows.row5214`, `OAI.MUB6.Certificate.GramRows.row5215`, `OAI.MUB6.Certificate.GramRows.row5216`, `OAI.MUB6.Certificate.GramRows.row5217`, `OAI.MUB6.Certificate.GramRows.row5218` and 465 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block3Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Data.lean), [`MutuallyUnbiased_GramFunctions_Block2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Block2.lean), [`MutuallyUnbiased_GramRows_Block106`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block106.lean), [`MutuallyUnbiased_GramRows_Block64`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block64.lean), [`MutuallyUnbiased_GramRows_Block65`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block65.lean), [`MutuallyUnbiased_GramRows_Block66`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block66.lean), [`MutuallyUnbiased_GramRows_Block67`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block67.lean), [`MutuallyUnbiased_GramRows_Block68`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block68.lean), [`MutuallyUnbiased_GramRows_Block69`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block69.lean), [`MutuallyUnbiased_GramRows_Block70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block70.lean), [`MutuallyUnbiased_GramRows_Block80`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block80.lean), [`MutuallyUnbiased_GramRows_Block81`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block81.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D085`, `OAIQ106D086`, `OAIQ106D087`, `OAIQ106D089` and `OAIQ106D090` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D198` and `OAIQ106D199`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D081
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D086
import Definitions.Def_OAIQ106D087
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

def entry10_7 : Integer.Sparse Key := [(key1289, -144), (key1309, 96), (key1350, 48), (key1384, 144), (key1417, -96), (key1471, -48), (key1539, 384), (key1566, -384), (key1895, 192), (key1902, -192)]

def entry10_10 : Integer.Sparse Key := [(key234, 192), (key246, -192), (key300, 48), (key314, -160), (key383, 64), (key404, 528), (key433, -480)]

end MUB6.Certificate.GramEntries.Block3

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

def terms1 : Array TaggedTerm := #[
  ⟨0, ![1, -2, -1, 0, 0, 2], -1⟩,
  ⟨0, ![1, -2, -1, 0, 2, 0], -1⟩,
  ⟨0, ![1, -2, -1, 2, 0, 0], 2⟩,
  ⟨0, ![1, -2, 0, -1, 0, 2], -1⟩,
  ⟨0, ![1, -2, 0, -1, 2, 0], -1⟩,
  ⟨0, ![1, -2, 0, 0, -1, 2], 2⟩,
  ⟨0, ![1, -2, 0, 0, 2, -1], 2⟩,
  ⟨0, ![1, -2, 0, 2, -1, 0], -1⟩,
  ⟨0, ![1, -2, 0, 2, 0, -1], -1⟩,
  ⟨0, ![1, -2, 2, -1, 0, 0], 2⟩,
  ⟨0, ![1, -2, 2, 0, -1, 0], -1⟩,
  ⟨0, ![1, -2, 2, 0, 0, -1], -1⟩,
  ⟨0, ![1, -1, -2, 0, 0, 2], 1⟩,
  ⟨0, ![1, -1, -2, 0, 2, 0], 1⟩,
  ⟨0, ![1, -1, -2, 2, 0, 0], -2⟩,
  ⟨0, ![1, -1, 0, -2, 0, 2], 1⟩,
  ⟨0, ![1, -1, 0, -2, 2, 0], 1⟩,
  ⟨0, ![1, -1, 0, 0, -2, 2], -2⟩,
  ⟨0, ![1, -1, 0, 0, 2, -2], -2⟩,
  ⟨0, ![1, -1, 0, 2, -2, 0], 1⟩,
  ⟨0, ![1, -1, 0, 2, 0, -2], 1⟩,
  ⟨0, ![1, -1, 2, -2, 0, 0], -2⟩,
  ⟨0, ![1, -1, 2, 0, -2, 0], 1⟩,
  ⟨0, ![1, -1, 2, 0, 0, -2], 1⟩,
  ⟨0, ![1, 0, -2, 0, -1, 2], -1⟩,
  ⟨0, ![1, 0, -2, 0, 2, -1], -1⟩,
  ⟨0, ![1, 0, -2, 2, -1, 0], 1⟩,
  ⟨0, ![1, 0, -2, 2, 0, -1], 1⟩,
  ⟨0, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨0, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨0, ![1, 0, -1, 2, -2, 0], -1⟩,
  ⟨0, ![1, 0, -1, 2, 0, -2], -1⟩,
  ⟨0, ![1, 0, 0, -2, -1, 2], -1⟩,
  ⟨0, ![1, 0, 0, -2, 2, -1], -1⟩,
  ⟨0, ![1, 0, 0, -1, -2, 2], 1⟩,
  ⟨0, ![1, 0, 0, -1, 2, -2], 1⟩,
  ⟨0, ![1, 0, 2, -2, -1, 0], 1⟩,
  ⟨0, ![1, 0, 2, -2, 0, -1], 1⟩,
  ⟨0, ![1, 0, 2, -1, -2, 0], -1⟩,
  ⟨0, ![1, 0, 2, -1, 0, -2], -1⟩
]

def terms2 : Array TaggedTerm := #[
  ⟨1, ![2, -2, -1, 0, 0, 1], -1⟩,
  ⟨1, ![2, -2, -1, 0, 1, 0], -1⟩,
  ⟨1, ![2, -2, -1, 1, 0, 0], 2⟩,
  ⟨1, ![2, -2, 0, -1, 0, 1], -1⟩,
  ⟨1, ![2, -2, 0, -1, 1, 0], -1⟩,
  ⟨1, ![2, -2, 0, 0, -1, 1], 2⟩,
  ⟨1, ![2, -2, 0, 0, 1, -1], 2⟩,
  ⟨1, ![2, -2, 0, 1, -1, 0], -1⟩,
  ⟨1, ![2, -2, 0, 1, 0, -1], -1⟩,
  ⟨1, ![2, -2, 1, -1, 0, 0], 2⟩,
  ⟨1, ![2, -2, 1, 0, -1, 0], -1⟩,
  ⟨1, ![2, -2, 1, 0, 0, -1], -1⟩,
  ⟨1, ![2, -1, -2, 0, 0, 1], 1⟩,
  ⟨1, ![2, -1, -2, 0, 1, 0], 1⟩,
  ⟨1, ![2, -1, -2, 1, 0, 0], -2⟩,
  ⟨1, ![2, -1, 0, -2, 0, 1], 1⟩,
  ⟨1, ![2, -1, 0, -2, 1, 0], 1⟩,
  ⟨1, ![2, -1, 0, 0, -2, 1], -2⟩,
  ⟨1, ![2, -1, 0, 0, 1, -2], -2⟩,
  ⟨1, ![2, -1, 0, 1, -2, 0], 1⟩,
  ⟨1, ![2, -1, 0, 1, 0, -2], 1⟩,
  ⟨1, ![2, -1, 1, -2, 0, 0], -2⟩,
  ⟨1, ![2, -1, 1, 0, -2, 0], 1⟩,
  ⟨1, ![2, -1, 1, 0, 0, -2], 1⟩,
  ⟨1, ![2, 0, -2, 0, -1, 1], -1⟩,
  ⟨1, ![2, 0, -2, 0, 1, -1], -1⟩,
  ⟨1, ![2, 0, -2, 1, -1, 0], 1⟩,
  ⟨1, ![2, 0, -2, 1, 0, -1], 1⟩,
  ⟨1, ![2, 0, -1, 0, -2, 1], 1⟩,
  ⟨1, ![2, 0, -1, 0, 1, -2], 1⟩,
  ⟨1, ![2, 0, -1, 1, -2, 0], -1⟩,
  ⟨1, ![2, 0, -1, 1, 0, -2], -1⟩,
  ⟨1, ![2, 0, 0, -2, -1, 1], -1⟩,
  ⟨1, ![2, 0, 0, -2, 1, -1], -1⟩,
  ⟨1, ![2, 0, 0, -1, -2, 1], 1⟩,
  ⟨1, ![2, 0, 0, -1, 1, -2], 1⟩,
  ⟨1, ![2, 0, 1, -2, -1, 0], 1⟩,
  ⟨1, ![2, 0, 1, -2, 0, -1], 1⟩,
  ⟨1, ![2, 0, 1, -1, -2, 0], -1⟩,
  ⟨1, ![2, 0, 1, -1, 0, -2], -1⟩
]

def terms3 : Array TaggedTerm := #[
  ⟨0, ![1, -3, 0, 0, 1, 1], -4⟩,
  ⟨0, ![1, -3, 0, 1, 0, 1], 2⟩,
  ⟨0, ![1, -3, 0, 1, 1, 0], 2⟩,
  ⟨0, ![1, -3, 1, 0, 0, 1], 2⟩,
  ⟨0, ![1, -3, 1, 0, 1, 0], 2⟩,
  ⟨0, ![1, -3, 1, 1, 0, 0], -4⟩,
  ⟨0, ![1, 0, -3, 0, 1, 1], 2⟩,
  ⟨0, ![1, 0, -3, 1, 0, 1], -1⟩,
  ⟨0, ![1, 0, -3, 1, 1, 0], -1⟩,
  ⟨0, ![1, 0, 0, -3, 1, 1], 2⟩,
  ⟨0, ![1, 0, 0, 1, -3, 1], -1⟩,
  ⟨0, ![1, 0, 0, 1, 1, -3], -1⟩,
  ⟨0, ![1, 0, 1, -3, 0, 1], -1⟩,
  ⟨0, ![1, 0, 1, -3, 1, 0], -1⟩,
  ⟨0, ![1, 0, 1, 0, -3, 1], -1⟩,
  ⟨0, ![1, 0, 1, 0, 1, -3], -1⟩,
  ⟨0, ![1, 0, 1, 1, -3, 0], 2⟩,
  ⟨0, ![1, 0, 1, 1, 0, -3], 2⟩,
  ⟨0, ![1, 1, -3, 0, 0, 1], -1⟩,
  ⟨0, ![1, 1, -3, 0, 1, 0], -1⟩,
  ⟨0, ![1, 1, -3, 1, 0, 0], 2⟩,
  ⟨0, ![1, 1, 0, -3, 0, 1], -1⟩,
  ⟨0, ![1, 1, 0, -3, 1, 0], -1⟩,
  ⟨0, ![1, 1, 0, 0, -3, 1], 2⟩,
  ⟨0, ![1, 1, 0, 0, 1, -3], 2⟩,
  ⟨0, ![1, 1, 0, 1, -3, 0], -1⟩,
  ⟨0, ![1, 1, 0, 1, 0, -3], -1⟩,
  ⟨0, ![1, 1, 1, -3, 0, 0], 2⟩,
  ⟨0, ![1, 1, 1, 0, -3, 0], -1⟩,
  ⟨0, ![1, 1, 1, 0, 0, -3], -1⟩
]

def terms4 : Array TaggedTerm := #[
  ⟨1, ![1, -3, 0, 0, 1, 1], -4⟩,
  ⟨1, ![1, -3, 0, 1, 0, 1], 2⟩,
  ⟨1, ![1, -3, 0, 1, 1, 0], 2⟩,
  ⟨1, ![1, -3, 1, 0, 0, 1], 2⟩,
  ⟨1, ![1, -3, 1, 0, 1, 0], 2⟩,
  ⟨1, ![1, -3, 1, 1, 0, 0], -4⟩,
  ⟨1, ![1, 0, -3, 0, 1, 1], 2⟩,
  ⟨1, ![1, 0, -3, 1, 0, 1], -1⟩,
  ⟨1, ![1, 0, -3, 1, 1, 0], -1⟩,
  ⟨1, ![1, 0, 0, -3, 1, 1], 2⟩,
  ⟨1, ![1, 0, 0, 1, -3, 1], -1⟩,
  ⟨1, ![1, 0, 0, 1, 1, -3], -1⟩,
  ⟨1, ![1, 0, 1, -3, 0, 1], -1⟩,
  ⟨1, ![1, 0, 1, -3, 1, 0], -1⟩,
  ⟨1, ![1, 0, 1, 0, -3, 1], -1⟩,
  ⟨1, ![1, 0, 1, 0, 1, -3], -1⟩,
  ⟨1, ![1, 0, 1, 1, -3, 0], 2⟩,
  ⟨1, ![1, 0, 1, 1, 0, -3], 2⟩,
  ⟨1, ![1, 1, -3, 0, 0, 1], -1⟩,
  ⟨1, ![1, 1, -3, 0, 1, 0], -1⟩,
  ⟨1, ![1, 1, -3, 1, 0, 0], 2⟩,
  ⟨1, ![1, 1, 0, -3, 0, 1], -1⟩,
  ⟨1, ![1, 1, 0, -3, 1, 0], -1⟩,
  ⟨1, ![1, 1, 0, 0, -3, 1], 2⟩,
  ⟨1, ![1, 1, 0, 0, 1, -3], 2⟩,
  ⟨1, ![1, 1, 0, 1, -3, 0], -1⟩,
  ⟨1, ![1, 1, 0, 1, 0, -3], -1⟩,
  ⟨1, ![1, 1, 1, -3, 0, 0], 2⟩,
  ⟨1, ![1, 1, 1, 0, -3, 0], -1⟩,
  ⟨1, ![1, 1, 1, 0, 0, -3], -1⟩
]

def terms5 : Array TaggedTerm := #[
  ⟨1, ![1, -1, -2, 0, 1, 1], -2⟩,
  ⟨1, ![1, -1, -2, 1, 0, 1], 1⟩,
  ⟨1, ![1, -1, -2, 1, 1, 0], 1⟩,
  ⟨1, ![1, -1, 0, -2, 1, 1], -2⟩,
  ⟨1, ![1, -1, 0, 1, -2, 1], 1⟩,
  ⟨1, ![1, -1, 0, 1, 1, -2], 1⟩,
  ⟨1, ![1, -1, 1, -2, 0, 1], 1⟩,
  ⟨1, ![1, -1, 1, -2, 1, 0], 1⟩,
  ⟨1, ![1, -1, 1, 0, -2, 1], 1⟩,
  ⟨1, ![1, -1, 1, 0, 1, -2], 1⟩,
  ⟨1, ![1, -1, 1, 1, -2, 0], -2⟩,
  ⟨1, ![1, -1, 1, 1, 0, -2], -2⟩,
  ⟨1, ![1, 0, -2, -1, 1, 1], 2⟩,
  ⟨1, ![1, 0, -2, 1, -1, 1], -1⟩,
  ⟨1, ![1, 0, -2, 1, 1, -1], -1⟩,
  ⟨1, ![1, 0, -1, -2, 1, 1], 2⟩,
  ⟨1, ![1, 0, -1, 1, -2, 1], -1⟩,
  ⟨1, ![1, 0, -1, 1, 1, -2], -1⟩,
  ⟨1, ![1, 0, 1, -2, -1, 1], -1⟩,
  ⟨1, ![1, 0, 1, -2, 1, -1], -1⟩,
  ⟨1, ![1, 0, 1, -1, -2, 1], -1⟩,
  ⟨1, ![1, 0, 1, -1, 1, -2], -1⟩,
  ⟨1, ![1, 0, 1, 1, -2, -1], 2⟩,
  ⟨1, ![1, 0, 1, 1, -1, -2], 2⟩,
  ⟨1, ![1, 1, -2, -1, 0, 1], -1⟩,
  ⟨1, ![1, 1, -2, -1, 1, 0], -1⟩,
  ⟨1, ![1, 1, -2, 0, -1, 1], 1⟩,
  ⟨1, ![1, 1, -2, 0, 1, -1], 1⟩,
  ⟨1, ![1, 1, -1, -2, 0, 1], -1⟩,
  ⟨1, ![1, 1, -1, -2, 1, 0], -1⟩,
  ⟨1, ![1, 1, -1, 1, -2, 0], 1⟩,
  ⟨1, ![1, 1, -1, 1, 0, -2], 1⟩,
  ⟨1, ![1, 1, 0, -2, -1, 1], 1⟩,
  ⟨1, ![1, 1, 0, -2, 1, -1], 1⟩,
  ⟨1, ![1, 1, 0, 1, -2, -1], -1⟩,
  ⟨1, ![1, 1, 0, 1, -1, -2], -1⟩,
  ⟨1, ![1, 1, 1, -1, -2, 0], 1⟩,
  ⟨1, ![1, 1, 1, -1, 0, -2], 1⟩,
  ⟨1, ![1, 1, 1, 0, -2, -1], -1⟩,
  ⟨1, ![1, 1, 1, 0, -1, -2], -1⟩
]

def terms6 : Array TaggedTerm := #[
  ⟨0, ![2, -2, -1, 0, 0, 1], -1⟩,
  ⟨0, ![2, -2, -1, 0, 1, 0], -1⟩,
  ⟨0, ![2, -2, -1, 1, 0, 0], 2⟩,
  ⟨0, ![2, -2, 0, -1, 0, 1], -1⟩,
  ⟨0, ![2, -2, 0, -1, 1, 0], -1⟩,
  ⟨0, ![2, -2, 0, 0, -1, 1], 2⟩,
  ⟨0, ![2, -2, 0, 0, 1, -1], 2⟩,
  ⟨0, ![2, -2, 0, 1, -1, 0], -1⟩,
  ⟨0, ![2, -2, 0, 1, 0, -1], -1⟩,
  ⟨0, ![2, -2, 1, -1, 0, 0], 2⟩,
  ⟨0, ![2, -2, 1, 0, -1, 0], -1⟩,
  ⟨0, ![2, -2, 1, 0, 0, -1], -1⟩,
  ⟨0, ![2, -1, -2, 0, 0, 1], 1⟩,
  ⟨0, ![2, -1, -2, 0, 1, 0], 1⟩,
  ⟨0, ![2, -1, -2, 1, 0, 0], -2⟩,
  ⟨0, ![2, -1, 0, -2, 0, 1], 1⟩,
  ⟨0, ![2, -1, 0, -2, 1, 0], 1⟩,
  ⟨0, ![2, -1, 0, 0, -2, 1], -2⟩,
  ⟨0, ![2, -1, 0, 0, 1, -2], -2⟩,
  ⟨0, ![2, -1, 0, 1, -2, 0], 1⟩,
  ⟨0, ![2, -1, 0, 1, 0, -2], 1⟩,
  ⟨0, ![2, -1, 1, -2, 0, 0], -2⟩,
  ⟨0, ![2, -1, 1, 0, -2, 0], 1⟩,
  ⟨0, ![2, -1, 1, 0, 0, -2], 1⟩,
  ⟨0, ![2, 0, -2, 0, -1, 1], -1⟩,
  ⟨0, ![2, 0, -2, 0, 1, -1], -1⟩,
  ⟨0, ![2, 0, -2, 1, -1, 0], 1⟩,
  ⟨0, ![2, 0, -2, 1, 0, -1], 1⟩,
  ⟨0, ![2, 0, -1, 0, -2, 1], 1⟩,
  ⟨0, ![2, 0, -1, 0, 1, -2], 1⟩,
  ⟨0, ![2, 0, -1, 1, -2, 0], -1⟩,
  ⟨0, ![2, 0, -1, 1, 0, -2], -1⟩,
  ⟨0, ![2, 0, 0, -2, -1, 1], -1⟩,
  ⟨0, ![2, 0, 0, -2, 1, -1], -1⟩,
  ⟨0, ![2, 0, 0, -1, -2, 1], 1⟩,
  ⟨0, ![2, 0, 0, -1, 1, -2], 1⟩,
  ⟨0, ![2, 0, 1, -2, -1, 0], 1⟩,
  ⟨0, ![2, 0, 1, -2, 0, -1], 1⟩,
  ⟨0, ![2, 0, 1, -1, -2, 0], -1⟩,
  ⟨0, ![2, 0, 1, -1, 0, -2], -1⟩
]

end MUB6.Certificate.GramFunctions.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10499 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5188 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5189 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5190 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

def row5191 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5192 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5193 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

def row5194 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

def row5195 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5196 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5197 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1319, 4), (key1327, -2), (key1352, -2), (key1355, 2), (key1386, -2), (key1394, 2), (key1419, 2), (key1427, -4), (key1445, 2), (key1473, 2), (key1481, -2), (key1541, 2), (key1549, -2), (key1568, -2), (key1576, 2), (key1625, 2), (key1634, -2), (key1684, -2), (key1690, 2)]

def row5198 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5199 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5200 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5201 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5202 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row5203 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5204 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5205 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row5206 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row5207 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5208 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5209 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 2), (key1541, -2), (key1549, 4), (key1557, -2), (key1568, 2), (key1576, -4), (key1594, 2), (key1625, 2), (key1634, -2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row5210 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5211 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5212 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5213 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5214 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5215 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5216 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5217 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5218 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5219 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5220 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5221 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5222 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5223 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5224 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5225 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -1), (key1541, 1), (key1549, -2), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row5226 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5227 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1319, -2), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1427, 2), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, 1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, 1), (key1690, -1)]

def row5228 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5229 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5230 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -2), (key277, -2), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

def row5231 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5232 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5233 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -4), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

def row5234 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -4), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

def row5235 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5236 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 3), (key277, -1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5237 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key253, 4), (key263, -2), (key277, -2), (key278, 2), (key302, -2), (key307, 2), (key316, 2), (key321, -4), (key331, 2), (key346, 2), (key347, -2), (key385, 2), (key390, -2), (key406, -2), (key411, 2), (key445, 2), (key453, -2), (key488, -2), (key489, 2)]

def row5238 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5239 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 2), (key331, -1), (key346, -1), (key347, 1), (key385, -1), (key390, 1), (key406, 1), (key411, -1), (key445, -1), (key453, 1), (key488, 1), (key489, -1)]

def row5240 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

def row5241 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

def row5242 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 2), (key445, 2), (key453, -2), (key657, 2), (key658, -2), (key661, -2), (key662, 2)]

def row5243 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

def row5244 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

def row5245 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 4), (key445, 2), (key453, -2), (key658, -2), (key661, -2), (key662, 2)]

def row5246 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 4), (key445, 2), (key453, -2), (key658, -2), (key661, -2), (key662, 2)]

def row5247 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5248 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

def row5249 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 2), (key445, 2), (key453, -2), (key657, 2), (key658, -2), (key661, -2), (key662, 2)]

def row5250 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

def row5251 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

def row5252 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -2), (key321, 1), (key347, 1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key421, -1), (key487, -1), (key488, 1), (key655, -1), (key657, 1), (key660, 1), (key661, -1)]

def row5253 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -2), (key321, 1), (key347, 1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key421, -1), (key487, -1), (key488, 1), (key655, -1), (key657, 1), (key660, 1), (key661, -1)]

def row5254 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key656, -1), (key658, 1), (key660, 1), (key662, -1)]

def row5255 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key656, -1), (key658, 1), (key660, 1), (key662, -1)]

def row5256 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key263, 1), (key277, -1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 2), (key347, -1), (key385, 2), (key390, -1), (key400, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

def row5257 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key263, 1), (key277, -1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 2), (key347, -1), (key385, 2), (key390, -1), (key400, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

def row5258 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

def row5259 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

def row5260 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

def row5261 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

def row5262 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 1), (key321, -2), (key331, 1), (key347, -1), (key385, 1), (key390, -1), (key400, 1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

def row5263 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 1), (key321, -2), (key331, 1), (key347, -1), (key385, 1), (key390, -1), (key400, 1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

def row5264 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key347, -1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -1), (key487, -1), (key489, 1), (key657, -1), (key658, 1), (key660, 1), (key662, -1)]

def row5265 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key347, -1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -1), (key487, -1), (key489, 1), (key657, -1), (key658, 1), (key660, 1), (key662, -1)]

def row5266 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key655, -1), (key656, 1), (key660, 1), (key661, -1)]

def row5267 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key655, -1), (key656, 1), (key660, 1), (key661, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5388 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1125, -4), (key1130, 4), (key1152, 4), (key1159, -4)]

def row5389 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5390 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5391 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5392 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5393 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1125, -4), (key1130, 4), (key1152, 4), (key1159, -4)]

def row5394 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5395 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5396 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5397 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5398 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5399 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5400 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5401 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5402 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5403 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5404 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5405 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5406 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5407 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5408 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5409 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5410 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5411 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5412 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5413 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5414 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5415 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

def row5416 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5417 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

def row5418 : Integer.Sparse Key := [(key25, -4), (key27, 4), (key37, 4), (key40, -4), (key50, 4), (key52, -4), (key76, -4), (key81, 4), (key117, -4), (key120, 4), (key139, 4), (key144, -4)]

def row5419 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

def row5420 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

def row5421 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

def row5422 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

def row5423 : Integer.Sparse Key := [(key25, -4), (key27, 4), (key37, 4), (key40, -4), (key50, 4), (key52, -4), (key76, -4), (key81, 4), (key117, -4), (key120, 4), (key139, 4), (key144, -4)]

def row5424 : Integer.Sparse Key := [(key37, -2), (key40, 2), (key76, 2), (key81, -2), (key117, -2), (key139, 2), (key197, 2), (key201, -2), (key210, 2), (key213, -2), (key379, -2), (key382, 2), (key464, 4), (key466, -2), (key483, -2), (key590, -4), (key592, 2), (key609, 2)]

def row5425 : Integer.Sparse Key := [(key37, 1), (key40, -1), (key76, -1), (key81, 1), (key117, 1), (key139, -1), (key197, -1), (key201, 1), (key210, -1), (key213, 1), (key379, 1), (key382, -1), (key464, -2), (key466, 1), (key483, 1), (key590, 2), (key592, -1), (key609, -1)]

def row5426 : Integer.Sparse Key := [(key37, 1), (key40, -1), (key76, -1), (key81, 1), (key117, 1), (key139, -1), (key197, -1), (key201, 1), (key210, -1), (key213, 1), (key379, 1), (key382, -1), (key464, -2), (key466, 1), (key483, 1), (key590, 2), (key592, -1), (key609, -1)]

def row5427 : Integer.Sparse Key := [(key37, -2), (key40, 2), (key76, 2), (key81, -2), (key210, 2), (key213, -2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key590, -2), (key592, 2)]

def row5428 : Integer.Sparse Key := [(key40, -1), (key81, 1), (key210, -1), (key213, 1), (key215, 1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key590, 1), (key592, -1)]

def row5429 : Integer.Sparse Key := [(key40, -1), (key81, 1), (key210, -1), (key213, 1), (key215, 1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key590, 1), (key592, -1)]

def row5430 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, -1), (key76, -1), (key210, -2), (key213, 1), (key217, -1), (key379, 2), (key382, -1), (key464, -1), (key466, 1), (key567, 1), (key590, 1), (key592, -1)]

def row5431 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, -1), (key76, -1), (key210, -2), (key213, 1), (key217, -1), (key379, 2), (key382, -1), (key464, -1), (key466, 1), (key567, 1), (key590, 1), (key592, -1)]

def row5432 : Integer.Sparse Key := [(key25, -1), (key50, 1), (key117, 1), (key139, -1), (key213, 1), (key215, 1), (key217, -1), (key382, -1), (key464, -2), (key466, 1), (key565, -1), (key567, 1), (key590, 2), (key592, -1)]

def row5433 : Integer.Sparse Key := [(key25, -1), (key50, 1), (key117, 1), (key139, -1), (key213, 1), (key215, 1), (key217, -1), (key382, -1), (key464, -2), (key466, 1), (key565, -1), (key567, 1), (key590, 2), (key592, -1)]

def row5434 : Integer.Sparse Key := [(key37, -1), (key76, 1), (key117, -1), (key139, 1), (key210, 2), (key213, -2), (key215, -1), (key217, 2), (key379, -2), (key382, 2), (key464, 3), (key466, -2), (key565, 1), (key567, -2), (key590, -3), (key592, 2)]

def row5435 : Integer.Sparse Key := [(key37, -1), (key76, 1), (key117, -1), (key139, 1), (key210, 2), (key213, -2), (key215, -1), (key217, 2), (key379, -2), (key382, 2), (key464, 3), (key466, -2), (key565, 1), (key567, -2), (key590, -3), (key592, 2)]

def row5436 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5437 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5438 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

def row5439 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5440 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5441 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

def row5442 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

def row5443 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5444 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5445 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

def row5446 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5447 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

def row5448 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, 4), (key1042, -4), (key1073, -4), (key1077, 4), (key1125, -4), (key1128, 4), (key1152, 4), (key1156, -4)]

def row5449 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5450 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5451 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5452 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5453 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, 4), (key1042, -4), (key1073, -4), (key1077, 4), (key1125, -4), (key1128, 4), (key1152, 4), (key1156, -4)]

def row5454 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5455 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5456 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5457 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5458 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5459 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5460 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5461 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5462 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5463 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5464 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5465 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5466 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5467 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5468 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5469 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5470 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5471 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5472 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5473 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5474 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5475 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

def row5476 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5477 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

def row5478 : Integer.Sparse Key := [(key10, -4), (key13, 8), (key15, -4), (key93, 4), (key96, -4), (key158, -4), (key163, 4), (key169, -4), (key170, 4), (key189, 4), (key192, -4)]

def row5479 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5480 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5481 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5482 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5483 : Integer.Sparse Key := [(key10, -4), (key13, 8), (key15, -4), (key93, 4), (key96, -4), (key158, -4), (key163, 4), (key169, -4), (key170, 4), (key189, 4), (key192, -4)]

def row5484 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 6), (key163, -6), (key169, -2), (key170, 2), (key189, -2), (key192, 2)]

def row5485 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -3), (key163, 3), (key169, 1), (key170, -1), (key189, 1), (key192, -1)]

def row5486 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -3), (key163, 3), (key169, 1), (key170, -1), (key189, 1), (key192, -1)]

def row5487 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 4), (key163, -6), (key170, 2), (key189, -2), (key192, 2)]

def row5488 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -2), (key163, 3), (key170, -1), (key189, 1), (key192, -1)]

def row5489 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -2), (key163, 3), (key170, -1), (key189, 1), (key192, -1)]

def row5490 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -6), (key163, 3), (key169, 4), (key170, -1), (key189, 1), (key192, -1)]

def row5491 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -6), (key163, 3), (key169, 4), (key170, -1), (key189, 1), (key192, -1)]

def row5492 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 3), (key169, -1), (key170, -1), (key189, 1), (key192, -1)]

def row5493 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 3), (key169, -1), (key170, -1), (key189, 1), (key192, -1)]

def row5494 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 6), (key163, -6), (key169, -2), (key170, 2), (key189, -2), (key192, 2)]

def row5495 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 6), (key163, -6), (key169, -2), (key170, 2), (key189, -2), (key192, 2)]

def row5496 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

def row5497 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

def row5498 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5499 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

def row5500 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

def row5501 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key163, -2), (key169, 4), (key170, -2), (key189, -2), (key192, 2)]

def row5502 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key163, -2), (key169, 4), (key170, -2), (key189, -2), (key192, 2)]

def row5503 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5504 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

def row5505 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

def row5506 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

def row5507 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

def row5598 : Integer.Sparse Key := [(key982, -4), (key986, 8), (key988, -4), (key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row5599 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5600 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5601 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5602 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5603 : Integer.Sparse Key := [(key982, -4), (key986, 8), (key988, -4), (key1096, 4), (key1100, -4), (key1171, -4), (key1175, 4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

def row5604 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5605 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5606 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5607 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5608 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5609 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5610 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5611 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5612 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5613 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5614 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5615 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5616 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5617 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5618 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5619 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5620 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5621 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5622 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5623 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5624 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5625 : Integer.Sparse Key := [(key982, 2), (key986, -4), (key988, 2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

def row5626 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5627 : Integer.Sparse Key := [(key982, -1), (key986, 2), (key988, -1), (key1096, 1), (key1100, -1), (key1171, -1), (key1175, 1), (key1185, -1), (key1186, 1), (key1222, 1), (key1224, -1)]

def row5628 : Integer.Sparse Key := [(key2362, -4), (key2365, 8), (key2367, -4), (key2457, 4), (key2460, -4), (key2521, -4), (key2525, 4), (key2532, -4), (key2533, 4), (key2562, 4), (key2564, -4)]

def row5629 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5630 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5631 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5632 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5633 : Integer.Sparse Key := [(key2362, -4), (key2365, 8), (key2367, -4), (key2457, 4), (key2460, -4), (key2521, -4), (key2525, 4), (key2532, -4), (key2533, 4), (key2562, 4), (key2564, -4)]

def row5634 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -6), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 2)]

def row5635 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -3), (key2525, 3), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5636 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -3), (key2525, 3), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5637 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -6), (key2533, 2), (key2562, -2), (key2564, 2)]

def row5638 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -2), (key2525, 3), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5639 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -2), (key2525, 3), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5640 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -6), (key2525, 3), (key2532, 4), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5641 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -6), (key2525, 3), (key2532, 4), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5642 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 3), (key2532, -1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5643 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 3), (key2532, -1), (key2533, -1), (key2562, 1), (key2564, -1)]

def row5644 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -6), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 2)]

def row5645 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -6), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 2)]

def row5646 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5647 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5648 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5649 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5650 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5651 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2525, -2), (key2532, 4), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5652 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2525, -2), (key2532, 4), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5653 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5654 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5655 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

def row5656 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5657 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

def row5698 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

def row5699 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5700 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5701 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

def row5702 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5703 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5704 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5705 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5706 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5707 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5708 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

def row5709 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

def row5710 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

def row5711 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5712 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5713 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

def row5714 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5715 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5716 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5717 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5718 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5719 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5720 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

def row5721 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

def row5722 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5723 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5724 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5725 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5726 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5727 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5728 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5729 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5730 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5731 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5732 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5733 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5734 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5735 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

def row5736 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

def row5737 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5778 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row5779 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5780 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5781 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row5782 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5783 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5784 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5785 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5786 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5787 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5788 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row5789 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

def row5790 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row5791 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5792 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5793 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row5794 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5795 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5796 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5797 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5798 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5799 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5800 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row5801 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

def row5802 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5803 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5804 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5805 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5806 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5807 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5808 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5809 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5810 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5811 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5812 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5813 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5814 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5815 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

def row5816 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5817 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

def row5858 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 2), (key2899, 2), (key2915, -2), (key2952, 2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

def row5859 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, 1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5860 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, 1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5861 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2915, -2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

def row5862 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2915, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5863 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2915, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5864 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, 2), (key2899, -1), (key2915, 1), (key2952, -4), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5865 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, 2), (key2899, -1), (key2915, 1), (key2952, -4), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5866 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -3), (key2899, -1), (key2915, 1), (key2952, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5867 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -3), (key2899, -1), (key2915, 1), (key2952, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

def row5868 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 2), (key2899, 2), (key2915, -2), (key2952, 2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

def row5869 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 2), (key2899, 2), (key2915, -2), (key2952, 2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

def row5870 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -2), (key2751, 2), (key2797, 2), (key2915, -2), (key2945, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

def row5871 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5872 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5873 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -4), (key2751, 2), (key2797, 2), (key2915, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

def row5874 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2751, -1), (key2797, -1), (key2915, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5875 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2751, -1), (key2797, -1), (key2915, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5876 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, -2), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 4), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5877 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, -2), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 4), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5878 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 3), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5879 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 3), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

def row5880 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -2), (key2751, 2), (key2797, 2), (key2915, -2), (key2945, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

def row5881 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -2), (key2751, 2), (key2797, 2), (key2915, -2), (key2945, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

def row5882 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2739, -1), (key2749, 2), (key2787, 1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5883 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2739, -1), (key2749, 2), (key2787, 1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5884 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2749, 1), (key2797, 1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5885 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2749, 1), (key2797, 1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5886 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2797, -1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5887 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2797, -1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5888 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, -1), (key2797, 2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5889 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 2), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, -1), (key2797, 2), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5890 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2730, 1), (key2739, 1), (key2749, 1), (key2787, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5891 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2730, 1), (key2739, 1), (key2749, 1), (key2787, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5892 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -2), (key2749, 1), (key2797, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5893 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -2), (key2749, 1), (key2797, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5894 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5895 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2797, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, 1), (key2940, 1), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row5896 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5897 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, 1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row5898 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5899 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5900 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

def row5901 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5902 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5903 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

def row5904 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

def row5905 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5906 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5907 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1318, 4), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, -2), (key1393, 2), (key1420, 2), (key1426, -4), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, 2), (key1548, -2), (key1569, -2), (key1575, 2), (key1624, 2), (key1633, -2), (key1683, -2), (key1689, 2)]

def row5908 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5909 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5910 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5911 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5912 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row5913 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5914 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5915 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row5916 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row5917 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5918 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5919 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 2), (key1542, -2), (key1548, 4), (key1556, -2), (key1569, 2), (key1575, -4), (key1593, 2), (key1624, 2), (key1633, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row5920 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5921 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5922 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5923 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5924 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5925 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5926 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5927 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5928 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5929 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5930 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5931 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5932 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5933 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5934 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5935 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -1), (key1542, 1), (key1548, -2), (key1556, 1), (key1569, -1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row5936 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5937 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1318, -2), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, -1), (key1548, 1), (key1569, 1), (key1575, -1), (key1624, -1), (key1633, 1), (key1683, 1), (key1689, -1)]

def row5938 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5939 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5940 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

def row5941 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5942 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5943 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

def row5944 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

def row5945 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5946 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5947 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key252, 4), (key262, -2), (key268, -2), (key273, 2), (key303, -2), (key306, 2), (key317, 2), (key320, -2), (key386, 2), (key389, -4), (key399, 2), (key407, -2), (key410, 2), (key468, 2), (key471, -2), (key569, 2), (key574, -2), (key594, -2), (key597, 2)]

def row5948 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5949 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5950 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5951 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5952 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7256 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7257 : Integer.Sparse Key := [(key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2277, -1), (key2283, 1), (key2288, 1), (key2296, -1), (key2342, 1), (key2344, -1), (key2348, -1), (key2350, 1)]

def row7258 : Integer.Sparse Key := [(key2081, -4), (key2083, 4), (key2088, 4), (key2090, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2332, 4), (key2334, 4), (key2339, -4)]

def row7259 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7260 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7261 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7262 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7263 : Integer.Sparse Key := [(key2081, -4), (key2083, 4), (key2088, 4), (key2090, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2332, 4), (key2334, 4), (key2339, -4)]

def row7264 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7265 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7266 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7267 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7268 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7269 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7270 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7271 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7272 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7273 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7274 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7275 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7276 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7277 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7278 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7279 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7280 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7281 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7282 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7283 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7284 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7285 : Integer.Sparse Key := [(key2081, 2), (key2083, -2), (key2088, -2), (key2090, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2332, -2), (key2334, -2), (key2339, 2)]

def row7286 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7287 : Integer.Sparse Key := [(key2081, -1), (key2083, 1), (key2088, 1), (key2090, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2332, 1), (key2334, 1), (key2339, -1)]

def row7288 : Integer.Sparse Key := [(key822, 4), (key823, -4), (key827, -4), (key828, 4), (key906, -4), (key910, 4), (key911, 4), (key918, -4), (key952, 4), (key953, -8), (key957, 4)]

def row7289 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7290 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7291 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7292 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7293 : Integer.Sparse Key := [(key822, 4), (key823, -4), (key827, -4), (key828, 4), (key906, -4), (key910, 4), (key911, 4), (key918, -4), (key952, 4), (key953, -8), (key957, 4)]

def row7294 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7295 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

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

def row7297 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7298 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7299 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7300 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7301 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7302 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7303 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7304 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7305 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7306 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7307 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7308 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7309 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7310 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7311 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7312 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7313 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7314 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7315 : Integer.Sparse Key := [(key822, -2), (key823, 2), (key827, 2), (key828, -2), (key906, 2), (key910, -2), (key911, -2), (key918, 2), (key952, -2), (key953, 4), (key957, -2)]

def row7316 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7317 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

end MUB6.Certificate.GramRows

end OAI
end


