-- Prove2me | Definitions.Def_OAIQ106D145
-- name    : OAIQ106D145
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:44:56.511194+00:00
-- url     : https://prove2.me/theorems/a97adeb6-9ab3-4552-af96-d13c69a5afc8
-- title:
--   Definitions bundle OAIQ106D145 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 297 declarations of OpenAI's Lean: 297 definitions. The definitions and types are `OAI.MUB6.Certificate.GramFunctions.Block2.terms7`, `OAI.MUB6.Certificate.GramRows.row5953`, `OAI.MUB6.Certificate.GramRows.row5954`, `OAI.MUB6.Certificate.GramRows.row5955`, `OAI.MUB6.Certificate.GramRows.row5956`, `OAI.MUB6.Certificate.GramRows.row5957`, `OAI.MUB6.Certificate.GramRows.row5958`, `OAI.MUB6.Certificate.GramRows.row5959`, `OAI.MUB6.Certificate.GramRows.row5960`, `OAI.MUB6.Certificate.GramRows.row5961`, `OAI.MUB6.Certificate.GramRows.row5962`, `OAI.MUB6.Certificate.GramRows.row5963`, `OAI.MUB6.Certificate.GramRows.row5964`, `OAI.MUB6.Certificate.GramRows.row5965`, `OAI.MUB6.Certificate.GramRows.row5966`, `OAI.MUB6.Certificate.GramRows.row5967`, `OAI.MUB6.Certificate.GramRows.row5968`, `OAI.MUB6.Certificate.GramRows.row5969`, `OAI.MUB6.Certificate.GramRows.row5970`, `OAI.MUB6.Certificate.GramRows.row5971`, `OAI.MUB6.Certificate.GramRows.row5972`, `OAI.MUB6.Certificate.GramRows.row5973`, `OAI.MUB6.Certificate.GramRows.row5974`, `OAI.MUB6.Certificate.GramRows.row5975`, `OAI.MUB6.Certificate.GramRows.row5976`, `OAI.MUB6.Certificate.GramRows.row5977`, `OAI.MUB6.Certificate.GramRows.row5978`, `OAI.MUB6.Certificate.GramRows.row5979`, `OAI.MUB6.Certificate.GramRows.row5980`, `OAI.MUB6.Certificate.GramRows.row5981`, `OAI.MUB6.Certificate.GramRows.row5982`, `OAI.MUB6.Certificate.GramRows.row5983`, `OAI.MUB6.Certificate.GramRows.row5984`, `OAI.MUB6.Certificate.GramRows.row5985`, `OAI.MUB6.Certificate.GramRows.row5986`, `OAI.MUB6.Certificate.GramRows.row5987`, `OAI.MUB6.Certificate.GramRows.row5988`, `OAI.MUB6.Certificate.GramRows.row5989`, `OAI.MUB6.Certificate.GramRows.row5990`, `OAI.MUB6.Certificate.GramRows.row5991` and 257 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramFunctions_Block2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Block2.lean), [`MutuallyUnbiased_GramRows_Block70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block70.lean), [`MutuallyUnbiased_GramRows_Block71`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block71.lean), [`MutuallyUnbiased_GramRows_Block72`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block72.lean), [`MutuallyUnbiased_GramRows_Block73`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block73.lean), [`MutuallyUnbiased_GramRows_Block77`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block77.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D085`, `OAIQ106D086`, `OAIQ106D087` and `OAIQ106D088` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D198`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D081
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D086
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D088

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block2

def terms7 : Array TaggedTerm := #[
  ⟨1, ![1, -1, -2, 0, 0, 2], 1⟩,
  ⟨1, ![1, -1, -2, 0, 2, 0], 1⟩,
  ⟨1, ![1, -1, -2, 2, 0, 0], -2⟩,
  ⟨1, ![1, -1, 0, -2, 0, 2], 1⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], 1⟩,
  ⟨1, ![1, -1, 0, 0, -2, 2], -2⟩,
  ⟨1, ![1, -1, 0, 0, 2, -2], -2⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], 1⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], 1⟩,
  ⟨1, ![1, -1, 2, -2, 0, 0], -2⟩,
  ⟨1, ![1, -1, 2, 0, -2, 0], 1⟩,
  ⟨1, ![1, -1, 2, 0, 0, -2], 1⟩,
  ⟨1, ![1, 0, -2, -1, 0, 2], -1⟩,
  ⟨1, ![1, 0, -2, -1, 2, 0], -1⟩,
  ⟨1, ![1, 0, -2, 2, -1, 0], 1⟩,
  ⟨1, ![1, 0, -2, 2, 0, -1], 1⟩,
  ⟨1, ![1, 0, -1, -2, 0, 2], -1⟩,
  ⟨1, ![1, 0, -1, -2, 2, 0], -1⟩,
  ⟨1, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨1, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨1, ![1, 0, 0, -1, -2, 2], 1⟩,
  ⟨1, ![1, 0, 0, -1, 2, -2], 1⟩,
  ⟨1, ![1, 0, 0, 2, -2, -1], -1⟩,
  ⟨1, ![1, 0, 0, 2, -1, -2], -1⟩,
  ⟨1, ![1, 0, 2, -2, -1, 0], 1⟩,
  ⟨1, ![1, 0, 2, -2, 0, -1], 1⟩,
  ⟨1, ![1, 0, 2, 0, -2, -1], -1⟩,
  ⟨1, ![1, 0, 2, 0, -1, -2], -1⟩,
  ⟨1, ![1, 2, -2, -1, 0, 0], 2⟩,
  ⟨1, ![1, 2, -2, 0, -1, 0], -1⟩,
  ⟨1, ![1, 2, -2, 0, 0, -1], -1⟩,
  ⟨1, ![1, 2, -1, -2, 0, 0], 2⟩,
  ⟨1, ![1, 2, -1, 0, -2, 0], -1⟩,
  ⟨1, ![1, 2, -1, 0, 0, -2], -1⟩,
  ⟨1, ![1, 2, 0, -2, -1, 0], -1⟩,
  ⟨1, ![1, 2, 0, -2, 0, -1], -1⟩,
  ⟨1, ![1, 2, 0, -1, -2, 0], -1⟩,
  ⟨1, ![1, 2, 0, -1, 0, -2], -1⟩,
  ⟨1, ![1, 2, 0, 0, -2, -1], 2⟩,
  ⟨1, ![1, 2, 0, 0, -1, -2], 2⟩
]

end MUB6.Certificate.GramFunctions.Block2

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

def row5953 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5954 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5955 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

def row5956 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

def row5957 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5958 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5959 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key252, -2), (key303, 2), (key306, -2), (key317, -2), (key320, 4), (key330, -2), (key336, -2), (key342, 2), (key386, -2), (key389, 2), (key407, 2), (key410, -4), (key420, 2), (key468, 2), (key477, -2), (key579, 2), (key585, -2), (key594, -2), (key603, 2)]

def row5960 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5961 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5962 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5963 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5964 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5965 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5966 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5967 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5968 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5969 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5970 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5971 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5972 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5973 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5974 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5975 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key252, 1), (key303, -1), (key306, 1), (key317, 1), (key320, -2), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, -1), (key410, 2), (key420, -1), (key468, -1), (key477, 1), (key579, -1), (key585, 1), (key594, 1), (key603, -1)]

def row5976 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5977 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key252, -2), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key320, 1), (key386, -1), (key389, 2), (key399, -1), (key407, 1), (key410, -1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key594, 1), (key597, -1)]

def row5978 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5979 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5980 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

def row5981 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5982 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5983 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

def row5984 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

def row5985 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5986 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5987 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1315, 4), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, -2), (key1390, 2), (key1419, 2), (key1423, -4), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, 2), (key1545, -2), (key1568, -2), (key1572, 2), (key1622, 2), (key1631, -2), (key1657, -2), (key1665, 2)]

def row5988 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5989 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row5990 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5991 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5992 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row5993 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5994 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5995 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row5996 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row5997 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5998 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row5999 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1315, -2), (key1386, 2), (key1390, -2), (key1419, -2), (key1423, 2), (key1541, -2), (key1545, 4), (key1554, -2), (key1568, 2), (key1572, -4), (key1591, 2), (key1622, 2), (key1631, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row6000 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6001 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6002 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6003 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6004 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6005 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6006 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6007 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6008 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6009 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6010 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6011 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6012 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6013 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6014 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row6015 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1315, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1423, -1), (key1541, 1), (key1545, -2), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6016 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6017 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1315, -2), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1423, 2), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, 1), (key1572, -1), (key1622, -1), (key1631, 1), (key1657, 1), (key1665, -1)]

def row6018 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6019 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6020 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6021 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6022 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6023 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6024 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6025 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6026 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6027 : Integer.Sparse Key := [(key25, 4), (key26, -4), (key37, -4), (key39, 4), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, -2), (key117, 4), (key119, -2), (key139, -2), (key142, 4), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6028 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6029 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6030 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6031 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6032 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6033 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6034 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6035 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6036 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6037 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6038 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6039 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 4), (key51, -4), (key76, -4), (key79, 4), (key107, -2), (key117, -2), (key119, 4), (key139, 4), (key142, -2), (key159, -2), (key173, 2), (key177, -2), (key182, -2), (key190, 2)]

def row6040 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6041 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6042 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6043 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6044 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6045 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6046 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6047 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6048 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6049 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6050 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6051 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6052 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6053 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6054 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6055 : Integer.Sparse Key := [(key25, 1), (key26, -1), (key37, -1), (key39, 1), (key50, -2), (key51, 2), (key76, 2), (key79, -2), (key107, 1), (key117, 1), (key119, -2), (key139, -2), (key142, 1), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6056 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6057 : Integer.Sparse Key := [(key25, -2), (key26, 2), (key37, 2), (key39, -2), (key50, 1), (key51, -1), (key76, -1), (key79, 1), (key107, 1), (key117, -2), (key119, 1), (key139, 1), (key142, -2), (key159, 1), (key173, -1), (key177, 1), (key182, 1), (key190, -1)]

def row6058 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6059 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6060 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6061 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6062 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6063 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6064 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6065 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6066 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6067 : Integer.Sparse Key := [(key1256, 4), (key1260, -4), (key1265, -4), (key1267, 4), (key1531, -2), (key1535, 2), (key1609, -2), (key1641, 2), (key1648, 4), (key1650, -2), (key1673, -2), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 4), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6068 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6069 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6070 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6071 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6072 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6073 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6074 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6075 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6076 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6077 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6078 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6079 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 4), (key1535, -4), (key1609, -2), (key1641, 2), (key1648, -2), (key1650, 4), (key1673, -2), (key1765, -4), (key1767, 4), (key1806, 4), (key1808, -2), (key1831, -2), (key1836, -2), (key1847, 2)]

def row6080 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6081 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6082 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6083 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6084 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6085 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6086 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6087 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6088 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6089 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6090 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6091 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6092 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6093 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6094 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6095 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, -1), (key1267, 1), (key1531, -2), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, 1), (key1650, -2), (key1673, 1), (key1765, 2), (key1767, -2), (key1806, -2), (key1808, 1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6096 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6097 : Integer.Sparse Key := [(key1256, -2), (key1260, 2), (key1265, 2), (key1267, -2), (key1531, 1), (key1535, -1), (key1609, 1), (key1641, -1), (key1648, -2), (key1650, 1), (key1673, 1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -2), (key1831, 1), (key1836, 1), (key1847, -1)]

def row6098 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6099 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6100 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

def row6101 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6102 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6103 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

def row6104 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

def row6105 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6106 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6107 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, 2), (key1447, -2), (key1455, -4), (key1457, 2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -2), (key1825, 2), (key1839, -2), (key1841, 2)]

def row6108 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6109 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6110 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6111 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6112 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

def row6113 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6114 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6115 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

def row6116 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

def row6117 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6118 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6119 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1447, 2), (key1455, 2), (key1466, -2), (key1573, 2), (key1596, -2), (key1655, -2), (key1667, 2), (key1788, -4), (key1790, 2), (key1798, 2), (key1813, 4), (key1817, -2), (key1825, -2), (key1839, -2), (key1841, 2)]

def row6120 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6121 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6122 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6123 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6124 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6125 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6126 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6127 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6128 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6129 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6130 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6131 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6132 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6133 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6134 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6135 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, 1), (key1447, -1), (key1455, -1), (key1466, 1), (key1573, -1), (key1596, 1), (key1655, 1), (key1667, -1), (key1788, 2), (key1790, -1), (key1798, -1), (key1813, -2), (key1817, 1), (key1825, 1), (key1839, 1), (key1841, -1)]

def row6136 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6137 : Integer.Sparse Key := [(key1391, -1), (key1397, 1), (key1424, -1), (key1447, 1), (key1455, 2), (key1457, -1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1774, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row6138 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6139 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6140 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -2), (key267, -2), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

def row6141 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6142 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6143 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -4), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6144 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -4), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

def row6145 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6146 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 3), (key267, -1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6147 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key251, 4), (key260, -2), (key267, -2), (key271, 2), (key302, -2), (key305, 2), (key316, 2), (key319, -4), (key328, 2), (key335, 2), (key340, -2), (key385, 2), (key388, -2), (key406, -2), (key409, 2), (key442, 2), (key450, -2), (key469, -2), (key475, 2)]

def row6148 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6149 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 2), (key328, -1), (key335, -1), (key340, 1), (key385, -1), (key388, 1), (key406, 1), (key409, -1), (key442, -1), (key450, 1), (key469, 1), (key475, -1)]

def row6150 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row6151 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row6152 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 2), (key442, 2), (key450, -2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

def row6153 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row6154 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row6155 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 4), (key442, 2), (key450, -2), (key583, -2), (key595, -2), (key601, 2)]

def row6156 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 4), (key442, 2), (key450, -2), (key583, -2), (key595, -2), (key601, 2)]

def row6157 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row6158 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -3), (key442, -1), (key450, 1), (key578, 1), (key583, 1), (key595, 1), (key601, -1)]

def row6159 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key251, -2), (key302, 2), (key305, -2), (key316, -4), (key319, 6), (key328, -2), (key335, -2), (key340, 2), (key406, 2), (key409, -4), (key418, 2), (key442, 2), (key450, -2), (key578, 2), (key583, -2), (key595, -2), (key601, 2)]

def row6160 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row6161 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 2), (key319, -3), (key328, 1), (key335, 1), (key340, -1), (key406, -1), (key409, 2), (key418, -1), (key442, -1), (key450, 1), (key578, -1), (key583, 1), (key595, 1), (key601, -1)]

def row6162 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -2), (key319, 1), (key340, 1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key418, -1), (key467, -1), (key469, 1), (key568, -1), (key578, 1), (key593, 1), (key595, -1)]

def row6163 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -2), (key319, 1), (key340, 1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key418, -1), (key467, -1), (key469, 1), (key568, -1), (key578, 1), (key593, 1), (key595, -1)]

def row6164 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key572, -1), (key583, 1), (key593, 1), (key601, -1)]

def row6165 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key572, -1), (key583, 1), (key593, 1), (key601, -1)]

def row6166 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key260, 1), (key267, -1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 2), (key340, -1), (key385, 2), (key388, -1), (key397, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

def row6167 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key260, 1), (key267, -1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 2), (key340, -1), (key385, 2), (key388, -1), (key397, -1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

def row6168 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

def row6169 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

def row6170 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

def row6171 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 2), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key328, -1), (key340, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key593, 1), (key595, -1)]

def row6172 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 1), (key319, -2), (key328, 1), (key340, -1), (key385, 1), (key388, -1), (key397, 1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

def row6173 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key316, 1), (key319, -2), (key328, 1), (key340, -1), (key385, 1), (key388, -1), (key397, 1), (key406, -1), (key409, 2), (key418, -2), (key467, -1), (key475, 1), (key583, 1), (key593, 1), (key601, -1)]

def row6174 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key340, -1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -1), (key467, -1), (key475, 1), (key578, -1), (key583, 1), (key593, 1), (key601, -1)]

def row6175 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key251, 1), (key302, -1), (key305, 1), (key319, -2), (key328, 1), (key335, 1), (key340, -1), (key385, 2), (key388, -1), (key406, -1), (key409, 2), (key418, -1), (key467, -1), (key475, 1), (key578, -1), (key583, 1), (key593, 1), (key601, -1)]

def row6176 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key568, -1), (key572, 1), (key593, 1), (key595, -1)]

def row6177 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key251, -2), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key319, 1), (key385, -1), (key388, 2), (key397, -1), (key406, 1), (key409, -1), (key467, -1), (key469, 1), (key568, -1), (key572, 1), (key593, 1), (key595, -1)]

def row6198 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6199 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6200 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

def row6201 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6202 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6203 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

def row6204 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

def row6205 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6206 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6207 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1319, -2), (key1386, 2), (key1394, -2), (key1419, -2), (key1427, 4), (key1445, -2), (key1473, -2), (key1481, 2), (key1541, -2), (key1549, 2), (key1568, 2), (key1576, -4), (key1594, 2), (key1682, 2), (key1690, -2), (key1904, 2), (key1912, -2), (key1919, -2), (key1927, 2)]

def row6208 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6209 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6210 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6211 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6212 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6213 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6214 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6215 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6216 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6217 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6218 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6219 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6220 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6221 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6222 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6223 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1319, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1427, -2), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, -1), (key1576, 2), (key1594, -1), (key1682, -1), (key1690, 1), (key1904, -1), (key1912, 1), (key1919, 1), (key1927, -1)]

def row6224 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6225 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6226 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

def row6227 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6228 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6229 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

def row6230 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6231 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6232 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6233 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6234 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6235 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1549, -1), (key1557, 1), (key1576, -1), (key1594, 1), (key1682, 2), (key1684, -1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, 1), (key1912, -1), (key1919, -2), (key1921, 1), (key1927, 1)]

def row6236 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

def row6237 : Integer.Sparse Key := [(key1319, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1427, -2), (key1445, 2), (key1473, 2), (key1481, -2), (key1549, 2), (key1557, -2), (key1576, 2), (key1594, -2), (key1682, -4), (key1684, 2), (key1690, 2), (key1897, -2), (key1900, 2), (key1904, -2), (key1912, 2), (key1919, 4), (key1921, -2), (key1927, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6278 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6279 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6280 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6281 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6282 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6283 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6284 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6285 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6286 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6287 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6288 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6289 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6290 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6291 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6292 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6293 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6294 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6295 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6296 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6297 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6298 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6299 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6300 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6301 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6302 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6303 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

def row6304 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6305 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6306 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

def row6307 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

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

def row6838 : Integer.Sparse Key := [(key1992, -1), (key1995, 1), (key2002, 1), (key2004, -1), (key2237, 1), (key2260, -1), (key2271, -1), (key2273, -1), (key2295, 2), (key2325, 1), (key2337, -1)]

end MUB6.Certificate.GramRows

end OAI
end


