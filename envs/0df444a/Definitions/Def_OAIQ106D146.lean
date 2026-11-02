-- Prove2me | Definitions.Def_OAIQ106D146
-- name    : OAIQ106D146
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:47:55.602125+00:00
-- url     : https://prove2.me/theorems/4d242c72-bf8b-47bc-a426-b8a37bb237df
-- title:
--   Definitions bundle OAIQ106D146 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 189 declarations of OpenAI's Lean: 189 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.entry10_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entry18_18`, `OAI.MUB6.Certificate.GramFunctions.Block2.terms8`, `OAI.MUB6.Certificate.GramRows.row6308`, `OAI.MUB6.Certificate.GramRows.row6309`, `OAI.MUB6.Certificate.GramRows.row6310`, `OAI.MUB6.Certificate.GramRows.row6311`, `OAI.MUB6.Certificate.GramRows.row6312`, `OAI.MUB6.Certificate.GramRows.row6313`, `OAI.MUB6.Certificate.GramRows.row6314`, `OAI.MUB6.Certificate.GramRows.row6315`, `OAI.MUB6.Certificate.GramRows.row6316`, `OAI.MUB6.Certificate.GramRows.row6317`, `OAI.MUB6.Certificate.GramRows.row6398`, `OAI.MUB6.Certificate.GramRows.row6399`, `OAI.MUB6.Certificate.GramRows.row6400`, `OAI.MUB6.Certificate.GramRows.row6401`, `OAI.MUB6.Certificate.GramRows.row6402`, `OAI.MUB6.Certificate.GramRows.row6403`, `OAI.MUB6.Certificate.GramRows.row6404`, `OAI.MUB6.Certificate.GramRows.row6405`, `OAI.MUB6.Certificate.GramRows.row6406`, `OAI.MUB6.Certificate.GramRows.row6407`, `OAI.MUB6.Certificate.GramRows.row6408`, `OAI.MUB6.Certificate.GramRows.row6409`, `OAI.MUB6.Certificate.GramRows.row6410`, `OAI.MUB6.Certificate.GramRows.row6411`, `OAI.MUB6.Certificate.GramRows.row6412`, `OAI.MUB6.Certificate.GramRows.row6413`, `OAI.MUB6.Certificate.GramRows.row6414`, `OAI.MUB6.Certificate.GramRows.row6415`, `OAI.MUB6.Certificate.GramRows.row6416`, `OAI.MUB6.Certificate.GramRows.row6417`, `OAI.MUB6.Certificate.GramRows.row6418`, `OAI.MUB6.Certificate.GramRows.row6419`, `OAI.MUB6.Certificate.GramRows.row6420`, `OAI.MUB6.Certificate.GramRows.row6421` and 149 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block3Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Data.lean), [`MutuallyUnbiased_GramFunctions_Block2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramFunctions/Block2.lean), [`MutuallyUnbiased_GramRows_Block73`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block73.lean), [`MutuallyUnbiased_GramRows_Block74`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block74.lean), [`MutuallyUnbiased_GramRows_Block75`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block75.lean), [`MutuallyUnbiased_GramRows_Block76`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block76.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D081`, `OAIQ106D083`, `OAIQ106D085`, `OAIQ106D087` and `OAIQ106D090` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D198` and `OAIQ106D199`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D081
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
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

def entry10_8 : Integer.Sparse Key := [(key238, 192), (key250, -192), (key304, 48), (key318, -48), (key387, -96), (key396, 48), (key408, 336), (key417, 192), (key437, -240), (key441, -48), (key449, -192)]

def entry10_9 : Integer.Sparse Key := [(key1309, -192), (key1350, 192), (key1417, -192), (key1471, 192), (key1539, -48), (key1566, -48), (key1615, -240), (key1680, 336), (key1895, 48), (key1902, 48), (key1917, -96)]

def entry11_7 : Integer.Sparse Key := [(key2584, -144), (key2588, -288), (key2599, -288), (key2763, 144), (key2767, 288), (key2888, -288), (key2909, -144), (key2930, 288), (key2967, 288), (key2988, 144)]

def entry11_9 : Integer.Sparse Key := [(key2584, 144), (key2588, -144), (key2763, 144), (key2767, -144), (key2840, 432), (key2875, -432), (key2888, 144), (key2909, -144), (key2967, 144), (key2988, -144)]

def entry18_18 : Integer.Sparse Key := [(key10, 96), (key15, -96), (key93, 144), (key96, -96), (key158, 64), (key163, -192), (key169, 128), (key170, -96), (key189, 144), (key192, -96)]

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

def terms8 : Array TaggedTerm := #[
  ⟨1, ![1, -2, -1, 0, 1, 1], -2⟩,
  ⟨1, ![1, -2, -1, 1, 0, 1], 1⟩,
  ⟨1, ![1, -2, -1, 1, 1, 0], 1⟩,
  ⟨1, ![1, -2, 0, -1, 1, 1], -2⟩,
  ⟨1, ![1, -2, 0, 1, -1, 1], 1⟩,
  ⟨1, ![1, -2, 0, 1, 1, -1], 1⟩,
  ⟨1, ![1, -2, 1, -1, 0, 1], 1⟩,
  ⟨1, ![1, -2, 1, -1, 1, 0], 1⟩,
  ⟨1, ![1, -2, 1, 0, -1, 1], 1⟩,
  ⟨1, ![1, -2, 1, 0, 1, -1], 1⟩,
  ⟨1, ![1, -2, 1, 1, -1, 0], -2⟩,
  ⟨1, ![1, -2, 1, 1, 0, -1], -2⟩,
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
  ⟨1, ![1, 1, -2, 1, -1, 0], 1⟩,
  ⟨1, ![1, 1, -2, 1, 0, -1], 1⟩,
  ⟨1, ![1, 1, -1, -2, 0, 1], -1⟩,
  ⟨1, ![1, 1, -1, -2, 1, 0], -1⟩,
  ⟨1, ![1, 1, -1, 0, -2, 1], 1⟩,
  ⟨1, ![1, 1, -1, 0, 1, -2], 1⟩,
  ⟨1, ![1, 1, 0, -1, -2, 1], 1⟩,
  ⟨1, ![1, 1, 0, -1, 1, -2], 1⟩,
  ⟨1, ![1, 1, 0, 1, -2, -1], -1⟩,
  ⟨1, ![1, 1, 0, 1, -1, -2], -1⟩,
  ⟨1, ![1, 1, 1, -2, -1, 0], 1⟩,
  ⟨1, ![1, 1, 1, -2, 0, -1], 1⟩,
  ⟨1, ![1, 1, 1, 0, -2, -1], -1⟩,
  ⟨1, ![1, 1, 1, 0, -1, -2], -1⟩
]

end MUB6.Certificate.GramFunctions.Block2

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

def row6308 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6309 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

def row6310 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6311 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6312 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6313 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6314 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6315 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

def row6316 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

def row6317 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

def row6398 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6399 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6400 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

def row6401 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6402 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6403 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

def row6404 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

def row6405 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6406 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6407 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

def row6408 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6409 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6410 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6411 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6412 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6413 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6414 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6415 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6416 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6417 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6418 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6419 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6420 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6421 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6422 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6423 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

def row6424 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6425 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6426 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

def row6427 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6428 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6429 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

def row6430 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6431 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6432 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6433 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6434 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6435 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

def row6436 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

def row6437 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

def row6498 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

def row6499 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6500 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6501 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

def row6502 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6503 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6504 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6505 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6506 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6507 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6508 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

def row6509 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

def row6510 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6511 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6512 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6513 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6514 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6515 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6516 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

def row6517 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6538 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

def row6539 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6540 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6541 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

def row6542 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6543 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6544 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6545 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6546 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6547 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6548 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

def row6549 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

def row6550 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6551 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6552 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6553 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6554 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6555 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6556 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6557 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

def row6578 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

def row6579 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6580 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6581 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

def row6582 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6583 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6584 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6585 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6586 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6587 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

def row6588 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

def row6589 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

def row6590 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -3), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 3), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2946, 2), (key2952, -1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6591 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -3), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 3), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2946, 2), (key2952, -1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6592 : Integer.Sparse Key := [(key2643, -2), (key2650, 2), (key2672, 1), (key2675, -1), (key2739, 1), (key2749, -2), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6593 : Integer.Sparse Key := [(key2643, -2), (key2650, 2), (key2672, 1), (key2675, -1), (key2739, 1), (key2749, -2), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6594 : Integer.Sparse Key := [(key2643, -1), (key2650, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2739, 1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6595 : Integer.Sparse Key := [(key2643, -1), (key2650, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2739, 1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6596 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, -1), (key2946, 2), (key2952, 1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6597 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, -1), (key2946, 2), (key2952, 1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6598 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

def row6599 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6600 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6601 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

def row6602 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6603 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6604 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6605 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6606 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6607 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6608 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

def row6609 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

def row6610 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

def row6611 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6612 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6613 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

def row6614 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6615 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6616 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6617 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6618 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6619 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6620 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

def row6621 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

def row6622 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6623 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6624 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6625 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6626 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6627 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6628 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6629 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6630 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6631 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6632 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6633 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6634 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6635 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

def row6636 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

def row6637 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

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

def row6678 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

def row6679 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6680 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6681 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 4), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

def row6682 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6683 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6684 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, 2), (key2650, -4), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6685 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, 2), (key2650, -4), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6686 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -3), (key2650, 1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6687 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -3), (key2650, 1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

def row6688 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

def row6689 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

def row6690 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2945, -2), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

def row6691 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6692 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6693 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -4), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

def row6694 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6695 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6696 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 4), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6697 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 4), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6698 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 3), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, -1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6699 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 3), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, -1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

def row6700 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2945, -2), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

def row6701 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2945, -2), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

def row6702 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 2), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6703 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 2), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6704 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2749, -1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2915, -1), (key2945, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6705 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2749, -1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2915, -1), (key2945, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6706 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6707 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

def row6708 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2739, 2), (key2749, -1), (key2751, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6709 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2739, 2), (key2749, -1), (key2751, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

def row6710 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2749, -1), (key2751, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

end MUB6.Certificate.GramRows

end OAI
end


