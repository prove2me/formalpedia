-- Prove2me | Definitions.Def_OAIQ106D160
-- name    : OAIQ106D160
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:26:42.606251+00:00
-- url     : https://prove2.me/theorems/d10f227f-f424-4e7b-8040-b0a555df73c3
-- title:
--   Definitions bundle OAIQ106D160 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 672 declarations of OpenAI's Lean: 672 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow14244`, `OAI.MUB6.Certificate.GramRows.rawRow14245`, `OAI.MUB6.Certificate.GramRows.rawRow14246`, `OAI.MUB6.Certificate.GramRows.rawRow14247`, `OAI.MUB6.Certificate.GramRows.rawRow14248`, `OAI.MUB6.Certificate.GramRows.rawRow14249`, `OAI.MUB6.Certificate.GramRows.rawRow1425`, `OAI.MUB6.Certificate.GramRows.rawRow14250`, `OAI.MUB6.Certificate.GramRows.rawRow14251`, `OAI.MUB6.Certificate.GramRows.rawRow14252`, `OAI.MUB6.Certificate.GramRows.rawRow14253`, `OAI.MUB6.Certificate.GramRows.rawRow14254`, `OAI.MUB6.Certificate.GramRows.rawRow14255`, `OAI.MUB6.Certificate.GramRows.rawRow14256`, `OAI.MUB6.Certificate.GramRows.rawRow14257`, `OAI.MUB6.Certificate.GramRows.rawRow14258`, `OAI.MUB6.Certificate.GramRows.rawRow14259`, `OAI.MUB6.Certificate.GramRows.rawRow1426`, `OAI.MUB6.Certificate.GramRows.rawRow14260`, `OAI.MUB6.Certificate.GramRows.rawRow14261`, `OAI.MUB6.Certificate.GramRows.rawRow14262`, `OAI.MUB6.Certificate.GramRows.rawRow14263`, `OAI.MUB6.Certificate.GramRows.rawRow14264`, `OAI.MUB6.Certificate.GramRows.rawRow14265`, `OAI.MUB6.Certificate.GramRows.rawRow14266`, `OAI.MUB6.Certificate.GramRows.rawRow14267`, `OAI.MUB6.Certificate.GramRows.rawRow14268`, `OAI.MUB6.Certificate.GramRows.rawRow14269`, `OAI.MUB6.Certificate.GramRows.rawRow1427`, `OAI.MUB6.Certificate.GramRows.rawRow14270`, `OAI.MUB6.Certificate.GramRows.rawRow14271`, `OAI.MUB6.Certificate.GramRows.rawRow14272`, `OAI.MUB6.Certificate.GramRows.rawRow14273`, `OAI.MUB6.Certificate.GramRows.rawRow14274`, `OAI.MUB6.Certificate.GramRows.rawRow14275`, `OAI.MUB6.Certificate.GramRows.rawRow14276`, `OAI.MUB6.Certificate.GramRows.rawRow14277`, `OAI.MUB6.Certificate.GramRows.rawRow14278`, `OAI.MUB6.Certificate.GramRows.rawRow14279`, `OAI.MUB6.Certificate.GramRows.rawRow1428` and 632 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block1.lean), [`MutuallyUnbiased_GramRows_Block135`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block135.lean), [`MutuallyUnbiased_GramRows_Block136`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block136.lean), [`MutuallyUnbiased_GramRows_Block137`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block137.lean), [`MutuallyUnbiased_GramRows_Block138`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block138.lean), [`MutuallyUnbiased_GramRows_Block139`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block139.lean), [`MutuallyUnbiased_GramRows_Block140`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block140.lean), [`MutuallyUnbiased_GramRows_Block35`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block35.lean), [`MutuallyUnbiased_TaoCertificate_Merge22`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge22.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092`, `OAIQ106D094` and `OAIQ106D140` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D200`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094
import Definitions.Def_OAIQ106D140

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow144 : Integer.Sparse Key := [(key1472, -1), (key1480, -1), (key1472, 2), (key1426, 1), (key1444, 1), (key1393, -1), (key1426, -1), (key1420, -2), (key1387, 1), (key1420, 1), (key1903, 1), (key1911, 1), (key1903, -2), (key1575, -1), (key1593, -1), (key1298, 1), (key1575, 1), (key1569, 2), (key1292, -1), (key1569, -1), (key1918, -1), (key1926, -1), (key1896, 1), (key1918, 1), (key1681, 1), (key1689, 1), (key1351, -1), (key1681, -1), (key1542, -1), (key1618, -1), (key1312, 1), (key1618, 1), (key1920, 2), (key1899, -1), (key1920, -1), (key1683, -2), (key1354, 1), (key1683, 1), (key1556, 1), (key1624, 1), (key1326, -1), (key1624, -1)]

def rawRow145 : Integer.Sparse Key := [(key1480, -1), (key1472, -1), (key1472, 2), (key1444, 1), (key1426, 1), (key1426, -1), (key1393, -1), (key1420, -2), (key1420, 1), (key1387, 1), (key1911, 1), (key1903, 1), (key1903, -2), (key1593, -1), (key1575, -1), (key1575, 1), (key1298, 1), (key1569, 2), (key1569, -1), (key1292, -1), (key1926, -1), (key1918, -1), (key1918, 1), (key1896, 1), (key1689, 1), (key1681, 1), (key1681, -1), (key1351, -1), (key1618, -1), (key1542, -1), (key1618, 1), (key1312, 1), (key1920, 2), (key1920, -1), (key1899, -1), (key1683, -2), (key1683, 1), (key1354, 1), (key1624, 1), (key1556, 1), (key1624, -1), (key1326, -1)]

def rawRow146 : Integer.Sparse Key := [(key1542, -1), (key1548, -1), (key1556, 2), (key1569, 1), (key1575, 1), (key1624, -1), (key1683, -1), (key1593, -2), (key1633, 1), (key1689, 1), (key1312, 1), (key1318, 1), (key1326, -2), (key1420, -1), (key1426, -1), (key1624, 1), (key1920, 1), (key1444, 2), (key1633, -1), (key1926, -1), (key1292, -1), (key1298, -1), (key1326, 1), (key1354, 1), (key1387, 1), (key1393, 1), (key1556, -1), (key1899, -1), (key1444, -1), (key1480, -1), (key1593, 1), (key1911, 1), (key1298, 2), (key1318, -1), (key1351, -1), (key1393, -2), (key1548, 1), (key1896, 1), (key1426, 1), (key1472, 1), (key1575, -1), (key1903, -1)]

def rawRow147 : Integer.Sparse Key := [(key1548, -1), (key1542, -1), (key1556, 2), (key1575, 1), (key1569, 1), (key1683, -1), (key1624, -1), (key1593, -2), (key1689, 1), (key1633, 1), (key1318, 1), (key1312, 1), (key1326, -2), (key1426, -1), (key1420, -1), (key1920, 1), (key1624, 1), (key1444, 2), (key1926, -1), (key1633, -1), (key1298, -1), (key1292, -1), (key1354, 1), (key1326, 1), (key1393, 1), (key1387, 1), (key1899, -1), (key1556, -1), (key1480, -1), (key1444, -1), (key1911, 1), (key1593, 1), (key1298, 2), (key1351, -1), (key1318, -1), (key1393, -2), (key1896, 1), (key1548, 1), (key1472, 1), (key1426, 1), (key1903, -1), (key1575, -1)]

def rawRow148 : Integer.Sparse Key := [(key1548, -1), (key1556, -1), (key1542, 2), (key1681, 1), (key1683, 1), (key1569, -1), (key1618, -1), (key1689, -2), (key1593, 1), (key1633, 1), (key1318, 1), (key1326, 1), (key1312, -2), (key1918, -1), (key1920, -1), (key1420, 1), (key1618, 1), (key1926, 2), (key1444, -1), (key1633, -1), (key1351, -1), (key1354, -1), (key1292, 1), (key1312, 1), (key1896, 1), (key1899, 1), (key1387, -1), (key1542, -1), (key1911, -1), (key1926, -1), (key1480, 1), (key1689, 1), (key1351, 2), (key1298, -1), (key1318, -1), (key1896, -2), (key1393, 1), (key1548, 1), (key1903, 1), (key1918, 1), (key1472, -1), (key1681, -1)]

def rawRow149 : Integer.Sparse Key := [(key1556, -1), (key1548, -1), (key1542, 2), (key1683, 1), (key1681, 1), (key1618, -1), (key1569, -1), (key1689, -2), (key1633, 1), (key1593, 1), (key1326, 1), (key1318, 1), (key1312, -2), (key1920, -1), (key1918, -1), (key1618, 1), (key1420, 1), (key1926, 2), (key1633, -1), (key1444, -1), (key1354, -1), (key1351, -1), (key1312, 1), (key1292, 1), (key1899, 1), (key1896, 1), (key1542, -1), (key1387, -1), (key1926, -1), (key1911, -1), (key1689, 1), (key1480, 1), (key1351, 2), (key1318, -1), (key1298, -1), (key1896, -2), (key1548, 1), (key1393, 1), (key1918, 1), (key1903, 1), (key1681, -1), (key1472, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14244 : Integer.Sparse Key := [(key1069, -2), (key1029, -2), (key1034, -2), (key1034, 6), (key1148, -2), (key1107, -2), (key1112, -2), (key1148, 2), (key1107, 2), (key1210, 2), (key994, 2), (key1191, 2), (key999, 2), (key1112, -2), (key1191, -2), (key999, -2), (key1121, 6), (key1121, -2), (key1197, -2), (key1013, -2)]

def rawRow14245 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1029, -2), (key1034, 6), (key1112, -2), (key1148, -2), (key1107, -2), (key1191, 2), (key1210, 2), (key999, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1191, -2), (key999, -2), (key1112, -2), (key1121, 6), (key1197, -2), (key1013, -2), (key1121, -2)]

def rawRow14246 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1029, -2), (key1034, 6), (key1148, -2), (key1112, -2), (key1107, -2), (key1210, 2), (key1191, 2), (key1148, 2), (key999, 2), (key1107, 2), (key994, 2), (key1191, -2), (key1112, -2), (key999, -2), (key1121, 6), (key1197, -2), (key1121, -2), (key1013, -2)]

def rawRow14247 : Integer.Sparse Key := [(key1034, -2), (key1034, -2), (key1069, -2), (key1029, 6), (key1191, -2), (key1191, -2), (key1210, -2), (key999, 2), (key999, 2), (key1112, 2), (key1112, 2), (key1148, 2), (key1148, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1197, 6), (key1013, -2), (key1121, -2), (key1121, -2)]

def rawRow14248 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1034, -2), (key1029, 6), (key1191, -2), (key1210, -2), (key1191, -2), (key1112, 2), (key1148, 2), (key999, 2), (key1148, 2), (key999, 2), (key1112, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1197, 6), (key1121, -2), (key1013, -2), (key1121, -2)]

def rawRow14249 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1034, -2), (key1029, 6), (key1210, -2), (key1191, -2), (key1191, -2), (key1148, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1112, 2), (key999, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1197, 6), (key1121, -2), (key1121, -2), (key1013, -2)]

def rawRow14250 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1148, -2), (key1121, 6), (key1029, -2), (key1034, -2), (key1069, -2), (key994, 2), (key999, 2), (key1107, 2), (key1191, 2), (key1148, 2), (key1210, 2), (key1013, -2), (key1121, -2), (key1197, -2), (key1034, 6), (key999, -2), (key1112, -2), (key1191, -2)]

def rawRow14251 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1148, -2), (key1121, 6), (key1034, -2), (key1029, -2), (key1069, -2), (key999, 2), (key994, 2), (key1191, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key1013, -2), (key1197, -2), (key1121, -2), (key1034, 6), (key999, -2), (key1191, -2), (key1112, -2)]

def rawRow14252 : Integer.Sparse Key := [(key1107, -2), (key1148, -2), (key1112, -2), (key1121, 6), (key1029, -2), (key1069, -2), (key1034, -2), (key1107, 2), (key1148, 2), (key994, 2), (key1210, 2), (key999, 2), (key1191, 2), (key1121, -2), (key1013, -2), (key1197, -2), (key1034, 6), (key1112, -2), (key999, -2), (key1191, -2)]

def rawRow14253 : Integer.Sparse Key := [(key1148, -2), (key1107, -2), (key1112, -2), (key1121, 6), (key1069, -2), (key1029, -2), (key1034, -2), (key1148, 2), (key1107, 2), (key1210, 2), (key994, 2), (key1191, 2), (key999, 2), (key1121, -2), (key1197, -2), (key1013, -2), (key1034, 6), (key1112, -2), (key1191, -2), (key999, -2)]

def rawRow14254 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1107, -2), (key1121, 6), (key1034, -2), (key1069, -2), (key1029, -2), (key1191, 2), (key1210, 2), (key999, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1197, -2), (key1013, -2), (key1121, -2), (key1034, 6), (key1191, -2), (key999, -2), (key1112, -2)]

def rawRow14255 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1107, -2), (key1121, 6), (key1069, -2), (key1034, -2), (key1029, -2), (key1210, 2), (key1191, 2), (key1148, 2), (key999, 2), (key1107, 2), (key994, 2), (key1197, -2), (key1121, -2), (key1013, -2), (key1034, 6), (key1191, -2), (key1112, -2), (key999, -2)]

def rawRow14256 : Integer.Sparse Key := [(key1107, -2), (key1121, -2), (key1148, -2), (key1112, 6), (key1107, -2), (key1121, -2), (key1148, -2), (key994, 2), (key1013, 2), (key1029, 2), (key1197, 2), (key1069, 2), (key1210, 2), (key999, -2), (key1034, -2), (key1191, -2), (key1112, 6), (key999, -2), (key1034, -2), (key1191, -2)]

def rawRow14257 : Integer.Sparse Key := [(key1121, -2), (key1107, -2), (key1148, -2), (key1112, 6), (key1121, -2), (key1107, -2), (key1148, -2), (key1013, 2), (key994, 2), (key1197, 2), (key1029, 2), (key1210, 2), (key1069, 2), (key999, -2), (key1191, -2), (key1034, -2), (key1112, 6), (key999, -2), (key1191, -2), (key1034, -2)]

def rawRow14258 : Integer.Sparse Key := [(key1107, -2), (key1148, -2), (key1121, -2), (key1112, 6), (key1107, -2), (key1148, -2), (key1121, -2), (key1029, 2), (key1069, 2), (key994, 2), (key1210, 2), (key1013, 2), (key1197, 2), (key1034, -2), (key999, -2), (key1191, -2), (key1112, 6), (key1034, -2), (key999, -2), (key1191, -2)]

def rawRow14259 : Integer.Sparse Key := [(key1148, -2), (key1107, -2), (key1121, -2), (key1112, 6), (key1148, -2), (key1107, -2), (key1121, -2), (key1069, 2), (key1029, 2), (key1210, 2), (key994, 2), (key1197, 2), (key1013, 2), (key1034, -2), (key1191, -2), (key999, -2), (key1112, 6), (key1034, -2), (key1191, -2), (key999, -2)]

def rawRow14260 : Integer.Sparse Key := [(key1121, -2), (key1148, -2), (key1107, -2), (key1112, 6), (key1121, -2), (key1148, -2), (key1107, -2), (key1197, 2), (key1210, 2), (key1013, 2), (key1069, 2), (key994, 2), (key1029, 2), (key1191, -2), (key999, -2), (key1034, -2), (key1112, 6), (key1191, -2), (key999, -2), (key1034, -2)]

def rawRow14261 : Integer.Sparse Key := [(key1148, -2), (key1121, -2), (key1107, -2), (key1112, 6), (key1148, -2), (key1121, -2), (key1107, -2), (key1210, 2), (key1197, 2), (key1069, 2), (key1013, 2), (key1029, 2), (key994, 2), (key1191, -2), (key1034, -2), (key999, -2), (key1112, 6), (key1191, -2), (key1034, -2), (key999, -2)]

def rawRow14262 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1148, -2), (key1107, 6), (key1191, -2), (key1197, -2), (key1210, -2), (key999, 2), (key1013, 2), (key1034, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key994, -2), (key1029, -2), (key1107, -2), (key1191, 6), (key999, -2), (key1034, -2), (key1112, -2)]

def rawRow14263 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1148, -2), (key1107, 6), (key1197, -2), (key1191, -2), (key1210, -2), (key1013, 2), (key999, 2), (key1121, 2), (key1034, 2), (key1148, 2), (key1069, 2), (key994, -2), (key1107, -2), (key1029, -2), (key1191, 6), (key999, -2), (key1112, -2), (key1034, -2)]

def rawRow14264 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1121, -2), (key1107, 6), (key1191, -2), (key1210, -2), (key1197, -2), (key1034, 2), (key1069, 2), (key999, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1029, -2), (key994, -2), (key1107, -2), (key1191, 6), (key1034, -2), (key999, -2), (key1112, -2)]

def rawRow14265 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1121, -2), (key1107, 6), (key1210, -2), (key1191, -2), (key1197, -2), (key1069, 2), (key1034, 2), (key1148, 2), (key999, 2), (key1121, 2), (key1013, 2), (key1029, -2), (key1107, -2), (key994, -2), (key1191, 6), (key1034, -2), (key1112, -2), (key999, -2)]

def rawRow14266 : Integer.Sparse Key := [(key1121, -2), (key1148, -2), (key1112, -2), (key1107, 6), (key1197, -2), (key1210, -2), (key1191, -2), (key1121, 2), (key1148, 2), (key1013, 2), (key1069, 2), (key999, 2), (key1034, 2), (key1107, -2), (key994, -2), (key1029, -2), (key1191, 6), (key1112, -2), (key999, -2), (key1034, -2)]

def rawRow14267 : Integer.Sparse Key := [(key1148, -2), (key1121, -2), (key1112, -2), (key1107, 6), (key1210, -2), (key1197, -2), (key1191, -2), (key1148, 2), (key1121, 2), (key1069, 2), (key1013, 2), (key1034, 2), (key999, 2), (key1107, -2), (key1029, -2), (key994, -2), (key1191, 6), (key1112, -2), (key1034, -2), (key999, -2)]

def rawRow14268 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1210, -2), (key1197, 6), (key1034, -2), (key1034, -2), (key1069, -2), (key999, 2), (key999, 2), (key1112, 2), (key1112, 2), (key1148, 2), (key1148, 2), (key1013, -2), (key1121, -2), (key1121, -2), (key1029, 6), (key994, -2), (key1107, -2), (key1107, -2)]

def rawRow14269 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1191, -2), (key1197, 6), (key1034, -2), (key1069, -2), (key1034, -2), (key1112, 2), (key1148, 2), (key999, 2), (key1148, 2), (key999, 2), (key1112, 2), (key1121, -2), (key1013, -2), (key1121, -2), (key1029, 6), (key1107, -2), (key994, -2), (key1107, -2)]

def rawRow14270 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1191, -2), (key1197, 6), (key1069, -2), (key1034, -2), (key1034, -2), (key1148, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1112, 2), (key999, 2), (key1121, -2), (key1121, -2), (key1013, -2), (key1029, 6), (key1107, -2), (key1107, -2), (key994, -2)]

def rawRow14271 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1210, -2), (key1191, 6), (key1112, -2), (key1121, -2), (key1148, -2), (key999, 2), (key1013, 2), (key1034, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key999, -2), (key1034, -2), (key1112, -2), (key1107, 6), (key994, -2), (key1029, -2), (key1107, -2)]

def rawRow14272 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1210, -2), (key1191, 6), (key1121, -2), (key1112, -2), (key1148, -2), (key1013, 2), (key999, 2), (key1121, 2), (key1034, 2), (key1148, 2), (key1069, 2), (key999, -2), (key1112, -2), (key1034, -2), (key1107, 6), (key994, -2), (key1107, -2), (key1029, -2)]

def rawRow14273 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1197, -2), (key1191, 6), (key1112, -2), (key1148, -2), (key1121, -2), (key1034, 2), (key1069, 2), (key999, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1034, -2), (key999, -2), (key1112, -2), (key1107, 6), (key1029, -2), (key994, -2), (key1107, -2)]

def rawRow14274 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1197, -2), (key1191, 6), (key1148, -2), (key1112, -2), (key1121, -2), (key1069, 2), (key1034, 2), (key1148, 2), (key999, 2), (key1121, 2), (key1013, 2), (key1034, -2), (key1112, -2), (key999, -2), (key1107, 6), (key1029, -2), (key1107, -2), (key994, -2)]

def rawRow14275 : Integer.Sparse Key := [(key1197, -2), (key1210, -2), (key1191, -2), (key1191, 6), (key1121, -2), (key1148, -2), (key1112, -2), (key1121, 2), (key1148, 2), (key1013, 2), (key1069, 2), (key999, 2), (key1034, 2), (key1112, -2), (key999, -2), (key1034, -2), (key1107, 6), (key1107, -2), (key994, -2), (key1029, -2)]

def rawRow14276 : Integer.Sparse Key := [(key1210, -2), (key1197, -2), (key1191, -2), (key1191, 6), (key1148, -2), (key1121, -2), (key1112, -2), (key1148, 2), (key1121, 2), (key1069, 2), (key1013, 2), (key1034, 2), (key999, 2), (key1112, -2), (key1034, -2), (key999, -2), (key1107, 6), (key1107, -2), (key1029, -2), (key994, -2)]

def rawRow14277 : Integer.Sparse Key := [(key2399, -2), (key2403, -2), (key2434, -2), (key2403, 6), (key2465, -2), (key2469, -2), (key2500, -2), (key2371, 2), (key2375, 2), (key2465, 2), (key2536, 2), (key2500, 2), (key2552, 2), (key2375, -2), (key2469, -2), (key2536, -2), (key2477, 6), (key2387, -2), (key2477, -2), (key2541, -2)]

def rawRow14278 : Integer.Sparse Key := [(key2403, -2), (key2399, -2), (key2434, -2), (key2403, 6), (key2469, -2), (key2465, -2), (key2500, -2), (key2375, 2), (key2371, 2), (key2536, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2375, -2), (key2536, -2), (key2469, -2), (key2477, 6), (key2387, -2), (key2541, -2), (key2477, -2)]

def rawRow14279 : Integer.Sparse Key := [(key2399, -2), (key2434, -2), (key2403, -2), (key2403, 6), (key2465, -2), (key2500, -2), (key2469, -2), (key2465, 2), (key2500, 2), (key2371, 2), (key2552, 2), (key2375, 2), (key2536, 2), (key2469, -2), (key2375, -2), (key2536, -2), (key2477, 6), (key2477, -2), (key2387, -2), (key2541, -2)]

def rawRow14280 : Integer.Sparse Key := [(key2434, -2), (key2399, -2), (key2403, -2), (key2403, 6), (key2500, -2), (key2465, -2), (key2469, -2), (key2500, 2), (key2465, 2), (key2552, 2), (key2371, 2), (key2536, 2), (key2375, 2), (key2469, -2), (key2536, -2), (key2375, -2), (key2477, 6), (key2477, -2), (key2541, -2), (key2387, -2)]

def rawRow14281 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2399, -2), (key2403, 6), (key2469, -2), (key2500, -2), (key2465, -2), (key2536, 2), (key2552, 2), (key2375, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2536, -2), (key2375, -2), (key2469, -2), (key2477, 6), (key2541, -2), (key2387, -2), (key2477, -2)]

def rawRow14282 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2399, -2), (key2403, 6), (key2500, -2), (key2469, -2), (key2465, -2), (key2552, 2), (key2536, 2), (key2500, 2), (key2375, 2), (key2465, 2), (key2371, 2), (key2536, -2), (key2469, -2), (key2375, -2), (key2477, 6), (key2541, -2), (key2477, -2), (key2387, -2)]

def rawRow14283 : Integer.Sparse Key := [(key2403, -2), (key2403, -2), (key2434, -2), (key2399, 6), (key2536, -2), (key2536, -2), (key2552, -2), (key2375, 2), (key2375, 2), (key2469, 2), (key2469, 2), (key2500, 2), (key2500, 2), (key2371, -2), (key2465, -2), (key2465, -2), (key2541, 6), (key2387, -2), (key2477, -2), (key2477, -2)]

def rawRow14284 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2403, -2), (key2399, 6), (key2536, -2), (key2552, -2), (key2536, -2), (key2469, 2), (key2500, 2), (key2375, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2465, -2), (key2371, -2), (key2465, -2), (key2541, 6), (key2477, -2), (key2387, -2), (key2477, -2)]

def rawRow14285 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2403, -2), (key2399, 6), (key2552, -2), (key2536, -2), (key2536, -2), (key2500, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2375, 2), (key2465, -2), (key2465, -2), (key2371, -2), (key2541, 6), (key2477, -2), (key2477, -2), (key2387, -2)]

def rawRow14286 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2500, -2), (key2477, 6), (key2399, -2), (key2403, -2), (key2434, -2), (key2371, 2), (key2375, 2), (key2465, 2), (key2536, 2), (key2500, 2), (key2552, 2), (key2387, -2), (key2477, -2), (key2541, -2), (key2403, 6), (key2375, -2), (key2469, -2), (key2536, -2)]

def rawRow14287 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2500, -2), (key2477, 6), (key2403, -2), (key2399, -2), (key2434, -2), (key2375, 2), (key2371, 2), (key2536, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2387, -2), (key2541, -2), (key2477, -2), (key2403, 6), (key2375, -2), (key2536, -2), (key2469, -2)]

def rawRow14288 : Integer.Sparse Key := [(key2465, -2), (key2500, -2), (key2469, -2), (key2477, 6), (key2399, -2), (key2434, -2), (key2403, -2), (key2465, 2), (key2500, 2), (key2371, 2), (key2552, 2), (key2375, 2), (key2536, 2), (key2477, -2), (key2387, -2), (key2541, -2), (key2403, 6), (key2469, -2), (key2375, -2), (key2536, -2)]

def rawRow14289 : Integer.Sparse Key := [(key2500, -2), (key2465, -2), (key2469, -2), (key2477, 6), (key2434, -2), (key2399, -2), (key2403, -2), (key2500, 2), (key2465, 2), (key2552, 2), (key2371, 2), (key2536, 2), (key2375, 2), (key2477, -2), (key2541, -2), (key2387, -2), (key2403, 6), (key2469, -2), (key2536, -2), (key2375, -2)]

def rawRow14290 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2465, -2), (key2477, 6), (key2403, -2), (key2434, -2), (key2399, -2), (key2536, 2), (key2552, 2), (key2375, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2541, -2), (key2387, -2), (key2477, -2), (key2403, 6), (key2536, -2), (key2375, -2), (key2469, -2)]

def rawRow14291 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2465, -2), (key2477, 6), (key2434, -2), (key2403, -2), (key2399, -2), (key2552, 2), (key2536, 2), (key2500, 2), (key2375, 2), (key2465, 2), (key2371, 2), (key2541, -2), (key2477, -2), (key2387, -2), (key2403, 6), (key2536, -2), (key2469, -2), (key2375, -2)]

def rawRow14292 : Integer.Sparse Key := [(key2465, -2), (key2477, -2), (key2500, -2), (key2469, 6), (key2465, -2), (key2477, -2), (key2500, -2), (key2371, 2), (key2387, 2), (key2399, 2), (key2541, 2), (key2434, 2), (key2552, 2), (key2375, -2), (key2403, -2), (key2536, -2), (key2469, 6), (key2375, -2), (key2403, -2), (key2536, -2)]

def rawRow14293 : Integer.Sparse Key := [(key2477, -2), (key2465, -2), (key2500, -2), (key2469, 6), (key2477, -2), (key2465, -2), (key2500, -2), (key2387, 2), (key2371, 2), (key2541, 2), (key2399, 2), (key2552, 2), (key2434, 2), (key2375, -2), (key2536, -2), (key2403, -2), (key2469, 6), (key2375, -2), (key2536, -2), (key2403, -2)]

def rawRow14294 : Integer.Sparse Key := [(key2465, -2), (key2500, -2), (key2477, -2), (key2469, 6), (key2465, -2), (key2500, -2), (key2477, -2), (key2399, 2), (key2434, 2), (key2371, 2), (key2552, 2), (key2387, 2), (key2541, 2), (key2403, -2), (key2375, -2), (key2536, -2), (key2469, 6), (key2403, -2), (key2375, -2), (key2536, -2)]

def rawRow14295 : Integer.Sparse Key := [(key2500, -2), (key2465, -2), (key2477, -2), (key2469, 6), (key2500, -2), (key2465, -2), (key2477, -2), (key2434, 2), (key2399, 2), (key2552, 2), (key2371, 2), (key2541, 2), (key2387, 2), (key2403, -2), (key2536, -2), (key2375, -2), (key2469, 6), (key2403, -2), (key2536, -2), (key2375, -2)]

def rawRow14296 : Integer.Sparse Key := [(key2477, -2), (key2500, -2), (key2465, -2), (key2469, 6), (key2477, -2), (key2500, -2), (key2465, -2), (key2541, 2), (key2552, 2), (key2387, 2), (key2434, 2), (key2371, 2), (key2399, 2), (key2536, -2), (key2375, -2), (key2403, -2), (key2469, 6), (key2536, -2), (key2375, -2), (key2403, -2)]

def rawRow14297 : Integer.Sparse Key := [(key2500, -2), (key2477, -2), (key2465, -2), (key2469, 6), (key2500, -2), (key2477, -2), (key2465, -2), (key2552, 2), (key2541, 2), (key2434, 2), (key2387, 2), (key2399, 2), (key2371, 2), (key2536, -2), (key2403, -2), (key2375, -2), (key2469, 6), (key2536, -2), (key2403, -2), (key2375, -2)]

def rawRow14298 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2500, -2), (key2465, 6), (key2536, -2), (key2541, -2), (key2552, -2), (key2375, 2), (key2387, 2), (key2403, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2371, -2), (key2399, -2), (key2465, -2), (key2536, 6), (key2375, -2), (key2403, -2), (key2469, -2)]

def rawRow14299 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2500, -2), (key2465, 6), (key2541, -2), (key2536, -2), (key2552, -2), (key2387, 2), (key2375, 2), (key2477, 2), (key2403, 2), (key2500, 2), (key2434, 2), (key2371, -2), (key2465, -2), (key2399, -2), (key2536, 6), (key2375, -2), (key2469, -2), (key2403, -2)]

def rawRow14300 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2477, -2), (key2465, 6), (key2536, -2), (key2552, -2), (key2541, -2), (key2403, 2), (key2434, 2), (key2375, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2399, -2), (key2371, -2), (key2465, -2), (key2536, 6), (key2403, -2), (key2375, -2), (key2469, -2)]

def rawRow14301 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2477, -2), (key2465, 6), (key2552, -2), (key2536, -2), (key2541, -2), (key2434, 2), (key2403, 2), (key2500, 2), (key2375, 2), (key2477, 2), (key2387, 2), (key2399, -2), (key2465, -2), (key2371, -2), (key2536, 6), (key2403, -2), (key2469, -2), (key2375, -2)]

def rawRow14302 : Integer.Sparse Key := [(key2477, -2), (key2500, -2), (key2469, -2), (key2465, 6), (key2541, -2), (key2552, -2), (key2536, -2), (key2477, 2), (key2500, 2), (key2387, 2), (key2434, 2), (key2375, 2), (key2403, 2), (key2465, -2), (key2371, -2), (key2399, -2), (key2536, 6), (key2469, -2), (key2375, -2), (key2403, -2)]

def rawRow14303 : Integer.Sparse Key := [(key2500, -2), (key2477, -2), (key2469, -2), (key2465, 6), (key2552, -2), (key2541, -2), (key2536, -2), (key2500, 2), (key2477, 2), (key2434, 2), (key2387, 2), (key2403, 2), (key2375, 2), (key2465, -2), (key2399, -2), (key2371, -2), (key2536, 6), (key2469, -2), (key2403, -2), (key2375, -2)]

def rawRow14304 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2552, -2), (key2541, 6), (key2403, -2), (key2403, -2), (key2434, -2), (key2375, 2), (key2375, 2), (key2469, 2), (key2469, 2), (key2500, 2), (key2500, 2), (key2387, -2), (key2477, -2), (key2477, -2), (key2399, 6), (key2371, -2), (key2465, -2), (key2465, -2)]

def rawRow14305 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2536, -2), (key2541, 6), (key2403, -2), (key2434, -2), (key2403, -2), (key2469, 2), (key2500, 2), (key2375, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2477, -2), (key2387, -2), (key2477, -2), (key2399, 6), (key2465, -2), (key2371, -2), (key2465, -2)]

def rawRow14306 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2536, -2), (key2541, 6), (key2434, -2), (key2403, -2), (key2403, -2), (key2500, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2375, 2), (key2477, -2), (key2477, -2), (key2387, -2), (key2399, 6), (key2465, -2), (key2465, -2), (key2371, -2)]

def rawRow14307 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2552, -2), (key2536, 6), (key2469, -2), (key2477, -2), (key2500, -2), (key2375, 2), (key2387, 2), (key2403, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2375, -2), (key2403, -2), (key2469, -2), (key2465, 6), (key2371, -2), (key2399, -2), (key2465, -2)]

def rawRow14308 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2552, -2), (key2536, 6), (key2477, -2), (key2469, -2), (key2500, -2), (key2387, 2), (key2375, 2), (key2477, 2), (key2403, 2), (key2500, 2), (key2434, 2), (key2375, -2), (key2469, -2), (key2403, -2), (key2465, 6), (key2371, -2), (key2465, -2), (key2399, -2)]

def rawRow14309 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2541, -2), (key2536, 6), (key2469, -2), (key2500, -2), (key2477, -2), (key2403, 2), (key2434, 2), (key2375, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2403, -2), (key2375, -2), (key2469, -2), (key2465, 6), (key2399, -2), (key2371, -2), (key2465, -2)]

def rawRow14310 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2541, -2), (key2536, 6), (key2500, -2), (key2469, -2), (key2477, -2), (key2434, 2), (key2403, 2), (key2500, 2), (key2375, 2), (key2477, 2), (key2387, 2), (key2403, -2), (key2469, -2), (key2375, -2), (key2465, 6), (key2399, -2), (key2465, -2), (key2371, -2)]

def rawRow14311 : Integer.Sparse Key := [(key2541, -2), (key2552, -2), (key2536, -2), (key2536, 6), (key2477, -2), (key2500, -2), (key2469, -2), (key2477, 2), (key2500, 2), (key2387, 2), (key2434, 2), (key2375, 2), (key2403, 2), (key2469, -2), (key2375, -2), (key2403, -2), (key2465, 6), (key2465, -2), (key2371, -2), (key2399, -2)]

def rawRow14312 : Integer.Sparse Key := [(key2552, -2), (key2541, -2), (key2536, -2), (key2536, 6), (key2500, -2), (key2477, -2), (key2469, -2), (key2500, 2), (key2477, 2), (key2434, 2), (key2387, 2), (key2403, 2), (key2375, 2), (key2469, -2), (key2403, -2), (key2375, -2), (key2465, 6), (key2465, -2), (key2399, -2), (key2371, -2)]

def rawRow14313 : Integer.Sparse Key := [(key2777, 6), (key2662, -2), (key2777, -2), (key2788, -2), (key2800, 6), (key2607, -2), (key2800, -2), (key2823, -2), (key2697, -2), (key2850, -2), (key2854, -2), (key2623, -2), (key2850, -2), (key2864, -2), (key2623, 2), (key2634, 2), (key2697, 2), (key2720, 2), (key2854, 2), (key2864, 2)]

def rawRow14314 : Integer.Sparse Key := [(key2777, 6), (key2662, -2), (key2788, -2), (key2777, -2), (key2800, 6), (key2607, -2), (key2823, -2), (key2800, -2), (key2697, -2), (key2854, -2), (key2850, -2), (key2623, -2), (key2864, -2), (key2850, -2), (key2634, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2864, 2), (key2854, 2)]

def rawRow14315 : Integer.Sparse Key := [(key2777, 6), (key2777, -2), (key2662, -2), (key2788, -2), (key2800, 6), (key2800, -2), (key2607, -2), (key2823, -2), (key2850, -2), (key2697, -2), (key2854, -2), (key2850, -2), (key2623, -2), (key2864, -2), (key2697, 2), (key2854, 2), (key2623, 2), (key2864, 2), (key2634, 2), (key2720, 2)]

def rawRow14316 : Integer.Sparse Key := [(key2777, 6), (key2777, -2), (key2788, -2), (key2662, -2), (key2800, 6), (key2800, -2), (key2823, -2), (key2607, -2), (key2850, -2), (key2854, -2), (key2697, -2), (key2850, -2), (key2864, -2), (key2623, -2), (key2854, 2), (key2697, 2), (key2864, 2), (key2623, 2), (key2720, 2), (key2634, 2)]

def rawRow14317 : Integer.Sparse Key := [(key2777, 6), (key2788, -2), (key2662, -2), (key2777, -2), (key2800, 6), (key2823, -2), (key2607, -2), (key2800, -2), (key2854, -2), (key2697, -2), (key2850, -2), (key2864, -2), (key2623, -2), (key2850, -2), (key2720, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2623, 2), (key2697, 2)]

def rawRow14318 : Integer.Sparse Key := [(key2777, 6), (key2788, -2), (key2777, -2), (key2662, -2), (key2800, 6), (key2823, -2), (key2800, -2), (key2607, -2), (key2854, -2), (key2850, -2), (key2697, -2), (key2864, -2), (key2850, -2), (key2623, -2), (key2864, 2), (key2720, 2), (key2854, 2), (key2634, 2), (key2697, 2), (key2623, 2)]

def rawRow14319 : Integer.Sparse Key := [(key2788, 6), (key2662, -2), (key2777, -2), (key2777, -2), (key2823, 6), (key2607, -2), (key2800, -2), (key2800, -2), (key2720, -2), (key2864, -2), (key2864, -2), (key2634, -2), (key2854, -2), (key2854, -2), (key2623, 2), (key2623, 2), (key2697, 2), (key2697, 2), (key2850, 2), (key2850, 2)]

def rawRow14320 : Integer.Sparse Key := [(key2788, 6), (key2777, -2), (key2662, -2), (key2777, -2), (key2823, 6), (key2800, -2), (key2607, -2), (key2800, -2), (key2864, -2), (key2720, -2), (key2864, -2), (key2854, -2), (key2634, -2), (key2854, -2), (key2697, 2), (key2850, 2), (key2623, 2), (key2850, 2), (key2623, 2), (key2697, 2)]

def rawRow14321 : Integer.Sparse Key := [(key2788, 6), (key2777, -2), (key2777, -2), (key2662, -2), (key2823, 6), (key2800, -2), (key2800, -2), (key2607, -2), (key2864, -2), (key2864, -2), (key2720, -2), (key2854, -2), (key2854, -2), (key2634, -2), (key2850, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2697, 2), (key2623, 2)]

def rawRow14322 : Integer.Sparse Key := [(key2800, 6), (key2697, -2), (key2850, -2), (key2854, -2), (key2777, 6), (key2623, -2), (key2850, -2), (key2864, -2), (key2662, -2), (key2777, -2), (key2788, -2), (key2607, -2), (key2800, -2), (key2823, -2), (key2623, 2), (key2634, 2), (key2697, 2), (key2720, 2), (key2854, 2), (key2864, 2)]

def rawRow14323 : Integer.Sparse Key := [(key2800, 6), (key2697, -2), (key2854, -2), (key2850, -2), (key2777, 6), (key2623, -2), (key2864, -2), (key2850, -2), (key2662, -2), (key2788, -2), (key2777, -2), (key2607, -2), (key2823, -2), (key2800, -2), (key2634, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2864, 2), (key2854, 2)]

def rawRow14324 : Integer.Sparse Key := [(key2800, 6), (key2850, -2), (key2697, -2), (key2854, -2), (key2777, 6), (key2850, -2), (key2623, -2), (key2864, -2), (key2777, -2), (key2662, -2), (key2788, -2), (key2800, -2), (key2607, -2), (key2823, -2), (key2697, 2), (key2854, 2), (key2623, 2), (key2864, 2), (key2634, 2), (key2720, 2)]

def rawRow14325 : Integer.Sparse Key := [(key2800, 6), (key2850, -2), (key2854, -2), (key2697, -2), (key2777, 6), (key2850, -2), (key2864, -2), (key2623, -2), (key2777, -2), (key2788, -2), (key2662, -2), (key2800, -2), (key2823, -2), (key2607, -2), (key2854, 2), (key2697, 2), (key2864, 2), (key2623, 2), (key2720, 2), (key2634, 2)]

def rawRow14326 : Integer.Sparse Key := [(key2800, 6), (key2854, -2), (key2697, -2), (key2850, -2), (key2777, 6), (key2864, -2), (key2623, -2), (key2850, -2), (key2788, -2), (key2662, -2), (key2777, -2), (key2823, -2), (key2607, -2), (key2800, -2), (key2720, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2623, 2), (key2697, 2)]

def rawRow14327 : Integer.Sparse Key := [(key2800, 6), (key2854, -2), (key2850, -2), (key2697, -2), (key2777, 6), (key2864, -2), (key2850, -2), (key2623, -2), (key2788, -2), (key2777, -2), (key2662, -2), (key2823, -2), (key2800, -2), (key2607, -2), (key2864, 2), (key2720, 2), (key2854, 2), (key2634, 2), (key2697, 2), (key2623, 2)]

def rawRow14328 : Integer.Sparse Key := [(key2850, 6), (key2697, -2), (key2800, -2), (key2854, -2), (key2850, 6), (key2623, -2), (key2777, -2), (key2864, -2), (key2697, -2), (key2800, -2), (key2854, -2), (key2623, -2), (key2777, -2), (key2864, -2), (key2607, 2), (key2634, 2), (key2662, 2), (key2720, 2), (key2788, 2), (key2823, 2)]

def rawRow14329 : Integer.Sparse Key := [(key2850, 6), (key2697, -2), (key2854, -2), (key2800, -2), (key2850, 6), (key2623, -2), (key2864, -2), (key2777, -2), (key2697, -2), (key2854, -2), (key2800, -2), (key2623, -2), (key2864, -2), (key2777, -2), (key2634, 2), (key2607, 2), (key2720, 2), (key2662, 2), (key2823, 2), (key2788, 2)]

def rawRow14330 : Integer.Sparse Key := [(key2850, 6), (key2800, -2), (key2697, -2), (key2854, -2), (key2850, 6), (key2777, -2), (key2623, -2), (key2864, -2), (key2800, -2), (key2697, -2), (key2854, -2), (key2777, -2), (key2623, -2), (key2864, -2), (key2662, 2), (key2788, 2), (key2607, 2), (key2823, 2), (key2634, 2), (key2720, 2)]

def rawRow14331 : Integer.Sparse Key := [(key2850, 6), (key2800, -2), (key2854, -2), (key2697, -2), (key2850, 6), (key2777, -2), (key2864, -2), (key2623, -2), (key2800, -2), (key2854, -2), (key2697, -2), (key2777, -2), (key2864, -2), (key2623, -2), (key2788, 2), (key2662, 2), (key2823, 2), (key2607, 2), (key2720, 2), (key2634, 2)]

def rawRow14332 : Integer.Sparse Key := [(key2850, 6), (key2854, -2), (key2697, -2), (key2800, -2), (key2850, 6), (key2864, -2), (key2623, -2), (key2777, -2), (key2854, -2), (key2697, -2), (key2800, -2), (key2864, -2), (key2623, -2), (key2777, -2), (key2720, 2), (key2823, 2), (key2634, 2), (key2788, 2), (key2607, 2), (key2662, 2)]

def rawRow14333 : Integer.Sparse Key := [(key2850, 6), (key2854, -2), (key2800, -2), (key2697, -2), (key2850, 6), (key2864, -2), (key2777, -2), (key2623, -2), (key2854, -2), (key2800, -2), (key2697, -2), (key2864, -2), (key2777, -2), (key2623, -2), (key2823, 2), (key2720, 2), (key2788, 2), (key2634, 2), (key2662, 2), (key2607, 2)]

def rawRow14334 : Integer.Sparse Key := [(key2854, 6), (key2697, -2), (key2800, -2), (key2850, -2), (key2864, 6), (key2623, -2), (key2777, -2), (key2850, -2), (key2720, -2), (key2823, -2), (key2864, -2), (key2634, -2), (key2788, -2), (key2854, -2), (key2607, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2777, 2), (key2800, 2)]

def rawRow14335 : Integer.Sparse Key := [(key2854, 6), (key2697, -2), (key2850, -2), (key2800, -2), (key2864, 6), (key2623, -2), (key2850, -2), (key2777, -2), (key2720, -2), (key2864, -2), (key2823, -2), (key2634, -2), (key2854, -2), (key2788, -2), (key2623, 2), (key2607, 2), (key2697, 2), (key2662, 2), (key2800, 2), (key2777, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14336 : Integer.Sparse Key := [(key2854, 6), (key2800, -2), (key2697, -2), (key2850, -2), (key2864, 6), (key2777, -2), (key2623, -2), (key2850, -2), (key2823, -2), (key2720, -2), (key2864, -2), (key2788, -2), (key2634, -2), (key2854, -2), (key2662, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2623, 2), (key2697, 2)]

def rawRow14337 : Integer.Sparse Key := [(key2854, 6), (key2800, -2), (key2850, -2), (key2697, -2), (key2864, 6), (key2777, -2), (key2850, -2), (key2623, -2), (key2823, -2), (key2864, -2), (key2720, -2), (key2788, -2), (key2854, -2), (key2634, -2), (key2777, 2), (key2662, 2), (key2800, 2), (key2607, 2), (key2697, 2), (key2623, 2)]

def rawRow14338 : Integer.Sparse Key := [(key2854, 6), (key2850, -2), (key2697, -2), (key2800, -2), (key2864, 6), (key2850, -2), (key2623, -2), (key2777, -2), (key2864, -2), (key2720, -2), (key2823, -2), (key2854, -2), (key2634, -2), (key2788, -2), (key2697, 2), (key2800, 2), (key2623, 2), (key2777, 2), (key2607, 2), (key2662, 2)]

def rawRow14339 : Integer.Sparse Key := [(key2854, 6), (key2850, -2), (key2800, -2), (key2697, -2), (key2864, 6), (key2850, -2), (key2777, -2), (key2623, -2), (key2864, -2), (key2823, -2), (key2720, -2), (key2854, -2), (key2788, -2), (key2634, -2), (key2800, 2), (key2697, 2), (key2777, 2), (key2623, 2), (key2662, 2), (key2607, 2)]

def rawRow14340 : Integer.Sparse Key := [(key2823, 6), (key2720, -2), (key2864, -2), (key2864, -2), (key2788, 6), (key2634, -2), (key2854, -2), (key2854, -2), (key2662, -2), (key2777, -2), (key2777, -2), (key2607, -2), (key2800, -2), (key2800, -2), (key2623, 2), (key2623, 2), (key2697, 2), (key2697, 2), (key2850, 2), (key2850, 2)]

def rawRow14341 : Integer.Sparse Key := [(key2823, 6), (key2864, -2), (key2720, -2), (key2864, -2), (key2788, 6), (key2854, -2), (key2634, -2), (key2854, -2), (key2777, -2), (key2662, -2), (key2777, -2), (key2800, -2), (key2607, -2), (key2800, -2), (key2697, 2), (key2850, 2), (key2623, 2), (key2850, 2), (key2623, 2), (key2697, 2)]

def rawRow14342 : Integer.Sparse Key := [(key2823, 6), (key2864, -2), (key2864, -2), (key2720, -2), (key2788, 6), (key2854, -2), (key2854, -2), (key2634, -2), (key2777, -2), (key2777, -2), (key2662, -2), (key2800, -2), (key2800, -2), (key2607, -2), (key2850, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2697, 2), (key2623, 2)]

def rawRow14343 : Integer.Sparse Key := [(key2864, 6), (key2720, -2), (key2823, -2), (key2864, -2), (key2854, 6), (key2634, -2), (key2788, -2), (key2854, -2), (key2697, -2), (key2800, -2), (key2850, -2), (key2623, -2), (key2777, -2), (key2850, -2), (key2607, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2777, 2), (key2800, 2)]

def rawRow14344 : Integer.Sparse Key := [(key2864, 6), (key2720, -2), (key2864, -2), (key2823, -2), (key2854, 6), (key2634, -2), (key2854, -2), (key2788, -2), (key2697, -2), (key2850, -2), (key2800, -2), (key2623, -2), (key2850, -2), (key2777, -2), (key2623, 2), (key2607, 2), (key2697, 2), (key2662, 2), (key2800, 2), (key2777, 2)]

def rawRow14345 : Integer.Sparse Key := [(key2864, 6), (key2823, -2), (key2720, -2), (key2864, -2), (key2854, 6), (key2788, -2), (key2634, -2), (key2854, -2), (key2800, -2), (key2697, -2), (key2850, -2), (key2777, -2), (key2623, -2), (key2850, -2), (key2662, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2623, 2), (key2697, 2)]

def rawRow14346 : Integer.Sparse Key := [(key2864, 6), (key2823, -2), (key2864, -2), (key2720, -2), (key2854, 6), (key2788, -2), (key2854, -2), (key2634, -2), (key2800, -2), (key2850, -2), (key2697, -2), (key2777, -2), (key2850, -2), (key2623, -2), (key2777, 2), (key2662, 2), (key2800, 2), (key2607, 2), (key2697, 2), (key2623, 2)]

def rawRow14347 : Integer.Sparse Key := [(key2864, 6), (key2864, -2), (key2720, -2), (key2823, -2), (key2854, 6), (key2854, -2), (key2634, -2), (key2788, -2), (key2850, -2), (key2697, -2), (key2800, -2), (key2850, -2), (key2623, -2), (key2777, -2), (key2697, 2), (key2800, 2), (key2623, 2), (key2777, 2), (key2607, 2), (key2662, 2)]

def rawRow14348 : Integer.Sparse Key := [(key2864, 6), (key2864, -2), (key2823, -2), (key2720, -2), (key2854, 6), (key2854, -2), (key2788, -2), (key2634, -2), (key2850, -2), (key2800, -2), (key2697, -2), (key2850, -2), (key2777, -2), (key2623, -2), (key2800, 2), (key2697, 2), (key2777, 2), (key2623, 2), (key2662, 2), (key2607, 2)]

def rawRow14349 : Integer.Sparse Key := [(key1028, -2), (key1032, -2), (key1068, -2), (key1032, 6), (key1106, -2), (key1110, -2), (key1147, -2), (key993, 2), (key997, 2), (key1106, 2), (key1189, 2), (key1147, 2), (key1209, 2), (key997, -2), (key1110, -2), (key1189, -2), (key1120, 6), (key1012, -2), (key1120, -2), (key1196, -2)]

def rawRow14350 : Integer.Sparse Key := [(key1032, -2), (key1028, -2), (key1068, -2), (key1032, 6), (key1110, -2), (key1106, -2), (key1147, -2), (key997, 2), (key993, 2), (key1189, 2), (key1106, 2), (key1209, 2), (key1147, 2), (key997, -2), (key1189, -2), (key1110, -2), (key1120, 6), (key1012, -2), (key1196, -2), (key1120, -2)]

def rawRow14351 : Integer.Sparse Key := [(key1028, -2), (key1068, -2), (key1032, -2), (key1032, 6), (key1106, -2), (key1147, -2), (key1110, -2), (key1106, 2), (key1147, 2), (key993, 2), (key1209, 2), (key997, 2), (key1189, 2), (key1110, -2), (key997, -2), (key1189, -2), (key1120, 6), (key1120, -2), (key1012, -2), (key1196, -2)]

def rawRow14352 : Integer.Sparse Key := [(key1068, -2), (key1028, -2), (key1032, -2), (key1032, 6), (key1147, -2), (key1106, -2), (key1110, -2), (key1147, 2), (key1106, 2), (key1209, 2), (key993, 2), (key1189, 2), (key997, 2), (key1110, -2), (key1189, -2), (key997, -2), (key1120, 6), (key1120, -2), (key1196, -2), (key1012, -2)]

def rawRow14353 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1028, -2), (key1032, 6), (key1110, -2), (key1147, -2), (key1106, -2), (key1189, 2), (key1209, 2), (key997, 2), (key1147, 2), (key993, 2), (key1106, 2), (key1189, -2), (key997, -2), (key1110, -2), (key1120, 6), (key1196, -2), (key1012, -2), (key1120, -2)]

def rawRow14354 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1028, -2), (key1032, 6), (key1147, -2), (key1110, -2), (key1106, -2), (key1209, 2), (key1189, 2), (key1147, 2), (key997, 2), (key1106, 2), (key993, 2), (key1189, -2), (key1110, -2), (key997, -2), (key1120, 6), (key1196, -2), (key1120, -2), (key1012, -2)]

def rawRow14355 : Integer.Sparse Key := [(key1032, -2), (key1032, -2), (key1068, -2), (key1028, 6), (key1189, -2), (key1189, -2), (key1209, -2), (key997, 2), (key997, 2), (key1110, 2), (key1110, 2), (key1147, 2), (key1147, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1196, 6), (key1012, -2), (key1120, -2), (key1120, -2)]

def rawRow14356 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1032, -2), (key1028, 6), (key1189, -2), (key1209, -2), (key1189, -2), (key1110, 2), (key1147, 2), (key997, 2), (key1147, 2), (key997, 2), (key1110, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1196, 6), (key1120, -2), (key1012, -2), (key1120, -2)]

def rawRow14357 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1032, -2), (key1028, 6), (key1209, -2), (key1189, -2), (key1189, -2), (key1147, 2), (key1110, 2), (key1147, 2), (key997, 2), (key1110, 2), (key997, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1196, 6), (key1120, -2), (key1120, -2), (key1012, -2)]

def rawRow14358 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1147, -2), (key1120, 6), (key1028, -2), (key1032, -2), (key1068, -2), (key993, 2), (key997, 2), (key1106, 2), (key1189, 2), (key1147, 2), (key1209, 2), (key1012, -2), (key1120, -2), (key1196, -2), (key1032, 6), (key997, -2), (key1110, -2), (key1189, -2)]

def rawRow14359 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1147, -2), (key1120, 6), (key1032, -2), (key1028, -2), (key1068, -2), (key997, 2), (key993, 2), (key1189, 2), (key1106, 2), (key1209, 2), (key1147, 2), (key1012, -2), (key1196, -2), (key1120, -2), (key1032, 6), (key997, -2), (key1189, -2), (key1110, -2)]

def rawRow14360 : Integer.Sparse Key := [(key1106, -2), (key1147, -2), (key1110, -2), (key1120, 6), (key1028, -2), (key1068, -2), (key1032, -2), (key1106, 2), (key1147, 2), (key993, 2), (key1209, 2), (key997, 2), (key1189, 2), (key1120, -2), (key1012, -2), (key1196, -2), (key1032, 6), (key1110, -2), (key997, -2), (key1189, -2)]

def rawRow14361 : Integer.Sparse Key := [(key1147, -2), (key1106, -2), (key1110, -2), (key1120, 6), (key1068, -2), (key1028, -2), (key1032, -2), (key1147, 2), (key1106, 2), (key1209, 2), (key993, 2), (key1189, 2), (key997, 2), (key1120, -2), (key1196, -2), (key1012, -2), (key1032, 6), (key1110, -2), (key1189, -2), (key997, -2)]

def rawRow14362 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1106, -2), (key1120, 6), (key1032, -2), (key1068, -2), (key1028, -2), (key1189, 2), (key1209, 2), (key997, 2), (key1147, 2), (key993, 2), (key1106, 2), (key1196, -2), (key1012, -2), (key1120, -2), (key1032, 6), (key1189, -2), (key997, -2), (key1110, -2)]

def rawRow14363 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1106, -2), (key1120, 6), (key1068, -2), (key1032, -2), (key1028, -2), (key1209, 2), (key1189, 2), (key1147, 2), (key997, 2), (key1106, 2), (key993, 2), (key1196, -2), (key1120, -2), (key1012, -2), (key1032, 6), (key1189, -2), (key1110, -2), (key997, -2)]

def rawRow14364 : Integer.Sparse Key := [(key1106, -2), (key1120, -2), (key1147, -2), (key1110, 6), (key1106, -2), (key1120, -2), (key1147, -2), (key993, 2), (key1012, 2), (key1028, 2), (key1196, 2), (key1068, 2), (key1209, 2), (key997, -2), (key1032, -2), (key1189, -2), (key1110, 6), (key997, -2), (key1032, -2), (key1189, -2)]

def rawRow14365 : Integer.Sparse Key := [(key1120, -2), (key1106, -2), (key1147, -2), (key1110, 6), (key1120, -2), (key1106, -2), (key1147, -2), (key1012, 2), (key993, 2), (key1196, 2), (key1028, 2), (key1209, 2), (key1068, 2), (key997, -2), (key1189, -2), (key1032, -2), (key1110, 6), (key997, -2), (key1189, -2), (key1032, -2)]

def rawRow14366 : Integer.Sparse Key := [(key1106, -2), (key1147, -2), (key1120, -2), (key1110, 6), (key1106, -2), (key1147, -2), (key1120, -2), (key1028, 2), (key1068, 2), (key993, 2), (key1209, 2), (key1012, 2), (key1196, 2), (key1032, -2), (key997, -2), (key1189, -2), (key1110, 6), (key1032, -2), (key997, -2), (key1189, -2)]

def rawRow14367 : Integer.Sparse Key := [(key1147, -2), (key1106, -2), (key1120, -2), (key1110, 6), (key1147, -2), (key1106, -2), (key1120, -2), (key1068, 2), (key1028, 2), (key1209, 2), (key993, 2), (key1196, 2), (key1012, 2), (key1032, -2), (key1189, -2), (key997, -2), (key1110, 6), (key1032, -2), (key1189, -2), (key997, -2)]

def rawRow14368 : Integer.Sparse Key := [(key1120, -2), (key1147, -2), (key1106, -2), (key1110, 6), (key1120, -2), (key1147, -2), (key1106, -2), (key1196, 2), (key1209, 2), (key1012, 2), (key1068, 2), (key993, 2), (key1028, 2), (key1189, -2), (key997, -2), (key1032, -2), (key1110, 6), (key1189, -2), (key997, -2), (key1032, -2)]

def rawRow14369 : Integer.Sparse Key := [(key1147, -2), (key1120, -2), (key1106, -2), (key1110, 6), (key1147, -2), (key1120, -2), (key1106, -2), (key1209, 2), (key1196, 2), (key1068, 2), (key1012, 2), (key1028, 2), (key993, 2), (key1189, -2), (key1032, -2), (key997, -2), (key1110, 6), (key1189, -2), (key1032, -2), (key997, -2)]

def rawRow14370 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1147, -2), (key1106, 6), (key1189, -2), (key1196, -2), (key1209, -2), (key997, 2), (key1012, 2), (key1032, 2), (key1120, 2), (key1068, 2), (key1147, 2), (key993, -2), (key1028, -2), (key1106, -2), (key1189, 6), (key997, -2), (key1032, -2), (key1110, -2)]

def rawRow14371 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1147, -2), (key1106, 6), (key1196, -2), (key1189, -2), (key1209, -2), (key1012, 2), (key997, 2), (key1120, 2), (key1032, 2), (key1147, 2), (key1068, 2), (key993, -2), (key1106, -2), (key1028, -2), (key1189, 6), (key997, -2), (key1110, -2), (key1032, -2)]

def rawRow14372 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1120, -2), (key1106, 6), (key1189, -2), (key1209, -2), (key1196, -2), (key1032, 2), (key1068, 2), (key997, 2), (key1147, 2), (key1012, 2), (key1120, 2), (key1028, -2), (key993, -2), (key1106, -2), (key1189, 6), (key1032, -2), (key997, -2), (key1110, -2)]

def rawRow14373 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1120, -2), (key1106, 6), (key1209, -2), (key1189, -2), (key1196, -2), (key1068, 2), (key1032, 2), (key1147, 2), (key997, 2), (key1120, 2), (key1012, 2), (key1028, -2), (key1106, -2), (key993, -2), (key1189, 6), (key1032, -2), (key1110, -2), (key997, -2)]

def rawRow14374 : Integer.Sparse Key := [(key1120, -2), (key1147, -2), (key1110, -2), (key1106, 6), (key1196, -2), (key1209, -2), (key1189, -2), (key1120, 2), (key1147, 2), (key1012, 2), (key1068, 2), (key997, 2), (key1032, 2), (key1106, -2), (key993, -2), (key1028, -2), (key1189, 6), (key1110, -2), (key997, -2), (key1032, -2)]

def rawRow14375 : Integer.Sparse Key := [(key1147, -2), (key1120, -2), (key1110, -2), (key1106, 6), (key1209, -2), (key1196, -2), (key1189, -2), (key1147, 2), (key1120, 2), (key1068, 2), (key1012, 2), (key1032, 2), (key997, 2), (key1106, -2), (key1028, -2), (key993, -2), (key1189, 6), (key1110, -2), (key1032, -2), (key997, -2)]

def rawRow14376 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1209, -2), (key1196, 6), (key1032, -2), (key1032, -2), (key1068, -2), (key997, 2), (key997, 2), (key1110, 2), (key1110, 2), (key1147, 2), (key1147, 2), (key1012, -2), (key1120, -2), (key1120, -2), (key1028, 6), (key993, -2), (key1106, -2), (key1106, -2)]

def rawRow14377 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1189, -2), (key1196, 6), (key1032, -2), (key1068, -2), (key1032, -2), (key1110, 2), (key1147, 2), (key997, 2), (key1147, 2), (key997, 2), (key1110, 2), (key1120, -2), (key1012, -2), (key1120, -2), (key1028, 6), (key1106, -2), (key993, -2), (key1106, -2)]

def rawRow14378 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1189, -2), (key1196, 6), (key1068, -2), (key1032, -2), (key1032, -2), (key1147, 2), (key1110, 2), (key1147, 2), (key997, 2), (key1110, 2), (key997, 2), (key1120, -2), (key1120, -2), (key1012, -2), (key1028, 6), (key1106, -2), (key1106, -2), (key993, -2)]

def rawRow14379 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1209, -2), (key1189, 6), (key1110, -2), (key1120, -2), (key1147, -2), (key997, 2), (key1012, 2), (key1032, 2), (key1120, 2), (key1068, 2), (key1147, 2), (key997, -2), (key1032, -2), (key1110, -2), (key1106, 6), (key993, -2), (key1028, -2), (key1106, -2)]

def rawRow14380 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1209, -2), (key1189, 6), (key1120, -2), (key1110, -2), (key1147, -2), (key1012, 2), (key997, 2), (key1120, 2), (key1032, 2), (key1147, 2), (key1068, 2), (key997, -2), (key1110, -2), (key1032, -2), (key1106, 6), (key993, -2), (key1106, -2), (key1028, -2)]

def rawRow14381 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1196, -2), (key1189, 6), (key1110, -2), (key1147, -2), (key1120, -2), (key1032, 2), (key1068, 2), (key997, 2), (key1147, 2), (key1012, 2), (key1120, 2), (key1032, -2), (key997, -2), (key1110, -2), (key1106, 6), (key1028, -2), (key993, -2), (key1106, -2)]

def rawRow14382 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1196, -2), (key1189, 6), (key1147, -2), (key1110, -2), (key1120, -2), (key1068, 2), (key1032, 2), (key1147, 2), (key997, 2), (key1120, 2), (key1012, 2), (key1032, -2), (key1110, -2), (key997, -2), (key1106, 6), (key1028, -2), (key1106, -2), (key993, -2)]

def rawRow14383 : Integer.Sparse Key := [(key1196, -2), (key1209, -2), (key1189, -2), (key1189, 6), (key1120, -2), (key1147, -2), (key1110, -2), (key1120, 2), (key1147, 2), (key1012, 2), (key1068, 2), (key997, 2), (key1032, 2), (key1110, -2), (key997, -2), (key1032, -2), (key1106, 6), (key1106, -2), (key993, -2), (key1028, -2)]

def rawRow14384 : Integer.Sparse Key := [(key1209, -2), (key1196, -2), (key1189, -2), (key1189, 6), (key1147, -2), (key1120, -2), (key1110, -2), (key1147, 2), (key1120, 2), (key1068, 2), (key1012, 2), (key1032, 2), (key997, 2), (key1110, -2), (key1032, -2), (key997, -2), (key1106, 6), (key1106, -2), (key1028, -2), (key993, -2)]

def rawRow14385 : Integer.Sparse Key := [(key1003, 4), (key1152, 4), (key1213, 4), (key1003, -2), (key1007, -2), (key1116, -2), (key1194, -2), (key1156, -2), (key1213, -2), (key1017, -2), (key1020, -2), (key1125, -2), (key1200, -2), (key1172, -2), (key1223, -2), (key1020, 4), (key1128, 4), (key1200, 4)]

def rawRow14386 : Integer.Sparse Key := [(key1003, 4), (key1213, 4), (key1152, 4), (key1007, -2), (key1003, -2), (key1194, -2), (key1116, -2), (key1213, -2), (key1156, -2), (key1020, -2), (key1017, -2), (key1200, -2), (key1125, -2), (key1223, -2), (key1172, -2), (key1020, 4), (key1200, 4), (key1128, 4)]

def rawRow14387 : Integer.Sparse Key := [(key1152, 4), (key1003, 4), (key1213, 4), (key1116, -2), (key1156, -2), (key1003, -2), (key1213, -2), (key1007, -2), (key1194, -2), (key1125, -2), (key1172, -2), (key1017, -2), (key1223, -2), (key1020, -2), (key1200, -2), (key1128, 4), (key1020, 4), (key1200, 4)]

def rawRow14388 : Integer.Sparse Key := [(key1152, 4), (key1213, 4), (key1003, 4), (key1156, -2), (key1116, -2), (key1213, -2), (key1003, -2), (key1194, -2), (key1007, -2), (key1172, -2), (key1125, -2), (key1223, -2), (key1017, -2), (key1200, -2), (key1020, -2), (key1128, 4), (key1200, 4), (key1020, 4)]

def rawRow14389 : Integer.Sparse Key := [(key1213, 4), (key1003, 4), (key1152, 4), (key1194, -2), (key1213, -2), (key1007, -2), (key1156, -2), (key1003, -2), (key1116, -2), (key1200, -2), (key1223, -2), (key1020, -2), (key1172, -2), (key1017, -2), (key1125, -2), (key1200, 4), (key1020, 4), (key1128, 4)]

def rawRow14390 : Integer.Sparse Key := [(key1213, 4), (key1152, 4), (key1003, 4), (key1213, -2), (key1194, -2), (key1156, -2), (key1007, -2), (key1116, -2), (key1003, -2), (key1223, -2), (key1200, -2), (key1172, -2), (key1020, -2), (key1125, -2), (key1017, -2), (key1200, 4), (key1128, 4), (key1020, 4)]

def rawRow14391 : Integer.Sparse Key := [(key1007, 4), (key1156, 4), (key1156, 4), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1020, -2), (key1020, -2), (key1128, -2), (key1128, -2), (key1172, -2), (key1172, -2), (key1017, 4), (key1125, 4), (key1125, 4)]

def rawRow14392 : Integer.Sparse Key := [(key1156, 4), (key1007, 4), (key1156, 4), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1125, 4), (key1017, 4), (key1125, 4)]

def rawRow14393 : Integer.Sparse Key := [(key1156, 4), (key1156, 4), (key1007, 4), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1172, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1020, -2), (key1125, 4), (key1125, 4), (key1017, 4)]

def rawRow14394 : Integer.Sparse Key := [(key1003, 4), (key1152, 4), (key1213, 4), (key1017, -2), (key1020, -2), (key1125, -2), (key1200, -2), (key1172, -2), (key1223, -2), (key1003, -2), (key1007, -2), (key1116, -2), (key1194, -2), (key1156, -2), (key1213, -2), (key1020, 4), (key1128, 4), (key1200, 4)]

def rawRow14395 : Integer.Sparse Key := [(key1003, 4), (key1213, 4), (key1152, 4), (key1020, -2), (key1017, -2), (key1200, -2), (key1125, -2), (key1223, -2), (key1172, -2), (key1007, -2), (key1003, -2), (key1194, -2), (key1116, -2), (key1213, -2), (key1156, -2), (key1020, 4), (key1200, 4), (key1128, 4)]

def rawRow14396 : Integer.Sparse Key := [(key1152, 4), (key1003, 4), (key1213, 4), (key1125, -2), (key1172, -2), (key1017, -2), (key1223, -2), (key1020, -2), (key1200, -2), (key1116, -2), (key1156, -2), (key1003, -2), (key1213, -2), (key1007, -2), (key1194, -2), (key1128, 4), (key1020, 4), (key1200, 4)]

def rawRow14397 : Integer.Sparse Key := [(key1152, 4), (key1213, 4), (key1003, 4), (key1172, -2), (key1125, -2), (key1223, -2), (key1017, -2), (key1200, -2), (key1020, -2), (key1156, -2), (key1116, -2), (key1213, -2), (key1003, -2), (key1194, -2), (key1007, -2), (key1128, 4), (key1200, 4), (key1020, 4)]

def rawRow14398 : Integer.Sparse Key := [(key1213, 4), (key1003, 4), (key1152, 4), (key1200, -2), (key1223, -2), (key1020, -2), (key1172, -2), (key1017, -2), (key1125, -2), (key1194, -2), (key1213, -2), (key1007, -2), (key1156, -2), (key1003, -2), (key1116, -2), (key1200, 4), (key1020, 4), (key1128, 4)]

def rawRow14399 : Integer.Sparse Key := [(key1213, 4), (key1152, 4), (key1003, 4), (key1223, -2), (key1200, -2), (key1172, -2), (key1020, -2), (key1125, -2), (key1017, -2), (key1213, -2), (key1194, -2), (key1156, -2), (key1007, -2), (key1116, -2), (key1003, -2), (key1200, 4), (key1128, 4), (key1020, 4)]

def rawRow14400 : Integer.Sparse Key := [(key1017, 4), (key1073, 4), (key1223, 4), (key1003, -2), (key1020, -2), (key1038, -2), (key1200, -2), (key1077, -2), (key1213, -2), (key1003, -2), (key1020, -2), (key1038, -2), (key1200, -2), (key1077, -2), (key1213, -2), (key1007, 4), (key1042, 4), (key1194, 4)]

def rawRow14401 : Integer.Sparse Key := [(key1017, 4), (key1223, 4), (key1073, 4), (key1020, -2), (key1003, -2), (key1200, -2), (key1038, -2), (key1213, -2), (key1077, -2), (key1020, -2), (key1003, -2), (key1200, -2), (key1038, -2), (key1213, -2), (key1077, -2), (key1007, 4), (key1194, 4), (key1042, 4)]

def rawRow14402 : Integer.Sparse Key := [(key1073, 4), (key1017, 4), (key1223, 4), (key1038, -2), (key1077, -2), (key1003, -2), (key1213, -2), (key1020, -2), (key1200, -2), (key1038, -2), (key1077, -2), (key1003, -2), (key1213, -2), (key1020, -2), (key1200, -2), (key1042, 4), (key1007, 4), (key1194, 4)]

def rawRow14403 : Integer.Sparse Key := [(key1073, 4), (key1223, 4), (key1017, 4), (key1077, -2), (key1038, -2), (key1213, -2), (key1003, -2), (key1200, -2), (key1020, -2), (key1077, -2), (key1038, -2), (key1213, -2), (key1003, -2), (key1200, -2), (key1020, -2), (key1042, 4), (key1194, 4), (key1007, 4)]

def rawRow14404 : Integer.Sparse Key := [(key1223, 4), (key1017, 4), (key1073, 4), (key1200, -2), (key1213, -2), (key1020, -2), (key1077, -2), (key1003, -2), (key1038, -2), (key1200, -2), (key1213, -2), (key1020, -2), (key1077, -2), (key1003, -2), (key1038, -2), (key1194, 4), (key1007, 4), (key1042, 4)]

def rawRow14405 : Integer.Sparse Key := [(key1223, 4), (key1073, 4), (key1017, 4), (key1213, -2), (key1200, -2), (key1077, -2), (key1020, -2), (key1038, -2), (key1003, -2), (key1213, -2), (key1200, -2), (key1077, -2), (key1020, -2), (key1038, -2), (key1003, -2), (key1194, 4), (key1042, 4), (key1007, 4)]

def rawRow14406 : Integer.Sparse Key := [(key1020, 4), (key1077, 4), (key1172, 4), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1007, -2), (key1020, -2), (key1042, -2), (key1128, -2), (key1077, -2), (key1156, -2), (key1003, 4), (key1038, 4), (key1116, 4)]

def rawRow14407 : Integer.Sparse Key := [(key1020, 4), (key1172, 4), (key1077, 4), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1020, -2), (key1007, -2), (key1128, -2), (key1042, -2), (key1156, -2), (key1077, -2), (key1003, 4), (key1116, 4), (key1038, 4)]

def rawRow14408 : Integer.Sparse Key := [(key1077, 4), (key1020, 4), (key1172, 4), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1042, -2), (key1077, -2), (key1007, -2), (key1156, -2), (key1020, -2), (key1128, -2), (key1038, 4), (key1003, 4), (key1116, 4)]

def rawRow14409 : Integer.Sparse Key := [(key1077, 4), (key1172, 4), (key1020, 4), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1077, -2), (key1042, -2), (key1156, -2), (key1007, -2), (key1128, -2), (key1020, -2), (key1038, 4), (key1116, 4), (key1003, 4)]

def rawRow14410 : Integer.Sparse Key := [(key1172, 4), (key1020, 4), (key1077, 4), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1128, -2), (key1156, -2), (key1020, -2), (key1077, -2), (key1007, -2), (key1042, -2), (key1116, 4), (key1003, 4), (key1038, 4)]

def rawRow14411 : Integer.Sparse Key := [(key1172, 4), (key1077, 4), (key1020, 4), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1156, -2), (key1128, -2), (key1077, -2), (key1020, -2), (key1042, -2), (key1007, -2), (key1116, 4), (key1038, 4), (key1003, 4)]

def rawRow14412 : Integer.Sparse Key := [(key1007, 4), (key1156, 4), (key1156, 4), (key1020, -2), (key1020, -2), (key1128, -2), (key1128, -2), (key1172, -2), (key1172, -2), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1017, 4), (key1125, 4), (key1125, 4)]

def rawRow14413 : Integer.Sparse Key := [(key1156, 4), (key1007, 4), (key1156, 4), (key1128, -2), (key1172, -2), (key1020, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1125, 4), (key1017, 4), (key1125, 4)]

def rawRow14414 : Integer.Sparse Key := [(key1156, 4), (key1156, 4), (key1007, 4), (key1172, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1020, -2), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1125, 4), (key1125, 4), (key1017, 4)]

def rawRow14415 : Integer.Sparse Key := [(key1020, 4), (key1077, 4), (key1172, 4), (key1007, -2), (key1020, -2), (key1042, -2), (key1128, -2), (key1077, -2), (key1156, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1003, 4), (key1038, 4), (key1116, 4)]

def rawRow14416 : Integer.Sparse Key := [(key1020, 4), (key1172, 4), (key1077, 4), (key1020, -2), (key1007, -2), (key1128, -2), (key1042, -2), (key1156, -2), (key1077, -2), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1003, 4), (key1116, 4), (key1038, 4)]

def rawRow14417 : Integer.Sparse Key := [(key1077, 4), (key1020, 4), (key1172, 4), (key1042, -2), (key1077, -2), (key1007, -2), (key1156, -2), (key1020, -2), (key1128, -2), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1038, 4), (key1003, 4), (key1116, 4)]

def rawRow14418 : Integer.Sparse Key := [(key1077, 4), (key1172, 4), (key1020, 4), (key1077, -2), (key1042, -2), (key1156, -2), (key1007, -2), (key1128, -2), (key1020, -2), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1038, 4), (key1116, 4), (key1003, 4)]

def rawRow14419 : Integer.Sparse Key := [(key1172, 4), (key1020, 4), (key1077, 4), (key1128, -2), (key1156, -2), (key1020, -2), (key1077, -2), (key1007, -2), (key1042, -2), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1116, 4), (key1003, 4), (key1038, 4)]

def rawRow14420 : Integer.Sparse Key := [(key1172, 4), (key1077, 4), (key1020, 4), (key1156, -2), (key1128, -2), (key1077, -2), (key1020, -2), (key1042, -2), (key1007, -2), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1116, 4), (key1038, 4), (key1003, 4)]

def rawRow14457 : Integer.Sparse Key := [(key2678, 4), (key2812, 4), (key2816, 4), (key2678, -4), (key2687, -4), (key2816, -4), (key2709, -4), (key2713, -4), (key2862, -4), (key2713, 12)]

def rawRow14458 : Integer.Sparse Key := [(key2678, 4), (key2816, 4), (key2812, 4), (key2687, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2709, -4), (key2862, -4), (key2713, 12)]

def rawRow14459 : Integer.Sparse Key := [(key2812, 4), (key2678, 4), (key2816, 4), (key2678, -4), (key2816, -4), (key2687, -4), (key2709, -4), (key2862, -4), (key2713, -4), (key2713, 12)]

def rawRow14460 : Integer.Sparse Key := [(key2812, 4), (key2816, 4), (key2678, 4), (key2816, -4), (key2678, -4), (key2687, -4), (key2862, -4), (key2709, -4), (key2713, -4), (key2713, 12)]

def rawRow14461 : Integer.Sparse Key := [(key2816, 4), (key2678, 4), (key2812, 4), (key2687, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2862, -4), (key2709, -4), (key2713, 12)]

def rawRow14462 : Integer.Sparse Key := [(key2816, 4), (key2812, 4), (key2678, 4), (key2816, -4), (key2687, -4), (key2678, -4), (key2862, -4), (key2713, -4), (key2709, -4), (key2713, 12)]

def rawRow14463 : Integer.Sparse Key := [(key2687, 4), (key2816, 4), (key2816, 4), (key2678, -4), (key2678, -4), (key2812, -4), (key2713, -4), (key2713, -4), (key2862, -4), (key2709, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14464 : Integer.Sparse Key := [(key2816, 4), (key2687, 4), (key2816, 4), (key2678, -4), (key2812, -4), (key2678, -4), (key2713, -4), (key2862, -4), (key2713, -4), (key2709, 12)]

def rawRow14465 : Integer.Sparse Key := [(key2816, 4), (key2816, 4), (key2687, 4), (key2812, -4), (key2678, -4), (key2678, -4), (key2862, -4), (key2713, -4), (key2713, -4), (key2709, 12)]

def rawRow14466 : Integer.Sparse Key := [(key2678, 4), (key2812, 4), (key2816, 4), (key2709, -4), (key2713, -4), (key2862, -4), (key2678, -4), (key2687, -4), (key2816, -4), (key2713, 12)]

def rawRow14467 : Integer.Sparse Key := [(key2678, 4), (key2816, 4), (key2812, 4), (key2713, -4), (key2709, -4), (key2862, -4), (key2687, -4), (key2678, -4), (key2816, -4), (key2713, 12)]

def rawRow14468 : Integer.Sparse Key := [(key2812, 4), (key2678, 4), (key2816, 4), (key2709, -4), (key2862, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2687, -4), (key2713, 12)]

def rawRow14469 : Integer.Sparse Key := [(key2812, 4), (key2816, 4), (key2678, 4), (key2862, -4), (key2709, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2687, -4), (key2713, 12)]

def rawRow14470 : Integer.Sparse Key := [(key2816, 4), (key2678, 4), (key2812, 4), (key2713, -4), (key2862, -4), (key2709, -4), (key2687, -4), (key2816, -4), (key2678, -4), (key2713, 12)]

def rawRow14471 : Integer.Sparse Key := [(key2816, 4), (key2812, 4), (key2678, 4), (key2862, -4), (key2713, -4), (key2709, -4), (key2816, -4), (key2687, -4), (key2678, -4), (key2713, 12)]

def rawRow14472 : Integer.Sparse Key := [(key2709, 4), (key2812, 4), (key2862, 4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2687, 12)]

def rawRow14473 : Integer.Sparse Key := [(key2709, 4), (key2862, 4), (key2812, 4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2687, 12)]

def rawRow14474 : Integer.Sparse Key := [(key2812, 4), (key2709, 4), (key2862, 4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2687, 12)]

def rawRow14475 : Integer.Sparse Key := [(key2812, 4), (key2862, 4), (key2709, 4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2687, 12)]

def rawRow14476 : Integer.Sparse Key := [(key2862, 4), (key2709, 4), (key2812, 4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2687, 12)]

def rawRow14477 : Integer.Sparse Key := [(key2862, 4), (key2812, 4), (key2709, 4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2687, 12)]

def rawRow14478 : Integer.Sparse Key := [(key2713, 4), (key2816, 4), (key2862, 4), (key2678, -4), (key2709, -4), (key2812, -4), (key2687, -4), (key2713, -4), (key2816, -4), (key2678, 12)]

def rawRow14479 : Integer.Sparse Key := [(key2713, 4), (key2862, 4), (key2816, 4), (key2709, -4), (key2678, -4), (key2812, -4), (key2713, -4), (key2687, -4), (key2816, -4), (key2678, 12)]

def rawRow14480 : Integer.Sparse Key := [(key2816, 4), (key2713, 4), (key2862, 4), (key2678, -4), (key2812, -4), (key2709, -4), (key2687, -4), (key2816, -4), (key2713, -4), (key2678, 12)]

def rawRow14481 : Integer.Sparse Key := [(key2816, 4), (key2862, 4), (key2713, 4), (key2812, -4), (key2678, -4), (key2709, -4), (key2816, -4), (key2687, -4), (key2713, -4), (key2678, 12)]

def rawRow14482 : Integer.Sparse Key := [(key2862, 4), (key2713, 4), (key2816, 4), (key2709, -4), (key2812, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2687, -4), (key2678, 12)]

def rawRow14483 : Integer.Sparse Key := [(key2862, 4), (key2816, 4), (key2713, 4), (key2812, -4), (key2709, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2687, -4), (key2678, 12)]

def rawRow14484 : Integer.Sparse Key := [(key2687, 4), (key2816, 4), (key2816, 4), (key2713, -4), (key2713, -4), (key2862, -4), (key2678, -4), (key2678, -4), (key2812, -4), (key2709, 12)]

def rawRow14485 : Integer.Sparse Key := [(key2816, 4), (key2687, 4), (key2816, 4), (key2713, -4), (key2862, -4), (key2713, -4), (key2678, -4), (key2812, -4), (key2678, -4), (key2709, 12)]

def rawRow14486 : Integer.Sparse Key := [(key2816, 4), (key2816, 4), (key2687, 4), (key2862, -4), (key2713, -4), (key2713, -4), (key2812, -4), (key2678, -4), (key2678, -4), (key2709, 12)]

def rawRow14487 : Integer.Sparse Key := [(key2713, 4), (key2816, 4), (key2862, 4), (key2687, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2709, -4), (key2812, -4), (key2678, 12)]

def rawRow14488 : Integer.Sparse Key := [(key2713, 4), (key2862, 4), (key2816, 4), (key2713, -4), (key2687, -4), (key2816, -4), (key2709, -4), (key2678, -4), (key2812, -4), (key2678, 12)]

def rawRow14489 : Integer.Sparse Key := [(key2816, 4), (key2713, 4), (key2862, 4), (key2687, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2812, -4), (key2709, -4), (key2678, 12)]

def rawRow14490 : Integer.Sparse Key := [(key2816, 4), (key2862, 4), (key2713, 4), (key2816, -4), (key2687, -4), (key2713, -4), (key2812, -4), (key2678, -4), (key2709, -4), (key2678, 12)]

def rawRow14491 : Integer.Sparse Key := [(key2862, 4), (key2713, 4), (key2816, 4), (key2713, -4), (key2816, -4), (key2687, -4), (key2709, -4), (key2812, -4), (key2678, -4), (key2678, 12)]

def rawRow14492 : Integer.Sparse Key := [(key2862, 4), (key2816, 4), (key2713, 4), (key2816, -4), (key2713, -4), (key2687, -4), (key2812, -4), (key2709, -4), (key2678, -4), (key2678, 12)]

def rawRow14493 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2401, 6), (key2839, -2), (key2842, -2), (key2965, -2), (key2583, 2), (key2586, 2), (key2839, 2), (key2874, 2), (key2965, 2), (key2987, 2), (key2586, -2), (key2842, -2), (key2874, -2), (key2886, 6), (key2597, -2), (key2886, -2), (key2908, -2)]

def rawRow14494 : Integer.Sparse Key := [(key2401, -2), (key2398, -2), (key2433, -2), (key2401, 6), (key2842, -2), (key2839, -2), (key2965, -2), (key2586, 2), (key2583, 2), (key2874, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2586, -2), (key2874, -2), (key2842, -2), (key2886, 6), (key2597, -2), (key2908, -2), (key2886, -2)]

def rawRow14495 : Integer.Sparse Key := [(key2398, -2), (key2433, -2), (key2401, -2), (key2401, 6), (key2839, -2), (key2965, -2), (key2842, -2), (key2839, 2), (key2965, 2), (key2583, 2), (key2987, 2), (key2586, 2), (key2874, 2), (key2842, -2), (key2586, -2), (key2874, -2), (key2886, 6), (key2886, -2), (key2597, -2), (key2908, -2)]

def rawRow14496 : Integer.Sparse Key := [(key2433, -2), (key2398, -2), (key2401, -2), (key2401, 6), (key2965, -2), (key2839, -2), (key2842, -2), (key2965, 2), (key2839, 2), (key2987, 2), (key2583, 2), (key2874, 2), (key2586, 2), (key2842, -2), (key2874, -2), (key2586, -2), (key2886, 6), (key2886, -2), (key2908, -2), (key2597, -2)]

def rawRow14497 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2398, -2), (key2401, 6), (key2842, -2), (key2965, -2), (key2839, -2), (key2874, 2), (key2987, 2), (key2586, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2874, -2), (key2586, -2), (key2842, -2), (key2886, 6), (key2908, -2), (key2597, -2), (key2886, -2)]

def rawRow14498 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2398, -2), (key2401, 6), (key2965, -2), (key2842, -2), (key2839, -2), (key2987, 2), (key2874, 2), (key2965, 2), (key2586, 2), (key2839, 2), (key2583, 2), (key2874, -2), (key2842, -2), (key2586, -2), (key2886, 6), (key2908, -2), (key2886, -2), (key2597, -2)]

def rawRow14499 : Integer.Sparse Key := [(key2401, -2), (key2401, -2), (key2433, -2), (key2398, 6), (key2874, -2), (key2874, -2), (key2987, -2), (key2586, 2), (key2586, 2), (key2842, 2), (key2842, 2), (key2965, 2), (key2965, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2908, 6), (key2597, -2), (key2886, -2), (key2886, -2)]

def rawRow14500 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2401, -2), (key2398, 6), (key2874, -2), (key2987, -2), (key2874, -2), (key2842, 2), (key2965, 2), (key2586, 2), (key2965, 2), (key2586, 2), (key2842, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2908, 6), (key2886, -2), (key2597, -2), (key2886, -2)]

def rawRow14501 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2401, -2), (key2398, 6), (key2987, -2), (key2874, -2), (key2874, -2), (key2965, 2), (key2842, 2), (key2965, 2), (key2586, 2), (key2842, 2), (key2586, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2908, 6), (key2886, -2), (key2886, -2), (key2597, -2)]

def rawRow14502 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2499, -2), (key2476, 6), (key2398, -2), (key2401, -2), (key2433, -2), (key2583, 2), (key2586, 2), (key2839, 2), (key2874, 2), (key2965, 2), (key2987, 2), (key2597, -2), (key2886, -2), (key2908, -2), (key2765, 6), (key2586, -2), (key2842, -2), (key2874, -2)]

def rawRow14503 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2499, -2), (key2476, 6), (key2401, -2), (key2398, -2), (key2433, -2), (key2586, 2), (key2583, 2), (key2874, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2597, -2), (key2908, -2), (key2886, -2), (key2765, 6), (key2586, -2), (key2874, -2), (key2842, -2)]

def rawRow14504 : Integer.Sparse Key := [(key2464, -2), (key2499, -2), (key2467, -2), (key2476, 6), (key2398, -2), (key2433, -2), (key2401, -2), (key2839, 2), (key2965, 2), (key2583, 2), (key2987, 2), (key2586, 2), (key2874, 2), (key2886, -2), (key2597, -2), (key2908, -2), (key2765, 6), (key2842, -2), (key2586, -2), (key2874, -2)]

def rawRow14505 : Integer.Sparse Key := [(key2499, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2433, -2), (key2398, -2), (key2401, -2), (key2965, 2), (key2839, 2), (key2987, 2), (key2583, 2), (key2874, 2), (key2586, 2), (key2886, -2), (key2908, -2), (key2597, -2), (key2765, 6), (key2842, -2), (key2874, -2), (key2586, -2)]

def rawRow14506 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2464, -2), (key2476, 6), (key2401, -2), (key2433, -2), (key2398, -2), (key2874, 2), (key2987, 2), (key2586, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2908, -2), (key2597, -2), (key2886, -2), (key2765, 6), (key2874, -2), (key2586, -2), (key2842, -2)]

def rawRow14507 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2464, -2), (key2476, 6), (key2433, -2), (key2401, -2), (key2398, -2), (key2987, 2), (key2874, 2), (key2965, 2), (key2586, 2), (key2839, 2), (key2583, 2), (key2908, -2), (key2886, -2), (key2597, -2), (key2765, 6), (key2874, -2), (key2842, -2), (key2586, -2)]

def rawRow14508 : Integer.Sparse Key := [(key2464, -2), (key2476, -2), (key2499, -2), (key2467, 6), (key2464, -2), (key2476, -2), (key2499, -2), (key2370, 2), (key2386, 2), (key2762, 2), (key2908, 2), (key2928, 2), (key2987, 2), (key2586, -2), (key2765, -2), (key2874, -2), (key2842, 6), (key2586, -2), (key2765, -2), (key2874, -2)]

def rawRow14509 : Integer.Sparse Key := [(key2476, -2), (key2464, -2), (key2499, -2), (key2467, 6), (key2476, -2), (key2464, -2), (key2499, -2), (key2386, 2), (key2370, 2), (key2908, 2), (key2762, 2), (key2987, 2), (key2928, 2), (key2586, -2), (key2874, -2), (key2765, -2), (key2842, 6), (key2586, -2), (key2874, -2), (key2765, -2)]

def rawRow14510 : Integer.Sparse Key := [(key2464, -2), (key2499, -2), (key2476, -2), (key2467, 6), (key2464, -2), (key2499, -2), (key2476, -2), (key2398, 2), (key2433, 2), (key2583, 2), (key2987, 2), (key2597, 2), (key2908, 2), (key2765, -2), (key2586, -2), (key2874, -2), (key2842, 6), (key2765, -2), (key2586, -2), (key2874, -2)]

def rawRow14511 : Integer.Sparse Key := [(key2499, -2), (key2464, -2), (key2476, -2), (key2467, 6), (key2499, -2), (key2464, -2), (key2476, -2), (key2433, 2), (key2398, 2), (key2987, 2), (key2583, 2), (key2908, 2), (key2597, 2), (key2765, -2), (key2874, -2), (key2586, -2), (key2842, 6), (key2765, -2), (key2874, -2), (key2586, -2)]

def rawRow14512 : Integer.Sparse Key := [(key2476, -2), (key2499, -2), (key2464, -2), (key2467, 6), (key2476, -2), (key2499, -2), (key2464, -2), (key2540, 2), (key2551, 2), (key2386, 2), (key2433, 2), (key2370, 2), (key2762, 2), (key2874, -2), (key2586, -2), (key2765, -2), (key2842, 6), (key2874, -2), (key2586, -2), (key2765, -2)]

def rawRow14513 : Integer.Sparse Key := [(key2499, -2), (key2476, -2), (key2464, -2), (key2467, 6), (key2499, -2), (key2476, -2), (key2464, -2), (key2551, 2), (key2540, 2), (key2433, 2), (key2386, 2), (key2398, 2), (key2583, 2), (key2874, -2), (key2765, -2), (key2586, -2), (key2842, 6), (key2874, -2), (key2765, -2), (key2586, -2)]

def rawRow14514 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2499, -2), (key2464, 6), (key2534, -2), (key2540, -2), (key2551, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2370, -2), (key2762, -2), (key2839, -2), (key2874, 6), (key2586, -2), (key2765, -2), (key2842, -2)]

def rawRow14515 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2499, -2), (key2464, 6), (key2540, -2), (key2534, -2), (key2551, -2), (key2386, 2), (key2373, 2), (key2476, 2), (key2401, 2), (key2499, 2), (key2433, 2), (key2370, -2), (key2839, -2), (key2762, -2), (key2874, 6), (key2586, -2), (key2842, -2), (key2765, -2)]

def rawRow14516 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2476, -2), (key2464, 6), (key2534, -2), (key2551, -2), (key2540, -2), (key2401, 2), (key2433, 2), (key2373, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2398, -2), (key2583, -2), (key2839, -2), (key2874, 6), (key2765, -2), (key2586, -2), (key2842, -2)]

def rawRow14517 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2476, -2), (key2464, 6), (key2551, -2), (key2534, -2), (key2540, -2), (key2433, 2), (key2401, 2), (key2499, 2), (key2373, 2), (key2476, 2), (key2386, 2), (key2398, -2), (key2839, -2), (key2583, -2), (key2874, 6), (key2765, -2), (key2842, -2), (key2586, -2)]

def rawRow14518 : Integer.Sparse Key := [(key2476, -2), (key2499, -2), (key2467, -2), (key2464, 6), (key2540, -2), (key2551, -2), (key2534, -2), (key2476, 2), (key2499, 2), (key2386, 2), (key2433, 2), (key2373, 2), (key2401, 2), (key2464, -2), (key2370, -2), (key2762, -2), (key2874, 6), (key2842, -2), (key2586, -2), (key2765, -2)]

def rawRow14519 : Integer.Sparse Key := [(key2499, -2), (key2476, -2), (key2467, -2), (key2464, 6), (key2551, -2), (key2540, -2), (key2534, -2), (key2499, 2), (key2476, 2), (key2433, 2), (key2386, 2), (key2401, 2), (key2373, 2), (key2464, -2), (key2398, -2), (key2583, -2), (key2874, 6), (key2842, -2), (key2765, -2), (key2586, -2)]

def rawRow14520 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2551, -2), (key2540, 6), (key2401, -2), (key2401, -2), (key2433, -2), (key2373, 2), (key2373, 2), (key2467, 2), (key2467, 2), (key2499, 2), (key2499, 2), (key2386, -2), (key2476, -2), (key2476, -2), (key2398, 6), (key2583, -2), (key2839, -2), (key2839, -2)]

def rawRow14521 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2534, -2), (key2540, 6), (key2401, -2), (key2433, -2), (key2401, -2), (key2467, 2), (key2499, 2), (key2373, 2), (key2499, 2), (key2373, 2), (key2467, 2), (key2476, -2), (key2386, -2), (key2476, -2), (key2398, 6), (key2839, -2), (key2583, -2), (key2839, -2)]

def rawRow14522 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2534, -2), (key2540, 6), (key2433, -2), (key2401, -2), (key2401, -2), (key2499, 2), (key2467, 2), (key2499, 2), (key2373, 2), (key2467, 2), (key2373, 2), (key2476, -2), (key2476, -2), (key2386, -2), (key2398, 6), (key2839, -2), (key2839, -2), (key2583, -2)]

def rawRow14523 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2551, -2), (key2534, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2373, -2), (key2401, -2), (key2467, -2), (key2464, 6), (key2370, -2), (key2762, -2), (key2839, -2)]

def rawRow14524 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2551, -2), (key2534, 6), (key2476, -2), (key2467, -2), (key2499, -2), (key2386, 2), (key2373, 2), (key2476, 2), (key2401, 2), (key2499, 2), (key2433, 2), (key2373, -2), (key2467, -2), (key2401, -2), (key2464, 6), (key2370, -2), (key2839, -2), (key2762, -2)]

def rawRow14525 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2540, -2), (key2534, 6), (key2467, -2), (key2499, -2), (key2476, -2), (key2401, 2), (key2433, 2), (key2373, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2401, -2), (key2373, -2), (key2467, -2), (key2464, 6), (key2398, -2), (key2583, -2), (key2839, -2)]

def rawRow14526 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2540, -2), (key2534, 6), (key2499, -2), (key2467, -2), (key2476, -2), (key2433, 2), (key2401, 2), (key2499, 2), (key2373, 2), (key2476, 2), (key2386, 2), (key2401, -2), (key2467, -2), (key2373, -2), (key2464, 6), (key2398, -2), (key2839, -2), (key2583, -2)]

def rawRow14527 : Integer.Sparse Key := [(key2540, -2), (key2551, -2), (key2534, -2), (key2534, 6), (key2476, -2), (key2499, -2), (key2467, -2), (key2476, 2), (key2499, 2), (key2386, 2), (key2433, 2), (key2373, 2), (key2401, 2), (key2467, -2), (key2373, -2), (key2401, -2), (key2464, 6), (key2464, -2), (key2370, -2), (key2762, -2)]

def rawRow14528 : Integer.Sparse Key := [(key2551, -2), (key2540, -2), (key2534, -2), (key2534, 6), (key2499, -2), (key2476, -2), (key2467, -2), (key2499, 2), (key2476, 2), (key2433, 2), (key2386, 2), (key2401, 2), (key2373, 2), (key2467, -2), (key2401, -2), (key2373, -2), (key2464, 6), (key2464, -2), (key2398, -2), (key2583, -2)]

def rawRow14529 : Integer.Sparse Key := [(key2011, 4), (key2125, 4), (key2135, 4), (key2011, -4), (key2020, -4), (key2135, -4), (key2040, -4), (key2048, -4), (key2220, -4), (key2048, 12)]

def rawRow14530 : Integer.Sparse Key := [(key2011, 4), (key2135, 4), (key2125, 4), (key2020, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2040, -4), (key2220, -4), (key2048, 12)]

def rawRow14531 : Integer.Sparse Key := [(key2125, 4), (key2011, 4), (key2135, 4), (key2011, -4), (key2135, -4), (key2020, -4), (key2040, -4), (key2220, -4), (key2048, -4), (key2048, 12)]

def rawRow14532 : Integer.Sparse Key := [(key2125, 4), (key2135, 4), (key2011, 4), (key2135, -4), (key2011, -4), (key2020, -4), (key2220, -4), (key2040, -4), (key2048, -4), (key2048, 12)]

def rawRow14533 : Integer.Sparse Key := [(key2135, 4), (key2011, 4), (key2125, 4), (key2020, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2220, -4), (key2040, -4), (key2048, 12)]

def rawRow14534 : Integer.Sparse Key := [(key2135, 4), (key2125, 4), (key2011, 4), (key2135, -4), (key2020, -4), (key2011, -4), (key2220, -4), (key2048, -4), (key2040, -4), (key2048, 12)]

def rawRow14535 : Integer.Sparse Key := [(key2020, 4), (key2135, 4), (key2135, 4), (key2011, -4), (key2011, -4), (key2125, -4), (key2048, -4), (key2048, -4), (key2220, -4), (key2040, 12)]

def rawRow14536 : Integer.Sparse Key := [(key2135, 4), (key2020, 4), (key2135, 4), (key2011, -4), (key2125, -4), (key2011, -4), (key2048, -4), (key2220, -4), (key2048, -4), (key2040, 12)]

def rawRow14537 : Integer.Sparse Key := [(key2135, 4), (key2135, 4), (key2020, 4), (key2125, -4), (key2011, -4), (key2011, -4), (key2220, -4), (key2048, -4), (key2048, -4), (key2040, 12)]

def rawRow14538 : Integer.Sparse Key := [(key2011, 4), (key2125, 4), (key2135, 4), (key2040, -4), (key2048, -4), (key2220, -4), (key2011, -4), (key2020, -4), (key2135, -4), (key2048, 12)]

def rawRow14539 : Integer.Sparse Key := [(key2011, 4), (key2135, 4), (key2125, 4), (key2048, -4), (key2040, -4), (key2220, -4), (key2020, -4), (key2011, -4), (key2135, -4), (key2048, 12)]

def rawRow14540 : Integer.Sparse Key := [(key2125, 4), (key2011, 4), (key2135, 4), (key2040, -4), (key2220, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2020, -4), (key2048, 12)]

def rawRow14541 : Integer.Sparse Key := [(key2125, 4), (key2135, 4), (key2011, 4), (key2220, -4), (key2040, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2020, -4), (key2048, 12)]

def rawRow14542 : Integer.Sparse Key := [(key2135, 4), (key2011, 4), (key2125, 4), (key2048, -4), (key2220, -4), (key2040, -4), (key2020, -4), (key2135, -4), (key2011, -4), (key2048, 12)]

def rawRow14543 : Integer.Sparse Key := [(key2135, 4), (key2125, 4), (key2011, 4), (key2220, -4), (key2048, -4), (key2040, -4), (key2135, -4), (key2020, -4), (key2011, -4), (key2048, 12)]

def rawRow14544 : Integer.Sparse Key := [(key2040, 4), (key2125, 4), (key2220, 4), (key2011, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2020, 12)]

def rawRow14545 : Integer.Sparse Key := [(key2040, 4), (key2220, 4), (key2125, 4), (key2048, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2020, 12)]

def rawRow14546 : Integer.Sparse Key := [(key2125, 4), (key2040, 4), (key2220, 4), (key2011, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2020, 12)]

def rawRow14547 : Integer.Sparse Key := [(key2125, 4), (key2220, 4), (key2040, 4), (key2135, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2020, 12)]

def rawRow14548 : Integer.Sparse Key := [(key2220, 4), (key2040, 4), (key2125, 4), (key2048, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2020, 12)]

def rawRow14549 : Integer.Sparse Key := [(key2220, 4), (key2125, 4), (key2040, 4), (key2135, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2020, 12)]

def rawRow14550 : Integer.Sparse Key := [(key2048, 4), (key2135, 4), (key2220, 4), (key2011, -4), (key2040, -4), (key2125, -4), (key2020, -4), (key2048, -4), (key2135, -4), (key2011, 12)]

def rawRow14551 : Integer.Sparse Key := [(key2048, 4), (key2220, 4), (key2135, 4), (key2040, -4), (key2011, -4), (key2125, -4), (key2048, -4), (key2020, -4), (key2135, -4), (key2011, 12)]

def rawRow14552 : Integer.Sparse Key := [(key2135, 4), (key2048, 4), (key2220, 4), (key2011, -4), (key2125, -4), (key2040, -4), (key2020, -4), (key2135, -4), (key2048, -4), (key2011, 12)]

def rawRow14553 : Integer.Sparse Key := [(key2135, 4), (key2220, 4), (key2048, 4), (key2125, -4), (key2011, -4), (key2040, -4), (key2135, -4), (key2020, -4), (key2048, -4), (key2011, 12)]

def rawRow14554 : Integer.Sparse Key := [(key2220, 4), (key2048, 4), (key2135, 4), (key2040, -4), (key2125, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2020, -4), (key2011, 12)]

def rawRow14555 : Integer.Sparse Key := [(key2220, 4), (key2135, 4), (key2048, 4), (key2125, -4), (key2040, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2020, -4), (key2011, 12)]

def rawRow14556 : Integer.Sparse Key := [(key2020, 4), (key2135, 4), (key2135, 4), (key2048, -4), (key2048, -4), (key2220, -4), (key2011, -4), (key2011, -4), (key2125, -4), (key2040, 12)]

def rawRow14557 : Integer.Sparse Key := [(key2135, 4), (key2020, 4), (key2135, 4), (key2048, -4), (key2220, -4), (key2048, -4), (key2011, -4), (key2125, -4), (key2011, -4), (key2040, 12)]

def rawRow14558 : Integer.Sparse Key := [(key2135, 4), (key2135, 4), (key2020, 4), (key2220, -4), (key2048, -4), (key2048, -4), (key2125, -4), (key2011, -4), (key2011, -4), (key2040, 12)]

def rawRow14559 : Integer.Sparse Key := [(key2048, 4), (key2135, 4), (key2220, 4), (key2020, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2040, -4), (key2125, -4), (key2011, 12)]

def rawRow14560 : Integer.Sparse Key := [(key2048, 4), (key2220, 4), (key2135, 4), (key2048, -4), (key2020, -4), (key2135, -4), (key2040, -4), (key2011, -4), (key2125, -4), (key2011, 12)]

def rawRow14561 : Integer.Sparse Key := [(key2135, 4), (key2048, 4), (key2220, 4), (key2020, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2125, -4), (key2040, -4), (key2011, 12)]

def rawRow14562 : Integer.Sparse Key := [(key2135, 4), (key2220, 4), (key2048, 4), (key2135, -4), (key2020, -4), (key2048, -4), (key2125, -4), (key2011, -4), (key2040, -4), (key2011, 12)]

def rawRow14563 : Integer.Sparse Key := [(key2220, 4), (key2048, 4), (key2135, 4), (key2048, -4), (key2135, -4), (key2020, -4), (key2040, -4), (key2125, -4), (key2011, -4), (key2011, 12)]

def rawRow14564 : Integer.Sparse Key := [(key2220, 4), (key2135, 4), (key2048, 4), (key2135, -4), (key2048, -4), (key2020, -4), (key2125, -4), (key2040, -4), (key2011, -4), (key2011, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14601 : Integer.Sparse Key := [(key1700, 4), (key1700, 4), (key1756, 4), (key1700, -2), (key1706, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1756, -2), (key1851, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1886, -2), (key1855, 4), (key1855, 4), (key1886, 4)]

def rawRow14602 : Integer.Sparse Key := [(key1700, 4), (key1756, 4), (key1700, 4), (key1706, -2), (key1700, -2), (key1756, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1855, 4), (key1886, 4), (key1855, 4)]

def rawRow14603 : Integer.Sparse Key := [(key1756, 4), (key1700, 4), (key1700, 4), (key1756, -2), (key1756, -2), (key1706, -2), (key1706, -2), (key1700, -2), (key1700, -2), (key1886, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1851, -2), (key1886, 4), (key1855, 4), (key1855, 4)]

def rawRow14604 : Integer.Sparse Key := [(key1706, 4), (key1706, 4), (key1706, 4), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow14605 : Integer.Sparse Key := [(key1700, 4), (key1700, 4), (key1756, 4), (key1851, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1886, -2), (key1700, -2), (key1706, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1756, -2), (key1855, 4), (key1855, 4), (key1886, 4)]

def rawRow14606 : Integer.Sparse Key := [(key1700, 4), (key1756, 4), (key1700, 4), (key1855, -2), (key1851, -2), (key1886, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1706, -2), (key1700, -2), (key1756, -2), (key1700, -2), (key1756, -2), (key1706, -2), (key1855, 4), (key1886, 4), (key1855, 4)]

def rawRow14607 : Integer.Sparse Key := [(key1756, 4), (key1700, 4), (key1700, 4), (key1886, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1851, -2), (key1756, -2), (key1756, -2), (key1706, -2), (key1706, -2), (key1700, -2), (key1700, -2), (key1886, 4), (key1855, 4), (key1855, 4)]

def rawRow14608 : Integer.Sparse Key := [(key1277, 4), (key1851, 4), (key1886, 4), (key1277, -2), (key1283, -2), (key1700, -2), (key1756, -2), (key1855, -2), (key1886, -2), (key1277, -2), (key1283, -2), (key1700, -2), (key1756, -2), (key1855, -2), (key1886, -2), (key1283, 4), (key1706, 4), (key1756, 4)]

def rawRow14609 : Integer.Sparse Key := [(key1277, 4), (key1886, 4), (key1851, 4), (key1283, -2), (key1277, -2), (key1756, -2), (key1700, -2), (key1886, -2), (key1855, -2), (key1283, -2), (key1277, -2), (key1756, -2), (key1700, -2), (key1886, -2), (key1855, -2), (key1283, 4), (key1756, 4), (key1706, 4)]

def rawRow14610 : Integer.Sparse Key := [(key1851, 4), (key1277, 4), (key1886, 4), (key1700, -2), (key1855, -2), (key1277, -2), (key1886, -2), (key1283, -2), (key1756, -2), (key1700, -2), (key1855, -2), (key1277, -2), (key1886, -2), (key1283, -2), (key1756, -2), (key1706, 4), (key1283, 4), (key1756, 4)]

def rawRow14611 : Integer.Sparse Key := [(key1851, 4), (key1886, 4), (key1277, 4), (key1855, -2), (key1700, -2), (key1886, -2), (key1277, -2), (key1756, -2), (key1283, -2), (key1855, -2), (key1700, -2), (key1886, -2), (key1277, -2), (key1756, -2), (key1283, -2), (key1706, 4), (key1756, 4), (key1283, 4)]

def rawRow14612 : Integer.Sparse Key := [(key1886, 4), (key1277, 4), (key1851, 4), (key1756, -2), (key1886, -2), (key1283, -2), (key1855, -2), (key1277, -2), (key1700, -2), (key1756, -2), (key1886, -2), (key1283, -2), (key1855, -2), (key1277, -2), (key1700, -2), (key1756, 4), (key1283, 4), (key1706, 4)]

def rawRow14613 : Integer.Sparse Key := [(key1886, 4), (key1851, 4), (key1277, 4), (key1886, -2), (key1756, -2), (key1855, -2), (key1283, -2), (key1700, -2), (key1277, -2), (key1886, -2), (key1756, -2), (key1855, -2), (key1283, -2), (key1700, -2), (key1277, -2), (key1756, 4), (key1706, 4), (key1283, 4)]

def rawRow14614 : Integer.Sparse Key := [(key1283, 4), (key1855, 4), (key1855, 4), (key1277, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1851, -2), (key1283, -2), (key1283, -2), (key1706, -2), (key1706, -2), (key1855, -2), (key1855, -2), (key1277, 4), (key1700, 4), (key1700, 4)]

def rawRow14615 : Integer.Sparse Key := [(key1855, 4), (key1283, 4), (key1855, 4), (key1700, -2), (key1851, -2), (key1277, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1706, -2), (key1855, -2), (key1283, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1700, 4), (key1277, 4), (key1700, 4)]

def rawRow14616 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1283, 4), (key1851, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1277, -2), (key1855, -2), (key1706, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1283, -2), (key1700, 4), (key1700, 4), (key1277, 4)]

def rawRow14617 : Integer.Sparse Key := [(key1706, 4), (key1706, 4), (key1706, 4), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow14618 : Integer.Sparse Key := [(key1283, 4), (key1855, 4), (key1855, 4), (key1283, -2), (key1283, -2), (key1706, -2), (key1706, -2), (key1855, -2), (key1855, -2), (key1277, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1851, -2), (key1277, 4), (key1700, 4), (key1700, 4)]

def rawRow14619 : Integer.Sparse Key := [(key1855, 4), (key1283, 4), (key1855, 4), (key1706, -2), (key1855, -2), (key1283, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1700, 4), (key1277, 4), (key1700, 4)]

def rawRow14620 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1283, 4), (key1855, -2), (key1706, -2), (key1855, -2), (key1283, -2), (key1706, -2), (key1283, -2), (key1851, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1277, -2), (key1700, 4), (key1700, 4), (key1277, 4)]

def rawRow14621 : Integer.Sparse Key := [(key220, -2), (key225, -2), (key225, -2), (key225, 6), (key492, -2), (key497, -2), (key497, -2), (key492, 2), (key497, 2), (key492, 2), (key551, 2), (key497, 2), (key551, 2), (key497, -2), (key497, -2), (key551, -2), (key664, 6), (key664, -2), (key664, -2), (key681, -2)]

def rawRow14622 : Integer.Sparse Key := [(key225, -2), (key220, -2), (key225, -2), (key225, 6), (key497, -2), (key492, -2), (key497, -2), (key497, 2), (key492, 2), (key551, 2), (key492, 2), (key551, 2), (key497, 2), (key497, -2), (key551, -2), (key497, -2), (key664, 6), (key664, -2), (key681, -2), (key664, -2)]

def rawRow14623 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key220, -2), (key225, 6), (key497, -2), (key497, -2), (key492, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key492, 2), (key492, 2), (key551, -2), (key497, -2), (key497, -2), (key664, 6), (key681, -2), (key664, -2), (key664, -2)]

def rawRow14624 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key225, -2), (key220, 6), (key551, -2), (key551, -2), (key551, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key492, -2), (key492, -2), (key492, -2), (key681, 6), (key664, -2), (key664, -2), (key664, -2)]

def rawRow14625 : Integer.Sparse Key := [(key492, -2), (key497, -2), (key497, -2), (key664, 6), (key220, -2), (key225, -2), (key225, -2), (key492, 2), (key497, 2), (key492, 2), (key551, 2), (key497, 2), (key551, 2), (key664, -2), (key664, -2), (key681, -2), (key225, 6), (key497, -2), (key497, -2), (key551, -2)]

def rawRow14626 : Integer.Sparse Key := [(key497, -2), (key492, -2), (key497, -2), (key664, 6), (key225, -2), (key220, -2), (key225, -2), (key497, 2), (key492, 2), (key551, 2), (key492, 2), (key551, 2), (key497, 2), (key664, -2), (key681, -2), (key664, -2), (key225, 6), (key497, -2), (key551, -2), (key497, -2)]

def rawRow14627 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key492, -2), (key664, 6), (key225, -2), (key225, -2), (key220, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key492, 2), (key492, 2), (key681, -2), (key664, -2), (key664, -2), (key225, 6), (key551, -2), (key497, -2), (key497, -2)]

def rawRow14628 : Integer.Sparse Key := [(key492, -2), (key497, -2), (key664, -2), (key497, 6), (key492, -2), (key497, -2), (key664, -2), (key220, 2), (key225, 2), (key492, 2), (key551, 2), (key664, 2), (key681, 2), (key225, -2), (key497, -2), (key551, -2), (key497, 6), (key225, -2), (key497, -2), (key551, -2)]

def rawRow14629 : Integer.Sparse Key := [(key497, -2), (key492, -2), (key664, -2), (key497, 6), (key497, -2), (key492, -2), (key664, -2), (key225, 2), (key220, 2), (key551, 2), (key492, 2), (key681, 2), (key664, 2), (key225, -2), (key551, -2), (key497, -2), (key497, 6), (key225, -2), (key551, -2), (key497, -2)]

def rawRow14630 : Integer.Sparse Key := [(key492, -2), (key664, -2), (key497, -2), (key497, 6), (key492, -2), (key664, -2), (key497, -2), (key492, 2), (key664, 2), (key220, 2), (key681, 2), (key225, 2), (key551, 2), (key497, -2), (key225, -2), (key551, -2), (key497, 6), (key497, -2), (key225, -2), (key551, -2)]

def rawRow14631 : Integer.Sparse Key := [(key664, -2), (key492, -2), (key497, -2), (key497, 6), (key664, -2), (key492, -2), (key497, -2), (key664, 2), (key492, 2), (key681, 2), (key220, 2), (key551, 2), (key225, 2), (key497, -2), (key551, -2), (key225, -2), (key497, 6), (key497, -2), (key551, -2), (key225, -2)]

def rawRow14632 : Integer.Sparse Key := [(key497, -2), (key664, -2), (key492, -2), (key497, 6), (key497, -2), (key664, -2), (key492, -2), (key551, 2), (key681, 2), (key225, 2), (key664, 2), (key220, 2), (key492, 2), (key551, -2), (key225, -2), (key497, -2), (key497, 6), (key551, -2), (key225, -2), (key497, -2)]

def rawRow14633 : Integer.Sparse Key := [(key664, -2), (key497, -2), (key492, -2), (key497, 6), (key664, -2), (key497, -2), (key492, -2), (key681, 2), (key551, 2), (key664, 2), (key225, 2), (key492, 2), (key220, 2), (key551, -2), (key497, -2), (key225, -2), (key497, 6), (key551, -2), (key497, -2), (key225, -2)]

def rawRow14634 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key664, -2), (key492, 6), (key551, -2), (key551, -2), (key681, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key664, 2), (key664, 2), (key220, -2), (key492, -2), (key492, -2), (key551, 6), (key225, -2), (key497, -2), (key497, -2)]

def rawRow14635 : Integer.Sparse Key := [(key497, -2), (key664, -2), (key497, -2), (key492, 6), (key551, -2), (key681, -2), (key551, -2), (key497, 2), (key664, 2), (key225, 2), (key664, 2), (key225, 2), (key497, 2), (key492, -2), (key220, -2), (key492, -2), (key551, 6), (key497, -2), (key225, -2), (key497, -2)]

def rawRow14636 : Integer.Sparse Key := [(key664, -2), (key497, -2), (key497, -2), (key492, 6), (key681, -2), (key551, -2), (key551, -2), (key664, 2), (key497, 2), (key664, 2), (key225, 2), (key497, 2), (key225, 2), (key492, -2), (key492, -2), (key220, -2), (key551, 6), (key497, -2), (key497, -2), (key225, -2)]

def rawRow14637 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key551, -2), (key681, 6), (key225, -2), (key225, -2), (key225, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key664, -2), (key664, -2), (key664, -2), (key220, 6), (key492, -2), (key492, -2), (key492, -2)]

def rawRow14638 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key681, -2), (key551, 6), (key497, -2), (key497, -2), (key664, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key664, 2), (key664, 2), (key225, -2), (key497, -2), (key497, -2), (key492, 6), (key220, -2), (key492, -2), (key492, -2)]

def rawRow14639 : Integer.Sparse Key := [(key551, -2), (key681, -2), (key551, -2), (key551, 6), (key497, -2), (key664, -2), (key497, -2), (key497, 2), (key664, 2), (key225, 2), (key664, 2), (key225, 2), (key497, 2), (key497, -2), (key225, -2), (key497, -2), (key492, 6), (key492, -2), (key220, -2), (key492, -2)]

def rawRow14640 : Integer.Sparse Key := [(key681, -2), (key551, -2), (key551, -2), (key551, 6), (key664, -2), (key497, -2), (key497, -2), (key664, 2), (key497, 2), (key664, 2), (key225, 2), (key497, 2), (key225, 2), (key497, -2), (key497, -2), (key225, -2), (key492, 6), (key492, -2), (key492, -2), (key220, -2)]

def rawRow14641 : Integer.Sparse Key := [(key1273, -2), (key1278, -2), (key1278, -2), (key1278, 6), (key1696, -2), (key1701, -2), (key1701, -2), (key1696, 2), (key1701, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1701, -2), (key1701, -2), (key1751, -2), (key1933, 6), (key1933, -2), (key1933, -2), (key1953, -2)]

def rawRow14642 : Integer.Sparse Key := [(key1278, -2), (key1273, -2), (key1278, -2), (key1278, 6), (key1701, -2), (key1696, -2), (key1701, -2), (key1701, 2), (key1696, 2), (key1751, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1701, -2), (key1751, -2), (key1701, -2), (key1933, 6), (key1933, -2), (key1953, -2), (key1933, -2)]

def rawRow14643 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1273, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1696, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1696, 2), (key1696, 2), (key1751, -2), (key1701, -2), (key1701, -2), (key1933, 6), (key1953, -2), (key1933, -2), (key1933, -2)]

def rawRow14644 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1278, -2), (key1273, 6), (key1751, -2), (key1751, -2), (key1751, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1696, -2), (key1696, -2), (key1696, -2), (key1953, 6), (key1933, -2), (key1933, -2), (key1933, -2)]

def rawRow14645 : Integer.Sparse Key := [(key1696, -2), (key1701, -2), (key1701, -2), (key1933, 6), (key1273, -2), (key1278, -2), (key1278, -2), (key1696, 2), (key1701, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1933, -2), (key1933, -2), (key1953, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1751, -2)]

def rawRow14646 : Integer.Sparse Key := [(key1701, -2), (key1696, -2), (key1701, -2), (key1933, 6), (key1278, -2), (key1273, -2), (key1278, -2), (key1701, 2), (key1696, 2), (key1751, 2), (key1696, 2), (key1751, 2), (key1701, 2), (key1933, -2), (key1953, -2), (key1933, -2), (key1278, 6), (key1701, -2), (key1751, -2), (key1701, -2)]

def rawRow14647 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1696, -2), (key1933, 6), (key1278, -2), (key1278, -2), (key1273, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1696, 2), (key1696, 2), (key1953, -2), (key1933, -2), (key1933, -2), (key1278, 6), (key1751, -2), (key1701, -2), (key1701, -2)]

def rawRow14648 : Integer.Sparse Key := [(key1696, -2), (key1701, -2), (key1933, -2), (key1701, 6), (key1696, -2), (key1701, -2), (key1933, -2), (key1273, 2), (key1278, 2), (key1696, 2), (key1751, 2), (key1933, 2), (key1953, 2), (key1278, -2), (key1701, -2), (key1751, -2), (key1701, 6), (key1278, -2), (key1701, -2), (key1751, -2)]

def rawRow14649 : Integer.Sparse Key := [(key1701, -2), (key1696, -2), (key1933, -2), (key1701, 6), (key1701, -2), (key1696, -2), (key1933, -2), (key1278, 2), (key1273, 2), (key1751, 2), (key1696, 2), (key1953, 2), (key1933, 2), (key1278, -2), (key1751, -2), (key1701, -2), (key1701, 6), (key1278, -2), (key1751, -2), (key1701, -2)]

def rawRow14650 : Integer.Sparse Key := [(key1696, -2), (key1933, -2), (key1701, -2), (key1701, 6), (key1696, -2), (key1933, -2), (key1701, -2), (key1696, 2), (key1933, 2), (key1273, 2), (key1953, 2), (key1278, 2), (key1751, 2), (key1701, -2), (key1278, -2), (key1751, -2), (key1701, 6), (key1701, -2), (key1278, -2), (key1751, -2)]

def rawRow14651 : Integer.Sparse Key := [(key1933, -2), (key1696, -2), (key1701, -2), (key1701, 6), (key1933, -2), (key1696, -2), (key1701, -2), (key1933, 2), (key1696, 2), (key1953, 2), (key1273, 2), (key1751, 2), (key1278, 2), (key1701, -2), (key1751, -2), (key1278, -2), (key1701, 6), (key1701, -2), (key1751, -2), (key1278, -2)]

def rawRow14652 : Integer.Sparse Key := [(key1701, -2), (key1933, -2), (key1696, -2), (key1701, 6), (key1701, -2), (key1933, -2), (key1696, -2), (key1751, 2), (key1953, 2), (key1278, 2), (key1933, 2), (key1273, 2), (key1696, 2), (key1751, -2), (key1278, -2), (key1701, -2), (key1701, 6), (key1751, -2), (key1278, -2), (key1701, -2)]

def rawRow14653 : Integer.Sparse Key := [(key1933, -2), (key1701, -2), (key1696, -2), (key1701, 6), (key1933, -2), (key1701, -2), (key1696, -2), (key1953, 2), (key1751, 2), (key1933, 2), (key1278, 2), (key1696, 2), (key1273, 2), (key1751, -2), (key1701, -2), (key1278, -2), (key1701, 6), (key1751, -2), (key1701, -2), (key1278, -2)]

def rawRow14654 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1933, -2), (key1696, 6), (key1751, -2), (key1751, -2), (key1953, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1933, 2), (key1933, 2), (key1273, -2), (key1696, -2), (key1696, -2), (key1751, 6), (key1278, -2), (key1701, -2), (key1701, -2)]

def rawRow14655 : Integer.Sparse Key := [(key1701, -2), (key1933, -2), (key1701, -2), (key1696, 6), (key1751, -2), (key1953, -2), (key1751, -2), (key1701, 2), (key1933, 2), (key1278, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1696, -2), (key1273, -2), (key1696, -2), (key1751, 6), (key1701, -2), (key1278, -2), (key1701, -2)]

def rawRow14656 : Integer.Sparse Key := [(key1933, -2), (key1701, -2), (key1701, -2), (key1696, 6), (key1953, -2), (key1751, -2), (key1751, -2), (key1933, 2), (key1701, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1696, -2), (key1696, -2), (key1273, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1278, -2)]

def rawRow14657 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1751, -2), (key1953, 6), (key1278, -2), (key1278, -2), (key1278, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1933, -2), (key1933, -2), (key1933, -2), (key1273, 6), (key1696, -2), (key1696, -2), (key1696, -2)]

def rawRow14658 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1953, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1933, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1933, 2), (key1933, 2), (key1278, -2), (key1701, -2), (key1701, -2), (key1696, 6), (key1273, -2), (key1696, -2), (key1696, -2)]

def rawRow14659 : Integer.Sparse Key := [(key1751, -2), (key1953, -2), (key1751, -2), (key1751, 6), (key1701, -2), (key1933, -2), (key1701, -2), (key1701, 2), (key1933, 2), (key1278, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1701, -2), (key1278, -2), (key1701, -2), (key1696, 6), (key1696, -2), (key1273, -2), (key1696, -2)]

def rawRow14660 : Integer.Sparse Key := [(key1953, -2), (key1751, -2), (key1751, -2), (key1751, 6), (key1933, -2), (key1701, -2), (key1701, -2), (key1933, 2), (key1701, 2), (key1933, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1701, -2), (key1701, -2), (key1278, -2), (key1696, 6), (key1696, -2), (key1696, -2), (key1273, -2)]

def rawRow14661 : Integer.Sparse Key := [(key1360, 6), (key1360, -2), (key1360, -2), (key1372, -2), (key1486, 6), (key1486, -2), (key1486, -2), (key1511, -2), (key1712, -2), (key1712, -2), (key1721, -2), (key1712, -2), (key1712, -2), (key1739, -2), (key1712, 2), (key1721, 2), (key1712, 2), (key1739, 2), (key1721, 2), (key1739, 2)]

def rawRow14662 : Integer.Sparse Key := [(key1360, 6), (key1360, -2), (key1372, -2), (key1360, -2), (key1486, 6), (key1486, -2), (key1511, -2), (key1486, -2), (key1712, -2), (key1721, -2), (key1712, -2), (key1712, -2), (key1739, -2), (key1712, -2), (key1721, 2), (key1712, 2), (key1739, 2), (key1712, 2), (key1739, 2), (key1721, 2)]

def rawRow14663 : Integer.Sparse Key := [(key1360, 6), (key1372, -2), (key1360, -2), (key1360, -2), (key1486, 6), (key1511, -2), (key1486, -2), (key1486, -2), (key1721, -2), (key1712, -2), (key1712, -2), (key1739, -2), (key1712, -2), (key1712, -2), (key1739, 2), (key1739, 2), (key1721, 2), (key1721, 2), (key1712, 2), (key1712, 2)]

def rawRow14664 : Integer.Sparse Key := [(key1372, 6), (key1360, -2), (key1360, -2), (key1360, -2), (key1511, 6), (key1486, -2), (key1486, -2), (key1486, -2), (key1739, -2), (key1739, -2), (key1739, -2), (key1721, -2), (key1721, -2), (key1721, -2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2)]

def rawRow14665 : Integer.Sparse Key := [(key1486, 6), (key1712, -2), (key1712, -2), (key1721, -2), (key1360, 6), (key1712, -2), (key1712, -2), (key1739, -2), (key1360, -2), (key1360, -2), (key1372, -2), (key1486, -2), (key1486, -2), (key1511, -2), (key1712, 2), (key1721, 2), (key1712, 2), (key1739, 2), (key1721, 2), (key1739, 2)]

def rawRow14666 : Integer.Sparse Key := [(key1486, 6), (key1712, -2), (key1721, -2), (key1712, -2), (key1360, 6), (key1712, -2), (key1739, -2), (key1712, -2), (key1360, -2), (key1372, -2), (key1360, -2), (key1486, -2), (key1511, -2), (key1486, -2), (key1721, 2), (key1712, 2), (key1739, 2), (key1712, 2), (key1739, 2), (key1721, 2)]

def rawRow14667 : Integer.Sparse Key := [(key1486, 6), (key1721, -2), (key1712, -2), (key1712, -2), (key1360, 6), (key1739, -2), (key1712, -2), (key1712, -2), (key1372, -2), (key1360, -2), (key1360, -2), (key1511, -2), (key1486, -2), (key1486, -2), (key1739, 2), (key1739, 2), (key1721, 2), (key1721, 2), (key1712, 2), (key1712, 2)]

def rawRow14668 : Integer.Sparse Key := [(key1712, 6), (key1486, -2), (key1712, -2), (key1721, -2), (key1712, 6), (key1360, -2), (key1712, -2), (key1739, -2), (key1486, -2), (key1712, -2), (key1721, -2), (key1360, -2), (key1712, -2), (key1739, -2), (key1360, 2), (key1372, 2), (key1486, 2), (key1511, 2), (key1721, 2), (key1739, 2)]

def rawRow14669 : Integer.Sparse Key := [(key1712, 6), (key1486, -2), (key1721, -2), (key1712, -2), (key1712, 6), (key1360, -2), (key1739, -2), (key1712, -2), (key1486, -2), (key1721, -2), (key1712, -2), (key1360, -2), (key1739, -2), (key1712, -2), (key1372, 2), (key1360, 2), (key1511, 2), (key1486, 2), (key1739, 2), (key1721, 2)]

def rawRow14670 : Integer.Sparse Key := [(key1712, 6), (key1712, -2), (key1486, -2), (key1721, -2), (key1712, 6), (key1712, -2), (key1360, -2), (key1739, -2), (key1712, -2), (key1486, -2), (key1721, -2), (key1712, -2), (key1360, -2), (key1739, -2), (key1486, 2), (key1721, 2), (key1360, 2), (key1739, 2), (key1372, 2), (key1511, 2)]

def rawRow14671 : Integer.Sparse Key := [(key1712, 6), (key1712, -2), (key1721, -2), (key1486, -2), (key1712, 6), (key1712, -2), (key1739, -2), (key1360, -2), (key1712, -2), (key1721, -2), (key1486, -2), (key1712, -2), (key1739, -2), (key1360, -2), (key1721, 2), (key1486, 2), (key1739, 2), (key1360, 2), (key1511, 2), (key1372, 2)]

def rawRow14672 : Integer.Sparse Key := [(key1712, 6), (key1721, -2), (key1486, -2), (key1712, -2), (key1712, 6), (key1739, -2), (key1360, -2), (key1712, -2), (key1721, -2), (key1486, -2), (key1712, -2), (key1739, -2), (key1360, -2), (key1712, -2), (key1511, 2), (key1739, 2), (key1372, 2), (key1721, 2), (key1360, 2), (key1486, 2)]

def rawRow14673 : Integer.Sparse Key := [(key1712, 6), (key1721, -2), (key1712, -2), (key1486, -2), (key1712, 6), (key1739, -2), (key1712, -2), (key1360, -2), (key1721, -2), (key1712, -2), (key1486, -2), (key1739, -2), (key1712, -2), (key1360, -2), (key1739, 2), (key1511, 2), (key1721, 2), (key1372, 2), (key1486, 2), (key1360, 2)]

def rawRow14674 : Integer.Sparse Key := [(key1721, 6), (key1486, -2), (key1712, -2), (key1712, -2), (key1739, 6), (key1360, -2), (key1712, -2), (key1712, -2), (key1511, -2), (key1739, -2), (key1739, -2), (key1372, -2), (key1721, -2), (key1721, -2), (key1360, 2), (key1360, 2), (key1486, 2), (key1486, 2), (key1712, 2), (key1712, 2)]

def rawRow14675 : Integer.Sparse Key := [(key1721, 6), (key1712, -2), (key1486, -2), (key1712, -2), (key1739, 6), (key1712, -2), (key1360, -2), (key1712, -2), (key1739, -2), (key1511, -2), (key1739, -2), (key1721, -2), (key1372, -2), (key1721, -2), (key1486, 2), (key1712, 2), (key1360, 2), (key1712, 2), (key1360, 2), (key1486, 2)]

def rawRow14676 : Integer.Sparse Key := [(key1721, 6), (key1712, -2), (key1712, -2), (key1486, -2), (key1739, 6), (key1712, -2), (key1712, -2), (key1360, -2), (key1739, -2), (key1739, -2), (key1511, -2), (key1721, -2), (key1721, -2), (key1372, -2), (key1712, 2), (key1486, 2), (key1712, 2), (key1360, 2), (key1486, 2), (key1360, 2)]

def rawRow14677 : Integer.Sparse Key := [(key1511, 6), (key1739, -2), (key1739, -2), (key1739, -2), (key1372, 6), (key1721, -2), (key1721, -2), (key1721, -2), (key1360, -2), (key1360, -2), (key1360, -2), (key1486, -2), (key1486, -2), (key1486, -2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2), (key1712, 2)]

def rawRow14678 : Integer.Sparse Key := [(key1739, 6), (key1511, -2), (key1739, -2), (key1739, -2), (key1721, 6), (key1372, -2), (key1721, -2), (key1721, -2), (key1486, -2), (key1712, -2), (key1712, -2), (key1360, -2), (key1712, -2), (key1712, -2), (key1360, 2), (key1360, 2), (key1486, 2), (key1486, 2), (key1712, 2), (key1712, 2)]

def rawRow14679 : Integer.Sparse Key := [(key1739, 6), (key1739, -2), (key1511, -2), (key1739, -2), (key1721, 6), (key1721, -2), (key1372, -2), (key1721, -2), (key1712, -2), (key1486, -2), (key1712, -2), (key1712, -2), (key1360, -2), (key1712, -2), (key1486, 2), (key1712, 2), (key1360, 2), (key1712, 2), (key1360, 2), (key1486, 2)]

def rawRow14680 : Integer.Sparse Key := [(key1739, 6), (key1739, -2), (key1739, -2), (key1511, -2), (key1721, 6), (key1721, -2), (key1721, -2), (key1372, -2), (key1712, -2), (key1712, -2), (key1486, -2), (key1712, -2), (key1712, -2), (key1360, -2), (key1712, 2), (key1486, 2), (key1712, 2), (key1360, 2), (key1486, 2), (key1360, 2)]

def rawRow14681 : Integer.Sparse Key := [(key221, -2), (key225, -2), (key225, -2), (key225, 6), (key493, -2), (key497, -2), (key497, -2), (key493, 2), (key497, 2), (key493, 2), (key551, 2), (key497, 2), (key551, 2), (key497, -2), (key497, -2), (key551, -2), (key619, 6), (key619, -2), (key619, -2), (key645, -2)]

def rawRow14682 : Integer.Sparse Key := [(key225, -2), (key221, -2), (key225, -2), (key225, 6), (key497, -2), (key493, -2), (key497, -2), (key497, 2), (key493, 2), (key551, 2), (key493, 2), (key551, 2), (key497, 2), (key497, -2), (key551, -2), (key497, -2), (key619, 6), (key619, -2), (key645, -2), (key619, -2)]

def rawRow14683 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key221, -2), (key225, 6), (key497, -2), (key497, -2), (key493, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key493, 2), (key493, 2), (key551, -2), (key497, -2), (key497, -2), (key619, 6), (key645, -2), (key619, -2), (key619, -2)]

def rawRow14684 : Integer.Sparse Key := [(key225, -2), (key225, -2), (key225, -2), (key221, 6), (key551, -2), (key551, -2), (key551, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key493, -2), (key493, -2), (key493, -2), (key645, 6), (key619, -2), (key619, -2), (key619, -2)]

def rawRow14685 : Integer.Sparse Key := [(key493, -2), (key497, -2), (key497, -2), (key619, 6), (key221, -2), (key225, -2), (key225, -2), (key493, 2), (key497, 2), (key493, 2), (key551, 2), (key497, 2), (key551, 2), (key619, -2), (key619, -2), (key645, -2), (key225, 6), (key497, -2), (key497, -2), (key551, -2)]

def rawRow14686 : Integer.Sparse Key := [(key497, -2), (key493, -2), (key497, -2), (key619, 6), (key225, -2), (key221, -2), (key225, -2), (key497, 2), (key493, 2), (key551, 2), (key493, 2), (key551, 2), (key497, 2), (key619, -2), (key645, -2), (key619, -2), (key225, 6), (key497, -2), (key551, -2), (key497, -2)]

def rawRow14687 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key493, -2), (key619, 6), (key225, -2), (key225, -2), (key221, -2), (key551, 2), (key551, 2), (key497, 2), (key497, 2), (key493, 2), (key493, 2), (key645, -2), (key619, -2), (key619, -2), (key225, 6), (key551, -2), (key497, -2), (key497, -2)]

def rawRow14688 : Integer.Sparse Key := [(key493, -2), (key497, -2), (key619, -2), (key497, 6), (key493, -2), (key497, -2), (key619, -2), (key221, 2), (key225, 2), (key493, 2), (key551, 2), (key619, 2), (key645, 2), (key225, -2), (key497, -2), (key551, -2), (key497, 6), (key225, -2), (key497, -2), (key551, -2)]

def rawRow14689 : Integer.Sparse Key := [(key497, -2), (key493, -2), (key619, -2), (key497, 6), (key497, -2), (key493, -2), (key619, -2), (key225, 2), (key221, 2), (key551, 2), (key493, 2), (key645, 2), (key619, 2), (key225, -2), (key551, -2), (key497, -2), (key497, 6), (key225, -2), (key551, -2), (key497, -2)]

def rawRow14690 : Integer.Sparse Key := [(key493, -2), (key619, -2), (key497, -2), (key497, 6), (key493, -2), (key619, -2), (key497, -2), (key493, 2), (key619, 2), (key221, 2), (key645, 2), (key225, 2), (key551, 2), (key497, -2), (key225, -2), (key551, -2), (key497, 6), (key497, -2), (key225, -2), (key551, -2)]

def rawRow14691 : Integer.Sparse Key := [(key619, -2), (key493, -2), (key497, -2), (key497, 6), (key619, -2), (key493, -2), (key497, -2), (key619, 2), (key493, 2), (key645, 2), (key221, 2), (key551, 2), (key225, 2), (key497, -2), (key551, -2), (key225, -2), (key497, 6), (key497, -2), (key551, -2), (key225, -2)]

def rawRow14692 : Integer.Sparse Key := [(key497, -2), (key619, -2), (key493, -2), (key497, 6), (key497, -2), (key619, -2), (key493, -2), (key551, 2), (key645, 2), (key225, 2), (key619, 2), (key221, 2), (key493, 2), (key551, -2), (key225, -2), (key497, -2), (key497, 6), (key551, -2), (key225, -2), (key497, -2)]

def rawRow14693 : Integer.Sparse Key := [(key619, -2), (key497, -2), (key493, -2), (key497, 6), (key619, -2), (key497, -2), (key493, -2), (key645, 2), (key551, 2), (key619, 2), (key225, 2), (key493, 2), (key221, 2), (key551, -2), (key497, -2), (key225, -2), (key497, 6), (key551, -2), (key497, -2), (key225, -2)]

def rawRow14694 : Integer.Sparse Key := [(key497, -2), (key497, -2), (key619, -2), (key493, 6), (key551, -2), (key551, -2), (key645, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key619, 2), (key619, 2), (key221, -2), (key493, -2), (key493, -2), (key551, 6), (key225, -2), (key497, -2), (key497, -2)]

def rawRow14695 : Integer.Sparse Key := [(key497, -2), (key619, -2), (key497, -2), (key493, 6), (key551, -2), (key645, -2), (key551, -2), (key497, 2), (key619, 2), (key225, 2), (key619, 2), (key225, 2), (key497, 2), (key493, -2), (key221, -2), (key493, -2), (key551, 6), (key497, -2), (key225, -2), (key497, -2)]

def rawRow14696 : Integer.Sparse Key := [(key619, -2), (key497, -2), (key497, -2), (key493, 6), (key645, -2), (key551, -2), (key551, -2), (key619, 2), (key497, 2), (key619, 2), (key225, 2), (key497, 2), (key225, 2), (key493, -2), (key493, -2), (key221, -2), (key551, 6), (key497, -2), (key497, -2), (key225, -2)]

def rawRow14697 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key551, -2), (key645, 6), (key225, -2), (key225, -2), (key225, -2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key497, 2), (key619, -2), (key619, -2), (key619, -2), (key221, 6), (key493, -2), (key493, -2), (key493, -2)]

def rawRow14698 : Integer.Sparse Key := [(key551, -2), (key551, -2), (key645, -2), (key551, 6), (key497, -2), (key497, -2), (key619, -2), (key225, 2), (key225, 2), (key497, 2), (key497, 2), (key619, 2), (key619, 2), (key225, -2), (key497, -2), (key497, -2), (key493, 6), (key221, -2), (key493, -2), (key493, -2)]

def rawRow14699 : Integer.Sparse Key := [(key551, -2), (key645, -2), (key551, -2), (key551, 6), (key497, -2), (key619, -2), (key497, -2), (key497, 2), (key619, 2), (key225, 2), (key619, 2), (key225, 2), (key497, 2), (key497, -2), (key225, -2), (key497, -2), (key493, 6), (key493, -2), (key221, -2), (key493, -2)]

def rawRow14700 : Integer.Sparse Key := [(key645, -2), (key551, -2), (key551, -2), (key551, 6), (key619, -2), (key497, -2), (key497, -2), (key619, 2), (key497, 2), (key619, 2), (key225, 2), (key497, 2), (key225, 2), (key497, -2), (key497, -2), (key225, -2), (key493, 6), (key493, -2), (key493, -2), (key221, -2)]

def rawRow14701 : Integer.Sparse Key := [(key496, 4), (key496, 4), (key559, 4), (key496, -2), (key502, -2), (key496, -2), (key559, -2), (key502, -2), (key559, -2), (key618, -2), (key622, -2), (key618, -2), (key648, -2), (key622, -2), (key648, -2), (key622, 4), (key622, 4), (key648, 4)]

def rawRow14702 : Integer.Sparse Key := [(key496, 4), (key559, 4), (key496, 4), (key502, -2), (key496, -2), (key559, -2), (key496, -2), (key559, -2), (key502, -2), (key622, -2), (key618, -2), (key648, -2), (key618, -2), (key648, -2), (key622, -2), (key622, 4), (key648, 4), (key622, 4)]

def rawRow14703 : Integer.Sparse Key := [(key559, 4), (key496, 4), (key496, 4), (key559, -2), (key559, -2), (key502, -2), (key502, -2), (key496, -2), (key496, -2), (key648, -2), (key648, -2), (key622, -2), (key622, -2), (key618, -2), (key618, -2), (key648, 4), (key622, 4), (key622, 4)]

def rawRow14704 : Integer.Sparse Key := [(key502, 4), (key502, 4), (key502, 4), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key618, 4), (key618, 4), (key618, 4)]

def rawRow14705 : Integer.Sparse Key := [(key496, 4), (key496, 4), (key559, 4), (key618, -2), (key622, -2), (key618, -2), (key648, -2), (key622, -2), (key648, -2), (key496, -2), (key502, -2), (key496, -2), (key559, -2), (key502, -2), (key559, -2), (key622, 4), (key622, 4), (key648, 4)]

def rawRow14706 : Integer.Sparse Key := [(key496, 4), (key559, 4), (key496, 4), (key622, -2), (key618, -2), (key648, -2), (key618, -2), (key648, -2), (key622, -2), (key502, -2), (key496, -2), (key559, -2), (key496, -2), (key559, -2), (key502, -2), (key622, 4), (key648, 4), (key622, 4)]

def rawRow14707 : Integer.Sparse Key := [(key559, 4), (key496, 4), (key496, 4), (key648, -2), (key648, -2), (key622, -2), (key622, -2), (key618, -2), (key618, -2), (key559, -2), (key559, -2), (key502, -2), (key502, -2), (key496, -2), (key496, -2), (key648, 4), (key622, 4), (key622, 4)]

def rawRow14708 : Integer.Sparse Key := [(key224, 4), (key618, 4), (key648, 4), (key224, -2), (key230, -2), (key496, -2), (key559, -2), (key622, -2), (key648, -2), (key224, -2), (key230, -2), (key496, -2), (key559, -2), (key622, -2), (key648, -2), (key230, 4), (key502, 4), (key559, 4)]

def rawRow14709 : Integer.Sparse Key := [(key224, 4), (key648, 4), (key618, 4), (key230, -2), (key224, -2), (key559, -2), (key496, -2), (key648, -2), (key622, -2), (key230, -2), (key224, -2), (key559, -2), (key496, -2), (key648, -2), (key622, -2), (key230, 4), (key559, 4), (key502, 4)]

def rawRow14710 : Integer.Sparse Key := [(key618, 4), (key224, 4), (key648, 4), (key496, -2), (key622, -2), (key224, -2), (key648, -2), (key230, -2), (key559, -2), (key496, -2), (key622, -2), (key224, -2), (key648, -2), (key230, -2), (key559, -2), (key502, 4), (key230, 4), (key559, 4)]

def rawRow14711 : Integer.Sparse Key := [(key618, 4), (key648, 4), (key224, 4), (key622, -2), (key496, -2), (key648, -2), (key224, -2), (key559, -2), (key230, -2), (key622, -2), (key496, -2), (key648, -2), (key224, -2), (key559, -2), (key230, -2), (key502, 4), (key559, 4), (key230, 4)]

def rawRow14712 : Integer.Sparse Key := [(key648, 4), (key224, 4), (key618, 4), (key559, -2), (key648, -2), (key230, -2), (key622, -2), (key224, -2), (key496, -2), (key559, -2), (key648, -2), (key230, -2), (key622, -2), (key224, -2), (key496, -2), (key559, 4), (key230, 4), (key502, 4)]

def rawRow14713 : Integer.Sparse Key := [(key648, 4), (key618, 4), (key224, 4), (key648, -2), (key559, -2), (key622, -2), (key230, -2), (key496, -2), (key224, -2), (key648, -2), (key559, -2), (key622, -2), (key230, -2), (key496, -2), (key224, -2), (key559, 4), (key502, 4), (key230, 4)]

def rawRow14714 : Integer.Sparse Key := [(key230, 4), (key622, 4), (key622, 4), (key224, -2), (key224, -2), (key496, -2), (key496, -2), (key618, -2), (key618, -2), (key230, -2), (key230, -2), (key502, -2), (key502, -2), (key622, -2), (key622, -2), (key224, 4), (key496, 4), (key496, 4)]

def rawRow14715 : Integer.Sparse Key := [(key622, 4), (key230, 4), (key622, 4), (key496, -2), (key618, -2), (key224, -2), (key618, -2), (key224, -2), (key496, -2), (key502, -2), (key622, -2), (key230, -2), (key622, -2), (key230, -2), (key502, -2), (key496, 4), (key224, 4), (key496, 4)]

def rawRow14716 : Integer.Sparse Key := [(key622, 4), (key622, 4), (key230, 4), (key618, -2), (key496, -2), (key618, -2), (key224, -2), (key496, -2), (key224, -2), (key622, -2), (key502, -2), (key622, -2), (key230, -2), (key502, -2), (key230, -2), (key496, 4), (key496, 4), (key224, 4)]

def rawRow14717 : Integer.Sparse Key := [(key502, 4), (key502, 4), (key502, 4), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key496, -2), (key618, 4), (key618, 4), (key618, 4)]

def rawRow14718 : Integer.Sparse Key := [(key230, 4), (key622, 4), (key622, 4), (key230, -2), (key230, -2), (key502, -2), (key502, -2), (key622, -2), (key622, -2), (key224, -2), (key224, -2), (key496, -2), (key496, -2), (key618, -2), (key618, -2), (key224, 4), (key496, 4), (key496, 4)]

def rawRow14719 : Integer.Sparse Key := [(key622, 4), (key230, 4), (key622, 4), (key502, -2), (key622, -2), (key230, -2), (key622, -2), (key230, -2), (key502, -2), (key496, -2), (key618, -2), (key224, -2), (key618, -2), (key224, -2), (key496, -2), (key496, 4), (key224, 4), (key496, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14720 : Integer.Sparse Key := [(key622, 4), (key622, 4), (key230, 4), (key622, -2), (key502, -2), (key622, -2), (key230, -2), (key502, -2), (key230, -2), (key618, -2), (key496, -2), (key618, -2), (key224, -2), (key496, -2), (key224, -2), (key496, 4), (key496, 4), (key224, 4)]

def rawRow14721 : Integer.Sparse Key := [(key1484, -1), (key1490, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1710, -1), (key1716, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, -1), (key1940, -1), (key1937, -1), (key1949, -1), (key1940, -1), (key1949, -1)]

def rawRow14722 : Integer.Sparse Key := [(key1490, -1), (key1484, -1), (key1513, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1716, -1), (key1710, -1), (key1741, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1937, 2), (key1949, 2), (key1937, 2), (key1940, -1), (key1937, -1), (key1949, -1), (key1937, -1), (key1949, -1), (key1940, -1)]

def rawRow14723 : Integer.Sparse Key := [(key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1484, -1), (key1484, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1710, -1), (key1710, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1), (key1949, 2), (key1937, 2), (key1937, 2), (key1949, -1), (key1949, -1), (key1940, -1), (key1940, -1), (key1937, -1), (key1937, -1)]

def rawRow14724 : Integer.Sparse Key := [(key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1484, 2), (key1484, 2), (key1484, 2), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1940, 2), (key1940, 2), (key1940, 2), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1)]

def rawRow14725 : Integer.Sparse Key := [(key1710, -1), (key1716, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1937, 2), (key1937, 2), (key1949, 2), (key1484, -1), (key1490, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1937, -1), (key1940, -1), (key1937, -1), (key1949, -1), (key1940, -1), (key1949, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1)]

def rawRow14726 : Integer.Sparse Key := [(key1716, -1), (key1710, -1), (key1741, -1), (key1710, -1), (key1741, -1), (key1716, -1), (key1937, 2), (key1949, 2), (key1937, 2), (key1490, -1), (key1484, -1), (key1513, -1), (key1484, -1), (key1513, -1), (key1490, -1), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1940, -1), (key1937, -1), (key1949, -1), (key1937, -1), (key1949, -1), (key1940, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1)]

def rawRow14727 : Integer.Sparse Key := [(key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1710, -1), (key1710, -1), (key1949, 2), (key1937, 2), (key1937, 2), (key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1484, -1), (key1484, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1949, -1), (key1949, -1), (key1940, -1), (key1940, -1), (key1937, -1), (key1937, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1)]

def rawRow14728 : Integer.Sparse Key := [(key1358, -1), (key1364, -1), (key1710, -1), (key1741, -1), (key1937, -1), (key1949, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1358, -1), (key1364, -1), (key1710, -1), (key1741, -1), (key1937, -1), (key1949, -1), (key1358, 2), (key1374, 2), (key1484, 2), (key1513, 2), (key1940, 2), (key1949, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1)]

def rawRow14729 : Integer.Sparse Key := [(key1364, -1), (key1358, -1), (key1741, -1), (key1710, -1), (key1949, -1), (key1937, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1364, -1), (key1358, -1), (key1741, -1), (key1710, -1), (key1949, -1), (key1937, -1), (key1374, 2), (key1358, 2), (key1513, 2), (key1484, 2), (key1949, 2), (key1940, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1)]

def rawRow14730 : Integer.Sparse Key := [(key1710, -1), (key1937, -1), (key1358, -1), (key1949, -1), (key1364, -1), (key1741, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1710, -1), (key1937, -1), (key1358, -1), (key1949, -1), (key1364, -1), (key1741, -1), (key1484, 2), (key1940, 2), (key1358, 2), (key1949, 2), (key1374, 2), (key1513, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1)]

def rawRow14731 : Integer.Sparse Key := [(key1937, -1), (key1710, -1), (key1949, -1), (key1358, -1), (key1741, -1), (key1364, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1937, -1), (key1710, -1), (key1949, -1), (key1358, -1), (key1741, -1), (key1364, -1), (key1940, 2), (key1484, 2), (key1949, 2), (key1358, 2), (key1513, 2), (key1374, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1)]

def rawRow14732 : Integer.Sparse Key := [(key1741, -1), (key1949, -1), (key1364, -1), (key1937, -1), (key1358, -1), (key1710, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1741, -1), (key1949, -1), (key1364, -1), (key1937, -1), (key1358, -1), (key1710, -1), (key1513, 2), (key1949, 2), (key1374, 2), (key1940, 2), (key1358, 2), (key1484, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1)]

def rawRow14733 : Integer.Sparse Key := [(key1949, -1), (key1741, -1), (key1937, -1), (key1364, -1), (key1710, -1), (key1358, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1949, -1), (key1741, -1), (key1937, -1), (key1364, -1), (key1710, -1), (key1358, -1), (key1949, 2), (key1513, 2), (key1940, 2), (key1374, 2), (key1484, 2), (key1358, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1)]

def rawRow14734 : Integer.Sparse Key := [(key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1937, -1), (key1937, -1), (key1358, 2), (key1710, 2), (key1710, 2), (key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1940, -1), (key1940, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1358, -1), (key1358, -1), (key1484, -1), (key1484, -1), (key1710, -1), (key1710, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1)]

def rawRow14735 : Integer.Sparse Key := [(key1716, -1), (key1937, -1), (key1364, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1710, 2), (key1358, 2), (key1710, 2), (key1723, -1), (key1940, -1), (key1374, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1484, -1), (key1710, -1), (key1358, -1), (key1710, -1), (key1358, -1), (key1484, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1)]

def rawRow14736 : Integer.Sparse Key := [(key1937, -1), (key1716, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1710, 2), (key1710, 2), (key1358, 2), (key1940, -1), (key1723, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1710, -1), (key1484, -1), (key1710, -1), (key1358, -1), (key1484, -1), (key1358, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1)]

def rawRow14737 : Integer.Sparse Key := [(key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1940, 2), (key1940, 2), (key1940, 2), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1937, -1), (key1484, 2), (key1484, 2), (key1484, 2), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1), (key1710, -1)]

def rawRow14738 : Integer.Sparse Key := [(key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1940, -1), (key1940, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1937, -1), (key1937, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1), (key1358, 2), (key1710, 2), (key1710, 2), (key1358, -1), (key1358, -1), (key1484, -1), (key1484, -1), (key1710, -1), (key1710, -1)]

def rawRow14739 : Integer.Sparse Key := [(key1723, -1), (key1940, -1), (key1374, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1716, -1), (key1937, -1), (key1364, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1710, 2), (key1358, 2), (key1710, 2), (key1484, -1), (key1710, -1), (key1358, -1), (key1710, -1), (key1358, -1), (key1484, -1)]

def rawRow14740 : Integer.Sparse Key := [(key1940, -1), (key1723, -1), (key1940, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1937, -1), (key1716, -1), (key1937, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, -1), (key1484, -1), (key1710, -1), (key1358, -1), (key1484, -1), (key1358, -1)]

def rawRow14741 : Integer.Sparse Key := [(key1501, 4), (key1501, 4), (key1506, 4), (key1501, -4), (key1506, -4), (key1506, -4), (key1733, -4), (key1735, -4), (key1735, -4), (key1735, 12)]

def rawRow14742 : Integer.Sparse Key := [(key1501, 4), (key1506, 4), (key1501, 4), (key1506, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1733, -4), (key1735, -4), (key1735, 12)]

def rawRow14743 : Integer.Sparse Key := [(key1506, 4), (key1501, 4), (key1501, 4), (key1506, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1735, -4), (key1733, -4), (key1735, 12)]

def rawRow14744 : Integer.Sparse Key := [(key1506, 4), (key1506, 4), (key1506, 4), (key1501, -4), (key1501, -4), (key1501, -4), (key1735, -4), (key1735, -4), (key1735, -4), (key1733, 12)]

def rawRow14745 : Integer.Sparse Key := [(key1501, 4), (key1501, 4), (key1506, 4), (key1733, -4), (key1735, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1506, -4), (key1735, 12)]

def rawRow14746 : Integer.Sparse Key := [(key1501, 4), (key1506, 4), (key1501, 4), (key1735, -4), (key1733, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1506, -4), (key1735, 12)]

def rawRow14747 : Integer.Sparse Key := [(key1506, 4), (key1501, 4), (key1501, 4), (key1735, -4), (key1735, -4), (key1733, -4), (key1506, -4), (key1506, -4), (key1501, -4), (key1735, 12)]

def rawRow14748 : Integer.Sparse Key := [(key1501, 4), (key1733, 4), (key1735, 4), (key1501, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1506, 12)]

def rawRow14749 : Integer.Sparse Key := [(key1501, 4), (key1735, 4), (key1733, 4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, 12)]

def rawRow14750 : Integer.Sparse Key := [(key1733, 4), (key1501, 4), (key1735, 4), (key1501, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1506, 12)]

def rawRow14751 : Integer.Sparse Key := [(key1733, 4), (key1735, 4), (key1501, 4), (key1735, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1506, 12)]

def rawRow14752 : Integer.Sparse Key := [(key1735, 4), (key1501, 4), (key1733, 4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1506, 12)]

def rawRow14753 : Integer.Sparse Key := [(key1735, 4), (key1733, 4), (key1501, 4), (key1735, -4), (key1506, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1506, 12)]

def rawRow14754 : Integer.Sparse Key := [(key1506, 4), (key1735, 4), (key1735, 4), (key1501, -4), (key1501, -4), (key1733, -4), (key1506, -4), (key1506, -4), (key1735, -4), (key1501, 12)]

def rawRow14755 : Integer.Sparse Key := [(key1735, 4), (key1506, 4), (key1735, 4), (key1501, -4), (key1733, -4), (key1501, -4), (key1506, -4), (key1735, -4), (key1506, -4), (key1501, 12)]

def rawRow14756 : Integer.Sparse Key := [(key1735, 4), (key1735, 4), (key1506, 4), (key1733, -4), (key1501, -4), (key1501, -4), (key1735, -4), (key1506, -4), (key1506, -4), (key1501, 12)]

def rawRow14757 : Integer.Sparse Key := [(key1506, 4), (key1506, 4), (key1506, 4), (key1735, -4), (key1735, -4), (key1735, -4), (key1501, -4), (key1501, -4), (key1501, -4), (key1733, 12)]

def rawRow14758 : Integer.Sparse Key := [(key1506, 4), (key1735, 4), (key1735, 4), (key1506, -4), (key1506, -4), (key1735, -4), (key1501, -4), (key1501, -4), (key1733, -4), (key1501, 12)]

def rawRow14759 : Integer.Sparse Key := [(key1735, 4), (key1506, 4), (key1735, 4), (key1506, -4), (key1735, -4), (key1506, -4), (key1501, -4), (key1733, -4), (key1501, -4), (key1501, 12)]

def rawRow14760 : Integer.Sparse Key := [(key1735, 4), (key1735, 4), (key1506, 4), (key1735, -4), (key1506, -4), (key1506, -4), (key1733, -4), (key1501, -4), (key1501, -4), (key1501, 12)]

def rawRow14761 : Integer.Sparse Key := [(key1274, -2), (key1278, -2), (key1278, -2), (key1278, 6), (key1697, -2), (key1701, -2), (key1701, -2), (key1697, 2), (key1701, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1701, -2), (key1701, -2), (key1751, -2), (key1852, 6), (key1852, -2), (key1852, -2), (key1884, -2)]

def rawRow14762 : Integer.Sparse Key := [(key1278, -2), (key1274, -2), (key1278, -2), (key1278, 6), (key1701, -2), (key1697, -2), (key1701, -2), (key1701, 2), (key1697, 2), (key1751, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1701, -2), (key1751, -2), (key1701, -2), (key1852, 6), (key1852, -2), (key1884, -2), (key1852, -2)]

def rawRow14763 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1274, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1697, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1697, 2), (key1697, 2), (key1751, -2), (key1701, -2), (key1701, -2), (key1852, 6), (key1884, -2), (key1852, -2), (key1852, -2)]

def rawRow14764 : Integer.Sparse Key := [(key1278, -2), (key1278, -2), (key1278, -2), (key1274, 6), (key1751, -2), (key1751, -2), (key1751, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1697, -2), (key1697, -2), (key1697, -2), (key1884, 6), (key1852, -2), (key1852, -2), (key1852, -2)]

def rawRow14765 : Integer.Sparse Key := [(key1697, -2), (key1701, -2), (key1701, -2), (key1852, 6), (key1274, -2), (key1278, -2), (key1278, -2), (key1697, 2), (key1701, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1751, 2), (key1852, -2), (key1852, -2), (key1884, -2), (key1278, 6), (key1701, -2), (key1701, -2), (key1751, -2)]

def rawRow14766 : Integer.Sparse Key := [(key1701, -2), (key1697, -2), (key1701, -2), (key1852, 6), (key1278, -2), (key1274, -2), (key1278, -2), (key1701, 2), (key1697, 2), (key1751, 2), (key1697, 2), (key1751, 2), (key1701, 2), (key1852, -2), (key1884, -2), (key1852, -2), (key1278, 6), (key1701, -2), (key1751, -2), (key1701, -2)]

def rawRow14767 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1697, -2), (key1852, 6), (key1278, -2), (key1278, -2), (key1274, -2), (key1751, 2), (key1751, 2), (key1701, 2), (key1701, 2), (key1697, 2), (key1697, 2), (key1884, -2), (key1852, -2), (key1852, -2), (key1278, 6), (key1751, -2), (key1701, -2), (key1701, -2)]

def rawRow14768 : Integer.Sparse Key := [(key1697, -2), (key1701, -2), (key1852, -2), (key1701, 6), (key1697, -2), (key1701, -2), (key1852, -2), (key1274, 2), (key1278, 2), (key1697, 2), (key1751, 2), (key1852, 2), (key1884, 2), (key1278, -2), (key1701, -2), (key1751, -2), (key1701, 6), (key1278, -2), (key1701, -2), (key1751, -2)]

def rawRow14769 : Integer.Sparse Key := [(key1701, -2), (key1697, -2), (key1852, -2), (key1701, 6), (key1701, -2), (key1697, -2), (key1852, -2), (key1278, 2), (key1274, 2), (key1751, 2), (key1697, 2), (key1884, 2), (key1852, 2), (key1278, -2), (key1751, -2), (key1701, -2), (key1701, 6), (key1278, -2), (key1751, -2), (key1701, -2)]

def rawRow14770 : Integer.Sparse Key := [(key1697, -2), (key1852, -2), (key1701, -2), (key1701, 6), (key1697, -2), (key1852, -2), (key1701, -2), (key1697, 2), (key1852, 2), (key1274, 2), (key1884, 2), (key1278, 2), (key1751, 2), (key1701, -2), (key1278, -2), (key1751, -2), (key1701, 6), (key1701, -2), (key1278, -2), (key1751, -2)]

def rawRow14771 : Integer.Sparse Key := [(key1852, -2), (key1697, -2), (key1701, -2), (key1701, 6), (key1852, -2), (key1697, -2), (key1701, -2), (key1852, 2), (key1697, 2), (key1884, 2), (key1274, 2), (key1751, 2), (key1278, 2), (key1701, -2), (key1751, -2), (key1278, -2), (key1701, 6), (key1701, -2), (key1751, -2), (key1278, -2)]

def rawRow14772 : Integer.Sparse Key := [(key1701, -2), (key1852, -2), (key1697, -2), (key1701, 6), (key1701, -2), (key1852, -2), (key1697, -2), (key1751, 2), (key1884, 2), (key1278, 2), (key1852, 2), (key1274, 2), (key1697, 2), (key1751, -2), (key1278, -2), (key1701, -2), (key1701, 6), (key1751, -2), (key1278, -2), (key1701, -2)]

def rawRow14773 : Integer.Sparse Key := [(key1852, -2), (key1701, -2), (key1697, -2), (key1701, 6), (key1852, -2), (key1701, -2), (key1697, -2), (key1884, 2), (key1751, 2), (key1852, 2), (key1278, 2), (key1697, 2), (key1274, 2), (key1751, -2), (key1701, -2), (key1278, -2), (key1701, 6), (key1751, -2), (key1701, -2), (key1278, -2)]

def rawRow14774 : Integer.Sparse Key := [(key1701, -2), (key1701, -2), (key1852, -2), (key1697, 6), (key1751, -2), (key1751, -2), (key1884, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1852, 2), (key1852, 2), (key1274, -2), (key1697, -2), (key1697, -2), (key1751, 6), (key1278, -2), (key1701, -2), (key1701, -2)]

def rawRow14775 : Integer.Sparse Key := [(key1701, -2), (key1852, -2), (key1701, -2), (key1697, 6), (key1751, -2), (key1884, -2), (key1751, -2), (key1701, 2), (key1852, 2), (key1278, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1697, -2), (key1274, -2), (key1697, -2), (key1751, 6), (key1701, -2), (key1278, -2), (key1701, -2)]

def rawRow14776 : Integer.Sparse Key := [(key1852, -2), (key1701, -2), (key1701, -2), (key1697, 6), (key1884, -2), (key1751, -2), (key1751, -2), (key1852, 2), (key1701, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1697, -2), (key1697, -2), (key1274, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1278, -2)]

def rawRow14777 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1751, -2), (key1884, 6), (key1278, -2), (key1278, -2), (key1278, -2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1701, 2), (key1852, -2), (key1852, -2), (key1852, -2), (key1274, 6), (key1697, -2), (key1697, -2), (key1697, -2)]

def rawRow14778 : Integer.Sparse Key := [(key1751, -2), (key1751, -2), (key1884, -2), (key1751, 6), (key1701, -2), (key1701, -2), (key1852, -2), (key1278, 2), (key1278, 2), (key1701, 2), (key1701, 2), (key1852, 2), (key1852, 2), (key1278, -2), (key1701, -2), (key1701, -2), (key1697, 6), (key1274, -2), (key1697, -2), (key1697, -2)]

def rawRow14779 : Integer.Sparse Key := [(key1751, -2), (key1884, -2), (key1751, -2), (key1751, 6), (key1701, -2), (key1852, -2), (key1701, -2), (key1701, 2), (key1852, 2), (key1278, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1701, -2), (key1278, -2), (key1701, -2), (key1697, 6), (key1697, -2), (key1274, -2), (key1697, -2)]

def rawRow14780 : Integer.Sparse Key := [(key1884, -2), (key1751, -2), (key1751, -2), (key1751, 6), (key1852, -2), (key1701, -2), (key1701, -2), (key1852, 2), (key1701, 2), (key1852, 2), (key1278, 2), (key1701, 2), (key1278, 2), (key1701, -2), (key1701, -2), (key1278, -2), (key1697, 6), (key1697, -2), (key1697, -2), (key1274, -2)]

def rawRow14781 : Integer.Sparse Key := [(key358, 4), (key358, 4), (key363, 4), (key358, -4), (key363, -4), (key363, -4), (key528, -4), (key532, -4), (key532, -4), (key532, 12)]

def rawRow14782 : Integer.Sparse Key := [(key358, 4), (key363, 4), (key358, 4), (key363, -4), (key358, -4), (key363, -4), (key532, -4), (key528, -4), (key532, -4), (key532, 12)]

def rawRow14783 : Integer.Sparse Key := [(key363, 4), (key358, 4), (key358, 4), (key363, -4), (key363, -4), (key358, -4), (key532, -4), (key532, -4), (key528, -4), (key532, 12)]

def rawRow14784 : Integer.Sparse Key := [(key363, 4), (key363, 4), (key363, 4), (key358, -4), (key358, -4), (key358, -4), (key532, -4), (key532, -4), (key532, -4), (key528, 12)]

def rawRow14785 : Integer.Sparse Key := [(key358, 4), (key358, 4), (key363, 4), (key528, -4), (key532, -4), (key532, -4), (key358, -4), (key363, -4), (key363, -4), (key532, 12)]

def rawRow14786 : Integer.Sparse Key := [(key358, 4), (key363, 4), (key358, 4), (key532, -4), (key528, -4), (key532, -4), (key363, -4), (key358, -4), (key363, -4), (key532, 12)]

def rawRow14787 : Integer.Sparse Key := [(key363, 4), (key358, 4), (key358, 4), (key532, -4), (key532, -4), (key528, -4), (key363, -4), (key363, -4), (key358, -4), (key532, 12)]

def rawRow14788 : Integer.Sparse Key := [(key358, 4), (key528, 4), (key532, 4), (key358, -4), (key363, -4), (key532, -4), (key358, -4), (key363, -4), (key532, -4), (key363, 12)]

def rawRow14789 : Integer.Sparse Key := [(key358, 4), (key532, 4), (key528, 4), (key363, -4), (key358, -4), (key532, -4), (key363, -4), (key358, -4), (key532, -4), (key363, 12)]

def rawRow14790 : Integer.Sparse Key := [(key528, 4), (key358, 4), (key532, 4), (key358, -4), (key532, -4), (key363, -4), (key358, -4), (key532, -4), (key363, -4), (key363, 12)]

def rawRow14791 : Integer.Sparse Key := [(key528, 4), (key532, 4), (key358, 4), (key532, -4), (key358, -4), (key363, -4), (key532, -4), (key358, -4), (key363, -4), (key363, 12)]

def rawRow14792 : Integer.Sparse Key := [(key532, 4), (key358, 4), (key528, 4), (key363, -4), (key532, -4), (key358, -4), (key363, -4), (key532, -4), (key358, -4), (key363, 12)]

def rawRow14793 : Integer.Sparse Key := [(key532, 4), (key528, 4), (key358, 4), (key532, -4), (key363, -4), (key358, -4), (key532, -4), (key363, -4), (key358, -4), (key363, 12)]

def rawRow14794 : Integer.Sparse Key := [(key363, 4), (key532, 4), (key532, 4), (key358, -4), (key358, -4), (key528, -4), (key363, -4), (key363, -4), (key532, -4), (key358, 12)]

def rawRow14795 : Integer.Sparse Key := [(key532, 4), (key363, 4), (key532, 4), (key358, -4), (key528, -4), (key358, -4), (key363, -4), (key532, -4), (key363, -4), (key358, 12)]

def rawRow14796 : Integer.Sparse Key := [(key532, 4), (key532, 4), (key363, 4), (key528, -4), (key358, -4), (key358, -4), (key532, -4), (key363, -4), (key363, -4), (key358, 12)]

def rawRow14797 : Integer.Sparse Key := [(key363, 4), (key363, 4), (key363, 4), (key532, -4), (key532, -4), (key532, -4), (key358, -4), (key358, -4), (key358, -4), (key528, 12)]

def rawRow14798 : Integer.Sparse Key := [(key363, 4), (key532, 4), (key532, 4), (key363, -4), (key363, -4), (key532, -4), (key358, -4), (key358, -4), (key528, -4), (key358, 12)]

def rawRow14799 : Integer.Sparse Key := [(key532, 4), (key363, 4), (key532, 4), (key363, -4), (key532, -4), (key363, -4), (key358, -4), (key528, -4), (key358, -4), (key358, 12)]

def rawRow14800 : Integer.Sparse Key := [(key532, 4), (key532, 4), (key363, 4), (key532, -4), (key363, -4), (key363, -4), (key528, -4), (key358, -4), (key358, -4), (key358, 12)]

def rawRow14801 : Integer.Sparse Key := [(key1485, -1), (key1490, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1711, -1), (key1716, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1711, 2), (key1723, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, -1), (key1867, -1), (key1861, -1), (key1877, -1), (key1867, -1), (key1877, -1)]

def rawRow14802 : Integer.Sparse Key := [(key1490, -1), (key1485, -1), (key1513, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1716, -1), (key1711, -1), (key1741, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1723, 2), (key1711, 2), (key1741, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1861, 2), (key1877, 2), (key1861, 2), (key1867, -1), (key1861, -1), (key1877, -1), (key1861, -1), (key1877, -1), (key1867, -1)]

def rawRow14803 : Integer.Sparse Key := [(key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1485, -1), (key1485, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1711, -1), (key1711, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1711, 2), (key1711, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, -1), (key1877, -1), (key1867, -1), (key1867, -1), (key1861, -1), (key1861, -1)]

def rawRow14804 : Integer.Sparse Key := [(key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1485, 2), (key1485, 2), (key1485, 2), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1)]

def rawRow14805 : Integer.Sparse Key := [(key1711, -1), (key1716, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1861, 2), (key1861, 2), (key1877, 2), (key1485, -1), (key1490, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1513, -1), (key1711, 2), (key1723, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1861, -1), (key1867, -1), (key1861, -1), (key1877, -1), (key1867, -1), (key1877, -1), (key1490, 2), (key1490, 2), (key1513, 2), (key1716, -1), (key1723, -1), (key1716, -1), (key1741, -1), (key1723, -1), (key1741, -1)]

def rawRow14806 : Integer.Sparse Key := [(key1716, -1), (key1711, -1), (key1741, -1), (key1711, -1), (key1741, -1), (key1716, -1), (key1861, 2), (key1877, 2), (key1861, 2), (key1490, -1), (key1485, -1), (key1513, -1), (key1485, -1), (key1513, -1), (key1490, -1), (key1723, 2), (key1711, 2), (key1741, 2), (key1711, 2), (key1741, 2), (key1723, 2), (key1867, -1), (key1861, -1), (key1877, -1), (key1861, -1), (key1877, -1), (key1867, -1), (key1490, 2), (key1513, 2), (key1490, 2), (key1723, -1), (key1716, -1), (key1741, -1), (key1716, -1), (key1741, -1), (key1723, -1)]

def rawRow14807 : Integer.Sparse Key := [(key1741, -1), (key1741, -1), (key1716, -1), (key1716, -1), (key1711, -1), (key1711, -1), (key1877, 2), (key1861, 2), (key1861, 2), (key1513, -1), (key1513, -1), (key1490, -1), (key1490, -1), (key1485, -1), (key1485, -1), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1711, 2), (key1711, 2), (key1877, -1), (key1877, -1), (key1867, -1), (key1867, -1), (key1861, -1), (key1861, -1), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, -1), (key1741, -1), (key1723, -1), (key1723, -1), (key1716, -1), (key1716, -1)]

def rawRow14808 : Integer.Sparse Key := [(key1359, -1), (key1364, -1), (key1711, -1), (key1741, -1), (key1861, -1), (key1877, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1359, -1), (key1364, -1), (key1711, -1), (key1741, -1), (key1861, -1), (key1877, -1), (key1359, 2), (key1374, 2), (key1485, 2), (key1513, 2), (key1867, 2), (key1877, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, -1), (key1374, -1), (key1490, -1), (key1513, -1), (key1723, -1), (key1741, -1)]

def rawRow14809 : Integer.Sparse Key := [(key1364, -1), (key1359, -1), (key1741, -1), (key1711, -1), (key1877, -1), (key1861, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1364, -1), (key1359, -1), (key1741, -1), (key1711, -1), (key1877, -1), (key1861, -1), (key1374, 2), (key1359, 2), (key1513, 2), (key1485, 2), (key1877, 2), (key1867, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1), (key1364, 2), (key1741, 2), (key1716, 2), (key1374, -1), (key1364, -1), (key1513, -1), (key1490, -1), (key1741, -1), (key1723, -1)]

def rawRow14810 : Integer.Sparse Key := [(key1711, -1), (key1861, -1), (key1359, -1), (key1877, -1), (key1364, -1), (key1741, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1711, -1), (key1861, -1), (key1359, -1), (key1877, -1), (key1364, -1), (key1741, -1), (key1485, 2), (key1867, 2), (key1359, 2), (key1877, 2), (key1374, 2), (key1513, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1), (key1716, 2), (key1364, 2), (key1741, 2), (key1490, -1), (key1723, -1), (key1364, -1), (key1741, -1), (key1374, -1), (key1513, -1)]

def rawRow14811 : Integer.Sparse Key := [(key1861, -1), (key1711, -1), (key1877, -1), (key1359, -1), (key1741, -1), (key1364, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1861, -1), (key1711, -1), (key1877, -1), (key1359, -1), (key1741, -1), (key1364, -1), (key1867, 2), (key1485, 2), (key1877, 2), (key1359, 2), (key1513, 2), (key1374, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1), (key1716, 2), (key1741, 2), (key1364, 2), (key1723, -1), (key1490, -1), (key1741, -1), (key1364, -1), (key1513, -1), (key1374, -1)]

def rawRow14812 : Integer.Sparse Key := [(key1741, -1), (key1877, -1), (key1364, -1), (key1861, -1), (key1359, -1), (key1711, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1741, -1), (key1877, -1), (key1364, -1), (key1861, -1), (key1359, -1), (key1711, -1), (key1513, 2), (key1877, 2), (key1374, 2), (key1867, 2), (key1359, 2), (key1485, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1), (key1741, 2), (key1364, 2), (key1716, 2), (key1513, -1), (key1741, -1), (key1374, -1), (key1723, -1), (key1364, -1), (key1490, -1)]

def rawRow14813 : Integer.Sparse Key := [(key1877, -1), (key1741, -1), (key1861, -1), (key1364, -1), (key1711, -1), (key1359, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1877, -1), (key1741, -1), (key1861, -1), (key1364, -1), (key1711, -1), (key1359, -1), (key1877, 2), (key1513, 2), (key1867, 2), (key1374, 2), (key1485, 2), (key1359, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, -1), (key1513, -1), (key1723, -1), (key1374, -1), (key1490, -1), (key1364, -1)]

def rawRow14814 : Integer.Sparse Key := [(key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1861, -1), (key1861, -1), (key1359, 2), (key1711, 2), (key1711, 2), (key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1867, -1), (key1867, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1861, 2), (key1861, 2), (key1359, -1), (key1359, -1), (key1485, -1), (key1485, -1), (key1711, -1), (key1711, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1)]

def rawRow14815 : Integer.Sparse Key := [(key1716, -1), (key1861, -1), (key1364, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1711, 2), (key1359, 2), (key1711, 2), (key1723, -1), (key1867, -1), (key1374, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1490, 2), (key1861, 2), (key1364, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1485, -1), (key1711, -1), (key1359, -1), (key1711, -1), (key1359, -1), (key1485, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1)]

def rawRow14816 : Integer.Sparse Key := [(key1861, -1), (key1716, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1711, 2), (key1711, 2), (key1359, 2), (key1867, -1), (key1723, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1861, 2), (key1490, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1711, -1), (key1485, -1), (key1711, -1), (key1359, -1), (key1485, -1), (key1359, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1)]

def rawRow14817 : Integer.Sparse Key := [(key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1723, -1), (key1867, 2), (key1867, 2), (key1867, 2), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1490, -1), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1861, -1), (key1485, 2), (key1485, 2), (key1485, 2), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1), (key1711, -1)]

def rawRow14818 : Integer.Sparse Key := [(key1374, -1), (key1374, -1), (key1723, -1), (key1723, -1), (key1867, -1), (key1867, -1), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, -1), (key1364, -1), (key1716, -1), (key1716, -1), (key1861, -1), (key1861, -1), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1861, 2), (key1861, 2), (key1364, -1), (key1364, -1), (key1490, -1), (key1490, -1), (key1716, -1), (key1716, -1), (key1359, 2), (key1711, 2), (key1711, 2), (key1359, -1), (key1359, -1), (key1485, -1), (key1485, -1), (key1711, -1), (key1711, -1)]

def rawRow14819 : Integer.Sparse Key := [(key1723, -1), (key1867, -1), (key1374, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1723, 2), (key1374, 2), (key1723, 2), (key1716, -1), (key1861, -1), (key1364, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1490, 2), (key1861, 2), (key1364, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1490, -1), (key1716, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1711, 2), (key1359, 2), (key1711, 2), (key1485, -1), (key1711, -1), (key1359, -1), (key1711, -1), (key1359, -1), (key1485, -1)]

def rawRow14820 : Integer.Sparse Key := [(key1867, -1), (key1723, -1), (key1867, -1), (key1374, -1), (key1723, -1), (key1374, -1), (key1723, 2), (key1723, 2), (key1374, 2), (key1861, -1), (key1716, -1), (key1861, -1), (key1364, -1), (key1716, -1), (key1364, -1), (key1861, 2), (key1490, 2), (key1861, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1716, -1), (key1490, -1), (key1716, -1), (key1364, -1), (key1490, -1), (key1364, -1), (key1711, 2), (key1711, 2), (key1359, 2), (key1711, -1), (key1485, -1), (key1711, -1), (key1359, -1), (key1485, -1), (key1359, -1)]

def rawRow14821 : Integer.Sparse Key := [(key288, -2), (key289, -2), (key289, -2), (key289, 6), (key513, -2), (key515, -2), (key515, -2), (key513, 2), (key515, 2), (key513, 2), (key547, 2), (key515, 2), (key547, 2), (key515, -2), (key515, -2), (key547, -2), (key670, 6), (key670, -2), (key670, -2), (key680, -2)]

def rawRow14822 : Integer.Sparse Key := [(key289, -2), (key288, -2), (key289, -2), (key289, 6), (key515, -2), (key513, -2), (key515, -2), (key515, 2), (key513, 2), (key547, 2), (key513, 2), (key547, 2), (key515, 2), (key515, -2), (key547, -2), (key515, -2), (key670, 6), (key670, -2), (key680, -2), (key670, -2)]

def rawRow14823 : Integer.Sparse Key := [(key289, -2), (key289, -2), (key288, -2), (key289, 6), (key515, -2), (key515, -2), (key513, -2), (key547, 2), (key547, 2), (key515, 2), (key515, 2), (key513, 2), (key513, 2), (key547, -2), (key515, -2), (key515, -2), (key670, 6), (key680, -2), (key670, -2), (key670, -2)]

def rawRow14824 : Integer.Sparse Key := [(key289, -2), (key289, -2), (key289, -2), (key288, 6), (key547, -2), (key547, -2), (key547, -2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key513, -2), (key513, -2), (key513, -2), (key680, 6), (key670, -2), (key670, -2), (key670, -2)]

def rawRow14825 : Integer.Sparse Key := [(key513, -2), (key515, -2), (key515, -2), (key547, 6), (key288, -2), (key289, -2), (key289, -2), (key513, 2), (key515, 2), (key513, 2), (key547, 2), (key515, 2), (key547, 2), (key670, -2), (key670, -2), (key680, -2), (key289, 6), (key515, -2), (key515, -2), (key547, -2)]

def rawRow14826 : Integer.Sparse Key := [(key515, -2), (key513, -2), (key515, -2), (key547, 6), (key289, -2), (key288, -2), (key289, -2), (key515, 2), (key513, 2), (key547, 2), (key513, 2), (key547, 2), (key515, 2), (key670, -2), (key680, -2), (key670, -2), (key289, 6), (key515, -2), (key547, -2), (key515, -2)]

def rawRow14827 : Integer.Sparse Key := [(key515, -2), (key515, -2), (key513, -2), (key547, 6), (key289, -2), (key289, -2), (key288, -2), (key547, 2), (key547, 2), (key515, 2), (key515, 2), (key513, 2), (key513, 2), (key680, -2), (key670, -2), (key670, -2), (key289, 6), (key547, -2), (key515, -2), (key515, -2)]

def rawRow14828 : Integer.Sparse Key := [(key513, -2), (key515, -2), (key547, -2), (key515, 6), (key513, -2), (key515, -2), (key547, -2), (key288, 2), (key289, 2), (key513, 2), (key547, 2), (key670, 2), (key680, 2), (key289, -2), (key515, -2), (key547, -2), (key515, 6), (key289, -2), (key515, -2), (key547, -2)]

def rawRow14829 : Integer.Sparse Key := [(key515, -2), (key513, -2), (key547, -2), (key515, 6), (key515, -2), (key513, -2), (key547, -2), (key289, 2), (key288, 2), (key547, 2), (key513, 2), (key680, 2), (key670, 2), (key289, -2), (key547, -2), (key515, -2), (key515, 6), (key289, -2), (key547, -2), (key515, -2)]

def rawRow14830 : Integer.Sparse Key := [(key513, -2), (key547, -2), (key515, -2), (key515, 6), (key513, -2), (key547, -2), (key515, -2), (key513, 2), (key547, 2), (key288, 2), (key680, 2), (key289, 2), (key547, 2), (key515, -2), (key289, -2), (key547, -2), (key515, 6), (key515, -2), (key289, -2), (key547, -2)]

def rawRow14831 : Integer.Sparse Key := [(key547, -2), (key513, -2), (key515, -2), (key515, 6), (key547, -2), (key513, -2), (key515, -2), (key547, 2), (key513, 2), (key680, 2), (key288, 2), (key547, 2), (key289, 2), (key515, -2), (key547, -2), (key289, -2), (key515, 6), (key515, -2), (key547, -2), (key289, -2)]

def rawRow14832 : Integer.Sparse Key := [(key515, -2), (key547, -2), (key513, -2), (key515, 6), (key515, -2), (key547, -2), (key513, -2), (key670, 2), (key680, 2), (key289, 2), (key547, 2), (key288, 2), (key513, 2), (key547, -2), (key289, -2), (key515, -2), (key515, 6), (key547, -2), (key289, -2), (key515, -2)]

def rawRow14833 : Integer.Sparse Key := [(key547, -2), (key515, -2), (key513, -2), (key515, 6), (key547, -2), (key515, -2), (key513, -2), (key680, 2), (key670, 2), (key547, 2), (key289, 2), (key513, 2), (key288, 2), (key547, -2), (key515, -2), (key289, -2), (key515, 6), (key547, -2), (key515, -2), (key289, -2)]

def rawRow14834 : Integer.Sparse Key := [(key515, -2), (key515, -2), (key547, -2), (key513, 6), (key670, -2), (key670, -2), (key680, -2), (key289, 2), (key289, 2), (key515, 2), (key515, 2), (key547, 2), (key547, 2), (key288, -2), (key513, -2), (key513, -2), (key547, 6), (key289, -2), (key515, -2), (key515, -2)]

def rawRow14835 : Integer.Sparse Key := [(key515, -2), (key547, -2), (key515, -2), (key513, 6), (key670, -2), (key680, -2), (key670, -2), (key515, 2), (key547, 2), (key289, 2), (key547, 2), (key289, 2), (key515, 2), (key513, -2), (key288, -2), (key513, -2), (key547, 6), (key515, -2), (key289, -2), (key515, -2)]

def rawRow14836 : Integer.Sparse Key := [(key547, -2), (key515, -2), (key515, -2), (key513, 6), (key680, -2), (key670, -2), (key670, -2), (key547, 2), (key515, 2), (key547, 2), (key289, 2), (key515, 2), (key289, 2), (key513, -2), (key513, -2), (key288, -2), (key547, 6), (key515, -2), (key515, -2), (key289, -2)]

def rawRow14837 : Integer.Sparse Key := [(key670, -2), (key670, -2), (key670, -2), (key680, 6), (key289, -2), (key289, -2), (key289, -2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key515, 2), (key547, -2), (key547, -2), (key547, -2), (key288, 6), (key513, -2), (key513, -2), (key513, -2)]

def rawRow14838 : Integer.Sparse Key := [(key670, -2), (key670, -2), (key680, -2), (key670, 6), (key515, -2), (key515, -2), (key547, -2), (key289, 2), (key289, 2), (key515, 2), (key515, 2), (key547, 2), (key547, 2), (key289, -2), (key515, -2), (key515, -2), (key513, 6), (key288, -2), (key513, -2), (key513, -2)]

def rawRow14839 : Integer.Sparse Key := [(key670, -2), (key680, -2), (key670, -2), (key670, 6), (key515, -2), (key547, -2), (key515, -2), (key515, 2), (key547, 2), (key289, 2), (key547, 2), (key289, 2), (key515, 2), (key515, -2), (key289, -2), (key515, -2), (key513, 6), (key513, -2), (key288, -2), (key513, -2)]

def rawRow14840 : Integer.Sparse Key := [(key680, -2), (key670, -2), (key670, -2), (key670, 6), (key547, -2), (key515, -2), (key515, -2), (key547, 2), (key515, 2), (key547, 2), (key289, 2), (key515, 2), (key289, 2), (key515, -2), (key515, -2), (key289, -2), (key513, 6), (key513, -2), (key513, -2), (key288, -2)]

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

def rawRow14853 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key984, -2), (key984, 6), (key1090, -2), (key1090, -2), (key1098, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1098, -2), (key1183, -2), (key1183, -2), (key1169, 6), (key1169, -2), (key1220, -2), (key1220, -2)]

def rawRow14854 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key976, -2), (key984, 6), (key1090, -2), (key1098, -2), (key1090, -2), (key1180, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1183, -2), (key1098, -2), (key1183, -2), (key1169, 6), (key1220, -2), (key1169, -2), (key1220, -2)]

def rawRow14855 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key976, -2), (key984, 6), (key1098, -2), (key1090, -2), (key1090, -2), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1183, -2), (key1183, -2), (key1098, -2), (key1169, 6), (key1220, -2), (key1220, -2), (key1169, -2)]

def rawRow14856 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key984, -2), (key976, 6), (key1180, -2), (key1183, -2), (key1183, -2), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1220, 6), (key1169, -2), (key1169, -2), (key1220, -2)]

def rawRow14857 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key984, -2), (key976, 6), (key1183, -2), (key1180, -2), (key1183, -2), (key1098, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1220, 6), (key1169, -2), (key1220, -2), (key1169, -2)]

def rawRow14858 : Integer.Sparse Key := [(key984, -2), (key984, -2), (key976, -2), (key976, 6), (key1183, -2), (key1183, -2), (key1180, -2), (key1183, 2), (key1183, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1220, 6), (key1220, -2), (key1169, -2), (key1169, -2)]

def rawRow14859 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1098, -2), (key1169, 6), (key976, -2), (key976, -2), (key984, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1169, -2), (key1220, -2), (key1220, -2), (key984, 6), (key1098, -2), (key1183, -2), (key1183, -2)]

def rawRow14860 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1090, -2), (key1169, 6), (key976, -2), (key984, -2), (key976, -2), (key1180, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1220, -2), (key1169, -2), (key1220, -2), (key984, 6), (key1183, -2), (key1098, -2), (key1183, -2)]

def rawRow14861 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1090, -2), (key1169, 6), (key984, -2), (key976, -2), (key976, -2), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1220, -2), (key1220, -2), (key1169, -2), (key984, 6), (key1183, -2), (key1183, -2), (key1098, -2)]

def rawRow14862 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1169, -2), (key1090, 6), (key1180, -2), (key1183, -2), (key1220, -2), (key976, 2), (key984, 2), (key1090, 2), (key1183, 2), (key1169, 2), (key1220, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1183, 6), (key984, -2), (key1098, -2), (key1183, -2)]

def rawRow14863 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1169, -2), (key1090, 6), (key1183, -2), (key1180, -2), (key1220, -2), (key984, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key1169, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1183, 6), (key984, -2), (key1183, -2), (key1098, -2)]

def rawRow14864 : Integer.Sparse Key := [(key1090, -2), (key1169, -2), (key1098, -2), (key1090, 6), (key1180, -2), (key1220, -2), (key1183, -2), (key1090, 2), (key1169, 2), (key976, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1183, 6), (key1098, -2), (key984, -2), (key1183, -2)]

def rawRow14865 : Integer.Sparse Key := [(key1169, -2), (key1090, -2), (key1098, -2), (key1090, 6), (key1220, -2), (key1180, -2), (key1183, -2), (key1169, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1183, 2), (key984, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1183, 6), (key1098, -2), (key1183, -2), (key984, -2)]

def rawRow14866 : Integer.Sparse Key := [(key1098, -2), (key1169, -2), (key1090, -2), (key1090, 6), (key1183, -2), (key1220, -2), (key1180, -2), (key1183, 2), (key1220, 2), (key984, 2), (key1169, 2), (key976, 2), (key1090, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1183, 6), (key1183, -2), (key984, -2), (key1098, -2)]

def rawRow14867 : Integer.Sparse Key := [(key1169, -2), (key1098, -2), (key1090, -2), (key1090, 6), (key1220, -2), (key1183, -2), (key1180, -2), (key1220, 2), (key1183, 2), (key1169, 2), (key984, 2), (key1090, 2), (key976, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1183, 6), (key1183, -2), (key1098, -2), (key984, -2)]

def rawRow14868 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1183, -2), (key1220, 6), (key976, -2), (key984, -2), (key984, -2), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1169, -2), (key1169, -2), (key1220, -2), (key976, 6), (key1090, -2), (key1090, -2), (key1180, -2)]

def rawRow14869 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1183, -2), (key1220, 6), (key984, -2), (key976, -2), (key984, -2), (key1098, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1169, -2), (key1220, -2), (key1169, -2), (key976, 6), (key1090, -2), (key1180, -2), (key1090, -2)]

def rawRow14870 : Integer.Sparse Key := [(key1183, -2), (key1183, -2), (key1180, -2), (key1220, 6), (key984, -2), (key984, -2), (key976, -2), (key1183, 2), (key1183, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1220, -2), (key1169, -2), (key1169, -2), (key976, 6), (key1180, -2), (key1090, -2), (key1090, -2)]

def rawRow14871 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1220, -2), (key1183, 6), (key1090, -2), (key1098, -2), (key1169, -2), (key976, 2), (key984, 2), (key1090, 2), (key1183, 2), (key1169, 2), (key1220, 2), (key984, -2), (key1098, -2), (key1183, -2), (key1090, 6), (key976, -2), (key1090, -2), (key1180, -2)]

def rawRow14872 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1220, -2), (key1183, 6), (key1098, -2), (key1090, -2), (key1169, -2), (key984, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key1169, 2), (key984, -2), (key1183, -2), (key1098, -2), (key1090, 6), (key976, -2), (key1180, -2), (key1090, -2)]

def rawRow14873 : Integer.Sparse Key := [(key1180, -2), (key1220, -2), (key1183, -2), (key1183, 6), (key1090, -2), (key1169, -2), (key1098, -2), (key1090, 2), (key1169, 2), (key976, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1098, -2), (key984, -2), (key1183, -2), (key1090, 6), (key1090, -2), (key976, -2), (key1180, -2)]

def rawRow14874 : Integer.Sparse Key := [(key1220, -2), (key1180, -2), (key1183, -2), (key1183, 6), (key1169, -2), (key1090, -2), (key1098, -2), (key1169, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1183, 2), (key984, 2), (key1098, -2), (key1183, -2), (key984, -2), (key1090, 6), (key1090, -2), (key1180, -2), (key976, -2)]

def rawRow14875 : Integer.Sparse Key := [(key1183, -2), (key1220, -2), (key1180, -2), (key1183, 6), (key1098, -2), (key1169, -2), (key1090, -2), (key1183, 2), (key1220, 2), (key984, 2), (key1169, 2), (key976, 2), (key1090, 2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, 6), (key1180, -2), (key976, -2), (key1090, -2)]

def rawRow14876 : Integer.Sparse Key := [(key1220, -2), (key1183, -2), (key1180, -2), (key1183, 6), (key1169, -2), (key1098, -2), (key1090, -2), (key1220, 2), (key1183, 2), (key1169, 2), (key984, 2), (key1090, 2), (key976, 2), (key1183, -2), (key1098, -2), (key984, -2), (key1090, 6), (key1180, -2), (key1090, -2), (key976, -2)]

def rawRow14877 : Integer.Sparse Key := [(key1183, -2), (key1183, -2), (key1220, -2), (key1180, 6), (key1183, -2), (key1183, -2), (key1220, -2), (key984, 2), (key984, 2), (key1098, 2), (key1098, 2), (key1169, 2), (key1169, 2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, 6), (key976, -2), (key1090, -2), (key1090, -2)]

def rawRow14878 : Integer.Sparse Key := [(key1183, -2), (key1220, -2), (key1183, -2), (key1180, 6), (key1183, -2), (key1220, -2), (key1183, -2), (key1098, 2), (key1169, 2), (key984, 2), (key1169, 2), (key984, 2), (key1098, 2), (key1090, -2), (key976, -2), (key1090, -2), (key1180, 6), (key1090, -2), (key976, -2), (key1090, -2)]

def rawRow14879 : Integer.Sparse Key := [(key1220, -2), (key1183, -2), (key1183, -2), (key1180, 6), (key1220, -2), (key1183, -2), (key1183, -2), (key1169, 2), (key1098, 2), (key1169, 2), (key984, 2), (key1098, 2), (key984, 2), (key1090, -2), (key1090, -2), (key976, -2), (key1180, 6), (key1090, -2), (key1090, -2), (key976, -2)]

def rawRow14880 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, -2), (key2366, 6), (key2456, -2), (key2456, -2), (key2461, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2461, -2), (key2523, -2), (key2523, -2), (key2567, 6), (key2567, -2), (key2579, -2), (key2579, -2)]

def rawRow14881 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2361, -2), (key2366, 6), (key2456, -2), (key2461, -2), (key2456, -2), (key2517, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2523, -2), (key2461, -2), (key2523, -2), (key2567, 6), (key2579, -2), (key2567, -2), (key2579, -2)]

def rawRow14882 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2361, -2), (key2366, 6), (key2461, -2), (key2456, -2), (key2456, -2), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2523, -2), (key2523, -2), (key2461, -2), (key2567, 6), (key2579, -2), (key2579, -2), (key2567, -2)]

def rawRow14883 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2363, -2), (key2361, 6), (key2517, -2), (key2523, -2), (key2523, -2), (key2456, 2), (key2461, 2), (key2456, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2579, 6), (key2567, -2), (key2567, -2), (key2579, -2)]

def rawRow14884 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2363, -2), (key2361, 6), (key2523, -2), (key2517, -2), (key2523, -2), (key2461, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2461, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2579, 6), (key2567, -2), (key2579, -2), (key2567, -2)]

def rawRow14885 : Integer.Sparse Key := [(key2363, -2), (key2363, -2), (key2357, -2), (key2361, 6), (key2523, -2), (key2523, -2), (key2517, -2), (key2523, 2), (key2523, 2), (key2461, 2), (key2461, 2), (key2456, 2), (key2456, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2579, 6), (key2579, -2), (key2567, -2), (key2567, -2)]

def rawRow14886 : Integer.Sparse Key := [(key2452, -2), (key2452, -2), (key2458, -2), (key2519, 6), (key2357, -2), (key2361, -2), (key2366, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2567, -2), (key2579, -2), (key2579, -2), (key2366, 6), (key2461, -2), (key2523, -2), (key2523, -2)]

def rawRow14887 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2452, -2), (key2519, 6), (key2357, -2), (key2363, -2), (key2361, -2), (key2517, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2579, -2), (key2567, -2), (key2579, -2), (key2366, 6), (key2523, -2), (key2461, -2), (key2523, -2)]

def rawRow14888 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2452, -2), (key2519, 6), (key2363, -2), (key2357, -2), (key2361, -2), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2579, -2), (key2579, -2), (key2567, -2), (key2366, 6), (key2523, -2), (key2523, -2), (key2461, -2)]

def rawRow14889 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2519, -2), (key2452, 6), (key2528, -2), (key2530, -2), (key2560, -2), (key2357, 2), (key2363, 2), (key2452, 2), (key2530, 2), (key2519, 2), (key2560, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2523, 6), (key2366, -2), (key2461, -2), (key2523, -2)]

def rawRow14890 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2519, -2), (key2452, 6), (key2530, -2), (key2528, -2), (key2560, -2), (key2363, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2519, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2523, 6), (key2366, -2), (key2523, -2), (key2461, -2)]

def rawRow14891 : Integer.Sparse Key := [(key2452, -2), (key2519, -2), (key2458, -2), (key2452, 6), (key2528, -2), (key2560, -2), (key2530, -2), (key2452, 2), (key2519, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2523, 6), (key2461, -2), (key2366, -2), (key2523, -2)]

def rawRow14892 : Integer.Sparse Key := [(key2519, -2), (key2452, -2), (key2458, -2), (key2452, 6), (key2560, -2), (key2528, -2), (key2530, -2), (key2519, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2363, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2523, 6), (key2461, -2), (key2523, -2), (key2366, -2)]

def rawRow14893 : Integer.Sparse Key := [(key2458, -2), (key2519, -2), (key2452, -2), (key2452, 6), (key2530, -2), (key2560, -2), (key2528, -2), (key2530, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2357, 2), (key2452, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2523, 6), (key2523, -2), (key2366, -2), (key2461, -2)]

def rawRow14894 : Integer.Sparse Key := [(key2519, -2), (key2458, -2), (key2452, -2), (key2452, 6), (key2560, -2), (key2530, -2), (key2528, -2), (key2560, 2), (key2530, 2), (key2519, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2523, 6), (key2523, -2), (key2461, -2), (key2366, -2)]

def rawRow14895 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2530, -2), (key2560, 6), (key2357, -2), (key2363, -2), (key2363, -2), (key2452, 2), (key2458, 2), (key2452, 2), (key2530, 2), (key2458, 2), (key2530, 2), (key2519, -2), (key2519, -2), (key2560, -2), (key2361, 6), (key2456, -2), (key2456, -2), (key2517, -2)]

def rawRow14896 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2530, -2), (key2560, 6), (key2363, -2), (key2357, -2), (key2363, -2), (key2458, 2), (key2452, 2), (key2530, 2), (key2452, 2), (key2530, 2), (key2458, 2), (key2519, -2), (key2560, -2), (key2519, -2), (key2361, 6), (key2456, -2), (key2517, -2), (key2456, -2)]

def rawRow14897 : Integer.Sparse Key := [(key2530, -2), (key2530, -2), (key2528, -2), (key2560, 6), (key2363, -2), (key2363, -2), (key2357, -2), (key2530, 2), (key2530, 2), (key2458, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2560, -2), (key2519, -2), (key2519, -2), (key2361, 6), (key2517, -2), (key2456, -2), (key2456, -2)]

def rawRow14898 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2560, -2), (key2530, 6), (key2452, -2), (key2458, -2), (key2519, -2), (key2357, 2), (key2363, 2), (key2452, 2), (key2530, 2), (key2519, 2), (key2560, 2), (key2363, -2), (key2458, -2), (key2530, -2), (key2456, 6), (key2361, -2), (key2456, -2), (key2517, -2)]

def rawRow14899 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2560, -2), (key2530, 6), (key2458, -2), (key2452, -2), (key2519, -2), (key2363, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2519, 2), (key2363, -2), (key2530, -2), (key2458, -2), (key2456, 6), (key2361, -2), (key2517, -2), (key2456, -2)]

def rawRow14900 : Integer.Sparse Key := [(key2528, -2), (key2560, -2), (key2530, -2), (key2530, 6), (key2452, -2), (key2519, -2), (key2458, -2), (key2452, 2), (key2519, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2458, -2), (key2363, -2), (key2530, -2), (key2456, 6), (key2456, -2), (key2361, -2), (key2517, -2)]

def rawRow14901 : Integer.Sparse Key := [(key2560, -2), (key2528, -2), (key2530, -2), (key2530, 6), (key2519, -2), (key2452, -2), (key2458, -2), (key2519, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2363, 2), (key2458, -2), (key2530, -2), (key2363, -2), (key2456, 6), (key2456, -2), (key2517, -2), (key2361, -2)]

def rawRow14902 : Integer.Sparse Key := [(key2530, -2), (key2560, -2), (key2528, -2), (key2530, 6), (key2458, -2), (key2519, -2), (key2452, -2), (key2530, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2357, 2), (key2452, 2), (key2530, -2), (key2363, -2), (key2458, -2), (key2456, 6), (key2517, -2), (key2361, -2), (key2456, -2)]

def rawRow14903 : Integer.Sparse Key := [(key2560, -2), (key2530, -2), (key2528, -2), (key2530, 6), (key2519, -2), (key2458, -2), (key2452, -2), (key2560, 2), (key2530, 2), (key2519, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2530, -2), (key2458, -2), (key2363, -2), (key2456, 6), (key2517, -2), (key2456, -2), (key2361, -2)]

def rawRow14904 : Integer.Sparse Key := [(key2530, -2), (key2530, -2), (key2560, -2), (key2528, 6), (key2530, -2), (key2530, -2), (key2560, -2), (key2363, 2), (key2363, 2), (key2458, 2), (key2458, 2), (key2519, 2), (key2519, 2), (key2357, -2), (key2452, -2), (key2452, -2), (key2517, 6), (key2361, -2), (key2456, -2), (key2456, -2)]

def rawRow14905 : Integer.Sparse Key := [(key2530, -2), (key2560, -2), (key2530, -2), (key2528, 6), (key2530, -2), (key2560, -2), (key2530, -2), (key2458, 2), (key2519, 2), (key2363, 2), (key2519, 2), (key2363, 2), (key2458, 2), (key2452, -2), (key2357, -2), (key2452, -2), (key2517, 6), (key2456, -2), (key2361, -2), (key2456, -2)]

def rawRow14906 : Integer.Sparse Key := [(key2560, -2), (key2530, -2), (key2530, -2), (key2528, 6), (key2560, -2), (key2530, -2), (key2530, -2), (key2519, 2), (key2458, 2), (key2519, 2), (key2363, 2), (key2458, 2), (key2363, 2), (key2452, -2), (key2452, -2), (key2357, -2), (key2517, 6), (key2456, -2), (key2456, -2), (key2361, -2)]

def rawRow14907 : Integer.Sparse Key := [(key2377, 6), (key2377, -2), (key2389, -2), (key2389, -2), (key2405, 6), (key2405, -2), (key2436, -2), (key2436, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2)]

def rawRow14908 : Integer.Sparse Key := [(key2377, 6), (key2389, -2), (key2377, -2), (key2389, -2), (key2405, 6), (key2436, -2), (key2405, -2), (key2436, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2502, -2), (key2471, -2), (key2502, -2), (key2502, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2502, 2)]

def rawRow14909 : Integer.Sparse Key := [(key2377, 6), (key2389, -2), (key2389, -2), (key2377, -2), (key2405, 6), (key2436, -2), (key2436, -2), (key2405, -2), (key2479, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2471, -2), (key2518, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2502, 2), (key2479, 2)]

def rawRow14910 : Integer.Sparse Key := [(key2389, 6), (key2377, -2), (key2377, -2), (key2389, -2), (key2436, 6), (key2405, -2), (key2405, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2471, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2479, 2), (key2502, 2)]

def rawRow14911 : Integer.Sparse Key := [(key2389, 6), (key2377, -2), (key2389, -2), (key2377, -2), (key2436, 6), (key2405, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2518, -2), (key2502, -2), (key2479, -2), (key2518, -2), (key2479, -2), (key2479, 2), (key2471, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2479, 2)]

def rawRow14912 : Integer.Sparse Key := [(key2389, 6), (key2389, -2), (key2377, -2), (key2377, -2), (key2436, 6), (key2436, -2), (key2405, -2), (key2405, -2), (key2518, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2479, -2), (key2479, -2), (key2502, 2), (key2502, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2471, 2)]

def rawRow14913 : Integer.Sparse Key := [(key2405, 6), (key2471, -2), (key2479, -2), (key2479, -2), (key2377, 6), (key2471, -2), (key2502, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2389, -2), (key2405, -2), (key2436, -2), (key2436, -2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2)]

def rawRow14914 : Integer.Sparse Key := [(key2405, 6), (key2479, -2), (key2471, -2), (key2479, -2), (key2377, 6), (key2502, -2), (key2471, -2), (key2502, -2), (key2389, -2), (key2377, -2), (key2389, -2), (key2436, -2), (key2405, -2), (key2436, -2), (key2502, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2502, 2)]

def rawRow14915 : Integer.Sparse Key := [(key2405, 6), (key2479, -2), (key2479, -2), (key2471, -2), (key2377, 6), (key2502, -2), (key2502, -2), (key2471, -2), (key2389, -2), (key2389, -2), (key2377, -2), (key2436, -2), (key2436, -2), (key2405, -2), (key2518, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2502, 2), (key2479, 2)]

def rawRow14916 : Integer.Sparse Key := [(key2479, 6), (key2405, -2), (key2471, -2), (key2479, -2), (key2502, 6), (key2377, -2), (key2471, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2518, -2), (key2377, 2), (key2389, 2), (key2405, 2), (key2436, 2), (key2479, 2), (key2502, 2)]

def rawRow14917 : Integer.Sparse Key := [(key2479, 6), (key2405, -2), (key2479, -2), (key2471, -2), (key2502, 6), (key2377, -2), (key2502, -2), (key2471, -2), (key2436, -2), (key2518, -2), (key2502, -2), (key2389, -2), (key2518, -2), (key2479, -2), (key2389, 2), (key2377, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2479, 2)]

def rawRow14918 : Integer.Sparse Key := [(key2479, 6), (key2471, -2), (key2405, -2), (key2479, -2), (key2502, 6), (key2471, -2), (key2377, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, -2), (key2389, -2), (key2518, -2), (key2405, 2), (key2479, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2436, 2)]

def rawRow14919 : Integer.Sparse Key := [(key2479, 6), (key2471, -2), (key2479, -2), (key2405, -2), (key2502, 6), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2479, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2436, 2), (key2389, 2)]

def rawRow14920 : Integer.Sparse Key := [(key2479, 6), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, 6), (key2502, -2), (key2377, -2), (key2471, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2436, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2377, 2), (key2405, 2)]

def rawRow14921 : Integer.Sparse Key := [(key2479, 6), (key2479, -2), (key2471, -2), (key2405, -2), (key2502, 6), (key2502, -2), (key2471, -2), (key2377, -2), (key2518, -2), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, -2), (key2389, -2), (key2502, 2), (key2436, 2), (key2479, 2), (key2389, 2), (key2405, 2), (key2377, 2)]

def rawRow14922 : Integer.Sparse Key := [(key2436, 6), (key2502, -2), (key2502, -2), (key2518, -2), (key2389, 6), (key2479, -2), (key2479, -2), (key2518, -2), (key2377, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2405, -2), (key2436, -2), (key2471, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2479, 2), (key2502, 2)]

def rawRow14923 : Integer.Sparse Key := [(key2436, 6), (key2502, -2), (key2518, -2), (key2502, -2), (key2389, 6), (key2479, -2), (key2518, -2), (key2479, -2), (key2377, -2), (key2389, -2), (key2377, -2), (key2405, -2), (key2436, -2), (key2405, -2), (key2479, 2), (key2471, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2479, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1425 : Integer.Sparse Key := [(key431, -1), (key427, -1), (key591, -1), (key427, -1), (key591, -1), (key431, -1), (key459, 2), (key608, 2), (key459, 2), (key380, 1), (key376, 1), (key566, 1), (key376, 1), (key566, 1), (key380, 1), (key482, -1), (key459, -1), (key608, -1), (key459, -1), (key608, -1), (key482, -1), (key380, -2), (key566, -2), (key380, -2), (key465, 1), (key431, 1), (key591, 1), (key431, 1), (key591, 1), (key465, 1)]

def rawRow1426 : Integer.Sparse Key := [(key591, -1), (key591, -1), (key431, -1), (key431, -1), (key427, -1), (key427, -1), (key608, 2), (key459, 2), (key459, 2), (key566, 1), (key566, 1), (key380, 1), (key380, 1), (key376, 1), (key376, 1), (key608, -1), (key608, -1), (key482, -1), (key482, -1), (key459, -1), (key459, -1), (key566, -2), (key380, -2), (key380, -2), (key591, 1), (key591, 1), (key465, 1), (key465, 1), (key431, 1), (key431, 1)]

def rawRow1427 : Integer.Sparse Key := [(key211, -1), (key211, -1), (key431, -1), (key431, -1), (key459, -1), (key459, -1), (key207, 2), (key427, 2), (key427, 2), (key216, 1), (key216, 1), (key465, 1), (key465, 1), (key482, 1), (key482, 1), (key207, -1), (key207, -1), (key376, -1), (key376, -1), (key427, -1), (key427, -1), (key216, -2), (key465, -2), (key465, -2), (key211, 1), (key211, 1), (key380, 1), (key380, 1), (key431, 1), (key431, 1)]

def rawRow1428 : Integer.Sparse Key := [(key431, -1), (key459, -1), (key211, -1), (key459, -1), (key211, -1), (key431, -1), (key427, 2), (key207, 2), (key427, 2), (key465, 1), (key482, 1), (key216, 1), (key482, 1), (key216, 1), (key465, 1), (key376, -1), (key427, -1), (key207, -1), (key427, -1), (key207, -1), (key376, -1), (key465, -2), (key216, -2), (key465, -2), (key380, 1), (key431, 1), (key211, 1), (key431, 1), (key211, 1), (key380, 1)]

def rawRow1429 : Integer.Sparse Key := [(key459, -1), (key431, -1), (key459, -1), (key211, -1), (key431, -1), (key211, -1), (key427, 2), (key427, 2), (key207, 2), (key482, 1), (key465, 1), (key482, 1), (key216, 1), (key465, 1), (key216, 1), (key427, -1), (key376, -1), (key427, -1), (key207, -1), (key376, -1), (key207, -1), (key465, -2), (key465, -2), (key216, -2), (key431, 1), (key380, 1), (key431, 1), (key211, 1), (key380, 1), (key211, 1)]

def rawRow1430 : Integer.Sparse Key := [(key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key482, 2), (key482, 2), (key482, 2), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key459, -1), (key459, -1), (key459, -1), (key459, -1), (key459, -1), (key459, -1), (key376, -2), (key376, -2), (key376, -2), (key427, 1), (key427, 1), (key427, 1), (key427, 1), (key427, 1), (key427, 1)]

def rawRow1431 : Integer.Sparse Key := [(key216, -1), (key216, -1), (key465, -1), (key465, -1), (key482, -1), (key482, -1), (key216, 2), (key465, 2), (key465, 2), (key211, 1), (key211, 1), (key431, 1), (key431, 1), (key459, 1), (key459, 1), (key211, -1), (key211, -1), (key380, -1), (key380, -1), (key431, -1), (key431, -1), (key207, -2), (key427, -2), (key427, -2), (key207, 1), (key207, 1), (key376, 1), (key376, 1), (key427, 1), (key427, 1)]

def rawRow1432 : Integer.Sparse Key := [(key465, -1), (key482, -1), (key216, -1), (key482, -1), (key216, -1), (key465, -1), (key465, 2), (key216, 2), (key465, 2), (key431, 1), (key459, 1), (key211, 1), (key459, 1), (key211, 1), (key431, 1), (key380, -1), (key431, -1), (key211, -1), (key431, -1), (key211, -1), (key380, -1), (key427, -2), (key207, -2), (key427, -2), (key376, 1), (key427, 1), (key207, 1), (key427, 1), (key207, 1), (key376, 1)]

def rawRow1433 : Integer.Sparse Key := [(key482, -1), (key465, -1), (key482, -1), (key216, -1), (key465, -1), (key216, -1), (key465, 2), (key465, 2), (key216, 2), (key459, 1), (key431, 1), (key459, 1), (key211, 1), (key431, 1), (key211, 1), (key431, -1), (key380, -1), (key431, -1), (key211, -1), (key380, -1), (key211, -1), (key427, -2), (key427, -2), (key207, -2), (key427, 1), (key376, 1), (key427, 1), (key207, 1), (key376, 1), (key207, 1)]

def rawRow1434 : Integer.Sparse Key := [(key1049, -2), (key1061, -2), (key1061, -2), (key1053, 2), (key1061, 2), (key1061, 2), (key1135, 2), (key1141, 2), (key1141, 2), (key1141, -6), (key1237, -2), (key1239, -2), (key1239, -2), (key1239, 6)]

def rawRow1435 : Integer.Sparse Key := [(key1061, -2), (key1049, -2), (key1061, -2), (key1061, 2), (key1053, 2), (key1061, 2), (key1141, 2), (key1135, 2), (key1141, 2), (key1141, -6), (key1239, -2), (key1237, -2), (key1239, -2), (key1239, 6)]

def rawRow1436 : Integer.Sparse Key := [(key1061, -2), (key1061, -2), (key1049, -2), (key1061, 2), (key1061, 2), (key1053, 2), (key1141, 2), (key1141, 2), (key1135, 2), (key1141, -6), (key1239, -2), (key1239, -2), (key1237, -2), (key1239, 6)]

def rawRow1437 : Integer.Sparse Key := [(key1053, -2), (key1053, -2), (key1053, -2), (key1049, 2), (key1049, 2), (key1049, 2), (key1141, 2), (key1141, 2), (key1141, 2), (key1135, -6), (key1239, -2), (key1239, -2), (key1239, -2), (key1237, 6)]

def rawRow1438 : Integer.Sparse Key := [(key1135, -2), (key1141, -2), (key1141, -2), (key1237, 2), (key1239, 2), (key1239, 2), (key1049, 2), (key1061, 2), (key1061, 2), (key1239, -6), (key1053, -2), (key1061, -2), (key1061, -2), (key1141, 6)]

def rawRow1439 : Integer.Sparse Key := [(key1141, -2), (key1135, -2), (key1141, -2), (key1239, 2), (key1237, 2), (key1239, 2), (key1061, 2), (key1049, 2), (key1061, 2), (key1239, -6), (key1061, -2), (key1053, -2), (key1061, -2), (key1141, 6)]

def rawRow1440 : Integer.Sparse Key := [(key1141, -2), (key1141, -2), (key1135, -2), (key1239, 2), (key1239, 2), (key1237, 2), (key1061, 2), (key1061, 2), (key1049, 2), (key1239, -6), (key1061, -2), (key1061, -2), (key1053, -2), (key1141, 6)]

def rawRow1441 : Integer.Sparse Key := [(key1053, -2), (key1053, -2), (key1237, -2), (key1049, 2), (key1049, 2), (key1135, 2), (key1061, 2), (key1061, 2), (key1239, 2), (key1049, -6), (key1061, -2), (key1061, -2), (key1141, -2), (key1053, 6)]

def rawRow1442 : Integer.Sparse Key := [(key1053, -2), (key1237, -2), (key1053, -2), (key1049, 2), (key1135, 2), (key1049, 2), (key1061, 2), (key1239, 2), (key1061, 2), (key1049, -6), (key1061, -2), (key1141, -2), (key1061, -2), (key1053, 6)]

def rawRow1443 : Integer.Sparse Key := [(key1237, -2), (key1053, -2), (key1053, -2), (key1135, 2), (key1049, 2), (key1049, 2), (key1239, 2), (key1061, 2), (key1061, 2), (key1049, -6), (key1141, -2), (key1061, -2), (key1061, -2), (key1053, 6)]

def rawRow1444 : Integer.Sparse Key := [(key1141, -2), (key1141, -2), (key1141, -2), (key1239, 2), (key1239, 2), (key1239, 2), (key1053, 2), (key1053, 2), (key1053, 2), (key1237, -6), (key1049, -2), (key1049, -2), (key1049, -2), (key1135, 6)]

def rawRow1445 : Integer.Sparse Key := [(key1061, -2), (key1061, -2), (key1239, -2), (key1061, 2), (key1061, 2), (key1141, 2), (key1053, 2), (key1053, 2), (key1237, 2), (key1053, -6), (key1049, -2), (key1049, -2), (key1135, -2), (key1049, 6)]

def rawRow1446 : Integer.Sparse Key := [(key1061, -2), (key1239, -2), (key1061, -2), (key1061, 2), (key1141, 2), (key1061, 2), (key1053, 2), (key1237, 2), (key1053, 2), (key1053, -6), (key1049, -2), (key1135, -2), (key1049, -2), (key1049, 6)]

def rawRow1447 : Integer.Sparse Key := [(key1239, -2), (key1061, -2), (key1061, -2), (key1141, 2), (key1061, 2), (key1061, 2), (key1237, 2), (key1053, 2), (key1053, 2), (key1053, -6), (key1135, -2), (key1049, -2), (key1049, -2), (key1049, 6)]

def rawRow1448 : Integer.Sparse Key := [(key207, -2), (key211, -2), (key211, -2), (key207, 1), (key211, 1), (key207, 1), (key216, 1), (key211, 1), (key216, 1), (key376, 2), (key380, 2), (key380, 2), (key376, -1), (key380, -1), (key376, -1), (key566, -1), (key380, -1), (key566, -1), (key427, -1), (key431, -1), (key427, -1), (key465, -1), (key431, -1), (key465, -1), (key427, 1), (key431, 1), (key427, 1), (key591, 1), (key431, 1), (key591, 1)]

def rawRow1449 : Integer.Sparse Key := [(key211, -2), (key207, -2), (key211, -2), (key211, 1), (key207, 1), (key216, 1), (key207, 1), (key216, 1), (key211, 1), (key380, 2), (key376, 2), (key380, 2), (key380, -1), (key376, -1), (key566, -1), (key376, -1), (key566, -1), (key380, -1), (key431, -1), (key427, -1), (key465, -1), (key427, -1), (key465, -1), (key431, -1), (key431, 1), (key427, 1), (key591, 1), (key427, 1), (key591, 1), (key431, 1)]

def rawRow1450 : Integer.Sparse Key := [(key211, -2), (key211, -2), (key207, -2), (key216, 1), (key216, 1), (key211, 1), (key211, 1), (key207, 1), (key207, 1), (key380, 2), (key380, 2), (key376, 2), (key566, -1), (key566, -1), (key380, -1), (key380, -1), (key376, -1), (key376, -1), (key465, -1), (key465, -1), (key431, -1), (key431, -1), (key427, -1), (key427, -1), (key591, 1), (key591, 1), (key431, 1), (key431, 1), (key427, 1), (key427, 1)]

def rawRow1451 : Integer.Sparse Key := [(key216, -2), (key216, -2), (key216, -2), (key211, 1), (key211, 1), (key211, 1), (key211, 1), (key211, 1), (key211, 1), (key566, 2), (key566, 2), (key566, 2), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key380, -1), (key591, -1), (key591, -1), (key591, -1), (key591, -1), (key591, -1), (key591, -1), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key465, 1), (key465, 1)]

def rawRow1452 : Integer.Sparse Key := [(key376, -2), (key380, -2), (key380, -2), (key427, 1), (key431, 1), (key427, 1), (key465, 1), (key431, 1), (key465, 1), (key207, 2), (key211, 2), (key211, 2), (key427, -1), (key431, -1), (key427, -1), (key591, -1), (key431, -1), (key591, -1), (key207, -1), (key211, -1), (key207, -1), (key216, -1), (key211, -1), (key216, -1), (key376, 1), (key380, 1), (key376, 1), (key566, 1), (key380, 1), (key566, 1)]

def rawRow1453 : Integer.Sparse Key := [(key380, -2), (key376, -2), (key380, -2), (key431, 1), (key427, 1), (key465, 1), (key427, 1), (key465, 1), (key431, 1), (key211, 2), (key207, 2), (key211, 2), (key431, -1), (key427, -1), (key591, -1), (key427, -1), (key591, -1), (key431, -1), (key211, -1), (key207, -1), (key216, -1), (key207, -1), (key216, -1), (key211, -1), (key380, 1), (key376, 1), (key566, 1), (key376, 1), (key566, 1), (key380, 1)]

def rawRow1454 : Integer.Sparse Key := [(key380, -2), (key380, -2), (key376, -2), (key465, 1), (key465, 1), (key431, 1), (key431, 1), (key427, 1), (key427, 1), (key211, 2), (key211, 2), (key207, 2), (key591, -1), (key591, -1), (key431, -1), (key431, -1), (key427, -1), (key427, -1), (key216, -1), (key216, -1), (key211, -1), (key211, -1), (key207, -1), (key207, -1), (key566, 1), (key566, 1), (key380, 1), (key380, 1), (key376, 1), (key376, 1)]

def rawRow1455 : Integer.Sparse Key := [(key465, -2), (key465, -2), (key482, -2), (key380, 1), (key380, 1), (key431, 1), (key431, 1), (key459, 1), (key459, 1), (key591, 2), (key591, 2), (key608, 2), (key211, -1), (key211, -1), (key431, -1), (key431, -1), (key459, -1), (key459, -1), (key566, -1), (key566, -1), (key591, -1), (key591, -1), (key608, -1), (key608, -1), (key216, 1), (key216, 1), (key465, 1), (key465, 1), (key482, 1), (key482, 1)]

def rawRow1456 : Integer.Sparse Key := [(key465, -2), (key482, -2), (key465, -2), (key431, 1), (key459, 1), (key380, 1), (key459, 1), (key380, 1), (key431, 1), (key591, 2), (key608, 2), (key591, 2), (key431, -1), (key459, -1), (key211, -1), (key459, -1), (key211, -1), (key431, -1), (key591, -1), (key608, -1), (key566, -1), (key608, -1), (key566, -1), (key591, -1), (key465, 1), (key482, 1), (key216, 1), (key482, 1), (key216, 1), (key465, 1)]

def rawRow1457 : Integer.Sparse Key := [(key482, -2), (key465, -2), (key465, -2), (key459, 1), (key431, 1), (key459, 1), (key380, 1), (key431, 1), (key380, 1), (key608, 2), (key591, 2), (key591, 2), (key459, -1), (key431, -1), (key459, -1), (key211, -1), (key431, -1), (key211, -1), (key608, -1), (key591, -1), (key608, -1), (key566, -1), (key591, -1), (key566, -1), (key482, 1), (key465, 1), (key482, 1), (key216, 1), (key465, 1), (key216, 1)]

def rawRow1458 : Integer.Sparse Key := [(key566, -2), (key566, -2), (key566, -2), (key591, 1), (key591, 1), (key591, 1), (key591, 1), (key591, 1), (key591, 1), (key216, 2), (key216, 2), (key216, 2), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key465, -1), (key211, -1), (key211, -1), (key211, -1), (key211, -1), (key211, -1), (key211, -1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1), (key380, 1)]

def rawRow1459 : Integer.Sparse Key := [(key591, -2), (key591, -2), (key608, -2), (key566, 1), (key566, 1), (key591, 1), (key591, 1), (key608, 1), (key608, 1), (key465, 2), (key465, 2), (key482, 2), (key216, -1), (key216, -1), (key465, -1), (key465, -1), (key482, -1), (key482, -1), (key380, -1), (key380, -1), (key431, -1), (key431, -1), (key459, -1), (key459, -1), (key211, 1), (key211, 1), (key431, 1), (key431, 1), (key459, 1), (key459, 1)]

def rawRow1460 : Integer.Sparse Key := [(key591, -2), (key608, -2), (key591, -2), (key591, 1), (key608, 1), (key566, 1), (key608, 1), (key566, 1), (key591, 1), (key465, 2), (key482, 2), (key465, 2), (key465, -1), (key482, -1), (key216, -1), (key482, -1), (key216, -1), (key465, -1), (key431, -1), (key459, -1), (key380, -1), (key459, -1), (key380, -1), (key431, -1), (key431, 1), (key459, 1), (key211, 1), (key459, 1), (key211, 1), (key431, 1)]

def rawRow1461 : Integer.Sparse Key := [(key608, -2), (key591, -2), (key591, -2), (key608, 1), (key591, 1), (key608, 1), (key566, 1), (key591, 1), (key566, 1), (key482, 2), (key465, 2), (key465, 2), (key482, -1), (key465, -1), (key482, -1), (key216, -1), (key465, -1), (key216, -1), (key459, -1), (key431, -1), (key459, -1), (key380, -1), (key431, -1), (key380, -1), (key459, 1), (key431, 1), (key459, 1), (key211, 1), (key431, 1), (key211, 1)]

def rawRow1462 : Integer.Sparse Key := [(key1, -2), (key4, -2), (key4, -2), (key4, 6), (key84, 2), (key87, 2), (key87, 2), (key87, -2), (key87, -2), (key148, -2), (key164, -6), (key164, 2), (key164, 2), (key184, 2)]

def rawRow1463 : Integer.Sparse Key := [(key4, -2), (key1, -2), (key4, -2), (key4, 6), (key87, 2), (key84, 2), (key87, 2), (key87, -2), (key148, -2), (key87, -2), (key164, -6), (key164, 2), (key184, 2), (key164, 2)]

def rawRow1464 : Integer.Sparse Key := [(key4, -2), (key4, -2), (key1, -2), (key4, 6), (key87, 2), (key87, 2), (key84, 2), (key148, -2), (key87, -2), (key87, -2), (key164, -6), (key184, 2), (key164, 2), (key164, 2)]

def rawRow1465 : Integer.Sparse Key := [(key4, -2), (key4, -2), (key4, -2), (key1, 6), (key148, 2), (key148, 2), (key148, 2), (key84, -2), (key84, -2), (key84, -2), (key184, -6), (key164, 2), (key164, 2), (key164, 2)]

def rawRow1466 : Integer.Sparse Key := [(key84, -2), (key87, -2), (key87, -2), (key148, 6), (key1, 2), (key4, 2), (key4, 2), (key164, -2), (key164, -2), (key184, -2), (key4, -6), (key87, 2), (key87, 2), (key148, 2)]

def rawRow1467 : Integer.Sparse Key := [(key87, -2), (key84, -2), (key87, -2), (key148, 6), (key4, 2), (key1, 2), (key4, 2), (key164, -2), (key184, -2), (key164, -2), (key4, -6), (key87, 2), (key148, 2), (key87, 2)]

def rawRow1468 : Integer.Sparse Key := [(key87, -2), (key87, -2), (key84, -2), (key148, 6), (key4, 2), (key4, 2), (key1, 2), (key184, -2), (key164, -2), (key164, -2), (key4, -6), (key148, 2), (key87, 2), (key87, 2)]

def rawRow1469 : Integer.Sparse Key := [(key87, -2), (key87, -2), (key148, -2), (key84, 6), (key164, 2), (key164, 2), (key184, 2), (key1, -2), (key84, -2), (key84, -2), (key148, -6), (key4, 2), (key87, 2), (key87, 2)]

def rawRow1470 : Integer.Sparse Key := [(key87, -2), (key148, -2), (key87, -2), (key84, 6), (key164, 2), (key184, 2), (key164, 2), (key84, -2), (key1, -2), (key84, -2), (key148, -6), (key87, 2), (key4, 2), (key87, 2)]

def rawRow1471 : Integer.Sparse Key := [(key148, -2), (key87, -2), (key87, -2), (key84, 6), (key184, 2), (key164, 2), (key164, 2), (key84, -2), (key84, -2), (key1, -2), (key148, -6), (key87, 2), (key87, 2), (key4, 2)]

def rawRow1472 : Integer.Sparse Key := [(key164, -2), (key164, -2), (key164, -2), (key184, 6), (key4, 2), (key4, 2), (key4, 2), (key148, -2), (key148, -2), (key148, -2), (key1, -6), (key84, 2), (key84, 2), (key84, 2)]

def rawRow1473 : Integer.Sparse Key := [(key164, -2), (key164, -2), (key184, -2), (key164, 6), (key87, 2), (key87, 2), (key148, 2), (key4, -2), (key87, -2), (key87, -2), (key84, -6), (key1, 2), (key84, 2), (key84, 2)]

def rawRow1474 : Integer.Sparse Key := [(key164, -2), (key184, -2), (key164, -2), (key164, 6), (key87, 2), (key148, 2), (key87, 2), (key87, -2), (key4, -2), (key87, -2), (key84, -6), (key84, 2), (key1, 2), (key84, 2)]

def rawRow1475 : Integer.Sparse Key := [(key184, -2), (key164, -2), (key164, -2), (key164, 6), (key148, 2), (key87, 2), (key87, 2), (key87, -2), (key87, -2), (key4, -2), (key84, -6), (key84, 2), (key84, 2), (key1, 2)]

def rawRow1476 : Integer.Sparse Key := [(key2672, -2), (key2749, -2), (key2749, -2), (key2675, 1), (key2675, 1), (key2730, 1), (key2730, 1), (key2751, 1), (key2751, 1), (key2787, 2), (key2906, 2), (key2906, 2), (key2797, -1), (key2797, -1), (key2833, -1), (key2833, -1), (key2915, -1), (key2915, -1), (key2940, -1), (key2940, -1), (key2985, -1), (key2985, -1), (key3001, -1), (key3001, -1), (key2945, 1), (key2945, 1), (key2962, 1), (key2962, 1), (key3004, 1), (key3004, 1)]

def rawRow1477 : Integer.Sparse Key := [(key2749, -2), (key2672, -2), (key2749, -2), (key2730, 1), (key2751, 1), (key2675, 1), (key2751, 1), (key2675, 1), (key2730, 1), (key2906, 2), (key2787, 2), (key2906, 2), (key2833, -1), (key2915, -1), (key2797, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2985, -1), (key3001, -1), (key2940, -1), (key3001, -1), (key2940, -1), (key2985, -1), (key2962, 1), (key3004, 1), (key2945, 1), (key3004, 1), (key2945, 1), (key2962, 1)]

def rawRow1478 : Integer.Sparse Key := [(key2749, -2), (key2749, -2), (key2672, -2), (key2751, 1), (key2730, 1), (key2751, 1), (key2675, 1), (key2730, 1), (key2675, 1), (key2906, 2), (key2906, 2), (key2787, 2), (key2915, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2797, -1), (key3001, -1), (key2985, -1), (key3001, -1), (key2940, -1), (key2985, -1), (key2940, -1), (key3004, 1), (key2962, 1), (key3004, 1), (key2945, 1), (key2962, 1), (key2945, 1)]

def rawRow1479 : Integer.Sparse Key := [(key2675, -2), (key2739, -2), (key2751, -2), (key2672, 1), (key2675, 1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, 1), (key2797, 2), (key2899, 2), (key2915, 2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, -1), (key2899, -1), (key2906, -1), (key2945, -1), (key2946, -1), (key2978, -1), (key2994, -1), (key2999, -1), (key3004, -1), (key2940, 1), (key2946, 1), (key2952, 1), (key2964, 1), (key2999, 1), (key3001, 1)]

def rawRow1480 : Integer.Sparse Key := [(key2675, -2), (key2751, -2), (key2739, -2), (key2675, 1), (key2672, 1), (key2730, 1), (key2707, 1), (key2749, 1), (key2739, 1), (key2797, 2), (key2915, 2), (key2899, 2), (key2797, -1), (key2787, -1), (key2833, -1), (key2810, -1), (key2906, -1), (key2899, -1), (key2946, -1), (key2945, -1), (key2994, -1), (key2978, -1), (key3004, -1), (key2999, -1), (key2946, 1), (key2940, 1), (key2964, 1), (key2952, 1), (key3001, 1), (key2999, 1)]

def rawRow1481 : Integer.Sparse Key := [(key2739, -2), (key2675, -2), (key2751, -2), (key2707, 1), (key2739, 1), (key2672, 1), (key2749, 1), (key2675, 1), (key2730, 1), (key2899, 2), (key2797, 2), (key2915, 2), (key2810, -1), (key2899, -1), (key2787, -1), (key2906, -1), (key2797, -1), (key2833, -1), (key2978, -1), (key2999, -1), (key2945, -1), (key3004, -1), (key2946, -1), (key2994, -1), (key2952, 1), (key2999, 1), (key2940, 1), (key3001, 1), (key2946, 1), (key2964, 1)]

def rawRow1482 : Integer.Sparse Key := [(key2739, -2), (key2751, -2), (key2675, -2), (key2739, 1), (key2707, 1), (key2749, 1), (key2672, 1), (key2730, 1), (key2675, 1), (key2899, 2), (key2915, 2), (key2797, 2), (key2899, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2833, -1), (key2797, -1), (key2999, -1), (key2978, -1), (key3004, -1), (key2945, -1), (key2994, -1), (key2946, -1), (key2999, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2964, 1), (key2946, 1)]

def rawRow1483 : Integer.Sparse Key := [(key2751, -2), (key2675, -2), (key2739, -2), (key2730, 1), (key2749, 1), (key2675, 1), (key2739, 1), (key2672, 1), (key2707, 1), (key2915, 2), (key2797, 2), (key2899, 2), (key2833, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2787, -1), (key2810, -1), (key2994, -1), (key3004, -1), (key2946, -1), (key2999, -1), (key2945, -1), (key2978, -1), (key2964, 1), (key3001, 1), (key2946, 1), (key2999, 1), (key2940, 1), (key2952, 1)]

def rawRow1484 : Integer.Sparse Key := [(key2751, -2), (key2739, -2), (key2675, -2), (key2749, 1), (key2730, 1), (key2739, 1), (key2675, 1), (key2707, 1), (key2672, 1), (key2915, 2), (key2899, 2), (key2797, 2), (key2906, -1), (key2833, -1), (key2899, -1), (key2797, -1), (key2810, -1), (key2787, -1), (key3004, -1), (key2994, -1), (key2999, -1), (key2946, -1), (key2978, -1), (key2945, -1), (key3001, 1), (key2964, 1), (key2999, 1), (key2946, 1), (key2952, 1), (key2940, 1)]

def rawRow1485 : Integer.Sparse Key := [(key2707, -2), (key2978, -2), (key2978, -2), (key2730, 1), (key2730, 1), (key2985, 1), (key2985, 1), (key2994, 1), (key2994, 1), (key2672, 2), (key2749, 2), (key2749, 2), (key2945, -1), (key2945, -1), (key2962, -1), (key2962, -1), (key3004, -1), (key3004, -1), (key2675, -1), (key2675, -1), (key2730, -1), (key2730, -1), (key2751, -1), (key2751, -1), (key2797, 1), (key2797, 1), (key2833, 1), (key2833, 1), (key2915, 1), (key2915, 1)]

def rawRow1486 : Integer.Sparse Key := [(key2978, -2), (key2707, -2), (key2978, -2), (key2985, 1), (key2994, 1), (key2730, 1), (key2994, 1), (key2730, 1), (key2985, 1), (key2749, 2), (key2672, 2), (key2749, 2), (key2962, -1), (key3004, -1), (key2945, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2730, -1), (key2751, -1), (key2675, -1), (key2751, -1), (key2675, -1), (key2730, -1), (key2833, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, 1), (key2833, 1)]

def rawRow1487 : Integer.Sparse Key := [(key2978, -2), (key2978, -2), (key2707, -2), (key2994, 1), (key2985, 1), (key2994, 1), (key2730, 1), (key2985, 1), (key2730, 1), (key2749, 2), (key2749, 2), (key2672, 2), (key3004, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2945, -1), (key2751, -1), (key2730, -1), (key2751, -1), (key2675, -1), (key2730, -1), (key2675, -1), (key2915, 1), (key2833, 1), (key2915, 1), (key2797, 1), (key2833, 1), (key2797, 1)]

def rawRow1488 : Integer.Sparse Key := [(key2739, -2), (key2899, -2), (key2999, -2), (key2749, 1), (key2751, 1), (key2906, 1), (key3001, 1), (key2915, 1), (key3004, 1), (key2675, 2), (key2797, 2), (key2946, 2), (key2730, -1), (key2751, -1), (key2833, -1), (key2964, -1), (key2915, -1), (key2994, -1), (key2672, -1), (key2675, -1), (key2707, -1), (key2730, -1), (key2739, -1), (key2749, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2833, 1), (key2899, 1), (key2906, 1)]

def rawRow1489 : Integer.Sparse Key := [(key2739, -2), (key2999, -2), (key2899, -2), (key2751, 1), (key2749, 1), (key3001, 1), (key2906, 1), (key3004, 1), (key2915, 1), (key2675, 2), (key2946, 2), (key2797, 2), (key2751, -1), (key2730, -1), (key2964, -1), (key2833, -1), (key2994, -1), (key2915, -1), (key2675, -1), (key2672, -1), (key2730, -1), (key2707, -1), (key2749, -1), (key2739, -1), (key2797, 1), (key2787, 1), (key2833, 1), (key2810, 1), (key2906, 1), (key2899, 1)]

def rawRow1490 : Integer.Sparse Key := [(key2899, -2), (key2739, -2), (key2999, -2), (key2906, 1), (key2915, 1), (key2749, 1), (key3004, 1), (key2751, 1), (key3001, 1), (key2797, 2), (key2675, 2), (key2946, 2), (key2833, -1), (key2915, -1), (key2730, -1), (key2994, -1), (key2751, -1), (key2964, -1), (key2707, -1), (key2739, -1), (key2672, -1), (key2749, -1), (key2675, -1), (key2730, -1), (key2810, 1), (key2899, 1), (key2787, 1), (key2906, 1), (key2797, 1), (key2833, 1)]

def rawRow1491 : Integer.Sparse Key := [(key2899, -2), (key2999, -2), (key2739, -2), (key2915, 1), (key2906, 1), (key3004, 1), (key2749, 1), (key3001, 1), (key2751, 1), (key2797, 2), (key2946, 2), (key2675, 2), (key2915, -1), (key2833, -1), (key2994, -1), (key2730, -1), (key2964, -1), (key2751, -1), (key2739, -1), (key2707, -1), (key2749, -1), (key2672, -1), (key2730, -1), (key2675, -1), (key2899, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2833, 1), (key2797, 1)]

def rawRow1492 : Integer.Sparse Key := [(key2999, -2), (key2739, -2), (key2899, -2), (key3001, 1), (key3004, 1), (key2751, 1), (key2915, 1), (key2749, 1), (key2906, 1), (key2946, 2), (key2675, 2), (key2797, 2), (key2964, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2730, -1), (key2833, -1), (key2730, -1), (key2749, -1), (key2675, -1), (key2739, -1), (key2672, -1), (key2707, -1), (key2833, 1), (key2906, 1), (key2797, 1), (key2899, 1), (key2787, 1), (key2810, 1)]

def rawRow1494 : Integer.Sparse Key := [(key1314, -6), (key1294, 2), (key1335, 2), (key1335, 2), (key1544, 6), (key1389, -2), (key1770, -2), (key1770, -2), (key1571, -2), (key1653, -2), (key1653, -2), (key1422, 2), (key1811, 2), (key1811, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined177_part2 : Sparse := [([1, 1, 0, -1, 1, 1, -2], 9)]

end MUB6.TaoCertificate

end OAI
end


