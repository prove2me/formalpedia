-- Prove2me | Definitions.Def_OAIQ106D161
-- name    : OAIQ106D161
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:46:54.155308+00:00
-- url     : https://prove2.me/theorems/f1ec6ea3-61e5-4daf-a38e-1a25c8265114
-- title:
--   Definitions bundle OAIQ106D161 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 714 declarations of OpenAI's Lean: 714 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow14924`, `OAI.MUB6.Certificate.GramRows.rawRow14925`, `OAI.MUB6.Certificate.GramRows.rawRow14926`, `OAI.MUB6.Certificate.GramRows.rawRow14927`, `OAI.MUB6.Certificate.GramRows.rawRow14928`, `OAI.MUB6.Certificate.GramRows.rawRow14929`, `OAI.MUB6.Certificate.GramRows.rawRow1493`, `OAI.MUB6.Certificate.GramRows.rawRow14930`, `OAI.MUB6.Certificate.GramRows.rawRow14931`, `OAI.MUB6.Certificate.GramRows.rawRow14932`, `OAI.MUB6.Certificate.GramRows.rawRow14933`, `OAI.MUB6.Certificate.GramRows.rawRow14934`, `OAI.MUB6.Certificate.GramRows.rawRow14935`, `OAI.MUB6.Certificate.GramRows.rawRow14936`, `OAI.MUB6.Certificate.GramRows.rawRow14937`, `OAI.MUB6.Certificate.GramRows.rawRow14938`, `OAI.MUB6.Certificate.GramRows.rawRow14939`, `OAI.MUB6.Certificate.GramRows.rawRow14940`, `OAI.MUB6.Certificate.GramRows.rawRow14941`, `OAI.MUB6.Certificate.GramRows.rawRow14942`, `OAI.MUB6.Certificate.GramRows.rawRow14943`, `OAI.MUB6.Certificate.GramRows.rawRow14944`, `OAI.MUB6.Certificate.GramRows.rawRow14945`, `OAI.MUB6.Certificate.GramRows.rawRow14946`, `OAI.MUB6.Certificate.GramRows.rawRow14947`, `OAI.MUB6.Certificate.GramRows.rawRow14948`, `OAI.MUB6.Certificate.GramRows.rawRow14949`, `OAI.MUB6.Certificate.GramRows.rawRow1495`, `OAI.MUB6.Certificate.GramRows.rawRow14950`, `OAI.MUB6.Certificate.GramRows.rawRow14951`, `OAI.MUB6.Certificate.GramRows.rawRow14952`, `OAI.MUB6.Certificate.GramRows.rawRow14953`, `OAI.MUB6.Certificate.GramRows.rawRow14954`, `OAI.MUB6.Certificate.GramRows.rawRow14955`, `OAI.MUB6.Certificate.GramRows.rawRow14956`, `OAI.MUB6.Certificate.GramRows.rawRow14957`, `OAI.MUB6.Certificate.GramRows.rawRow14958`, `OAI.MUB6.Certificate.GramRows.rawRow14959`, `OAI.MUB6.Certificate.GramRows.rawRow1496`, `OAI.MUB6.Certificate.GramRows.rawRow14960` and 674 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block1`, `MutuallyUnbiased_GramRows_Block140`, `MutuallyUnbiased_GramRows_Block141`, `MutuallyUnbiased_GramRows_Block142`, `MutuallyUnbiased_GramRows_Block143`, `MutuallyUnbiased_GramRows_Block144`, `MutuallyUnbiased_GramRows_Block145`, `MutuallyUnbiased_GramRows_Block146`, `MutuallyUnbiased_GramRows_Block147`, `MutuallyUnbiased_GramRows_Block148`, `MutuallyUnbiased_GramRows_Block35`, `MutuallyUnbiased_GramRows_Block36`, `MutuallyUnbiased_TaoCertificate_Merge34`.
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092` and `OAIQ106D140` of this split.
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

def rawRow150 : Integer.Sparse Key := [(key1569, -1), (key1575, -1), (key1593, 2), (key1542, 1), (key1548, 1), (key1633, -1), (key1689, -1), (key1556, -2), (key1624, 1), (key1683, 1), (key1420, 1), (key1426, 1), (key1444, -2), (key1312, -1), (key1318, -1), (key1633, 1), (key1926, 1), (key1326, 2), (key1624, -1), (key1920, -1), (key1387, -1), (key1393, -1), (key1444, 1), (key1480, 1), (key1292, 1), (key1298, 1), (key1593, -1), (key1911, -1), (key1326, -1), (key1354, -1), (key1556, 1), (key1899, 1), (key1393, 2), (key1426, -1), (key1472, -1), (key1298, -2), (key1575, 1), (key1903, 1), (key1318, 1), (key1351, 1), (key1548, -1), (key1896, -1)]

def rawRow151 : Integer.Sparse Key := [(key1575, -1), (key1569, -1), (key1593, 2), (key1548, 1), (key1542, 1), (key1689, -1), (key1633, -1), (key1556, -2), (key1683, 1), (key1624, 1), (key1426, 1), (key1420, 1), (key1444, -2), (key1318, -1), (key1312, -1), (key1926, 1), (key1633, 1), (key1326, 2), (key1920, -1), (key1624, -1), (key1393, -1), (key1387, -1), (key1480, 1), (key1444, 1), (key1298, 1), (key1292, 1), (key1911, -1), (key1593, -1), (key1354, -1), (key1326, -1), (key1899, 1), (key1556, 1), (key1393, 2), (key1472, -1), (key1426, -1), (key1298, -2), (key1903, 1), (key1575, 1), (key1351, 1), (key1318, 1), (key1896, -1), (key1548, -1)]

def rawRow152 : Integer.Sparse Key := [(key1575, -1), (key1593, -1), (key1569, 2), (key1681, 1), (key1689, 1), (key1542, -1), (key1618, -1), (key1683, -2), (key1556, 1), (key1624, 1), (key1426, 1), (key1444, 1), (key1420, -2), (key1918, -1), (key1926, -1), (key1312, 1), (key1618, 1), (key1920, 2), (key1326, -1), (key1624, -1), (key1472, -1), (key1480, -1), (key1387, 1), (key1420, 1), (key1903, 1), (key1911, 1), (key1292, -1), (key1569, -1), (key1899, -1), (key1920, -1), (key1354, 1), (key1683, 1), (key1472, 2), (key1393, -1), (key1426, -1), (key1903, -2), (key1298, 1), (key1575, 1), (key1896, 1), (key1918, 1), (key1351, -1), (key1681, -1)]

def rawRow153 : Integer.Sparse Key := [(key1593, -1), (key1575, -1), (key1569, 2), (key1689, 1), (key1681, 1), (key1618, -1), (key1542, -1), (key1683, -2), (key1624, 1), (key1556, 1), (key1444, 1), (key1426, 1), (key1420, -2), (key1926, -1), (key1918, -1), (key1618, 1), (key1312, 1), (key1920, 2), (key1624, -1), (key1326, -1), (key1480, -1), (key1472, -1), (key1420, 1), (key1387, 1), (key1911, 1), (key1903, 1), (key1569, -1), (key1292, -1), (key1920, -1), (key1899, -1), (key1683, 1), (key1354, 1), (key1472, 2), (key1426, -1), (key1393, -1), (key1903, -2), (key1575, 1), (key1298, 1), (key1918, 1), (key1896, 1), (key1681, -1), (key1351, -1)]

def rawRow154 : Integer.Sparse Key := [(key1681, -1), (key1683, -1), (key1689, 2), (key1548, 1), (key1556, 1), (key1593, -1), (key1633, -1), (key1542, -2), (key1569, 1), (key1618, 1), (key1918, 1), (key1920, 1), (key1926, -2), (key1318, -1), (key1326, -1), (key1444, 1), (key1633, 1), (key1312, 2), (key1420, -1), (key1618, -1), (key1896, -1), (key1899, -1), (key1911, 1), (key1926, 1), (key1351, 1), (key1354, 1), (key1480, -1), (key1689, -1), (key1292, -1), (key1312, -1), (key1387, 1), (key1542, 1), (key1896, 2), (key1903, -1), (key1918, -1), (key1351, -2), (key1472, 1), (key1681, 1), (key1298, 1), (key1318, 1), (key1393, -1), (key1548, -1)]

def rawRow155 : Integer.Sparse Key := [(key1683, -1), (key1681, -1), (key1689, 2), (key1556, 1), (key1548, 1), (key1633, -1), (key1593, -1), (key1542, -2), (key1618, 1), (key1569, 1), (key1920, 1), (key1918, 1), (key1926, -2), (key1326, -1), (key1318, -1), (key1633, 1), (key1444, 1), (key1312, 2), (key1618, -1), (key1420, -1), (key1899, -1), (key1896, -1), (key1926, 1), (key1911, 1), (key1354, 1), (key1351, 1), (key1689, -1), (key1480, -1), (key1312, -1), (key1292, -1), (key1542, 1), (key1387, 1), (key1896, 2), (key1918, -1), (key1903, -1), (key1351, -2), (key1681, 1), (key1472, 1), (key1318, 1), (key1298, 1), (key1548, -1), (key1393, -1)]

def rawRow156 : Integer.Sparse Key := [(key1681, -1), (key1689, -1), (key1683, 2), (key1575, 1), (key1593, 1), (key1556, -1), (key1624, -1), (key1569, -2), (key1542, 1), (key1618, 1), (key1918, 1), (key1926, 1), (key1920, -2), (key1426, -1), (key1444, -1), (key1326, 1), (key1624, 1), (key1420, 2), (key1312, -1), (key1618, -1), (key1903, -1), (key1911, -1), (key1899, 1), (key1920, 1), (key1472, 1), (key1480, 1), (key1354, -1), (key1683, -1), (key1387, -1), (key1420, -1), (key1292, 1), (key1569, 1), (key1903, 2), (key1896, -1), (key1918, -1), (key1472, -2), (key1351, 1), (key1681, 1), (key1393, 1), (key1426, 1), (key1298, -1), (key1575, -1)]

def rawRow157 : Integer.Sparse Key := [(key1689, -1), (key1681, -1), (key1683, 2), (key1593, 1), (key1575, 1), (key1624, -1), (key1556, -1), (key1569, -2), (key1618, 1), (key1542, 1), (key1926, 1), (key1918, 1), (key1920, -2), (key1444, -1), (key1426, -1), (key1624, 1), (key1326, 1), (key1420, 2), (key1618, -1), (key1312, -1), (key1911, -1), (key1903, -1), (key1920, 1), (key1899, 1), (key1480, 1), (key1472, 1), (key1683, -1), (key1354, -1), (key1420, -1), (key1387, -1), (key1569, 1), (key1292, 1), (key1903, 2), (key1918, -1), (key1896, -1), (key1472, -2), (key1681, 1), (key1351, 1), (key1426, 1), (key1393, 1), (key1575, -1), (key1298, -1)]

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

def rawRow14924 : Integer.Sparse Key := [(key2436, 6), (key2518, -2), (key2502, -2), (key2502, -2), (key2389, 6), (key2518, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2377, -2), (key2377, -2), (key2436, -2), (key2405, -2), (key2405, -2), (key2502, 2), (key2502, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2471, 2)]

def rawRow14925 : Integer.Sparse Key := [(key2502, 6), (key2436, -2), (key2502, -2), (key2518, -2), (key2479, 6), (key2389, -2), (key2479, -2), (key2518, -2), (key2405, -2), (key2471, -2), (key2479, -2), (key2377, -2), (key2471, -2), (key2502, -2), (key2377, 2), (key2389, 2), (key2405, 2), (key2436, 2), (key2479, 2), (key2502, 2)]

def rawRow14926 : Integer.Sparse Key := [(key2502, 6), (key2436, -2), (key2518, -2), (key2502, -2), (key2479, 6), (key2389, -2), (key2518, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2471, -2), (key2377, -2), (key2502, -2), (key2471, -2), (key2389, 2), (key2377, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2479, 2)]

def rawRow14927 : Integer.Sparse Key := [(key2502, 6), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, 6), (key2479, -2), (key2389, -2), (key2518, -2), (key2471, -2), (key2405, -2), (key2479, -2), (key2471, -2), (key2377, -2), (key2502, -2), (key2405, 2), (key2479, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2436, 2)]

def rawRow14928 : Integer.Sparse Key := [(key2502, 6), (key2502, -2), (key2518, -2), (key2436, -2), (key2479, 6), (key2479, -2), (key2518, -2), (key2389, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2479, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2436, 2), (key2389, 2)]

def rawRow14929 : Integer.Sparse Key := [(key2502, 6), (key2518, -2), (key2436, -2), (key2502, -2), (key2479, 6), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2436, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2377, 2), (key2405, 2)]

def rawRow14930 : Integer.Sparse Key := [(key2502, 6), (key2518, -2), (key2502, -2), (key2436, -2), (key2479, 6), (key2518, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2471, -2), (key2405, -2), (key2502, -2), (key2471, -2), (key2377, -2), (key2502, 2), (key2436, 2), (key2479, 2), (key2389, 2), (key2405, 2), (key2377, 2)]

def rawRow14931 : Integer.Sparse Key := [(key2518, 6), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, 6), (key2389, -2), (key2479, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2377, 2), (key2377, 2), (key2405, 2), (key2405, 2), (key2471, 2), (key2471, 2)]

def rawRow14932 : Integer.Sparse Key := [(key2518, 6), (key2502, -2), (key2436, -2), (key2502, -2), (key2518, 6), (key2479, -2), (key2389, -2), (key2479, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2405, 2), (key2471, 2), (key2377, 2), (key2471, 2), (key2377, 2), (key2405, 2)]

def rawRow14933 : Integer.Sparse Key := [(key2518, 6), (key2502, -2), (key2502, -2), (key2436, -2), (key2518, 6), (key2479, -2), (key2479, -2), (key2389, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2471, 2), (key2405, 2), (key2471, 2), (key2377, 2), (key2405, 2), (key2377, 2)]

def rawRow14934 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key983, -2), (key983, 6), (key1090, -2), (key1090, -2), (key1097, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1182, 2), (key1182, 2), (key1097, -2), (key1182, -2), (key1182, -2), (key1168, 6), (key1168, -2), (key1219, -2), (key1219, -2)]

def rawRow14935 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key976, -2), (key983, 6), (key1090, -2), (key1097, -2), (key1090, -2), (key1180, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1182, -2), (key1097, -2), (key1182, -2), (key1168, 6), (key1219, -2), (key1168, -2), (key1219, -2)]

def rawRow14936 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key976, -2), (key983, 6), (key1097, -2), (key1090, -2), (key1090, -2), (key1182, 2), (key1180, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1182, -2), (key1182, -2), (key1097, -2), (key1168, 6), (key1219, -2), (key1219, -2), (key1168, -2)]

def rawRow14937 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key983, -2), (key976, 6), (key1180, -2), (key1182, -2), (key1182, -2), (key1090, 2), (key1097, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1182, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1219, 6), (key1168, -2), (key1168, -2), (key1219, -2)]

def rawRow14938 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key983, -2), (key976, 6), (key1182, -2), (key1180, -2), (key1182, -2), (key1097, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1219, 6), (key1168, -2), (key1219, -2), (key1168, -2)]

def rawRow14939 : Integer.Sparse Key := [(key983, -2), (key983, -2), (key976, -2), (key976, 6), (key1182, -2), (key1182, -2), (key1180, -2), (key1182, 2), (key1182, 2), (key1097, 2), (key1097, 2), (key1090, 2), (key1090, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1219, 6), (key1219, -2), (key1168, -2), (key1168, -2)]

def rawRow14940 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1097, -2), (key1168, 6), (key976, -2), (key976, -2), (key983, -2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1182, 2), (key1182, 2), (key1168, -2), (key1219, -2), (key1219, -2), (key983, 6), (key1097, -2), (key1182, -2), (key1182, -2)]

def rawRow14941 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1090, -2), (key1168, 6), (key976, -2), (key983, -2), (key976, -2), (key1180, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1219, -2), (key1168, -2), (key1219, -2), (key983, 6), (key1182, -2), (key1097, -2), (key1182, -2)]

def rawRow14942 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1090, -2), (key1168, 6), (key983, -2), (key976, -2), (key976, -2), (key1182, 2), (key1180, 2), (key1182, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1219, -2), (key1219, -2), (key1168, -2), (key983, 6), (key1182, -2), (key1182, -2), (key1097, -2)]

def rawRow14943 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1168, -2), (key1090, 6), (key1180, -2), (key1182, -2), (key1219, -2), (key976, 2), (key983, 2), (key1090, 2), (key1182, 2), (key1168, 2), (key1219, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1182, 6), (key983, -2), (key1097, -2), (key1182, -2)]

def rawRow14944 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1168, -2), (key1090, 6), (key1182, -2), (key1180, -2), (key1219, -2), (key983, 2), (key976, 2), (key1182, 2), (key1090, 2), (key1219, 2), (key1168, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1182, 6), (key983, -2), (key1182, -2), (key1097, -2)]

def rawRow14945 : Integer.Sparse Key := [(key1090, -2), (key1168, -2), (key1097, -2), (key1090, 6), (key1180, -2), (key1219, -2), (key1182, -2), (key1090, 2), (key1168, 2), (key976, 2), (key1219, 2), (key983, 2), (key1182, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1182, 6), (key1097, -2), (key983, -2), (key1182, -2)]

def rawRow14946 : Integer.Sparse Key := [(key1168, -2), (key1090, -2), (key1097, -2), (key1090, 6), (key1219, -2), (key1180, -2), (key1182, -2), (key1168, 2), (key1090, 2), (key1219, 2), (key976, 2), (key1182, 2), (key983, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1182, 6), (key1097, -2), (key1182, -2), (key983, -2)]

def rawRow14947 : Integer.Sparse Key := [(key1097, -2), (key1168, -2), (key1090, -2), (key1090, 6), (key1182, -2), (key1219, -2), (key1180, -2), (key1182, 2), (key1219, 2), (key983, 2), (key1168, 2), (key976, 2), (key1090, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1182, 6), (key1182, -2), (key983, -2), (key1097, -2)]

def rawRow14948 : Integer.Sparse Key := [(key1168, -2), (key1097, -2), (key1090, -2), (key1090, 6), (key1219, -2), (key1182, -2), (key1180, -2), (key1219, 2), (key1182, 2), (key1168, 2), (key983, 2), (key1090, 2), (key976, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1182, 6), (key1182, -2), (key1097, -2), (key983, -2)]

def rawRow14949 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1182, -2), (key1219, 6), (key976, -2), (key983, -2), (key983, -2), (key1090, 2), (key1097, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1182, 2), (key1168, -2), (key1168, -2), (key1219, -2), (key976, 6), (key1090, -2), (key1090, -2), (key1180, -2)]

def rawRow14950 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1182, -2), (key1219, 6), (key983, -2), (key976, -2), (key983, -2), (key1097, 2), (key1090, 2), (key1182, 2), (key1090, 2), (key1182, 2), (key1097, 2), (key1168, -2), (key1219, -2), (key1168, -2), (key976, 6), (key1090, -2), (key1180, -2), (key1090, -2)]

def rawRow14951 : Integer.Sparse Key := [(key1182, -2), (key1182, -2), (key1180, -2), (key1219, 6), (key983, -2), (key983, -2), (key976, -2), (key1182, 2), (key1182, 2), (key1097, 2), (key1097, 2), (key1090, 2), (key1090, 2), (key1219, -2), (key1168, -2), (key1168, -2), (key976, 6), (key1180, -2), (key1090, -2), (key1090, -2)]

def rawRow14952 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1219, -2), (key1182, 6), (key1090, -2), (key1097, -2), (key1168, -2), (key976, 2), (key983, 2), (key1090, 2), (key1182, 2), (key1168, 2), (key1219, 2), (key983, -2), (key1097, -2), (key1182, -2), (key1090, 6), (key976, -2), (key1090, -2), (key1180, -2)]

def rawRow14953 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1219, -2), (key1182, 6), (key1097, -2), (key1090, -2), (key1168, -2), (key983, 2), (key976, 2), (key1182, 2), (key1090, 2), (key1219, 2), (key1168, 2), (key983, -2), (key1182, -2), (key1097, -2), (key1090, 6), (key976, -2), (key1180, -2), (key1090, -2)]

def rawRow14954 : Integer.Sparse Key := [(key1180, -2), (key1219, -2), (key1182, -2), (key1182, 6), (key1090, -2), (key1168, -2), (key1097, -2), (key1090, 2), (key1168, 2), (key976, 2), (key1219, 2), (key983, 2), (key1182, 2), (key1097, -2), (key983, -2), (key1182, -2), (key1090, 6), (key1090, -2), (key976, -2), (key1180, -2)]

def rawRow14955 : Integer.Sparse Key := [(key1219, -2), (key1180, -2), (key1182, -2), (key1182, 6), (key1168, -2), (key1090, -2), (key1097, -2), (key1168, 2), (key1090, 2), (key1219, 2), (key976, 2), (key1182, 2), (key983, 2), (key1097, -2), (key1182, -2), (key983, -2), (key1090, 6), (key1090, -2), (key1180, -2), (key976, -2)]

def rawRow14956 : Integer.Sparse Key := [(key1182, -2), (key1219, -2), (key1180, -2), (key1182, 6), (key1097, -2), (key1168, -2), (key1090, -2), (key1182, 2), (key1219, 2), (key983, 2), (key1168, 2), (key976, 2), (key1090, 2), (key1182, -2), (key983, -2), (key1097, -2), (key1090, 6), (key1180, -2), (key976, -2), (key1090, -2)]

def rawRow14957 : Integer.Sparse Key := [(key1219, -2), (key1182, -2), (key1180, -2), (key1182, 6), (key1168, -2), (key1097, -2), (key1090, -2), (key1219, 2), (key1182, 2), (key1168, 2), (key983, 2), (key1090, 2), (key976, 2), (key1182, -2), (key1097, -2), (key983, -2), (key1090, 6), (key1180, -2), (key1090, -2), (key976, -2)]

def rawRow14958 : Integer.Sparse Key := [(key1182, -2), (key1182, -2), (key1219, -2), (key1180, 6), (key1182, -2), (key1182, -2), (key1219, -2), (key983, 2), (key983, 2), (key1097, 2), (key1097, 2), (key1168, 2), (key1168, 2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, 6), (key976, -2), (key1090, -2), (key1090, -2)]

def rawRow14959 : Integer.Sparse Key := [(key1182, -2), (key1219, -2), (key1182, -2), (key1180, 6), (key1182, -2), (key1219, -2), (key1182, -2), (key1097, 2), (key1168, 2), (key983, 2), (key1168, 2), (key983, 2), (key1097, 2), (key1090, -2), (key976, -2), (key1090, -2), (key1180, 6), (key1090, -2), (key976, -2), (key1090, -2)]

def rawRow14960 : Integer.Sparse Key := [(key1219, -2), (key1182, -2), (key1182, -2), (key1180, 6), (key1219, -2), (key1182, -2), (key1182, -2), (key1168, 2), (key1097, 2), (key1168, 2), (key983, 2), (key1097, 2), (key983, 2), (key1090, -2), (key1090, -2), (key976, -2), (key1180, 6), (key1090, -2), (key1090, -2), (key976, -2)]

def rawRow14961 : Integer.Sparse Key := [(key1096, 4), (key1185, 4), (key1185, 4), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key1186, -2), (key1186, -2), (key1171, -2), (key1171, -2), (key1222, -2), (key1222, -2), (key1224, -2), (key1224, -2), (key1175, 4), (key1224, 4), (key1224, 4)]

def rawRow14962 : Integer.Sparse Key := [(key1185, 4), (key1096, 4), (key1185, 4), (key1185, -2), (key1186, -2), (key1100, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1224, 4), (key1175, 4), (key1224, 4)]

def rawRow14963 : Integer.Sparse Key := [(key1185, 4), (key1185, 4), (key1096, 4), (key1186, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1100, -2), (key1224, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1171, -2), (key1224, 4), (key1224, 4), (key1175, 4)]

def rawRow14964 : Integer.Sparse Key := [(key1100, 4), (key1100, 4), (key1186, 4), (key1096, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1185, -2), (key1171, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1224, -2), (key1171, 4), (key1171, 4), (key1222, 4)]

def rawRow14965 : Integer.Sparse Key := [(key1100, 4), (key1186, 4), (key1100, 4), (key1100, -2), (key1096, -2), (key1185, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1171, 4), (key1222, 4), (key1171, 4)]

def rawRow14966 : Integer.Sparse Key := [(key1186, 4), (key1100, 4), (key1100, 4), (key1185, -2), (key1185, -2), (key1100, -2), (key1100, -2), (key1096, -2), (key1096, -2), (key1224, -2), (key1224, -2), (key1175, -2), (key1175, -2), (key1171, -2), (key1171, -2), (key1222, 4), (key1171, 4), (key1171, 4)]

def rawRow14967 : Integer.Sparse Key := [(key1096, 4), (key1185, 4), (key1185, 4), (key1171, -2), (key1171, -2), (key1222, -2), (key1222, -2), (key1224, -2), (key1224, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key1186, -2), (key1186, -2), (key1175, 4), (key1224, 4), (key1224, 4)]

def rawRow14968 : Integer.Sparse Key := [(key1185, 4), (key1096, 4), (key1185, 4), (key1222, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1224, 4), (key1175, 4), (key1224, 4)]

def rawRow14969 : Integer.Sparse Key := [(key1185, 4), (key1185, 4), (key1096, 4), (key1224, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1171, -2), (key1186, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1100, -2), (key1224, 4), (key1224, 4), (key1175, 4)]

def rawRow14970 : Integer.Sparse Key := [(key986, 4), (key1171, 4), (key1224, 4), (key982, -2), (key986, -2), (key1096, -2), (key1185, -2), (key1171, -2), (key1222, -2), (key986, -2), (key988, -2), (key1100, -2), (key1186, -2), (key1175, -2), (key1224, -2), (key986, 4), (key1100, 4), (key1185, 4)]

def rawRow14971 : Integer.Sparse Key := [(key986, 4), (key1224, 4), (key1171, 4), (key986, -2), (key982, -2), (key1185, -2), (key1096, -2), (key1222, -2), (key1171, -2), (key988, -2), (key986, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key1175, -2), (key986, 4), (key1185, 4), (key1100, 4)]

def rawRow14972 : Integer.Sparse Key := [(key1171, 4), (key986, 4), (key1224, 4), (key1096, -2), (key1171, -2), (key982, -2), (key1222, -2), (key986, -2), (key1185, -2), (key1100, -2), (key1175, -2), (key986, -2), (key1224, -2), (key988, -2), (key1186, -2), (key1100, 4), (key986, 4), (key1185, 4)]

def rawRow14973 : Integer.Sparse Key := [(key1171, 4), (key1224, 4), (key986, 4), (key1171, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1185, -2), (key986, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1186, -2), (key988, -2), (key1100, 4), (key1185, 4), (key986, 4)]

def rawRow14974 : Integer.Sparse Key := [(key1224, 4), (key986, 4), (key1171, 4), (key1185, -2), (key1222, -2), (key986, -2), (key1171, -2), (key982, -2), (key1096, -2), (key1186, -2), (key1224, -2), (key988, -2), (key1175, -2), (key986, -2), (key1100, -2), (key1185, 4), (key986, 4), (key1100, 4)]

def rawRow14975 : Integer.Sparse Key := [(key1224, 4), (key1171, 4), (key986, 4), (key1222, -2), (key1185, -2), (key1171, -2), (key986, -2), (key1096, -2), (key982, -2), (key1224, -2), (key1186, -2), (key1175, -2), (key988, -2), (key1100, -2), (key986, -2), (key1185, 4), (key1100, 4), (key986, 4)]

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

def rawRow14976 : Integer.Sparse Key := [(key1100, 4), (key1100, 4), (key1186, 4), (key1171, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1224, -2), (key1096, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1185, -2), (key1171, 4), (key1171, 4), (key1222, 4)]

def rawRow14977 : Integer.Sparse Key := [(key1100, 4), (key1186, 4), (key1100, 4), (key1175, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1171, 4), (key1222, 4), (key1171, 4)]

def rawRow14978 : Integer.Sparse Key := [(key1186, 4), (key1100, 4), (key1100, 4), (key1224, -2), (key1224, -2), (key1175, -2), (key1175, -2), (key1171, -2), (key1171, -2), (key1185, -2), (key1185, -2), (key1100, -2), (key1100, -2), (key1096, -2), (key1096, -2), (key1222, 4), (key1171, 4), (key1171, 4)]

def rawRow14979 : Integer.Sparse Key := [(key986, 4), (key1171, 4), (key1224, 4), (key986, -2), (key988, -2), (key1100, -2), (key1186, -2), (key1175, -2), (key1224, -2), (key982, -2), (key986, -2), (key1096, -2), (key1185, -2), (key1171, -2), (key1222, -2), (key986, 4), (key1100, 4), (key1185, 4)]

def rawRow14980 : Integer.Sparse Key := [(key986, 4), (key1224, 4), (key1171, 4), (key988, -2), (key986, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key1175, -2), (key986, -2), (key982, -2), (key1185, -2), (key1096, -2), (key1222, -2), (key1171, -2), (key986, 4), (key1185, 4), (key1100, 4)]

def rawRow14981 : Integer.Sparse Key := [(key1171, 4), (key986, 4), (key1224, 4), (key1100, -2), (key1175, -2), (key986, -2), (key1224, -2), (key988, -2), (key1186, -2), (key1096, -2), (key1171, -2), (key982, -2), (key1222, -2), (key986, -2), (key1185, -2), (key1100, 4), (key986, 4), (key1185, 4)]

def rawRow14982 : Integer.Sparse Key := [(key1171, 4), (key1224, 4), (key986, 4), (key1175, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1186, -2), (key988, -2), (key1171, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1185, -2), (key986, -2), (key1100, 4), (key1185, 4), (key986, 4)]

def rawRow14983 : Integer.Sparse Key := [(key1224, 4), (key986, 4), (key1171, 4), (key1186, -2), (key1224, -2), (key988, -2), (key1175, -2), (key986, -2), (key1100, -2), (key1185, -2), (key1222, -2), (key986, -2), (key1171, -2), (key982, -2), (key1096, -2), (key1185, 4), (key986, 4), (key1100, 4)]

def rawRow14984 : Integer.Sparse Key := [(key1224, 4), (key1171, 4), (key986, 4), (key1224, -2), (key1186, -2), (key1175, -2), (key988, -2), (key1100, -2), (key986, -2), (key1222, -2), (key1185, -2), (key1171, -2), (key986, -2), (key1096, -2), (key982, -2), (key1185, 4), (key1100, 4), (key986, 4)]

def rawRow14985 : Integer.Sparse Key := [(key988, 4), (key1175, 4), (key1175, 4), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key1171, -2), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key1171, -2), (key982, 4), (key1096, 4), (key1096, 4)]

def rawRow14986 : Integer.Sparse Key := [(key1175, 4), (key988, 4), (key1175, 4), (key1100, -2), (key1171, -2), (key986, -2), (key1171, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1171, -2), (key986, -2), (key1100, -2), (key1096, 4), (key982, 4), (key1096, 4)]

def rawRow14987 : Integer.Sparse Key := [(key1175, 4), (key1175, 4), (key988, 4), (key1171, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1100, -2), (key986, -2), (key1171, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1100, -2), (key986, -2), (key1096, 4), (key1096, 4), (key982, 4)]

def rawRow15015 : Integer.Sparse Key := [(key2420, 4), (key2427, 4), (key2427, 4), (key2427, -4), (key2427, -4), (key2438, -4), (key2495, -4), (key2495, -4), (key2504, -4), (key2504, 12)]

def rawRow15016 : Integer.Sparse Key := [(key2427, 4), (key2420, 4), (key2427, 4), (key2427, -4), (key2438, -4), (key2427, -4), (key2495, -4), (key2504, -4), (key2495, -4), (key2504, 12)]

def rawRow15017 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2420, 4), (key2438, -4), (key2427, -4), (key2427, -4), (key2504, -4), (key2495, -4), (key2495, -4), (key2504, 12)]

def rawRow15018 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2438, 4), (key2420, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2504, -4), (key2504, -4), (key2495, 12)]

def rawRow15019 : Integer.Sparse Key := [(key2427, 4), (key2438, 4), (key2427, 4), (key2427, -4), (key2420, -4), (key2427, -4), (key2504, -4), (key2495, -4), (key2504, -4), (key2495, 12)]

def rawRow15020 : Integer.Sparse Key := [(key2438, 4), (key2427, 4), (key2427, 4), (key2427, -4), (key2427, -4), (key2420, -4), (key2504, -4), (key2504, -4), (key2495, -4), (key2495, 12)]

def rawRow15021 : Integer.Sparse Key := [(key2420, 4), (key2427, 4), (key2427, 4), (key2495, -4), (key2495, -4), (key2504, -4), (key2427, -4), (key2427, -4), (key2438, -4), (key2504, 12)]

def rawRow15022 : Integer.Sparse Key := [(key2427, 4), (key2420, 4), (key2427, 4), (key2495, -4), (key2504, -4), (key2495, -4), (key2427, -4), (key2438, -4), (key2427, -4), (key2504, 12)]

def rawRow15023 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2420, 4), (key2504, -4), (key2495, -4), (key2495, -4), (key2438, -4), (key2427, -4), (key2427, -4), (key2504, 12)]

def rawRow15024 : Integer.Sparse Key := [(key2427, 4), (key2495, 4), (key2504, 4), (key2420, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2438, -4), (key2504, -4), (key2427, 12)]

def rawRow15025 : Integer.Sparse Key := [(key2427, 4), (key2504, 4), (key2495, 4), (key2427, -4), (key2420, -4), (key2495, -4), (key2438, -4), (key2427, -4), (key2504, -4), (key2427, 12)]

def rawRow15026 : Integer.Sparse Key := [(key2495, 4), (key2427, 4), (key2504, 4), (key2420, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2504, -4), (key2438, -4), (key2427, 12)]

def rawRow15027 : Integer.Sparse Key := [(key2495, 4), (key2504, 4), (key2427, 4), (key2495, -4), (key2420, -4), (key2427, -4), (key2504, -4), (key2427, -4), (key2438, -4), (key2427, 12)]

def rawRow15028 : Integer.Sparse Key := [(key2504, 4), (key2427, 4), (key2495, 4), (key2427, -4), (key2495, -4), (key2420, -4), (key2438, -4), (key2504, -4), (key2427, -4), (key2427, 12)]

def rawRow15029 : Integer.Sparse Key := [(key2504, 4), (key2495, 4), (key2427, 4), (key2495, -4), (key2427, -4), (key2420, -4), (key2504, -4), (key2438, -4), (key2427, -4), (key2427, 12)]

def rawRow15030 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2438, 4), (key2495, -4), (key2504, -4), (key2504, -4), (key2420, -4), (key2427, -4), (key2427, -4), (key2495, 12)]

def rawRow15031 : Integer.Sparse Key := [(key2427, 4), (key2438, 4), (key2427, 4), (key2504, -4), (key2495, -4), (key2504, -4), (key2427, -4), (key2420, -4), (key2427, -4), (key2495, 12)]

def rawRow15032 : Integer.Sparse Key := [(key2438, 4), (key2427, 4), (key2427, 4), (key2504, -4), (key2504, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2420, -4), (key2495, 12)]

def rawRow15033 : Integer.Sparse Key := [(key2427, 4), (key2495, 4), (key2504, 4), (key2427, -4), (key2438, -4), (key2504, -4), (key2420, -4), (key2427, -4), (key2495, -4), (key2427, 12)]

def rawRow15034 : Integer.Sparse Key := [(key2427, 4), (key2504, 4), (key2495, 4), (key2438, -4), (key2427, -4), (key2504, -4), (key2427, -4), (key2420, -4), (key2495, -4), (key2427, 12)]

def rawRow15035 : Integer.Sparse Key := [(key2495, 4), (key2427, 4), (key2504, 4), (key2427, -4), (key2504, -4), (key2438, -4), (key2420, -4), (key2495, -4), (key2427, -4), (key2427, 12)]

def rawRow15036 : Integer.Sparse Key := [(key2495, 4), (key2504, 4), (key2427, 4), (key2504, -4), (key2427, -4), (key2438, -4), (key2495, -4), (key2420, -4), (key2427, -4), (key2427, 12)]

def rawRow15037 : Integer.Sparse Key := [(key2504, 4), (key2427, 4), (key2495, 4), (key2438, -4), (key2504, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2420, -4), (key2427, 12)]

def rawRow15038 : Integer.Sparse Key := [(key2504, 4), (key2495, 4), (key2427, 4), (key2504, -4), (key2438, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2420, -4), (key2427, 12)]

def rawRow15039 : Integer.Sparse Key := [(key2438, 4), (key2504, 4), (key2504, 4), (key2427, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2420, 12)]

def rawRow15040 : Integer.Sparse Key := [(key2504, 4), (key2438, 4), (key2504, 4), (key2427, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2420, 12)]

def rawRow15041 : Integer.Sparse Key := [(key2504, 4), (key2504, 4), (key2438, 4), (key2495, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2420, 12)]

def rawRow15042 : Integer.Sparse Key := [(key2361, -2), (key2361, -2), (key2364, -2), (key2364, 6), (key2456, -2), (key2456, -2), (key2459, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2459, -2), (key2520, -2), (key2520, -2), (key2531, 6), (key2531, -2), (key2561, -2), (key2561, -2)]

def rawRow15043 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2361, -2), (key2364, 6), (key2456, -2), (key2459, -2), (key2456, -2), (key2517, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2520, -2), (key2459, -2), (key2520, -2), (key2531, 6), (key2561, -2), (key2531, -2), (key2561, -2)]

def rawRow15044 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2361, -2), (key2364, 6), (key2459, -2), (key2456, -2), (key2456, -2), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2520, -2), (key2520, -2), (key2459, -2), (key2531, 6), (key2561, -2), (key2561, -2), (key2531, -2)]

def rawRow15045 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2364, -2), (key2361, 6), (key2517, -2), (key2520, -2), (key2520, -2), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2561, 6), (key2531, -2), (key2531, -2), (key2561, -2)]

def rawRow15046 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2364, -2), (key2361, 6), (key2520, -2), (key2517, -2), (key2520, -2), (key2459, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2561, 6), (key2531, -2), (key2561, -2), (key2531, -2)]

def rawRow15047 : Integer.Sparse Key := [(key2364, -2), (key2364, -2), (key2361, -2), (key2361, 6), (key2520, -2), (key2520, -2), (key2517, -2), (key2520, 2), (key2520, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2561, 6), (key2561, -2), (key2531, -2), (key2531, -2)]

def rawRow15048 : Integer.Sparse Key := [(key2456, -2), (key2456, -2), (key2459, -2), (key2531, 6), (key2361, -2), (key2361, -2), (key2364, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2531, -2), (key2561, -2), (key2561, -2), (key2364, 6), (key2459, -2), (key2520, -2), (key2520, -2)]

def rawRow15049 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2456, -2), (key2531, 6), (key2361, -2), (key2364, -2), (key2361, -2), (key2517, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2561, -2), (key2531, -2), (key2561, -2), (key2364, 6), (key2520, -2), (key2459, -2), (key2520, -2)]

def rawRow15050 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2456, -2), (key2531, 6), (key2364, -2), (key2361, -2), (key2361, -2), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2561, -2), (key2561, -2), (key2531, -2), (key2364, 6), (key2520, -2), (key2520, -2), (key2459, -2)]

def rawRow15051 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2531, -2), (key2456, 6), (key2517, -2), (key2520, -2), (key2561, -2), (key2361, 2), (key2364, 2), (key2456, 2), (key2520, 2), (key2531, 2), (key2561, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2520, 6), (key2364, -2), (key2459, -2), (key2520, -2)]

def rawRow15052 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2531, -2), (key2456, 6), (key2520, -2), (key2517, -2), (key2561, -2), (key2364, 2), (key2361, 2), (key2520, 2), (key2456, 2), (key2561, 2), (key2531, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2520, 6), (key2364, -2), (key2520, -2), (key2459, -2)]

def rawRow15053 : Integer.Sparse Key := [(key2456, -2), (key2531, -2), (key2459, -2), (key2456, 6), (key2517, -2), (key2561, -2), (key2520, -2), (key2456, 2), (key2531, 2), (key2361, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2520, 6), (key2459, -2), (key2364, -2), (key2520, -2)]

def rawRow15054 : Integer.Sparse Key := [(key2531, -2), (key2456, -2), (key2459, -2), (key2456, 6), (key2561, -2), (key2517, -2), (key2520, -2), (key2531, 2), (key2456, 2), (key2561, 2), (key2361, 2), (key2520, 2), (key2364, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2520, 6), (key2459, -2), (key2520, -2), (key2364, -2)]

def rawRow15055 : Integer.Sparse Key := [(key2459, -2), (key2531, -2), (key2456, -2), (key2456, 6), (key2520, -2), (key2561, -2), (key2517, -2), (key2520, 2), (key2561, 2), (key2364, 2), (key2531, 2), (key2361, 2), (key2456, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2520, 6), (key2520, -2), (key2364, -2), (key2459, -2)]

def rawRow15056 : Integer.Sparse Key := [(key2531, -2), (key2459, -2), (key2456, -2), (key2456, 6), (key2561, -2), (key2520, -2), (key2517, -2), (key2561, 2), (key2520, 2), (key2531, 2), (key2364, 2), (key2456, 2), (key2361, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2520, 6), (key2520, -2), (key2459, -2), (key2364, -2)]

def rawRow15057 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2520, -2), (key2561, 6), (key2361, -2), (key2364, -2), (key2364, -2), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2531, -2), (key2531, -2), (key2561, -2), (key2361, 6), (key2456, -2), (key2456, -2), (key2517, -2)]

def rawRow15058 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2520, -2), (key2561, 6), (key2364, -2), (key2361, -2), (key2364, -2), (key2459, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2531, -2), (key2561, -2), (key2531, -2), (key2361, 6), (key2456, -2), (key2517, -2), (key2456, -2)]

def rawRow15059 : Integer.Sparse Key := [(key2520, -2), (key2520, -2), (key2517, -2), (key2561, 6), (key2364, -2), (key2364, -2), (key2361, -2), (key2520, 2), (key2520, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2561, -2), (key2531, -2), (key2531, -2), (key2361, 6), (key2517, -2), (key2456, -2), (key2456, -2)]

def rawRow15060 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2561, -2), (key2520, 6), (key2456, -2), (key2459, -2), (key2531, -2), (key2361, 2), (key2364, 2), (key2456, 2), (key2520, 2), (key2531, 2), (key2561, 2), (key2364, -2), (key2459, -2), (key2520, -2), (key2456, 6), (key2361, -2), (key2456, -2), (key2517, -2)]

def rawRow15061 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2561, -2), (key2520, 6), (key2459, -2), (key2456, -2), (key2531, -2), (key2364, 2), (key2361, 2), (key2520, 2), (key2456, 2), (key2561, 2), (key2531, 2), (key2364, -2), (key2520, -2), (key2459, -2), (key2456, 6), (key2361, -2), (key2517, -2), (key2456, -2)]

def rawRow15062 : Integer.Sparse Key := [(key2517, -2), (key2561, -2), (key2520, -2), (key2520, 6), (key2456, -2), (key2531, -2), (key2459, -2), (key2456, 2), (key2531, 2), (key2361, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2459, -2), (key2364, -2), (key2520, -2), (key2456, 6), (key2456, -2), (key2361, -2), (key2517, -2)]

def rawRow15063 : Integer.Sparse Key := [(key2561, -2), (key2517, -2), (key2520, -2), (key2520, 6), (key2531, -2), (key2456, -2), (key2459, -2), (key2531, 2), (key2456, 2), (key2561, 2), (key2361, 2), (key2520, 2), (key2364, 2), (key2459, -2), (key2520, -2), (key2364, -2), (key2456, 6), (key2456, -2), (key2517, -2), (key2361, -2)]

def rawRow15064 : Integer.Sparse Key := [(key2520, -2), (key2561, -2), (key2517, -2), (key2520, 6), (key2459, -2), (key2531, -2), (key2456, -2), (key2520, 2), (key2561, 2), (key2364, 2), (key2531, 2), (key2361, 2), (key2456, 2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, 6), (key2517, -2), (key2361, -2), (key2456, -2)]

def rawRow15065 : Integer.Sparse Key := [(key2561, -2), (key2520, -2), (key2517, -2), (key2520, 6), (key2531, -2), (key2459, -2), (key2456, -2), (key2561, 2), (key2520, 2), (key2531, 2), (key2364, 2), (key2456, 2), (key2361, 2), (key2520, -2), (key2459, -2), (key2364, -2), (key2456, 6), (key2517, -2), (key2456, -2), (key2361, -2)]

def rawRow15066 : Integer.Sparse Key := [(key2520, -2), (key2520, -2), (key2561, -2), (key2517, 6), (key2520, -2), (key2520, -2), (key2561, -2), (key2364, 2), (key2364, 2), (key2459, 2), (key2459, 2), (key2531, 2), (key2531, 2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, 6), (key2361, -2), (key2456, -2), (key2456, -2)]

def rawRow15067 : Integer.Sparse Key := [(key2520, -2), (key2561, -2), (key2520, -2), (key2517, 6), (key2520, -2), (key2561, -2), (key2520, -2), (key2459, 2), (key2531, 2), (key2364, 2), (key2531, 2), (key2364, 2), (key2459, 2), (key2456, -2), (key2361, -2), (key2456, -2), (key2517, 6), (key2456, -2), (key2361, -2), (key2456, -2)]

def rawRow15068 : Integer.Sparse Key := [(key2561, -2), (key2520, -2), (key2520, -2), (key2517, 6), (key2561, -2), (key2520, -2), (key2520, -2), (key2531, 2), (key2459, 2), (key2531, 2), (key2364, 2), (key2459, 2), (key2364, 2), (key2456, -2), (key2456, -2), (key2361, -2), (key2517, 6), (key2456, -2), (key2456, -2), (key2361, -2)]

def rawRow15069 : Integer.Sparse Key := [(key1975, 4), (key1980, 4), (key1980, 4), (key1980, -4), (key1980, -4), (key1996, -4), (key2217, -4), (key2217, -4), (key2261, -4), (key2261, 12)]

def rawRow15070 : Integer.Sparse Key := [(key1980, 4), (key1975, 4), (key1980, 4), (key1980, -4), (key1996, -4), (key1980, -4), (key2217, -4), (key2261, -4), (key2217, -4), (key2261, 12)]

def rawRow15071 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1975, 4), (key1996, -4), (key1980, -4), (key1980, -4), (key2261, -4), (key2217, -4), (key2217, -4), (key2261, 12)]

def rawRow15072 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1996, 4), (key1975, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key2261, -4), (key2261, -4), (key2217, 12)]

def rawRow15073 : Integer.Sparse Key := [(key1980, 4), (key1996, 4), (key1980, 4), (key1980, -4), (key1975, -4), (key1980, -4), (key2261, -4), (key2217, -4), (key2261, -4), (key2217, 12)]

def rawRow15074 : Integer.Sparse Key := [(key1996, 4), (key1980, 4), (key1980, 4), (key1980, -4), (key1980, -4), (key1975, -4), (key2261, -4), (key2261, -4), (key2217, -4), (key2217, 12)]

def rawRow15075 : Integer.Sparse Key := [(key1975, 4), (key1980, 4), (key1980, 4), (key2217, -4), (key2217, -4), (key2261, -4), (key1980, -4), (key1980, -4), (key1996, -4), (key2261, 12)]

def rawRow15076 : Integer.Sparse Key := [(key1980, 4), (key1975, 4), (key1980, 4), (key2217, -4), (key2261, -4), (key2217, -4), (key1980, -4), (key1996, -4), (key1980, -4), (key2261, 12)]

def rawRow15077 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1975, 4), (key2261, -4), (key2217, -4), (key2217, -4), (key1996, -4), (key1980, -4), (key1980, -4), (key2261, 12)]

def rawRow15078 : Integer.Sparse Key := [(key1980, 4), (key2217, 4), (key2261, 4), (key1975, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1996, -4), (key2261, -4), (key1980, 12)]

def rawRow15079 : Integer.Sparse Key := [(key1980, 4), (key2261, 4), (key2217, 4), (key1980, -4), (key1975, -4), (key2217, -4), (key1996, -4), (key1980, -4), (key2261, -4), (key1980, 12)]

def rawRow15080 : Integer.Sparse Key := [(key2217, 4), (key1980, 4), (key2261, 4), (key1975, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key2261, -4), (key1996, -4), (key1980, 12)]

def rawRow15081 : Integer.Sparse Key := [(key2217, 4), (key2261, 4), (key1980, 4), (key2217, -4), (key1975, -4), (key1980, -4), (key2261, -4), (key1980, -4), (key1996, -4), (key1980, 12)]

def rawRow15082 : Integer.Sparse Key := [(key2261, 4), (key1980, 4), (key2217, 4), (key1980, -4), (key2217, -4), (key1975, -4), (key1996, -4), (key2261, -4), (key1980, -4), (key1980, 12)]

def rawRow15083 : Integer.Sparse Key := [(key2261, 4), (key2217, 4), (key1980, 4), (key2217, -4), (key1980, -4), (key1975, -4), (key2261, -4), (key1996, -4), (key1980, -4), (key1980, 12)]

def rawRow15084 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1996, 4), (key2217, -4), (key2261, -4), (key2261, -4), (key1975, -4), (key1980, -4), (key1980, -4), (key2217, 12)]

def rawRow15085 : Integer.Sparse Key := [(key1980, 4), (key1996, 4), (key1980, 4), (key2261, -4), (key2217, -4), (key2261, -4), (key1980, -4), (key1975, -4), (key1980, -4), (key2217, 12)]

def rawRow15086 : Integer.Sparse Key := [(key1996, 4), (key1980, 4), (key1980, 4), (key2261, -4), (key2261, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key1975, -4), (key2217, 12)]

def rawRow15087 : Integer.Sparse Key := [(key1980, 4), (key2217, 4), (key2261, 4), (key1980, -4), (key1996, -4), (key2261, -4), (key1975, -4), (key1980, -4), (key2217, -4), (key1980, 12)]

def rawRow15088 : Integer.Sparse Key := [(key1980, 4), (key2261, 4), (key2217, 4), (key1996, -4), (key1980, -4), (key2261, -4), (key1980, -4), (key1975, -4), (key2217, -4), (key1980, 12)]

def rawRow15089 : Integer.Sparse Key := [(key2217, 4), (key1980, 4), (key2261, 4), (key1980, -4), (key2261, -4), (key1996, -4), (key1975, -4), (key2217, -4), (key1980, -4), (key1980, 12)]

def rawRow15090 : Integer.Sparse Key := [(key2217, 4), (key2261, 4), (key1980, 4), (key2261, -4), (key1980, -4), (key1996, -4), (key2217, -4), (key1975, -4), (key1980, -4), (key1980, 12)]

def rawRow15091 : Integer.Sparse Key := [(key2261, 4), (key1980, 4), (key2217, 4), (key1996, -4), (key2261, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1975, -4), (key1980, 12)]

def rawRow15092 : Integer.Sparse Key := [(key2261, 4), (key2217, 4), (key1980, 4), (key2261, -4), (key1996, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1975, -4), (key1980, 12)]

def rawRow15093 : Integer.Sparse Key := [(key1996, 4), (key2261, 4), (key2261, 4), (key1980, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1975, 12)]

def rawRow15094 : Integer.Sparse Key := [(key2261, 4), (key1996, 4), (key2261, 4), (key1980, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1975, 12)]

def rawRow15095 : Integer.Sparse Key := [(key2261, 4), (key2261, 4), (key1996, 4), (key2217, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key1975, 12)]

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

def rawRow15123 : Integer.Sparse Key := [(key1277, -2), (key1277, -2), (key1283, -2), (key1283, 6), (key1700, -2), (key1700, -2), (key1706, -2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1855, 2), (key1855, 2), (key1706, -2), (key1855, -2), (key1855, -2), (key1756, 6), (key1756, -2), (key1886, -2), (key1886, -2)]

def rawRow15124 : Integer.Sparse Key := [(key1277, -2), (key1283, -2), (key1277, -2), (key1283, 6), (key1700, -2), (key1706, -2), (key1700, -2), (key1851, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1855, -2), (key1706, -2), (key1855, -2), (key1756, 6), (key1886, -2), (key1756, -2), (key1886, -2)]

def rawRow15125 : Integer.Sparse Key := [(key1283, -2), (key1277, -2), (key1277, -2), (key1283, 6), (key1706, -2), (key1700, -2), (key1700, -2), (key1855, 2), (key1851, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1700, 2), (key1855, -2), (key1855, -2), (key1706, -2), (key1756, 6), (key1886, -2), (key1886, -2), (key1756, -2)]

def rawRow15126 : Integer.Sparse Key := [(key1277, -2), (key1283, -2), (key1283, -2), (key1277, 6), (key1851, -2), (key1855, -2), (key1855, -2), (key1700, 2), (key1706, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1855, 2), (key1700, -2), (key1700, -2), (key1851, -2), (key1886, 6), (key1756, -2), (key1756, -2), (key1886, -2)]

def rawRow15127 : Integer.Sparse Key := [(key1283, -2), (key1277, -2), (key1283, -2), (key1277, 6), (key1855, -2), (key1851, -2), (key1855, -2), (key1706, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1700, -2), (key1851, -2), (key1700, -2), (key1886, 6), (key1756, -2), (key1886, -2), (key1756, -2)]

def rawRow15128 : Integer.Sparse Key := [(key1283, -2), (key1283, -2), (key1277, -2), (key1277, 6), (key1855, -2), (key1855, -2), (key1851, -2), (key1855, 2), (key1855, 2), (key1706, 2), (key1706, 2), (key1700, 2), (key1700, 2), (key1851, -2), (key1700, -2), (key1700, -2), (key1886, 6), (key1886, -2), (key1756, -2), (key1756, -2)]

def rawRow15129 : Integer.Sparse Key := [(key1700, -2), (key1700, -2), (key1706, -2), (key1756, 6), (key1277, -2), (key1277, -2), (key1283, -2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1855, 2), (key1855, 2), (key1756, -2), (key1886, -2), (key1886, -2), (key1283, 6), (key1706, -2), (key1855, -2), (key1855, -2)]

def rawRow15130 : Integer.Sparse Key := [(key1700, -2), (key1706, -2), (key1700, -2), (key1756, 6), (key1277, -2), (key1283, -2), (key1277, -2), (key1851, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1886, -2), (key1756, -2), (key1886, -2), (key1283, 6), (key1855, -2), (key1706, -2), (key1855, -2)]

def rawRow15131 : Integer.Sparse Key := [(key1706, -2), (key1700, -2), (key1700, -2), (key1756, 6), (key1283, -2), (key1277, -2), (key1277, -2), (key1855, 2), (key1851, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1700, 2), (key1886, -2), (key1886, -2), (key1756, -2), (key1283, 6), (key1855, -2), (key1855, -2), (key1706, -2)]

def rawRow15132 : Integer.Sparse Key := [(key1700, -2), (key1706, -2), (key1756, -2), (key1700, 6), (key1851, -2), (key1855, -2), (key1886, -2), (key1277, 2), (key1283, 2), (key1700, 2), (key1855, 2), (key1756, 2), (key1886, 2), (key1277, -2), (key1700, -2), (key1851, -2), (key1855, 6), (key1283, -2), (key1706, -2), (key1855, -2)]

def rawRow15133 : Integer.Sparse Key := [(key1706, -2), (key1700, -2), (key1756, -2), (key1700, 6), (key1855, -2), (key1851, -2), (key1886, -2), (key1283, 2), (key1277, 2), (key1855, 2), (key1700, 2), (key1886, 2), (key1756, 2), (key1277, -2), (key1851, -2), (key1700, -2), (key1855, 6), (key1283, -2), (key1855, -2), (key1706, -2)]

def rawRow15134 : Integer.Sparse Key := [(key1700, -2), (key1756, -2), (key1706, -2), (key1700, 6), (key1851, -2), (key1886, -2), (key1855, -2), (key1700, 2), (key1756, 2), (key1277, 2), (key1886, 2), (key1283, 2), (key1855, 2), (key1700, -2), (key1277, -2), (key1851, -2), (key1855, 6), (key1706, -2), (key1283, -2), (key1855, -2)]

def rawRow15135 : Integer.Sparse Key := [(key1756, -2), (key1700, -2), (key1706, -2), (key1700, 6), (key1886, -2), (key1851, -2), (key1855, -2), (key1756, 2), (key1700, 2), (key1886, 2), (key1277, 2), (key1855, 2), (key1283, 2), (key1700, -2), (key1851, -2), (key1277, -2), (key1855, 6), (key1706, -2), (key1855, -2), (key1283, -2)]

def rawRow15136 : Integer.Sparse Key := [(key1706, -2), (key1756, -2), (key1700, -2), (key1700, 6), (key1855, -2), (key1886, -2), (key1851, -2), (key1855, 2), (key1886, 2), (key1283, 2), (key1756, 2), (key1277, 2), (key1700, 2), (key1851, -2), (key1277, -2), (key1700, -2), (key1855, 6), (key1855, -2), (key1283, -2), (key1706, -2)]

def rawRow15137 : Integer.Sparse Key := [(key1756, -2), (key1706, -2), (key1700, -2), (key1700, 6), (key1886, -2), (key1855, -2), (key1851, -2), (key1886, 2), (key1855, 2), (key1756, 2), (key1283, 2), (key1700, 2), (key1277, 2), (key1851, -2), (key1700, -2), (key1277, -2), (key1855, 6), (key1855, -2), (key1706, -2), (key1283, -2)]

def rawRow15138 : Integer.Sparse Key := [(key1851, -2), (key1855, -2), (key1855, -2), (key1886, 6), (key1277, -2), (key1283, -2), (key1283, -2), (key1700, 2), (key1706, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1855, 2), (key1756, -2), (key1756, -2), (key1886, -2), (key1277, 6), (key1700, -2), (key1700, -2), (key1851, -2)]

def rawRow15139 : Integer.Sparse Key := [(key1855, -2), (key1851, -2), (key1855, -2), (key1886, 6), (key1283, -2), (key1277, -2), (key1283, -2), (key1706, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1756, -2), (key1886, -2), (key1756, -2), (key1277, 6), (key1700, -2), (key1851, -2), (key1700, -2)]

def rawRow15140 : Integer.Sparse Key := [(key1855, -2), (key1855, -2), (key1851, -2), (key1886, 6), (key1283, -2), (key1283, -2), (key1277, -2), (key1855, 2), (key1855, 2), (key1706, 2), (key1706, 2), (key1700, 2), (key1700, 2), (key1886, -2), (key1756, -2), (key1756, -2), (key1277, 6), (key1851, -2), (key1700, -2), (key1700, -2)]

def rawRow15141 : Integer.Sparse Key := [(key1851, -2), (key1855, -2), (key1886, -2), (key1855, 6), (key1700, -2), (key1706, -2), (key1756, -2), (key1277, 2), (key1283, 2), (key1700, 2), (key1855, 2), (key1756, 2), (key1886, 2), (key1283, -2), (key1706, -2), (key1855, -2), (key1700, 6), (key1277, -2), (key1700, -2), (key1851, -2)]

def rawRow15142 : Integer.Sparse Key := [(key1855, -2), (key1851, -2), (key1886, -2), (key1855, 6), (key1706, -2), (key1700, -2), (key1756, -2), (key1283, 2), (key1277, 2), (key1855, 2), (key1700, 2), (key1886, 2), (key1756, 2), (key1283, -2), (key1855, -2), (key1706, -2), (key1700, 6), (key1277, -2), (key1851, -2), (key1700, -2)]

def rawRow15143 : Integer.Sparse Key := [(key1851, -2), (key1886, -2), (key1855, -2), (key1855, 6), (key1700, -2), (key1756, -2), (key1706, -2), (key1700, 2), (key1756, 2), (key1277, 2), (key1886, 2), (key1283, 2), (key1855, 2), (key1706, -2), (key1283, -2), (key1855, -2), (key1700, 6), (key1700, -2), (key1277, -2), (key1851, -2)]

def rawRow15144 : Integer.Sparse Key := [(key1886, -2), (key1851, -2), (key1855, -2), (key1855, 6), (key1756, -2), (key1700, -2), (key1706, -2), (key1756, 2), (key1700, 2), (key1886, 2), (key1277, 2), (key1855, 2), (key1283, 2), (key1706, -2), (key1855, -2), (key1283, -2), (key1700, 6), (key1700, -2), (key1851, -2), (key1277, -2)]

def rawRow15145 : Integer.Sparse Key := [(key1855, -2), (key1886, -2), (key1851, -2), (key1855, 6), (key1706, -2), (key1756, -2), (key1700, -2), (key1855, 2), (key1886, 2), (key1283, 2), (key1756, 2), (key1277, 2), (key1700, 2), (key1855, -2), (key1283, -2), (key1706, -2), (key1700, 6), (key1851, -2), (key1277, -2), (key1700, -2)]

def rawRow15146 : Integer.Sparse Key := [(key1886, -2), (key1855, -2), (key1851, -2), (key1855, 6), (key1756, -2), (key1706, -2), (key1700, -2), (key1886, 2), (key1855, 2), (key1756, 2), (key1283, 2), (key1700, 2), (key1277, 2), (key1855, -2), (key1706, -2), (key1283, -2), (key1700, 6), (key1851, -2), (key1700, -2), (key1277, -2)]

def rawRow15147 : Integer.Sparse Key := [(key1855, -2), (key1855, -2), (key1886, -2), (key1851, 6), (key1855, -2), (key1855, -2), (key1886, -2), (key1283, 2), (key1283, 2), (key1706, 2), (key1706, 2), (key1756, 2), (key1756, 2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, 6), (key1277, -2), (key1700, -2), (key1700, -2)]

def rawRow15148 : Integer.Sparse Key := [(key1855, -2), (key1886, -2), (key1855, -2), (key1851, 6), (key1855, -2), (key1886, -2), (key1855, -2), (key1706, 2), (key1756, 2), (key1283, 2), (key1756, 2), (key1283, 2), (key1706, 2), (key1700, -2), (key1277, -2), (key1700, -2), (key1851, 6), (key1700, -2), (key1277, -2), (key1700, -2)]

def rawRow15149 : Integer.Sparse Key := [(key1886, -2), (key1855, -2), (key1855, -2), (key1851, 6), (key1886, -2), (key1855, -2), (key1855, -2), (key1756, 2), (key1706, 2), (key1756, 2), (key1283, 2), (key1706, 2), (key1283, 2), (key1700, -2), (key1700, -2), (key1277, -2), (key1851, 6), (key1700, -2), (key1700, -2), (key1277, -2)]

def rawRow15150 : Integer.Sparse Key := [(key2362, 2), (key2365, 2), (key2365, 2), (key2365, -2), (key2365, -2), (key2367, -2), (key2457, 2), (key2460, 2), (key2460, 2), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2525, -1), (key2525, -1), (key2532, -2), (key2532, -2), (key2533, -2), (key2532, -1), (key2532, -1), (key2562, -1), (key2562, -1), (key2564, -1), (key2564, -1), (key2533, 4), (key2564, 4), (key2564, 4)]

def rawRow15151 : Integer.Sparse Key := [(key2365, 2), (key2362, 2), (key2365, 2), (key2365, -2), (key2367, -2), (key2365, -2), (key2460, 2), (key2457, 2), (key2460, 2), (key2521, -1), (key2525, -1), (key2460, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2532, -2), (key2533, -2), (key2532, -2), (key2562, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow15152 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2362, 2), (key2367, -2), (key2365, -2), (key2365, -2), (key2460, 2), (key2460, 2), (key2457, 2), (key2525, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2460, -1), (key2533, -2), (key2532, -2), (key2532, -2), (key2564, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2532, -1), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow15153 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2367, 2), (key2362, -2), (key2365, -2), (key2365, -2), (key2521, 2), (key2521, 2), (key2525, 2), (key2457, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2521, -1), (key2562, -2), (key2564, -2), (key2564, -2), (key2532, -1), (key2533, -1), (key2532, -1), (key2564, -1), (key2533, -1), (key2564, -1), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow15154 : Integer.Sparse Key := [(key2365, 2), (key2367, 2), (key2365, 2), (key2365, -2), (key2362, -2), (key2365, -2), (key2521, 2), (key2525, 2), (key2521, 2), (key2460, -1), (key2457, -1), (key2521, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2564, -2), (key2562, -2), (key2564, -2), (key2533, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2533, -1), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow15155 : Integer.Sparse Key := [(key2367, 2), (key2365, 2), (key2365, 2), (key2365, -2), (key2365, -2), (key2362, -2), (key2525, 2), (key2521, 2), (key2521, 2), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2457, -1), (key2457, -1), (key2564, -2), (key2564, -2), (key2562, -2), (key2564, -1), (key2564, -1), (key2533, -1), (key2533, -1), (key2532, -1), (key2532, -1), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow15156 : Integer.Sparse Key := [(key2457, 2), (key2460, 2), (key2460, 2), (key2521, -2), (key2521, -2), (key2525, -2), (key2362, 2), (key2365, 2), (key2365, 2), (key2532, -1), (key2532, -1), (key2562, -1), (key2562, -1), (key2564, -1), (key2564, -1), (key2365, -2), (key2365, -2), (key2367, -2), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2525, -1), (key2525, -1), (key2533, 4), (key2564, 4), (key2564, 4)]

def rawRow15157 : Integer.Sparse Key := [(key2460, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2521, -2), (key2365, 2), (key2362, 2), (key2365, 2), (key2562, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2365, -2), (key2367, -2), (key2365, -2), (key2521, -1), (key2525, -1), (key2460, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow15158 : Integer.Sparse Key := [(key2460, 2), (key2460, 2), (key2457, 2), (key2525, -2), (key2521, -2), (key2521, -2), (key2365, 2), (key2365, 2), (key2362, 2), (key2564, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2532, -1), (key2367, -2), (key2365, -2), (key2365, -2), (key2525, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2460, -1), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow15159 : Integer.Sparse Key := [(key2460, 2), (key2521, 2), (key2525, 2), (key2457, -2), (key2460, -2), (key2521, -2), (key2532, 2), (key2562, 2), (key2564, 2), (key2362, -1), (key2365, -1), (key2457, -1), (key2521, -1), (key2532, -1), (key2562, -1), (key2521, -2), (key2525, -2), (key2564, -2), (key2365, -1), (key2367, -1), (key2460, -1), (key2525, -1), (key2533, -1), (key2564, -1), (key2365, 4), (key2460, 4), (key2521, 4)]

def rawRow15160 : Integer.Sparse Key := [(key2460, 2), (key2525, 2), (key2521, 2), (key2460, -2), (key2457, -2), (key2521, -2), (key2532, 2), (key2564, 2), (key2562, 2), (key2365, -1), (key2362, -1), (key2521, -1), (key2457, -1), (key2562, -1), (key2532, -1), (key2525, -2), (key2521, -2), (key2564, -2), (key2367, -1), (key2365, -1), (key2525, -1), (key2460, -1), (key2564, -1), (key2533, -1), (key2365, 4), (key2521, 4), (key2460, 4)]

def rawRow15161 : Integer.Sparse Key := [(key2521, 2), (key2460, 2), (key2525, 2), (key2457, -2), (key2521, -2), (key2460, -2), (key2562, 2), (key2532, 2), (key2564, 2), (key2457, -1), (key2521, -1), (key2362, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, -1), (key2533, -1), (key2365, -1), (key2564, -1), (key2367, -1), (key2525, -1), (key2460, 4), (key2365, 4), (key2521, 4)]

def rawRow15162 : Integer.Sparse Key := [(key2521, 2), (key2525, 2), (key2460, 2), (key2521, -2), (key2457, -2), (key2460, -2), (key2562, 2), (key2564, 2), (key2532, 2), (key2521, -1), (key2457, -1), (key2562, -1), (key2362, -1), (key2521, -1), (key2365, -1), (key2564, -2), (key2521, -2), (key2525, -2), (key2533, -1), (key2460, -1), (key2564, -1), (key2365, -1), (key2525, -1), (key2367, -1), (key2460, 4), (key2521, 4), (key2365, 4)]

def rawRow15163 : Integer.Sparse Key := [(key2525, 2), (key2460, 2), (key2521, 2), (key2460, -2), (key2521, -2), (key2457, -2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2362, -1), (key2457, -1), (key2525, -2), (key2564, -2), (key2521, -2), (key2525, -1), (key2564, -1), (key2367, -1), (key2533, -1), (key2365, -1), (key2460, -1), (key2521, 4), (key2365, 4), (key2460, 4)]

def rawRow15164 : Integer.Sparse Key := [(key2525, 2), (key2521, 2), (key2460, 2), (key2521, -2), (key2460, -2), (key2457, -2), (key2564, 2), (key2562, 2), (key2532, 2), (key2562, -1), (key2532, -1), (key2521, -1), (key2365, -1), (key2457, -1), (key2362, -1), (key2564, -2), (key2525, -2), (key2521, -2), (key2564, -1), (key2525, -1), (key2533, -1), (key2367, -1), (key2460, -1), (key2365, -1), (key2521, 4), (key2460, 4), (key2365, 4)]

def rawRow15165 : Integer.Sparse Key := [(key2532, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2), (key2564, -2), (key2365, 2), (key2365, 2), (key2367, 2), (key2521, -1), (key2525, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2564, -1), (key2362, -2), (key2365, -2), (key2365, -2), (key2457, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2521, -1), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow15166 : Integer.Sparse Key := [(key2532, 2), (key2533, 2), (key2532, 2), (key2564, -2), (key2562, -2), (key2564, -2), (key2365, 2), (key2367, 2), (key2365, 2), (key2525, -1), (key2521, -1), (key2564, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2365, -2), (key2362, -2), (key2365, -2), (key2460, -1), (key2457, -1), (key2521, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow15167 : Integer.Sparse Key := [(key2533, 2), (key2532, 2), (key2532, 2), (key2564, -2), (key2564, -2), (key2562, -2), (key2367, 2), (key2365, 2), (key2365, 2), (key2564, -1), (key2564, -1), (key2525, -1), (key2525, -1), (key2521, -1), (key2521, -1), (key2365, -2), (key2365, -2), (key2362, -2), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2457, -1), (key2457, -1), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow15168 : Integer.Sparse Key := [(key2532, 2), (key2562, 2), (key2564, 2), (key2532, -2), (key2533, -2), (key2564, -2), (key2460, 2), (key2521, 2), (key2525, 2), (key2365, -1), (key2367, -1), (key2460, -1), (key2533, -1), (key2525, -1), (key2564, -1), (key2457, -2), (key2460, -2), (key2521, -2), (key2362, -1), (key2365, -1), (key2457, -1), (key2521, -1), (key2532, -1), (key2562, -1), (key2365, 4), (key2460, 4), (key2521, 4)]

def rawRow15169 : Integer.Sparse Key := [(key2532, 2), (key2564, 2), (key2562, 2), (key2533, -2), (key2532, -2), (key2564, -2), (key2460, 2), (key2525, 2), (key2521, 2), (key2367, -1), (key2365, -1), (key2533, -1), (key2460, -1), (key2564, -1), (key2525, -1), (key2460, -2), (key2457, -2), (key2521, -2), (key2365, -1), (key2362, -1), (key2521, -1), (key2457, -1), (key2562, -1), (key2532, -1), (key2365, 4), (key2521, 4), (key2460, 4)]

def rawRow15170 : Integer.Sparse Key := [(key2562, 2), (key2532, 2), (key2564, 2), (key2532, -2), (key2564, -2), (key2533, -2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, -1), (key2525, -1), (key2365, -1), (key2564, -1), (key2367, -1), (key2533, -1), (key2457, -2), (key2521, -2), (key2460, -2), (key2457, -1), (key2521, -1), (key2362, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2460, 4), (key2365, 4), (key2521, 4)]

def rawRow15171 : Integer.Sparse Key := [(key2562, 2), (key2564, 2), (key2532, 2), (key2564, -2), (key2532, -2), (key2533, -2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, -1), (key2460, -1), (key2564, -1), (key2365, -1), (key2533, -1), (key2367, -1), (key2521, -2), (key2457, -2), (key2460, -2), (key2521, -1), (key2457, -1), (key2562, -1), (key2362, -1), (key2521, -1), (key2365, -1), (key2460, 4), (key2521, 4), (key2365, 4)]

def rawRow15172 : Integer.Sparse Key := [(key2564, 2), (key2532, 2), (key2562, 2), (key2533, -2), (key2564, -2), (key2532, -2), (key2525, 2), (key2460, 2), (key2521, 2), (key2533, -1), (key2564, -1), (key2367, -1), (key2525, -1), (key2365, -1), (key2460, -1), (key2460, -2), (key2521, -2), (key2457, -2), (key2532, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2362, -1), (key2457, -1), (key2521, 4), (key2365, 4), (key2460, 4)]

def rawRow15173 : Integer.Sparse Key := [(key2564, 2), (key2562, 2), (key2532, 2), (key2564, -2), (key2533, -2), (key2532, -2), (key2525, 2), (key2521, 2), (key2460, 2), (key2564, -1), (key2533, -1), (key2525, -1), (key2367, -1), (key2460, -1), (key2365, -1), (key2521, -2), (key2460, -2), (key2457, -2), (key2562, -1), (key2532, -1), (key2521, -1), (key2365, -1), (key2457, -1), (key2362, -1), (key2521, 4), (key2460, 4), (key2365, 4)]

def rawRow15174 : Integer.Sparse Key := [(key2533, 2), (key2564, 2), (key2564, 2), (key2532, -2), (key2532, -2), (key2562, -2), (key2533, 2), (key2564, 2), (key2564, 2), (key2365, -1), (key2365, -1), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2532, -2), (key2532, -2), (key2562, -2), (key2365, -1), (key2365, -1), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2362, 4), (key2457, 4), (key2457, 4)]

def rawRow15175 : Integer.Sparse Key := [(key2564, 2), (key2533, 2), (key2564, 2), (key2532, -2), (key2562, -2), (key2532, -2), (key2564, 2), (key2533, 2), (key2564, 2), (key2460, -1), (key2521, -1), (key2365, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2532, -2), (key2562, -2), (key2532, -2), (key2460, -1), (key2521, -1), (key2365, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2457, 4), (key2362, 4), (key2457, 4)]

def rawRow15176 : Integer.Sparse Key := [(key2564, 2), (key2564, 2), (key2533, 2), (key2562, -2), (key2532, -2), (key2532, -2), (key2564, 2), (key2564, 2), (key2533, 2), (key2521, -1), (key2460, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2365, -1), (key2562, -2), (key2532, -2), (key2532, -2), (key2521, -1), (key2460, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2365, -1), (key2457, 4), (key2457, 4), (key2362, 4)]

def rawRow15195 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1001, -2), (key1015, 6), (key1028, -2), (key1036, -2), (key1036, -2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1123, -2), (key1123, -2), (key1235, -2), (key1071, 6), (key1150, -2), (key1150, -2), (key1242, -2)]

def rawRow15196 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1001, -2), (key1015, 6), (key1036, -2), (key1028, -2), (key1036, -2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1123, -2), (key1235, -2), (key1123, -2), (key1071, 6), (key1150, -2), (key1242, -2), (key1150, -2)]

def rawRow15197 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key993, -2), (key1015, 6), (key1036, -2), (key1036, -2), (key1028, -2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1235, -2), (key1123, -2), (key1123, -2), (key1071, 6), (key1242, -2), (key1150, -2), (key1150, -2)]

def rawRow15198 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1015, -2), (key1001, 6), (key1106, -2), (key1114, -2), (key1123, -2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1036, -2), (key1114, -2), (key1232, -2), (key1150, 6), (key1071, -2), (key1150, -2), (key1242, -2)]

def rawRow15199 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1015, -2), (key1001, 6), (key1114, -2), (key1106, -2), (key1123, -2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1036, -2), (key1232, -2), (key1114, -2), (key1150, 6), (key1071, -2), (key1242, -2), (key1150, -2)]

def rawRow15200 : Integer.Sparse Key := [(key993, -2), (key1015, -2), (key1001, -2), (key1001, 6), (key1106, -2), (key1123, -2), (key1114, -2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1114, -2), (key1036, -2), (key1232, -2), (key1150, 6), (key1150, -2), (key1071, -2), (key1242, -2)]

def rawRow15201 : Integer.Sparse Key := [(key1015, -2), (key993, -2), (key1001, -2), (key1001, 6), (key1123, -2), (key1106, -2), (key1114, -2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1114, -2), (key1232, -2), (key1036, -2), (key1150, 6), (key1150, -2), (key1242, -2), (key1071, -2)]

def rawRow15202 : Integer.Sparse Key := [(key1001, -2), (key1015, -2), (key993, -2), (key1001, 6), (key1114, -2), (key1123, -2), (key1106, -2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1232, -2), (key1036, -2), (key1114, -2), (key1150, 6), (key1242, -2), (key1071, -2), (key1150, -2)]

def rawRow15203 : Integer.Sparse Key := [(key1015, -2), (key1001, -2), (key993, -2), (key1001, 6), (key1123, -2), (key1114, -2), (key1106, -2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1232, -2), (key1114, -2), (key1036, -2), (key1150, 6), (key1242, -2), (key1150, -2), (key1071, -2)]

def rawRow15204 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1036, -2), (key1071, 6), (key993, -2), (key1001, -2), (key1001, -2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1150, -2), (key1150, -2), (key1242, -2), (key1015, 6), (key1123, -2), (key1123, -2), (key1235, -2)]

def rawRow15205 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1036, -2), (key1071, 6), (key1001, -2), (key993, -2), (key1001, -2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1150, -2), (key1242, -2), (key1150, -2), (key1015, 6), (key1123, -2), (key1235, -2), (key1123, -2)]

def rawRow15206 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1028, -2), (key1071, 6), (key1001, -2), (key1001, -2), (key993, -2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1242, -2), (key1150, -2), (key1150, -2), (key1015, 6), (key1235, -2), (key1123, -2), (key1123, -2)]

def rawRow15207 : Integer.Sparse Key := [(key1106, -2), (key1114, -2), (key1123, -2), (key1150, 6), (key993, -2), (key1001, -2), (key1015, -2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1071, -2), (key1150, -2), (key1242, -2), (key1001, 6), (key1036, -2), (key1114, -2), (key1232, -2)]

def rawRow15208 : Integer.Sparse Key := [(key1114, -2), (key1106, -2), (key1123, -2), (key1150, 6), (key1001, -2), (key993, -2), (key1015, -2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1071, -2), (key1242, -2), (key1150, -2), (key1001, 6), (key1036, -2), (key1232, -2), (key1114, -2)]

def rawRow15209 : Integer.Sparse Key := [(key1106, -2), (key1123, -2), (key1114, -2), (key1150, 6), (key993, -2), (key1015, -2), (key1001, -2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1150, -2), (key1071, -2), (key1242, -2), (key1001, 6), (key1114, -2), (key1036, -2), (key1232, -2)]

def rawRow15210 : Integer.Sparse Key := [(key1123, -2), (key1106, -2), (key1114, -2), (key1150, 6), (key1015, -2), (key993, -2), (key1001, -2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1150, -2), (key1242, -2), (key1071, -2), (key1001, 6), (key1114, -2), (key1232, -2), (key1036, -2)]

def rawRow15211 : Integer.Sparse Key := [(key1114, -2), (key1123, -2), (key1106, -2), (key1150, 6), (key1001, -2), (key1015, -2), (key993, -2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1242, -2), (key1071, -2), (key1150, -2), (key1001, 6), (key1232, -2), (key1036, -2), (key1114, -2)]

def rawRow15212 : Integer.Sparse Key := [(key1123, -2), (key1114, -2), (key1106, -2), (key1150, 6), (key1015, -2), (key1001, -2), (key993, -2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1242, -2), (key1150, -2), (key1071, -2), (key1001, 6), (key1232, -2), (key1114, -2), (key1036, -2)]

def rawRow15213 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2376, -2), (key2388, 6), (key2762, -2), (key2768, -2), (key2768, -2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key2916, -2), (key2916, -2), (key2925, -2), (key3005, 6), (key3019, -2), (key3019, -2), (key3028, -2)]

def rawRow15214 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2376, -2), (key2388, 6), (key2768, -2), (key2762, -2), (key2768, -2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2916, -2), (key2925, -2), (key2916, -2), (key3005, 6), (key3019, -2), (key3028, -2), (key3019, -2)]

def rawRow15215 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2370, -2), (key2388, 6), (key2768, -2), (key2768, -2), (key2762, -2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key2925, -2), (key2916, -2), (key2916, -2), (key3005, 6), (key3028, -2), (key3019, -2), (key3019, -2)]

def rawRow15216 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2376, 6), (key2839, -2), (key2845, -2), (key2916, -2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key2768, -2), (key2845, -2), (key2876, -2), (key3019, 6), (key3005, -2), (key3019, -2), (key3028, -2)]

def rawRow15217 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2388, -2), (key2376, 6), (key2845, -2), (key2839, -2), (key2916, -2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key2768, -2), (key2876, -2), (key2845, -2), (key3019, 6), (key3005, -2), (key3028, -2), (key3019, -2)]

def rawRow15218 : Integer.Sparse Key := [(key2370, -2), (key2388, -2), (key2376, -2), (key2376, 6), (key2839, -2), (key2916, -2), (key2845, -2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key2845, -2), (key2768, -2), (key2876, -2), (key3019, 6), (key3019, -2), (key3005, -2), (key3028, -2)]

def rawRow15219 : Integer.Sparse Key := [(key2388, -2), (key2370, -2), (key2376, -2), (key2376, 6), (key2916, -2), (key2839, -2), (key2845, -2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key2845, -2), (key2876, -2), (key2768, -2), (key3019, 6), (key3019, -2), (key3028, -2), (key3005, -2)]

def rawRow15220 : Integer.Sparse Key := [(key2376, -2), (key2388, -2), (key2370, -2), (key2376, 6), (key2845, -2), (key2916, -2), (key2839, -2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key2876, -2), (key2768, -2), (key2845, -2), (key3019, 6), (key3028, -2), (key3005, -2), (key3019, -2)]

def rawRow15221 : Integer.Sparse Key := [(key2388, -2), (key2376, -2), (key2370, -2), (key2376, 6), (key2916, -2), (key2845, -2), (key2839, -2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key2876, -2), (key2845, -2), (key2768, -2), (key3019, 6), (key3028, -2), (key3019, -2), (key3005, -2)]

def rawRow15222 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2404, -2), (key2435, 6), (key2583, -2), (key2589, -2), (key2589, -2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key3019, -2), (key3019, -2), (key3028, -2), (key2604, 6), (key2916, -2), (key2916, -2), (key2925, -2)]

def rawRow15223 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2404, -2), (key2435, 6), (key2589, -2), (key2583, -2), (key2589, -2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key3019, -2), (key3028, -2), (key3019, -2), (key2604, 6), (key2916, -2), (key2925, -2), (key2916, -2)]

def rawRow15224 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2398, -2), (key2435, 6), (key2589, -2), (key2589, -2), (key2583, -2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key3028, -2), (key3019, -2), (key3019, -2), (key2604, 6), (key2925, -2), (key2916, -2), (key2916, -2)]

def rawRow15225 : Integer.Sparse Key := [(key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2370, -2), (key2376, -2), (key2388, -2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2), (key2589, 6), (key2768, -2), (key2845, -2), (key2876, -2)]

def rawRow15226 : Integer.Sparse Key := [(key2470, -2), (key2464, -2), (key2478, -2), (key2501, 6), (key2376, -2), (key2370, -2), (key2388, -2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key3005, -2), (key3028, -2), (key3019, -2), (key2589, 6), (key2768, -2), (key2876, -2), (key2845, -2)]

def rawRow15227 : Integer.Sparse Key := [(key2464, -2), (key2478, -2), (key2470, -2), (key2501, 6), (key2370, -2), (key2388, -2), (key2376, -2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key3019, -2), (key3005, -2), (key3028, -2), (key2589, 6), (key2845, -2), (key2768, -2), (key2876, -2)]

def rawRow15228 : Integer.Sparse Key := [(key2478, -2), (key2464, -2), (key2470, -2), (key2501, 6), (key2388, -2), (key2370, -2), (key2376, -2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key3019, -2), (key3028, -2), (key3005, -2), (key2589, 6), (key2845, -2), (key2876, -2), (key2768, -2)]

def rawRow15229 : Integer.Sparse Key := [(key2470, -2), (key2478, -2), (key2464, -2), (key2501, 6), (key2376, -2), (key2388, -2), (key2370, -2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key3028, -2), (key3005, -2), (key3019, -2), (key2589, 6), (key2876, -2), (key2768, -2), (key2845, -2)]

def rawRow15230 : Integer.Sparse Key := [(key2478, -2), (key2470, -2), (key2464, -2), (key2501, 6), (key2388, -2), (key2376, -2), (key2370, -2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key3028, -2), (key3019, -2), (key3005, -2), (key2589, 6), (key2876, -2), (key2845, -2), (key2768, -2)]

def rawRow15231 : Integer.Sparse Key := [(key2610, 6), (key2626, -2), (key2626, -2), (key2635, -2), (key2665, 6), (key2700, -2), (key2700, -2), (key2721, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

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

def rawRow15232 : Integer.Sparse Key := [(key2610, 6), (key2626, -2), (key2635, -2), (key2626, -2), (key2665, 6), (key2700, -2), (key2721, -2), (key2700, -2), (key2780, -2), (key2789, -2), (key2780, -2), (key2803, -2), (key2824, -2), (key2803, -2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

def rawRow15233 : Integer.Sparse Key := [(key2610, 6), (key2635, -2), (key2626, -2), (key2626, -2), (key2665, 6), (key2721, -2), (key2700, -2), (key2700, -2), (key2789, -2), (key2780, -2), (key2780, -2), (key2824, -2), (key2803, -2), (key2803, -2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

def rawRow15234 : Integer.Sparse Key := [(key2626, 6), (key2610, -2), (key2626, -2), (key2635, -2), (key2700, 6), (key2665, -2), (key2700, -2), (key2721, -2), (key2803, -2), (key2853, -2), (key2855, -2), (key2780, -2), (key2853, -2), (key2865, -2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

def rawRow15235 : Integer.Sparse Key := [(key2626, 6), (key2610, -2), (key2635, -2), (key2626, -2), (key2700, 6), (key2665, -2), (key2721, -2), (key2700, -2), (key2803, -2), (key2855, -2), (key2853, -2), (key2780, -2), (key2865, -2), (key2853, -2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

def rawRow15236 : Integer.Sparse Key := [(key2626, 6), (key2626, -2), (key2610, -2), (key2635, -2), (key2700, 6), (key2700, -2), (key2665, -2), (key2721, -2), (key2853, -2), (key2803, -2), (key2855, -2), (key2853, -2), (key2780, -2), (key2865, -2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

def rawRow15237 : Integer.Sparse Key := [(key2626, 6), (key2626, -2), (key2635, -2), (key2610, -2), (key2700, 6), (key2700, -2), (key2721, -2), (key2665, -2), (key2853, -2), (key2855, -2), (key2803, -2), (key2853, -2), (key2865, -2), (key2780, -2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

def rawRow15238 : Integer.Sparse Key := [(key2626, 6), (key2635, -2), (key2610, -2), (key2626, -2), (key2700, 6), (key2721, -2), (key2665, -2), (key2700, -2), (key2855, -2), (key2803, -2), (key2853, -2), (key2865, -2), (key2780, -2), (key2853, -2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

def rawRow15239 : Integer.Sparse Key := [(key2626, 6), (key2635, -2), (key2626, -2), (key2610, -2), (key2700, 6), (key2721, -2), (key2700, -2), (key2665, -2), (key2855, -2), (key2853, -2), (key2803, -2), (key2865, -2), (key2853, -2), (key2780, -2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

def rawRow15240 : Integer.Sparse Key := [(key2665, 6), (key2780, -2), (key2780, -2), (key2789, -2), (key2610, 6), (key2803, -2), (key2803, -2), (key2824, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

def rawRow15241 : Integer.Sparse Key := [(key2665, 6), (key2780, -2), (key2789, -2), (key2780, -2), (key2610, 6), (key2803, -2), (key2824, -2), (key2803, -2), (key2626, -2), (key2635, -2), (key2626, -2), (key2700, -2), (key2721, -2), (key2700, -2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

def rawRow15242 : Integer.Sparse Key := [(key2665, 6), (key2789, -2), (key2780, -2), (key2780, -2), (key2610, 6), (key2824, -2), (key2803, -2), (key2803, -2), (key2635, -2), (key2626, -2), (key2626, -2), (key2721, -2), (key2700, -2), (key2700, -2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

def rawRow15243 : Integer.Sparse Key := [(key2700, 6), (key2803, -2), (key2853, -2), (key2855, -2), (key2626, 6), (key2780, -2), (key2853, -2), (key2865, -2), (key2610, -2), (key2626, -2), (key2635, -2), (key2665, -2), (key2700, -2), (key2721, -2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

def rawRow15244 : Integer.Sparse Key := [(key2700, 6), (key2803, -2), (key2855, -2), (key2853, -2), (key2626, 6), (key2780, -2), (key2865, -2), (key2853, -2), (key2610, -2), (key2635, -2), (key2626, -2), (key2665, -2), (key2721, -2), (key2700, -2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

def rawRow15245 : Integer.Sparse Key := [(key2700, 6), (key2853, -2), (key2803, -2), (key2855, -2), (key2626, 6), (key2853, -2), (key2780, -2), (key2865, -2), (key2626, -2), (key2610, -2), (key2635, -2), (key2700, -2), (key2665, -2), (key2721, -2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

def rawRow15246 : Integer.Sparse Key := [(key2700, 6), (key2853, -2), (key2855, -2), (key2803, -2), (key2626, 6), (key2853, -2), (key2865, -2), (key2780, -2), (key2626, -2), (key2635, -2), (key2610, -2), (key2700, -2), (key2721, -2), (key2665, -2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

def rawRow15247 : Integer.Sparse Key := [(key2700, 6), (key2855, -2), (key2803, -2), (key2853, -2), (key2626, 6), (key2865, -2), (key2780, -2), (key2853, -2), (key2635, -2), (key2610, -2), (key2626, -2), (key2721, -2), (key2665, -2), (key2700, -2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

def rawRow15248 : Integer.Sparse Key := [(key2700, 6), (key2855, -2), (key2853, -2), (key2803, -2), (key2626, 6), (key2865, -2), (key2853, -2), (key2780, -2), (key2635, -2), (key2626, -2), (key2610, -2), (key2721, -2), (key2700, -2), (key2665, -2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

def rawRow15249 : Integer.Sparse Key := [(key994, -2), (key1000, -2), (key1000, -2), (key1014, 6), (key1029, -2), (key1035, -2), (key1035, -2), (key1107, 2), (key1113, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1231, 2), (key1122, -2), (key1122, -2), (key1234, -2), (key1070, 6), (key1149, -2), (key1149, -2), (key1241, -2)]

def rawRow15250 : Integer.Sparse Key := [(key1000, -2), (key994, -2), (key1000, -2), (key1014, 6), (key1035, -2), (key1029, -2), (key1035, -2), (key1113, 2), (key1107, 2), (key1231, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1122, -2), (key1234, -2), (key1122, -2), (key1070, 6), (key1149, -2), (key1241, -2), (key1149, -2)]

def rawRow15251 : Integer.Sparse Key := [(key1000, -2), (key1000, -2), (key994, -2), (key1014, 6), (key1035, -2), (key1035, -2), (key1029, -2), (key1231, 2), (key1231, 2), (key1113, 2), (key1113, 2), (key1107, 2), (key1107, 2), (key1234, -2), (key1122, -2), (key1122, -2), (key1070, 6), (key1241, -2), (key1149, -2), (key1149, -2)]

def rawRow15252 : Integer.Sparse Key := [(key994, -2), (key1000, -2), (key1014, -2), (key1000, 6), (key1107, -2), (key1113, -2), (key1122, -2), (key1029, 2), (key1035, 2), (key1107, 2), (key1231, 2), (key1122, 2), (key1234, 2), (key1035, -2), (key1113, -2), (key1231, -2), (key1149, 6), (key1070, -2), (key1149, -2), (key1241, -2)]

def rawRow15253 : Integer.Sparse Key := [(key1000, -2), (key994, -2), (key1014, -2), (key1000, 6), (key1113, -2), (key1107, -2), (key1122, -2), (key1035, 2), (key1029, 2), (key1231, 2), (key1107, 2), (key1234, 2), (key1122, 2), (key1035, -2), (key1231, -2), (key1113, -2), (key1149, 6), (key1070, -2), (key1241, -2), (key1149, -2)]

def rawRow15254 : Integer.Sparse Key := [(key994, -2), (key1014, -2), (key1000, -2), (key1000, 6), (key1107, -2), (key1122, -2), (key1113, -2), (key1107, 2), (key1122, 2), (key1029, 2), (key1234, 2), (key1035, 2), (key1231, 2), (key1113, -2), (key1035, -2), (key1231, -2), (key1149, 6), (key1149, -2), (key1070, -2), (key1241, -2)]

def rawRow15255 : Integer.Sparse Key := [(key1014, -2), (key994, -2), (key1000, -2), (key1000, 6), (key1122, -2), (key1107, -2), (key1113, -2), (key1122, 2), (key1107, 2), (key1234, 2), (key1029, 2), (key1231, 2), (key1035, 2), (key1113, -2), (key1231, -2), (key1035, -2), (key1149, 6), (key1149, -2), (key1241, -2), (key1070, -2)]

def rawRow15256 : Integer.Sparse Key := [(key1000, -2), (key1014, -2), (key994, -2), (key1000, 6), (key1113, -2), (key1122, -2), (key1107, -2), (key1231, 2), (key1234, 2), (key1035, 2), (key1122, 2), (key1029, 2), (key1107, 2), (key1231, -2), (key1035, -2), (key1113, -2), (key1149, 6), (key1241, -2), (key1070, -2), (key1149, -2)]

def rawRow15257 : Integer.Sparse Key := [(key1014, -2), (key1000, -2), (key994, -2), (key1000, 6), (key1122, -2), (key1113, -2), (key1107, -2), (key1234, 2), (key1231, 2), (key1122, 2), (key1035, 2), (key1107, 2), (key1029, 2), (key1231, -2), (key1113, -2), (key1035, -2), (key1149, 6), (key1241, -2), (key1149, -2), (key1070, -2)]

def rawRow15258 : Integer.Sparse Key := [(key1029, -2), (key1035, -2), (key1035, -2), (key1070, 6), (key994, -2), (key1000, -2), (key1000, -2), (key1107, 2), (key1113, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1231, 2), (key1149, -2), (key1149, -2), (key1241, -2), (key1014, 6), (key1122, -2), (key1122, -2), (key1234, -2)]

def rawRow15259 : Integer.Sparse Key := [(key1035, -2), (key1029, -2), (key1035, -2), (key1070, 6), (key1000, -2), (key994, -2), (key1000, -2), (key1113, 2), (key1107, 2), (key1231, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1149, -2), (key1241, -2), (key1149, -2), (key1014, 6), (key1122, -2), (key1234, -2), (key1122, -2)]

def rawRow15260 : Integer.Sparse Key := [(key1035, -2), (key1035, -2), (key1029, -2), (key1070, 6), (key1000, -2), (key1000, -2), (key994, -2), (key1231, 2), (key1231, 2), (key1113, 2), (key1113, 2), (key1107, 2), (key1107, 2), (key1241, -2), (key1149, -2), (key1149, -2), (key1014, 6), (key1234, -2), (key1122, -2), (key1122, -2)]

def rawRow15261 : Integer.Sparse Key := [(key1107, -2), (key1113, -2), (key1122, -2), (key1149, 6), (key994, -2), (key1000, -2), (key1014, -2), (key1029, 2), (key1035, 2), (key1107, 2), (key1231, 2), (key1122, 2), (key1234, 2), (key1070, -2), (key1149, -2), (key1241, -2), (key1000, 6), (key1035, -2), (key1113, -2), (key1231, -2)]

def rawRow15262 : Integer.Sparse Key := [(key1113, -2), (key1107, -2), (key1122, -2), (key1149, 6), (key1000, -2), (key994, -2), (key1014, -2), (key1035, 2), (key1029, 2), (key1231, 2), (key1107, 2), (key1234, 2), (key1122, 2), (key1070, -2), (key1241, -2), (key1149, -2), (key1000, 6), (key1035, -2), (key1231, -2), (key1113, -2)]

def rawRow15263 : Integer.Sparse Key := [(key1107, -2), (key1122, -2), (key1113, -2), (key1149, 6), (key994, -2), (key1014, -2), (key1000, -2), (key1107, 2), (key1122, 2), (key1029, 2), (key1234, 2), (key1035, 2), (key1231, 2), (key1149, -2), (key1070, -2), (key1241, -2), (key1000, 6), (key1113, -2), (key1035, -2), (key1231, -2)]

def rawRow15264 : Integer.Sparse Key := [(key1122, -2), (key1107, -2), (key1113, -2), (key1149, 6), (key1014, -2), (key994, -2), (key1000, -2), (key1122, 2), (key1107, 2), (key1234, 2), (key1029, 2), (key1231, 2), (key1035, 2), (key1149, -2), (key1241, -2), (key1070, -2), (key1000, 6), (key1113, -2), (key1231, -2), (key1035, -2)]

def rawRow15265 : Integer.Sparse Key := [(key1113, -2), (key1122, -2), (key1107, -2), (key1149, 6), (key1000, -2), (key1014, -2), (key994, -2), (key1231, 2), (key1234, 2), (key1035, 2), (key1122, 2), (key1029, 2), (key1107, 2), (key1241, -2), (key1070, -2), (key1149, -2), (key1000, 6), (key1231, -2), (key1035, -2), (key1113, -2)]

def rawRow15266 : Integer.Sparse Key := [(key1122, -2), (key1113, -2), (key1107, -2), (key1149, 6), (key1014, -2), (key1000, -2), (key994, -2), (key1234, 2), (key1231, 2), (key1122, 2), (key1035, 2), (key1107, 2), (key1029, 2), (key1241, -2), (key1149, -2), (key1070, -2), (key1000, 6), (key1231, -2), (key1113, -2), (key1035, -2)]

def rawRow15267 : Integer.Sparse Key := [(key1116, 4), (key1116, 4), (key1233, 4), (key1125, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1236, -2), (key1152, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1243, -2), (key1174, 4), (key1174, 4), (key1247, 4)]

def rawRow15268 : Integer.Sparse Key := [(key1116, 4), (key1233, 4), (key1116, 4), (key1130, -2), (key1125, -2), (key1236, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1174, 4), (key1247, 4), (key1174, 4)]

def rawRow15269 : Integer.Sparse Key := [(key1233, 4), (key1116, 4), (key1116, 4), (key1236, -2), (key1236, -2), (key1130, -2), (key1130, -2), (key1125, -2), (key1125, -2), (key1243, -2), (key1243, -2), (key1159, -2), (key1159, -2), (key1152, -2), (key1152, -2), (key1247, 4), (key1174, 4), (key1174, 4)]

def rawRow15270 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1236, 4), (key1038, -2), (key1044, -2), (key1116, -2), (key1233, -2), (key1130, -2), (key1236, -2), (key1073, -2), (key1080, -2), (key1152, -2), (key1243, -2), (key1174, -2), (key1247, -2), (key1080, 4), (key1159, 4), (key1243, 4)]

def rawRow15271 : Integer.Sparse Key := [(key1038, 4), (key1236, 4), (key1125, 4), (key1044, -2), (key1038, -2), (key1233, -2), (key1116, -2), (key1236, -2), (key1130, -2), (key1080, -2), (key1073, -2), (key1243, -2), (key1152, -2), (key1247, -2), (key1174, -2), (key1080, 4), (key1243, 4), (key1159, 4)]

def rawRow15272 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1236, 4), (key1116, -2), (key1130, -2), (key1038, -2), (key1236, -2), (key1044, -2), (key1233, -2), (key1152, -2), (key1174, -2), (key1073, -2), (key1247, -2), (key1080, -2), (key1243, -2), (key1159, 4), (key1080, 4), (key1243, 4)]

def rawRow15273 : Integer.Sparse Key := [(key1125, 4), (key1236, 4), (key1038, 4), (key1130, -2), (key1116, -2), (key1236, -2), (key1038, -2), (key1233, -2), (key1044, -2), (key1174, -2), (key1152, -2), (key1247, -2), (key1073, -2), (key1243, -2), (key1080, -2), (key1159, 4), (key1243, 4), (key1080, 4)]

def rawRow15274 : Integer.Sparse Key := [(key1236, 4), (key1038, 4), (key1125, 4), (key1233, -2), (key1236, -2), (key1044, -2), (key1130, -2), (key1038, -2), (key1116, -2), (key1243, -2), (key1247, -2), (key1080, -2), (key1174, -2), (key1073, -2), (key1152, -2), (key1243, 4), (key1080, 4), (key1159, 4)]

def rawRow15275 : Integer.Sparse Key := [(key1236, 4), (key1125, 4), (key1038, 4), (key1236, -2), (key1233, -2), (key1130, -2), (key1044, -2), (key1116, -2), (key1038, -2), (key1247, -2), (key1243, -2), (key1174, -2), (key1080, -2), (key1152, -2), (key1073, -2), (key1243, 4), (key1159, 4), (key1080, 4)]

def rawRow15276 : Integer.Sparse Key := [(key1116, 4), (key1116, 4), (key1233, 4), (key1152, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1243, -2), (key1125, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1236, -2), (key1174, 4), (key1174, 4), (key1247, 4)]

def rawRow15277 : Integer.Sparse Key := [(key1116, 4), (key1233, 4), (key1116, 4), (key1159, -2), (key1152, -2), (key1243, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1174, 4), (key1247, 4), (key1174, 4)]

def rawRow15278 : Integer.Sparse Key := [(key1233, 4), (key1116, 4), (key1116, 4), (key1243, -2), (key1243, -2), (key1159, -2), (key1159, -2), (key1152, -2), (key1152, -2), (key1236, -2), (key1236, -2), (key1130, -2), (key1130, -2), (key1125, -2), (key1125, -2), (key1247, 4), (key1174, 4), (key1174, 4)]

def rawRow15279 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1236, 4), (key1073, -2), (key1080, -2), (key1152, -2), (key1243, -2), (key1174, -2), (key1247, -2), (key1038, -2), (key1044, -2), (key1116, -2), (key1233, -2), (key1130, -2), (key1236, -2), (key1080, 4), (key1159, 4), (key1243, 4)]

def rawRow15280 : Integer.Sparse Key := [(key1038, 4), (key1236, 4), (key1125, 4), (key1080, -2), (key1073, -2), (key1243, -2), (key1152, -2), (key1247, -2), (key1174, -2), (key1044, -2), (key1038, -2), (key1233, -2), (key1116, -2), (key1236, -2), (key1130, -2), (key1080, 4), (key1243, 4), (key1159, 4)]

def rawRow15281 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1236, 4), (key1152, -2), (key1174, -2), (key1073, -2), (key1247, -2), (key1080, -2), (key1243, -2), (key1116, -2), (key1130, -2), (key1038, -2), (key1236, -2), (key1044, -2), (key1233, -2), (key1159, 4), (key1080, 4), (key1243, 4)]

def rawRow15282 : Integer.Sparse Key := [(key1125, 4), (key1236, 4), (key1038, 4), (key1174, -2), (key1152, -2), (key1247, -2), (key1073, -2), (key1243, -2), (key1080, -2), (key1130, -2), (key1116, -2), (key1236, -2), (key1038, -2), (key1233, -2), (key1044, -2), (key1159, 4), (key1243, 4), (key1080, 4)]

def rawRow15283 : Integer.Sparse Key := [(key1236, 4), (key1038, 4), (key1125, 4), (key1243, -2), (key1247, -2), (key1080, -2), (key1174, -2), (key1073, -2), (key1152, -2), (key1233, -2), (key1236, -2), (key1044, -2), (key1130, -2), (key1038, -2), (key1116, -2), (key1243, 4), (key1080, 4), (key1159, 4)]

def rawRow15284 : Integer.Sparse Key := [(key1236, 4), (key1125, 4), (key1038, 4), (key1247, -2), (key1243, -2), (key1174, -2), (key1080, -2), (key1152, -2), (key1073, -2), (key1236, -2), (key1233, -2), (key1130, -2), (key1044, -2), (key1116, -2), (key1038, -2), (key1243, 4), (key1159, 4), (key1080, 4)]

def rawRow15303 : Integer.Sparse Key := [(key2681, 4), (key2681, 4), (key2688, 4), (key2712, -4), (key2714, -4), (key2714, -4), (key2815, -4), (key2817, -4), (key2817, -4), (key2863, 12)]

def rawRow15304 : Integer.Sparse Key := [(key2681, 4), (key2688, 4), (key2681, 4), (key2714, -4), (key2712, -4), (key2714, -4), (key2817, -4), (key2815, -4), (key2817, -4), (key2863, 12)]

def rawRow15305 : Integer.Sparse Key := [(key2688, 4), (key2681, 4), (key2681, 4), (key2714, -4), (key2714, -4), (key2712, -4), (key2817, -4), (key2817, -4), (key2815, -4), (key2863, 12)]

def rawRow15306 : Integer.Sparse Key := [(key2681, 4), (key2712, 4), (key2714, 4), (key2681, -4), (key2688, -4), (key2714, -4), (key2815, -4), (key2817, -4), (key2863, -4), (key2817, 12)]

def rawRow15307 : Integer.Sparse Key := [(key2681, 4), (key2714, 4), (key2712, 4), (key2688, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2815, -4), (key2863, -4), (key2817, 12)]

def rawRow15308 : Integer.Sparse Key := [(key2712, 4), (key2681, 4), (key2714, 4), (key2681, -4), (key2714, -4), (key2688, -4), (key2815, -4), (key2863, -4), (key2817, -4), (key2817, 12)]

def rawRow15309 : Integer.Sparse Key := [(key2712, 4), (key2714, 4), (key2681, 4), (key2714, -4), (key2681, -4), (key2688, -4), (key2863, -4), (key2815, -4), (key2817, -4), (key2817, 12)]

def rawRow15310 : Integer.Sparse Key := [(key2714, 4), (key2681, 4), (key2712, 4), (key2688, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2863, -4), (key2815, -4), (key2817, 12)]

def rawRow15311 : Integer.Sparse Key := [(key2714, 4), (key2712, 4), (key2681, 4), (key2714, -4), (key2688, -4), (key2681, -4), (key2863, -4), (key2817, -4), (key2815, -4), (key2817, 12)]

def rawRow15312 : Integer.Sparse Key := [(key2681, 4), (key2681, 4), (key2688, 4), (key2815, -4), (key2817, -4), (key2817, -4), (key2712, -4), (key2714, -4), (key2714, -4), (key2863, 12)]

def rawRow15313 : Integer.Sparse Key := [(key2681, 4), (key2688, 4), (key2681, 4), (key2817, -4), (key2815, -4), (key2817, -4), (key2714, -4), (key2712, -4), (key2714, -4), (key2863, 12)]

def rawRow15314 : Integer.Sparse Key := [(key2688, 4), (key2681, 4), (key2681, 4), (key2817, -4), (key2817, -4), (key2815, -4), (key2714, -4), (key2714, -4), (key2712, -4), (key2863, 12)]

def rawRow15315 : Integer.Sparse Key := [(key2681, 4), (key2815, 4), (key2817, 4), (key2681, -4), (key2688, -4), (key2817, -4), (key2712, -4), (key2714, -4), (key2863, -4), (key2714, 12)]

def rawRow15316 : Integer.Sparse Key := [(key2681, 4), (key2817, 4), (key2815, 4), (key2688, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2712, -4), (key2863, -4), (key2714, 12)]

def rawRow15317 : Integer.Sparse Key := [(key2815, 4), (key2681, 4), (key2817, 4), (key2681, -4), (key2817, -4), (key2688, -4), (key2712, -4), (key2863, -4), (key2714, -4), (key2714, 12)]

def rawRow15318 : Integer.Sparse Key := [(key2815, 4), (key2817, 4), (key2681, 4), (key2817, -4), (key2681, -4), (key2688, -4), (key2863, -4), (key2712, -4), (key2714, -4), (key2714, 12)]

def rawRow15319 : Integer.Sparse Key := [(key2817, 4), (key2681, 4), (key2815, 4), (key2688, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2863, -4), (key2712, -4), (key2714, 12)]

def rawRow15320 : Integer.Sparse Key := [(key2817, 4), (key2815, 4), (key2681, 4), (key2817, -4), (key2688, -4), (key2681, -4), (key2863, -4), (key2714, -4), (key2712, -4), (key2714, 12)]

def rawRow15321 : Integer.Sparse Key := [(key2681, 4), (key2712, 4), (key2714, 4), (key2815, -4), (key2817, -4), (key2863, -4), (key2681, -4), (key2688, -4), (key2714, -4), (key2817, 12)]

def rawRow15322 : Integer.Sparse Key := [(key2681, 4), (key2714, 4), (key2712, 4), (key2817, -4), (key2815, -4), (key2863, -4), (key2688, -4), (key2681, -4), (key2714, -4), (key2817, 12)]

def rawRow15323 : Integer.Sparse Key := [(key2712, 4), (key2681, 4), (key2714, 4), (key2815, -4), (key2863, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2688, -4), (key2817, 12)]

def rawRow15324 : Integer.Sparse Key := [(key2712, 4), (key2714, 4), (key2681, 4), (key2863, -4), (key2815, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2688, -4), (key2817, 12)]

def rawRow15325 : Integer.Sparse Key := [(key2714, 4), (key2681, 4), (key2712, 4), (key2817, -4), (key2863, -4), (key2815, -4), (key2688, -4), (key2714, -4), (key2681, -4), (key2817, 12)]

def rawRow15326 : Integer.Sparse Key := [(key2714, 4), (key2712, 4), (key2681, 4), (key2863, -4), (key2817, -4), (key2815, -4), (key2714, -4), (key2688, -4), (key2681, -4), (key2817, 12)]

def rawRow15327 : Integer.Sparse Key := [(key2681, 4), (key2815, 4), (key2817, 4), (key2712, -4), (key2714, -4), (key2863, -4), (key2681, -4), (key2688, -4), (key2817, -4), (key2714, 12)]

def rawRow15328 : Integer.Sparse Key := [(key2681, 4), (key2817, 4), (key2815, 4), (key2714, -4), (key2712, -4), (key2863, -4), (key2688, -4), (key2681, -4), (key2817, -4), (key2714, 12)]

def rawRow15329 : Integer.Sparse Key := [(key2815, 4), (key2681, 4), (key2817, 4), (key2712, -4), (key2863, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2688, -4), (key2714, 12)]

def rawRow15330 : Integer.Sparse Key := [(key2815, 4), (key2817, 4), (key2681, 4), (key2863, -4), (key2712, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2688, -4), (key2714, 12)]

def rawRow15331 : Integer.Sparse Key := [(key2817, 4), (key2681, 4), (key2815, 4), (key2714, -4), (key2863, -4), (key2712, -4), (key2688, -4), (key2817, -4), (key2681, -4), (key2714, 12)]

def rawRow15332 : Integer.Sparse Key := [(key2817, 4), (key2815, 4), (key2681, 4), (key2863, -4), (key2714, -4), (key2712, -4), (key2817, -4), (key2688, -4), (key2681, -4), (key2714, 12)]

def rawRow15333 : Integer.Sparse Key := [(key2712, 4), (key2815, 4), (key2863, 4), (key2681, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2688, 12)]

def rawRow15334 : Integer.Sparse Key := [(key2712, 4), (key2863, 4), (key2815, 4), (key2714, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2688, 12)]

def rawRow15335 : Integer.Sparse Key := [(key2815, 4), (key2712, 4), (key2863, 4), (key2681, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2688, 12)]

def rawRow15336 : Integer.Sparse Key := [(key2815, 4), (key2863, 4), (key2712, 4), (key2817, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2688, 12)]

def rawRow15337 : Integer.Sparse Key := [(key2863, 4), (key2712, 4), (key2815, 4), (key2714, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2688, 12)]

def rawRow15338 : Integer.Sparse Key := [(key2863, 4), (key2815, 4), (key2712, 4), (key2817, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2688, 12)]

def rawRow15339 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2599, 6), (key2763, -2), (key2767, -2), (key2767, -2), (key2840, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2888, -2), (key2888, -2), (key2909, -2), (key2930, 6), (key2967, -2), (key2967, -2), (key2988, -2)]

def rawRow15340 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2599, 6), (key2767, -2), (key2763, -2), (key2767, -2), (key2844, 2), (key2840, 2), (key2875, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2888, -2), (key2909, -2), (key2888, -2), (key2930, 6), (key2967, -2), (key2988, -2), (key2967, -2)]

def rawRow15341 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2599, 6), (key2767, -2), (key2767, -2), (key2763, -2), (key2875, 2), (key2875, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2909, -2), (key2888, -2), (key2888, -2), (key2930, 6), (key2988, -2), (key2967, -2), (key2967, -2)]

def rawRow15342 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2599, -2), (key2588, 6), (key2840, -2), (key2844, -2), (key2888, -2), (key2763, 2), (key2767, 2), (key2840, 2), (key2875, 2), (key2888, 2), (key2909, 2), (key2767, -2), (key2844, -2), (key2875, -2), (key2967, 6), (key2930, -2), (key2967, -2), (key2988, -2)]

def rawRow15343 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2599, -2), (key2588, 6), (key2844, -2), (key2840, -2), (key2888, -2), (key2767, 2), (key2763, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2888, 2), (key2767, -2), (key2875, -2), (key2844, -2), (key2967, 6), (key2930, -2), (key2988, -2), (key2967, -2)]

def rawRow15344 : Integer.Sparse Key := [(key2584, -2), (key2599, -2), (key2588, -2), (key2588, 6), (key2840, -2), (key2888, -2), (key2844, -2), (key2840, 2), (key2888, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2844, -2), (key2767, -2), (key2875, -2), (key2967, 6), (key2967, -2), (key2930, -2), (key2988, -2)]

def rawRow15345 : Integer.Sparse Key := [(key2599, -2), (key2584, -2), (key2588, -2), (key2588, 6), (key2888, -2), (key2840, -2), (key2844, -2), (key2888, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2875, 2), (key2767, 2), (key2844, -2), (key2875, -2), (key2767, -2), (key2967, 6), (key2967, -2), (key2988, -2), (key2930, -2)]

def rawRow15346 : Integer.Sparse Key := [(key2588, -2), (key2599, -2), (key2584, -2), (key2588, 6), (key2844, -2), (key2888, -2), (key2840, -2), (key2875, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2763, 2), (key2840, 2), (key2875, -2), (key2767, -2), (key2844, -2), (key2967, 6), (key2988, -2), (key2930, -2), (key2967, -2)]

def rawRow15347 : Integer.Sparse Key := [(key2599, -2), (key2588, -2), (key2584, -2), (key2588, 6), (key2888, -2), (key2844, -2), (key2840, -2), (key2909, 2), (key2875, 2), (key2888, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2875, -2), (key2844, -2), (key2767, -2), (key2967, 6), (key2988, -2), (key2967, -2), (key2930, -2)]

def rawRow15348 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2930, 6), (key2584, -2), (key2588, -2), (key2588, -2), (key2840, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2967, -2), (key2967, -2), (key2988, -2), (key2599, 6), (key2888, -2), (key2888, -2), (key2909, -2)]

def rawRow15349 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2930, 6), (key2588, -2), (key2584, -2), (key2588, -2), (key2844, 2), (key2840, 2), (key2875, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2967, -2), (key2988, -2), (key2967, -2), (key2599, 6), (key2888, -2), (key2909, -2), (key2888, -2)]

def rawRow15350 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2930, 6), (key2588, -2), (key2588, -2), (key2584, -2), (key2875, 2), (key2875, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2988, -2), (key2967, -2), (key2967, -2), (key2599, 6), (key2909, -2), (key2888, -2), (key2888, -2)]

def rawRow15351 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2930, -2), (key2767, 6), (key2840, -2), (key2844, -2), (key2967, -2), (key2584, 2), (key2588, 2), (key2840, 2), (key2875, 2), (key2967, 2), (key2988, 2), (key2588, -2), (key2844, -2), (key2875, -2), (key2888, 6), (key2599, -2), (key2888, -2), (key2909, -2)]

def rawRow15352 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2930, -2), (key2767, 6), (key2844, -2), (key2840, -2), (key2967, -2), (key2588, 2), (key2584, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2588, -2), (key2875, -2), (key2844, -2), (key2888, 6), (key2599, -2), (key2909, -2), (key2888, -2)]

def rawRow15353 : Integer.Sparse Key := [(key2763, -2), (key2930, -2), (key2767, -2), (key2767, 6), (key2840, -2), (key2967, -2), (key2844, -2), (key2840, 2), (key2967, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2844, -2), (key2588, -2), (key2875, -2), (key2888, 6), (key2888, -2), (key2599, -2), (key2909, -2)]

def rawRow15354 : Integer.Sparse Key := [(key2930, -2), (key2763, -2), (key2767, -2), (key2767, 6), (key2967, -2), (key2840, -2), (key2844, -2), (key2967, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2875, 2), (key2588, 2), (key2844, -2), (key2875, -2), (key2588, -2), (key2888, 6), (key2888, -2), (key2909, -2), (key2599, -2)]

def rawRow15355 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2763, -2), (key2767, 6), (key2844, -2), (key2967, -2), (key2840, -2), (key2875, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2584, 2), (key2840, 2), (key2875, -2), (key2588, -2), (key2844, -2), (key2888, 6), (key2909, -2), (key2599, -2), (key2888, -2)]

def rawRow15356 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2763, -2), (key2767, 6), (key2967, -2), (key2844, -2), (key2840, -2), (key2988, 2), (key2875, 2), (key2967, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2875, -2), (key2844, -2), (key2588, -2), (key2888, 6), (key2909, -2), (key2888, -2), (key2599, -2)]

def rawRow15357 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2888, -2), (key2967, 6), (key2584, -2), (key2588, -2), (key2599, -2), (key2763, 2), (key2767, 2), (key2840, 2), (key2875, 2), (key2888, 2), (key2909, 2), (key2930, -2), (key2967, -2), (key2988, -2), (key2588, 6), (key2767, -2), (key2844, -2), (key2875, -2)]

def rawRow15358 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2888, -2), (key2967, 6), (key2588, -2), (key2584, -2), (key2599, -2), (key2767, 2), (key2763, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2888, 2), (key2930, -2), (key2988, -2), (key2967, -2), (key2588, 6), (key2767, -2), (key2875, -2), (key2844, -2)]

def rawRow15359 : Integer.Sparse Key := [(key2840, -2), (key2888, -2), (key2844, -2), (key2967, 6), (key2584, -2), (key2599, -2), (key2588, -2), (key2840, 2), (key2888, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2967, -2), (key2930, -2), (key2988, -2), (key2588, 6), (key2844, -2), (key2767, -2), (key2875, -2)]

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

def rawRow15360 : Integer.Sparse Key := [(key2888, -2), (key2840, -2), (key2844, -2), (key2967, 6), (key2599, -2), (key2584, -2), (key2588, -2), (key2888, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2875, 2), (key2767, 2), (key2967, -2), (key2988, -2), (key2930, -2), (key2588, 6), (key2844, -2), (key2875, -2), (key2767, -2)]

def rawRow15361 : Integer.Sparse Key := [(key2844, -2), (key2888, -2), (key2840, -2), (key2967, 6), (key2588, -2), (key2599, -2), (key2584, -2), (key2875, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2763, 2), (key2840, 2), (key2988, -2), (key2930, -2), (key2967, -2), (key2588, 6), (key2875, -2), (key2767, -2), (key2844, -2)]

def rawRow15362 : Integer.Sparse Key := [(key2888, -2), (key2844, -2), (key2840, -2), (key2967, 6), (key2599, -2), (key2588, -2), (key2584, -2), (key2909, 2), (key2875, 2), (key2888, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2988, -2), (key2967, -2), (key2930, -2), (key2588, 6), (key2875, -2), (key2844, -2), (key2767, -2)]

def rawRow15363 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2967, -2), (key2888, 6), (key2763, -2), (key2767, -2), (key2930, -2), (key2584, 2), (key2588, 2), (key2840, 2), (key2875, 2), (key2967, 2), (key2988, 2), (key2599, -2), (key2888, -2), (key2909, -2), (key2767, 6), (key2588, -2), (key2844, -2), (key2875, -2)]

def rawRow15364 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2967, -2), (key2888, 6), (key2767, -2), (key2763, -2), (key2930, -2), (key2588, 2), (key2584, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2599, -2), (key2909, -2), (key2888, -2), (key2767, 6), (key2588, -2), (key2875, -2), (key2844, -2)]

def rawRow15365 : Integer.Sparse Key := [(key2840, -2), (key2967, -2), (key2844, -2), (key2888, 6), (key2763, -2), (key2930, -2), (key2767, -2), (key2840, 2), (key2967, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2888, -2), (key2599, -2), (key2909, -2), (key2767, 6), (key2844, -2), (key2588, -2), (key2875, -2)]

def rawRow15366 : Integer.Sparse Key := [(key2967, -2), (key2840, -2), (key2844, -2), (key2888, 6), (key2930, -2), (key2763, -2), (key2767, -2), (key2967, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2875, 2), (key2588, 2), (key2888, -2), (key2909, -2), (key2599, -2), (key2767, 6), (key2844, -2), (key2875, -2), (key2588, -2)]

def rawRow15367 : Integer.Sparse Key := [(key2844, -2), (key2967, -2), (key2840, -2), (key2888, 6), (key2767, -2), (key2930, -2), (key2763, -2), (key2875, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2584, 2), (key2840, 2), (key2909, -2), (key2599, -2), (key2888, -2), (key2767, 6), (key2875, -2), (key2588, -2), (key2844, -2)]

def rawRow15368 : Integer.Sparse Key := [(key2967, -2), (key2844, -2), (key2840, -2), (key2888, 6), (key2930, -2), (key2767, -2), (key2763, -2), (key2988, 2), (key2875, 2), (key2967, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2909, -2), (key2888, -2), (key2599, -2), (key2767, 6), (key2875, -2), (key2844, -2), (key2588, -2)]

def rawRow15369 : Integer.Sparse Key := [(key2840, -2), (key2888, -2), (key2967, -2), (key2844, 6), (key2840, -2), (key2888, -2), (key2967, -2), (key2584, 2), (key2599, 2), (key2763, 2), (key2909, 2), (key2930, 2), (key2988, 2), (key2588, -2), (key2767, -2), (key2875, -2), (key2844, 6), (key2588, -2), (key2767, -2), (key2875, -2)]

def rawRow15370 : Integer.Sparse Key := [(key2888, -2), (key2840, -2), (key2967, -2), (key2844, 6), (key2888, -2), (key2840, -2), (key2967, -2), (key2599, 2), (key2584, 2), (key2909, 2), (key2763, 2), (key2988, 2), (key2930, 2), (key2588, -2), (key2875, -2), (key2767, -2), (key2844, 6), (key2588, -2), (key2875, -2), (key2767, -2)]

def rawRow15371 : Integer.Sparse Key := [(key2840, -2), (key2967, -2), (key2888, -2), (key2844, 6), (key2840, -2), (key2967, -2), (key2888, -2), (key2763, 2), (key2930, 2), (key2584, 2), (key2988, 2), (key2599, 2), (key2909, 2), (key2767, -2), (key2588, -2), (key2875, -2), (key2844, 6), (key2767, -2), (key2588, -2), (key2875, -2)]

def rawRow15372 : Integer.Sparse Key := [(key2967, -2), (key2840, -2), (key2888, -2), (key2844, 6), (key2967, -2), (key2840, -2), (key2888, -2), (key2930, 2), (key2763, 2), (key2988, 2), (key2584, 2), (key2909, 2), (key2599, 2), (key2767, -2), (key2875, -2), (key2588, -2), (key2844, 6), (key2767, -2), (key2875, -2), (key2588, -2)]

def rawRow15373 : Integer.Sparse Key := [(key2888, -2), (key2967, -2), (key2840, -2), (key2844, 6), (key2888, -2), (key2967, -2), (key2840, -2), (key2909, 2), (key2988, 2), (key2599, 2), (key2930, 2), (key2584, 2), (key2763, 2), (key2875, -2), (key2588, -2), (key2767, -2), (key2844, 6), (key2875, -2), (key2588, -2), (key2767, -2)]

def rawRow15374 : Integer.Sparse Key := [(key2967, -2), (key2888, -2), (key2840, -2), (key2844, 6), (key2967, -2), (key2888, -2), (key2840, -2), (key2988, 2), (key2909, 2), (key2930, 2), (key2599, 2), (key2763, 2), (key2584, 2), (key2875, -2), (key2767, -2), (key2588, -2), (key2844, 6), (key2875, -2), (key2767, -2), (key2588, -2)]

def rawRow15375 : Integer.Sparse Key := [(key2012, 4), (key2012, 4), (key2025, 4), (key2041, -4), (key2054, -4), (key2054, -4), (key2126, -4), (key2143, -4), (key2143, -4), (key2227, 12)]

def rawRow15376 : Integer.Sparse Key := [(key2012, 4), (key2025, 4), (key2012, 4), (key2054, -4), (key2041, -4), (key2054, -4), (key2143, -4), (key2126, -4), (key2143, -4), (key2227, 12)]

def rawRow15377 : Integer.Sparse Key := [(key2025, 4), (key2012, 4), (key2012, 4), (key2054, -4), (key2054, -4), (key2041, -4), (key2143, -4), (key2143, -4), (key2126, -4), (key2227, 12)]

def rawRow15378 : Integer.Sparse Key := [(key2012, 4), (key2041, 4), (key2054, 4), (key2012, -4), (key2025, -4), (key2054, -4), (key2126, -4), (key2143, -4), (key2227, -4), (key2143, 12)]

def rawRow15379 : Integer.Sparse Key := [(key2012, 4), (key2054, 4), (key2041, 4), (key2025, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2126, -4), (key2227, -4), (key2143, 12)]

def rawRow15380 : Integer.Sparse Key := [(key2041, 4), (key2012, 4), (key2054, 4), (key2012, -4), (key2054, -4), (key2025, -4), (key2126, -4), (key2227, -4), (key2143, -4), (key2143, 12)]

def rawRow15381 : Integer.Sparse Key := [(key2041, 4), (key2054, 4), (key2012, 4), (key2054, -4), (key2012, -4), (key2025, -4), (key2227, -4), (key2126, -4), (key2143, -4), (key2143, 12)]

def rawRow15382 : Integer.Sparse Key := [(key2054, 4), (key2012, 4), (key2041, 4), (key2025, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2227, -4), (key2126, -4), (key2143, 12)]

def rawRow15383 : Integer.Sparse Key := [(key2054, 4), (key2041, 4), (key2012, 4), (key2054, -4), (key2025, -4), (key2012, -4), (key2227, -4), (key2143, -4), (key2126, -4), (key2143, 12)]

def rawRow15384 : Integer.Sparse Key := [(key2012, 4), (key2012, 4), (key2025, 4), (key2126, -4), (key2143, -4), (key2143, -4), (key2041, -4), (key2054, -4), (key2054, -4), (key2227, 12)]

def rawRow15385 : Integer.Sparse Key := [(key2012, 4), (key2025, 4), (key2012, 4), (key2143, -4), (key2126, -4), (key2143, -4), (key2054, -4), (key2041, -4), (key2054, -4), (key2227, 12)]

def rawRow15386 : Integer.Sparse Key := [(key2025, 4), (key2012, 4), (key2012, 4), (key2143, -4), (key2143, -4), (key2126, -4), (key2054, -4), (key2054, -4), (key2041, -4), (key2227, 12)]

def rawRow15387 : Integer.Sparse Key := [(key2012, 4), (key2126, 4), (key2143, 4), (key2012, -4), (key2025, -4), (key2143, -4), (key2041, -4), (key2054, -4), (key2227, -4), (key2054, 12)]

def rawRow15388 : Integer.Sparse Key := [(key2012, 4), (key2143, 4), (key2126, 4), (key2025, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2041, -4), (key2227, -4), (key2054, 12)]

def rawRow15389 : Integer.Sparse Key := [(key2126, 4), (key2012, 4), (key2143, 4), (key2012, -4), (key2143, -4), (key2025, -4), (key2041, -4), (key2227, -4), (key2054, -4), (key2054, 12)]

def rawRow15390 : Integer.Sparse Key := [(key2126, 4), (key2143, 4), (key2012, 4), (key2143, -4), (key2012, -4), (key2025, -4), (key2227, -4), (key2041, -4), (key2054, -4), (key2054, 12)]

def rawRow15391 : Integer.Sparse Key := [(key2143, 4), (key2012, 4), (key2126, 4), (key2025, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2227, -4), (key2041, -4), (key2054, 12)]

def rawRow15392 : Integer.Sparse Key := [(key2143, 4), (key2126, 4), (key2012, 4), (key2143, -4), (key2025, -4), (key2012, -4), (key2227, -4), (key2054, -4), (key2041, -4), (key2054, 12)]

def rawRow15393 : Integer.Sparse Key := [(key2012, 4), (key2041, 4), (key2054, 4), (key2126, -4), (key2143, -4), (key2227, -4), (key2012, -4), (key2025, -4), (key2054, -4), (key2143, 12)]

def rawRow15394 : Integer.Sparse Key := [(key2012, 4), (key2054, 4), (key2041, 4), (key2143, -4), (key2126, -4), (key2227, -4), (key2025, -4), (key2012, -4), (key2054, -4), (key2143, 12)]

def rawRow15395 : Integer.Sparse Key := [(key2041, 4), (key2012, 4), (key2054, 4), (key2126, -4), (key2227, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2025, -4), (key2143, 12)]

def rawRow15396 : Integer.Sparse Key := [(key2041, 4), (key2054, 4), (key2012, 4), (key2227, -4), (key2126, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2025, -4), (key2143, 12)]

def rawRow15397 : Integer.Sparse Key := [(key2054, 4), (key2012, 4), (key2041, 4), (key2143, -4), (key2227, -4), (key2126, -4), (key2025, -4), (key2054, -4), (key2012, -4), (key2143, 12)]

def rawRow15398 : Integer.Sparse Key := [(key2054, 4), (key2041, 4), (key2012, 4), (key2227, -4), (key2143, -4), (key2126, -4), (key2054, -4), (key2025, -4), (key2012, -4), (key2143, 12)]

def rawRow15399 : Integer.Sparse Key := [(key2012, 4), (key2126, 4), (key2143, 4), (key2041, -4), (key2054, -4), (key2227, -4), (key2012, -4), (key2025, -4), (key2143, -4), (key2054, 12)]

def rawRow15400 : Integer.Sparse Key := [(key2012, 4), (key2143, 4), (key2126, 4), (key2054, -4), (key2041, -4), (key2227, -4), (key2025, -4), (key2012, -4), (key2143, -4), (key2054, 12)]

def rawRow15401 : Integer.Sparse Key := [(key2126, 4), (key2012, 4), (key2143, 4), (key2041, -4), (key2227, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2025, -4), (key2054, 12)]

def rawRow15402 : Integer.Sparse Key := [(key2126, 4), (key2143, 4), (key2012, 4), (key2227, -4), (key2041, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2025, -4), (key2054, 12)]

def rawRow15403 : Integer.Sparse Key := [(key2143, 4), (key2012, 4), (key2126, 4), (key2054, -4), (key2227, -4), (key2041, -4), (key2025, -4), (key2143, -4), (key2012, -4), (key2054, 12)]

def rawRow15404 : Integer.Sparse Key := [(key2143, 4), (key2126, 4), (key2012, 4), (key2227, -4), (key2054, -4), (key2041, -4), (key2143, -4), (key2025, -4), (key2012, -4), (key2054, 12)]

def rawRow15405 : Integer.Sparse Key := [(key2041, 4), (key2126, 4), (key2227, 4), (key2012, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2025, 12)]

def rawRow15406 : Integer.Sparse Key := [(key2041, 4), (key2227, 4), (key2126, 4), (key2054, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2025, 12)]

def rawRow15407 : Integer.Sparse Key := [(key2126, 4), (key2041, 4), (key2227, 4), (key2012, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2025, 12)]

def rawRow15408 : Integer.Sparse Key := [(key2126, 4), (key2227, 4), (key2041, 4), (key2143, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2025, 12)]

def rawRow15409 : Integer.Sparse Key := [(key2227, 4), (key2041, 4), (key2126, 4), (key2054, -4), (key2143, -4), (key2012, -4), (key2054, -4), (key2143, -4), (key2012, -4), (key2025, 12)]

def rawRow15410 : Integer.Sparse Key := [(key2227, 4), (key2126, 4), (key2041, 4), (key2143, -4), (key2054, -4), (key2012, -4), (key2143, -4), (key2054, -4), (key2012, -4), (key2025, 12)]

def rawRow15447 : Integer.Sparse Key := [(key1358, -2), (key1364, -2), (key1364, -2), (key1374, 6), (key1484, -2), (key1490, -2), (key1490, -2), (key1710, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1723, -2), (key1723, -2), (key1940, -2), (key1513, 6), (key1741, -2), (key1741, -2), (key1949, -2)]

def rawRow15448 : Integer.Sparse Key := [(key1364, -2), (key1358, -2), (key1364, -2), (key1374, 6), (key1490, -2), (key1484, -2), (key1490, -2), (key1716, 2), (key1710, 2), (key1937, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1723, -2), (key1940, -2), (key1723, -2), (key1513, 6), (key1741, -2), (key1949, -2), (key1741, -2)]

def rawRow15449 : Integer.Sparse Key := [(key1364, -2), (key1364, -2), (key1358, -2), (key1374, 6), (key1490, -2), (key1490, -2), (key1484, -2), (key1937, 2), (key1937, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1940, -2), (key1723, -2), (key1723, -2), (key1513, 6), (key1949, -2), (key1741, -2), (key1741, -2)]

def rawRow15450 : Integer.Sparse Key := [(key1358, -2), (key1364, -2), (key1374, -2), (key1364, 6), (key1710, -2), (key1716, -2), (key1723, -2), (key1484, 2), (key1490, 2), (key1710, 2), (key1937, 2), (key1723, 2), (key1940, 2), (key1490, -2), (key1716, -2), (key1937, -2), (key1741, 6), (key1513, -2), (key1741, -2), (key1949, -2)]

def rawRow15451 : Integer.Sparse Key := [(key1364, -2), (key1358, -2), (key1374, -2), (key1364, 6), (key1716, -2), (key1710, -2), (key1723, -2), (key1490, 2), (key1484, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1723, 2), (key1490, -2), (key1937, -2), (key1716, -2), (key1741, 6), (key1513, -2), (key1949, -2), (key1741, -2)]

def rawRow15452 : Integer.Sparse Key := [(key1358, -2), (key1374, -2), (key1364, -2), (key1364, 6), (key1710, -2), (key1723, -2), (key1716, -2), (key1710, 2), (key1723, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1716, -2), (key1490, -2), (key1937, -2), (key1741, 6), (key1741, -2), (key1513, -2), (key1949, -2)]

def rawRow15453 : Integer.Sparse Key := [(key1374, -2), (key1358, -2), (key1364, -2), (key1364, 6), (key1723, -2), (key1710, -2), (key1716, -2), (key1723, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1937, 2), (key1490, 2), (key1716, -2), (key1937, -2), (key1490, -2), (key1741, 6), (key1741, -2), (key1949, -2), (key1513, -2)]

def rawRow15454 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1358, -2), (key1364, 6), (key1716, -2), (key1723, -2), (key1710, -2), (key1937, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1484, 2), (key1710, 2), (key1937, -2), (key1490, -2), (key1716, -2), (key1741, 6), (key1949, -2), (key1513, -2), (key1741, -2)]

def rawRow15455 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1358, -2), (key1364, 6), (key1723, -2), (key1716, -2), (key1710, -2), (key1940, 2), (key1937, 2), (key1723, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1937, -2), (key1716, -2), (key1490, -2), (key1741, 6), (key1949, -2), (key1741, -2), (key1513, -2)]

def rawRow15456 : Integer.Sparse Key := [(key1484, -2), (key1490, -2), (key1490, -2), (key1513, 6), (key1358, -2), (key1364, -2), (key1364, -2), (key1710, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1741, -2), (key1741, -2), (key1949, -2), (key1374, 6), (key1723, -2), (key1723, -2), (key1940, -2)]

def rawRow15457 : Integer.Sparse Key := [(key1490, -2), (key1484, -2), (key1490, -2), (key1513, 6), (key1364, -2), (key1358, -2), (key1364, -2), (key1716, 2), (key1710, 2), (key1937, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1741, -2), (key1949, -2), (key1741, -2), (key1374, 6), (key1723, -2), (key1940, -2), (key1723, -2)]

def rawRow15458 : Integer.Sparse Key := [(key1490, -2), (key1490, -2), (key1484, -2), (key1513, 6), (key1364, -2), (key1364, -2), (key1358, -2), (key1937, 2), (key1937, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1949, -2), (key1741, -2), (key1741, -2), (key1374, 6), (key1940, -2), (key1723, -2), (key1723, -2)]

def rawRow15459 : Integer.Sparse Key := [(key1484, -2), (key1490, -2), (key1513, -2), (key1490, 6), (key1710, -2), (key1716, -2), (key1741, -2), (key1358, 2), (key1364, 2), (key1710, 2), (key1937, 2), (key1741, 2), (key1949, 2), (key1364, -2), (key1716, -2), (key1937, -2), (key1723, 6), (key1374, -2), (key1723, -2), (key1940, -2)]

def rawRow15460 : Integer.Sparse Key := [(key1490, -2), (key1484, -2), (key1513, -2), (key1490, 6), (key1716, -2), (key1710, -2), (key1741, -2), (key1364, 2), (key1358, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1741, 2), (key1364, -2), (key1937, -2), (key1716, -2), (key1723, 6), (key1374, -2), (key1940, -2), (key1723, -2)]

def rawRow15461 : Integer.Sparse Key := [(key1484, -2), (key1513, -2), (key1490, -2), (key1490, 6), (key1710, -2), (key1741, -2), (key1716, -2), (key1710, 2), (key1741, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1716, -2), (key1364, -2), (key1937, -2), (key1723, 6), (key1723, -2), (key1374, -2), (key1940, -2)]

def rawRow15462 : Integer.Sparse Key := [(key1513, -2), (key1484, -2), (key1490, -2), (key1490, 6), (key1741, -2), (key1710, -2), (key1716, -2), (key1741, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1937, 2), (key1364, 2), (key1716, -2), (key1937, -2), (key1364, -2), (key1723, 6), (key1723, -2), (key1940, -2), (key1374, -2)]

def rawRow15463 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1484, -2), (key1490, 6), (key1716, -2), (key1741, -2), (key1710, -2), (key1937, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1358, 2), (key1710, 2), (key1937, -2), (key1364, -2), (key1716, -2), (key1723, 6), (key1940, -2), (key1374, -2), (key1723, -2)]

def rawRow15464 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1484, -2), (key1490, 6), (key1741, -2), (key1716, -2), (key1710, -2), (key1949, 2), (key1937, 2), (key1741, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1937, -2), (key1716, -2), (key1364, -2), (key1723, 6), (key1940, -2), (key1723, -2), (key1374, -2)]

def rawRow15465 : Integer.Sparse Key := [(key1710, -2), (key1716, -2), (key1723, -2), (key1741, 6), (key1358, -2), (key1364, -2), (key1374, -2), (key1484, 2), (key1490, 2), (key1710, 2), (key1937, 2), (key1723, 2), (key1940, 2), (key1513, -2), (key1741, -2), (key1949, -2), (key1364, 6), (key1490, -2), (key1716, -2), (key1937, -2)]

def rawRow15466 : Integer.Sparse Key := [(key1716, -2), (key1710, -2), (key1723, -2), (key1741, 6), (key1364, -2), (key1358, -2), (key1374, -2), (key1490, 2), (key1484, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1723, 2), (key1513, -2), (key1949, -2), (key1741, -2), (key1364, 6), (key1490, -2), (key1937, -2), (key1716, -2)]

def rawRow15467 : Integer.Sparse Key := [(key1710, -2), (key1723, -2), (key1716, -2), (key1741, 6), (key1358, -2), (key1374, -2), (key1364, -2), (key1710, 2), (key1723, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1741, -2), (key1513, -2), (key1949, -2), (key1364, 6), (key1716, -2), (key1490, -2), (key1937, -2)]

def rawRow15468 : Integer.Sparse Key := [(key1723, -2), (key1710, -2), (key1716, -2), (key1741, 6), (key1374, -2), (key1358, -2), (key1364, -2), (key1723, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1937, 2), (key1490, 2), (key1741, -2), (key1949, -2), (key1513, -2), (key1364, 6), (key1716, -2), (key1937, -2), (key1490, -2)]

def rawRow15469 : Integer.Sparse Key := [(key1716, -2), (key1723, -2), (key1710, -2), (key1741, 6), (key1364, -2), (key1374, -2), (key1358, -2), (key1937, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1484, 2), (key1710, 2), (key1949, -2), (key1513, -2), (key1741, -2), (key1364, 6), (key1937, -2), (key1490, -2), (key1716, -2)]

def rawRow15470 : Integer.Sparse Key := [(key1723, -2), (key1716, -2), (key1710, -2), (key1741, 6), (key1374, -2), (key1364, -2), (key1358, -2), (key1940, 2), (key1937, 2), (key1723, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1949, -2), (key1741, -2), (key1513, -2), (key1364, 6), (key1937, -2), (key1716, -2), (key1490, -2)]

def rawRow15471 : Integer.Sparse Key := [(key1710, -2), (key1716, -2), (key1741, -2), (key1723, 6), (key1484, -2), (key1490, -2), (key1513, -2), (key1358, 2), (key1364, 2), (key1710, 2), (key1937, 2), (key1741, 2), (key1949, 2), (key1374, -2), (key1723, -2), (key1940, -2), (key1490, 6), (key1364, -2), (key1716, -2), (key1937, -2)]

def rawRow15472 : Integer.Sparse Key := [(key1716, -2), (key1710, -2), (key1741, -2), (key1723, 6), (key1490, -2), (key1484, -2), (key1513, -2), (key1364, 2), (key1358, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1741, 2), (key1374, -2), (key1940, -2), (key1723, -2), (key1490, 6), (key1364, -2), (key1937, -2), (key1716, -2)]

def rawRow15473 : Integer.Sparse Key := [(key1710, -2), (key1741, -2), (key1716, -2), (key1723, 6), (key1484, -2), (key1513, -2), (key1490, -2), (key1710, 2), (key1741, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1723, -2), (key1374, -2), (key1940, -2), (key1490, 6), (key1716, -2), (key1364, -2), (key1937, -2)]

def rawRow15474 : Integer.Sparse Key := [(key1741, -2), (key1710, -2), (key1716, -2), (key1723, 6), (key1513, -2), (key1484, -2), (key1490, -2), (key1741, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1937, 2), (key1364, 2), (key1723, -2), (key1940, -2), (key1374, -2), (key1490, 6), (key1716, -2), (key1937, -2), (key1364, -2)]

def rawRow15475 : Integer.Sparse Key := [(key1716, -2), (key1741, -2), (key1710, -2), (key1723, 6), (key1490, -2), (key1513, -2), (key1484, -2), (key1937, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1358, 2), (key1710, 2), (key1940, -2), (key1374, -2), (key1723, -2), (key1490, 6), (key1937, -2), (key1364, -2), (key1716, -2)]

def rawRow15476 : Integer.Sparse Key := [(key1741, -2), (key1716, -2), (key1710, -2), (key1723, 6), (key1513, -2), (key1490, -2), (key1484, -2), (key1949, 2), (key1937, 2), (key1741, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1940, -2), (key1723, -2), (key1374, -2), (key1490, 6), (key1937, -2), (key1716, -2), (key1364, -2)]

def rawRow15477 : Integer.Sparse Key := [(key1710, -2), (key1723, -2), (key1741, -2), (key1716, 6), (key1710, -2), (key1723, -2), (key1741, -2), (key1358, 2), (key1374, 2), (key1484, 2), (key1940, 2), (key1513, 2), (key1949, 2), (key1364, -2), (key1490, -2), (key1937, -2), (key1716, 6), (key1364, -2), (key1490, -2), (key1937, -2)]

def rawRow15478 : Integer.Sparse Key := [(key1723, -2), (key1710, -2), (key1741, -2), (key1716, 6), (key1723, -2), (key1710, -2), (key1741, -2), (key1374, 2), (key1358, 2), (key1940, 2), (key1484, 2), (key1949, 2), (key1513, 2), (key1364, -2), (key1937, -2), (key1490, -2), (key1716, 6), (key1364, -2), (key1937, -2), (key1490, -2)]

def rawRow15479 : Integer.Sparse Key := [(key1710, -2), (key1741, -2), (key1723, -2), (key1716, 6), (key1710, -2), (key1741, -2), (key1723, -2), (key1484, 2), (key1513, 2), (key1358, 2), (key1949, 2), (key1374, 2), (key1940, 2), (key1490, -2), (key1364, -2), (key1937, -2), (key1716, 6), (key1490, -2), (key1364, -2), (key1937, -2)]

def rawRow15480 : Integer.Sparse Key := [(key1741, -2), (key1710, -2), (key1723, -2), (key1716, 6), (key1741, -2), (key1710, -2), (key1723, -2), (key1513, 2), (key1484, 2), (key1949, 2), (key1358, 2), (key1940, 2), (key1374, 2), (key1490, -2), (key1937, -2), (key1364, -2), (key1716, 6), (key1490, -2), (key1937, -2), (key1364, -2)]

def rawRow15481 : Integer.Sparse Key := [(key1723, -2), (key1741, -2), (key1710, -2), (key1716, 6), (key1723, -2), (key1741, -2), (key1710, -2), (key1940, 2), (key1949, 2), (key1374, 2), (key1513, 2), (key1358, 2), (key1484, 2), (key1937, -2), (key1364, -2), (key1490, -2), (key1716, 6), (key1937, -2), (key1364, -2), (key1490, -2)]

def rawRow15482 : Integer.Sparse Key := [(key1741, -2), (key1723, -2), (key1710, -2), (key1716, 6), (key1741, -2), (key1723, -2), (key1710, -2), (key1949, 2), (key1940, 2), (key1513, 2), (key1374, 2), (key1484, 2), (key1358, 2), (key1937, -2), (key1490, -2), (key1364, -2), (key1716, 6), (key1937, -2), (key1490, -2), (key1364, -2)]

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

def rawRow15561 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key1015, -2), (key993, 6), (key1232, -2), (key1232, -2), (key1235, -2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1028, -2), (key1106, -2), (key1106, -2), (key1242, 6), (key1071, -2), (key1150, -2), (key1150, -2)]

def rawRow15562 : Integer.Sparse Key := [(key1001, -2), (key1015, -2), (key1001, -2), (key993, 6), (key1232, -2), (key1235, -2), (key1232, -2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1106, -2), (key1028, -2), (key1106, -2), (key1242, 6), (key1150, -2), (key1071, -2), (key1150, -2)]

def rawRow15563 : Integer.Sparse Key := [(key1015, -2), (key1001, -2), (key1001, -2), (key993, 6), (key1235, -2), (key1232, -2), (key1232, -2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1106, -2), (key1106, -2), (key1028, -2), (key1242, 6), (key1150, -2), (key1150, -2), (key1071, -2)]

def rawRow15564 : Integer.Sparse Key := [(key1232, -2), (key1232, -2), (key1235, -2), (key1242, 6), (key1001, -2), (key1001, -2), (key1015, -2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1071, -2), (key1150, -2), (key1150, -2), (key993, 6), (key1028, -2), (key1106, -2), (key1106, -2)]

def rawRow15565 : Integer.Sparse Key := [(key1232, -2), (key1235, -2), (key1232, -2), (key1242, 6), (key1001, -2), (key1015, -2), (key1001, -2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, -2), (key1071, -2), (key1150, -2), (key993, 6), (key1106, -2), (key1028, -2), (key1106, -2)]

def rawRow15566 : Integer.Sparse Key := [(key1235, -2), (key1232, -2), (key1232, -2), (key1242, 6), (key1015, -2), (key1001, -2), (key1001, -2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1150, -2), (key1150, -2), (key1071, -2), (key993, 6), (key1106, -2), (key1106, -2), (key1028, -2)]

def rawRow15567 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2388, -2), (key2370, 6), (key2876, -2), (key2876, -2), (key2925, -2), (key2768, 2), (key2768, 2), (key2845, 2), (key2845, 2), (key2916, 2), (key2916, 2), (key2762, -2), (key2839, -2), (key2839, -2), (key3028, 6), (key3005, -2), (key3019, -2), (key3019, -2)]

def rawRow15568 : Integer.Sparse Key := [(key2376, -2), (key2388, -2), (key2376, -2), (key2370, 6), (key2876, -2), (key2925, -2), (key2876, -2), (key2845, 2), (key2916, 2), (key2768, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2839, -2), (key2762, -2), (key2839, -2), (key3028, 6), (key3019, -2), (key3005, -2), (key3019, -2)]

def rawRow15569 : Integer.Sparse Key := [(key2388, -2), (key2376, -2), (key2376, -2), (key2370, 6), (key2925, -2), (key2876, -2), (key2876, -2), (key2916, 2), (key2845, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2768, 2), (key2839, -2), (key2839, -2), (key2762, -2), (key3028, 6), (key3019, -2), (key3019, -2), (key3005, -2)]

def rawRow15570 : Integer.Sparse Key := [(key2568, -2), (key2568, -2), (key2570, -2), (key2575, 6), (key2376, -2), (key2376, -2), (key2388, -2), (key2404, 2), (key2404, 2), (key2470, 2), (key2470, 2), (key2478, 2), (key2478, 2), (key2435, -2), (key2501, -2), (key2501, -2), (key2370, 6), (key2762, -2), (key2839, -2), (key2839, -2)]

def rawRow15571 : Integer.Sparse Key := [(key2568, -2), (key2570, -2), (key2568, -2), (key2575, 6), (key2376, -2), (key2388, -2), (key2376, -2), (key2470, 2), (key2478, 2), (key2404, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2501, -2), (key2435, -2), (key2501, -2), (key2370, 6), (key2839, -2), (key2762, -2), (key2839, -2)]

def rawRow15572 : Integer.Sparse Key := [(key2570, -2), (key2568, -2), (key2568, -2), (key2575, 6), (key2388, -2), (key2376, -2), (key2376, -2), (key2478, 2), (key2470, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2404, 2), (key2501, -2), (key2501, -2), (key2435, -2), (key2370, 6), (key2839, -2), (key2839, -2), (key2762, -2)]

def rawRow15573 : Integer.Sparse Key := [(key2635, 6), (key2610, -2), (key2626, -2), (key2626, -2), (key2721, 6), (key2665, -2), (key2700, -2), (key2700, -2), (key2824, -2), (key2865, -2), (key2865, -2), (key2789, -2), (key2855, -2), (key2855, -2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

def rawRow15574 : Integer.Sparse Key := [(key2635, 6), (key2626, -2), (key2610, -2), (key2626, -2), (key2721, 6), (key2700, -2), (key2665, -2), (key2700, -2), (key2865, -2), (key2824, -2), (key2865, -2), (key2855, -2), (key2789, -2), (key2855, -2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

def rawRow15575 : Integer.Sparse Key := [(key2635, 6), (key2626, -2), (key2626, -2), (key2610, -2), (key2721, 6), (key2700, -2), (key2700, -2), (key2665, -2), (key2865, -2), (key2865, -2), (key2824, -2), (key2855, -2), (key2855, -2), (key2789, -2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

def rawRow15576 : Integer.Sparse Key := [(key2721, 6), (key2824, -2), (key2865, -2), (key2865, -2), (key2635, 6), (key2789, -2), (key2855, -2), (key2855, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

def rawRow15577 : Integer.Sparse Key := [(key2721, 6), (key2865, -2), (key2824, -2), (key2865, -2), (key2635, 6), (key2855, -2), (key2789, -2), (key2855, -2), (key2626, -2), (key2610, -2), (key2626, -2), (key2700, -2), (key2665, -2), (key2700, -2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

def rawRow15578 : Integer.Sparse Key := [(key2721, 6), (key2865, -2), (key2865, -2), (key2824, -2), (key2635, 6), (key2855, -2), (key2855, -2), (key2789, -2), (key2626, -2), (key2626, -2), (key2610, -2), (key2700, -2), (key2700, -2), (key2665, -2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

def rawRow15579 : Integer.Sparse Key := [(key1000, -2), (key1000, -2), (key1014, -2), (key994, 6), (key1231, -2), (key1231, -2), (key1234, -2), (key1035, 2), (key1035, 2), (key1113, 2), (key1113, 2), (key1122, 2), (key1122, 2), (key1029, -2), (key1107, -2), (key1107, -2), (key1241, 6), (key1070, -2), (key1149, -2), (key1149, -2)]

def rawRow15580 : Integer.Sparse Key := [(key1000, -2), (key1014, -2), (key1000, -2), (key994, 6), (key1231, -2), (key1234, -2), (key1231, -2), (key1113, 2), (key1122, 2), (key1035, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1107, -2), (key1029, -2), (key1107, -2), (key1241, 6), (key1149, -2), (key1070, -2), (key1149, -2)]

def rawRow15581 : Integer.Sparse Key := [(key1014, -2), (key1000, -2), (key1000, -2), (key994, 6), (key1234, -2), (key1231, -2), (key1231, -2), (key1122, 2), (key1113, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1035, 2), (key1107, -2), (key1107, -2), (key1029, -2), (key1241, 6), (key1149, -2), (key1149, -2), (key1070, -2)]

def rawRow15582 : Integer.Sparse Key := [(key1231, -2), (key1231, -2), (key1234, -2), (key1241, 6), (key1000, -2), (key1000, -2), (key1014, -2), (key1035, 2), (key1035, 2), (key1113, 2), (key1113, 2), (key1122, 2), (key1122, 2), (key1070, -2), (key1149, -2), (key1149, -2), (key994, 6), (key1029, -2), (key1107, -2), (key1107, -2)]

def rawRow15583 : Integer.Sparse Key := [(key1231, -2), (key1234, -2), (key1231, -2), (key1241, 6), (key1000, -2), (key1014, -2), (key1000, -2), (key1113, 2), (key1122, 2), (key1035, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1149, -2), (key1070, -2), (key1149, -2), (key994, 6), (key1107, -2), (key1029, -2), (key1107, -2)]

def rawRow15584 : Integer.Sparse Key := [(key1234, -2), (key1231, -2), (key1231, -2), (key1241, 6), (key1014, -2), (key1000, -2), (key1000, -2), (key1122, 2), (key1113, 2), (key1122, 2), (key1035, 2), (key1113, 2), (key1035, 2), (key1149, -2), (key1149, -2), (key1070, -2), (key994, 6), (key1107, -2), (key1107, -2), (key1029, -2)]

def rawRow15585 : Integer.Sparse Key := [(key1044, 4), (key1130, 4), (key1130, 4), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1080, -2), (key1080, -2), (key1159, -2), (key1159, -2), (key1174, -2), (key1174, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

def rawRow15586 : Integer.Sparse Key := [(key1130, 4), (key1044, 4), (key1130, 4), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

def rawRow15587 : Integer.Sparse Key := [(key1130, 4), (key1130, 4), (key1044, 4), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1174, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1080, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

def rawRow15588 : Integer.Sparse Key := [(key1044, 4), (key1130, 4), (key1130, 4), (key1080, -2), (key1080, -2), (key1159, -2), (key1159, -2), (key1174, -2), (key1174, -2), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

def rawRow15589 : Integer.Sparse Key := [(key1130, 4), (key1044, 4), (key1130, 4), (key1159, -2), (key1174, -2), (key1080, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

def rawRow15590 : Integer.Sparse Key := [(key1130, 4), (key1130, 4), (key1044, 4), (key1174, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1080, -2), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

def rawRow15597 : Integer.Sparse Key := [(key2688, 4), (key2714, 4), (key2714, 4), (key2681, -4), (key2681, -4), (key2712, -4), (key2817, -4), (key2817, -4), (key2863, -4), (key2815, 12)]

def rawRow15598 : Integer.Sparse Key := [(key2714, 4), (key2688, 4), (key2714, 4), (key2681, -4), (key2712, -4), (key2681, -4), (key2817, -4), (key2863, -4), (key2817, -4), (key2815, 12)]

def rawRow15599 : Integer.Sparse Key := [(key2714, 4), (key2714, 4), (key2688, 4), (key2712, -4), (key2681, -4), (key2681, -4), (key2863, -4), (key2817, -4), (key2817, -4), (key2815, 12)]

def rawRow15600 : Integer.Sparse Key := [(key2688, 4), (key2817, 4), (key2817, 4), (key2681, -4), (key2681, -4), (key2815, -4), (key2714, -4), (key2714, -4), (key2863, -4), (key2712, 12)]

def rawRow15601 : Integer.Sparse Key := [(key2817, 4), (key2688, 4), (key2817, 4), (key2681, -4), (key2815, -4), (key2681, -4), (key2714, -4), (key2863, -4), (key2714, -4), (key2712, 12)]

def rawRow15602 : Integer.Sparse Key := [(key2817, 4), (key2817, 4), (key2688, 4), (key2815, -4), (key2681, -4), (key2681, -4), (key2863, -4), (key2714, -4), (key2714, -4), (key2712, 12)]

def rawRow15603 : Integer.Sparse Key := [(key2688, 4), (key2714, 4), (key2714, 4), (key2817, -4), (key2817, -4), (key2863, -4), (key2681, -4), (key2681, -4), (key2712, -4), (key2815, 12)]

def rawRow15604 : Integer.Sparse Key := [(key2714, 4), (key2688, 4), (key2714, 4), (key2817, -4), (key2863, -4), (key2817, -4), (key2681, -4), (key2712, -4), (key2681, -4), (key2815, 12)]

def rawRow15605 : Integer.Sparse Key := [(key2714, 4), (key2714, 4), (key2688, 4), (key2863, -4), (key2817, -4), (key2817, -4), (key2712, -4), (key2681, -4), (key2681, -4), (key2815, 12)]

def rawRow15606 : Integer.Sparse Key := [(key2688, 4), (key2817, 4), (key2817, 4), (key2714, -4), (key2714, -4), (key2863, -4), (key2681, -4), (key2681, -4), (key2815, -4), (key2712, 12)]

def rawRow15607 : Integer.Sparse Key := [(key2817, 4), (key2688, 4), (key2817, 4), (key2714, -4), (key2863, -4), (key2714, -4), (key2681, -4), (key2815, -4), (key2681, -4), (key2712, 12)]

def rawRow15608 : Integer.Sparse Key := [(key2817, 4), (key2817, 4), (key2688, 4), (key2863, -4), (key2714, -4), (key2714, -4), (key2815, -4), (key2681, -4), (key2681, -4), (key2712, 12)]

def rawRow15609 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2599, -2), (key2584, 6), (key2875, -2), (key2875, -2), (key2909, -2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2888, 2), (key2888, 2), (key2763, -2), (key2840, -2), (key2840, -2), (key2988, 6), (key2930, -2), (key2967, -2), (key2967, -2)]

def rawRow15610 : Integer.Sparse Key := [(key2588, -2), (key2599, -2), (key2588, -2), (key2584, 6), (key2875, -2), (key2909, -2), (key2875, -2), (key2844, 2), (key2888, 2), (key2767, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2840, -2), (key2763, -2), (key2840, -2), (key2988, 6), (key2967, -2), (key2930, -2), (key2967, -2)]

def rawRow15611 : Integer.Sparse Key := [(key2599, -2), (key2588, -2), (key2588, -2), (key2584, 6), (key2909, -2), (key2875, -2), (key2875, -2), (key2888, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2840, -2), (key2840, -2), (key2763, -2), (key2988, 6), (key2967, -2), (key2967, -2), (key2930, -2)]

def rawRow15612 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2930, -2), (key2763, 6), (key2875, -2), (key2875, -2), (key2988, -2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2967, 2), (key2967, 2), (key2584, -2), (key2840, -2), (key2840, -2), (key2909, 6), (key2599, -2), (key2888, -2), (key2888, -2)]

def rawRow15613 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2767, -2), (key2763, 6), (key2875, -2), (key2988, -2), (key2875, -2), (key2844, 2), (key2967, 2), (key2588, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2840, -2), (key2584, -2), (key2840, -2), (key2909, 6), (key2888, -2), (key2599, -2), (key2888, -2)]

def rawRow15614 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2767, -2), (key2763, 6), (key2988, -2), (key2875, -2), (key2875, -2), (key2967, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2840, -2), (key2840, -2), (key2584, -2), (key2909, 6), (key2888, -2), (key2888, -2), (key2599, -2)]

def rawRow15615 : Integer.Sparse Key := [(key2875, -2), (key2875, -2), (key2909, -2), (key2988, 6), (key2588, -2), (key2588, -2), (key2599, -2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2888, 2), (key2888, 2), (key2930, -2), (key2967, -2), (key2967, -2), (key2584, 6), (key2763, -2), (key2840, -2), (key2840, -2)]

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

def rawRow15616 : Integer.Sparse Key := [(key2875, -2), (key2909, -2), (key2875, -2), (key2988, 6), (key2588, -2), (key2599, -2), (key2588, -2), (key2844, 2), (key2888, 2), (key2767, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2967, -2), (key2930, -2), (key2967, -2), (key2584, 6), (key2840, -2), (key2763, -2), (key2840, -2)]

def rawRow15617 : Integer.Sparse Key := [(key2909, -2), (key2875, -2), (key2875, -2), (key2988, 6), (key2599, -2), (key2588, -2), (key2588, -2), (key2888, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2967, -2), (key2967, -2), (key2930, -2), (key2584, 6), (key2840, -2), (key2840, -2), (key2763, -2)]

def rawRow15618 : Integer.Sparse Key := [(key2875, -2), (key2875, -2), (key2988, -2), (key2909, 6), (key2767, -2), (key2767, -2), (key2930, -2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2967, 2), (key2967, 2), (key2599, -2), (key2888, -2), (key2888, -2), (key2763, 6), (key2584, -2), (key2840, -2), (key2840, -2)]

def rawRow15619 : Integer.Sparse Key := [(key2875, -2), (key2988, -2), (key2875, -2), (key2909, 6), (key2767, -2), (key2930, -2), (key2767, -2), (key2844, 2), (key2967, 2), (key2588, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2888, -2), (key2599, -2), (key2888, -2), (key2763, 6), (key2840, -2), (key2584, -2), (key2840, -2)]

def rawRow15620 : Integer.Sparse Key := [(key2988, -2), (key2875, -2), (key2875, -2), (key2909, 6), (key2930, -2), (key2767, -2), (key2767, -2), (key2967, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2888, -2), (key2888, -2), (key2599, -2), (key2763, 6), (key2840, -2), (key2840, -2), (key2584, -2)]

def rawRow15621 : Integer.Sparse Key := [(key2025, 4), (key2054, 4), (key2054, 4), (key2012, -4), (key2012, -4), (key2041, -4), (key2143, -4), (key2143, -4), (key2227, -4), (key2126, 12)]

def rawRow15622 : Integer.Sparse Key := [(key2054, 4), (key2025, 4), (key2054, 4), (key2012, -4), (key2041, -4), (key2012, -4), (key2143, -4), (key2227, -4), (key2143, -4), (key2126, 12)]

def rawRow15623 : Integer.Sparse Key := [(key2054, 4), (key2054, 4), (key2025, 4), (key2041, -4), (key2012, -4), (key2012, -4), (key2227, -4), (key2143, -4), (key2143, -4), (key2126, 12)]

def rawRow15624 : Integer.Sparse Key := [(key2025, 4), (key2143, 4), (key2143, 4), (key2012, -4), (key2012, -4), (key2126, -4), (key2054, -4), (key2054, -4), (key2227, -4), (key2041, 12)]

def rawRow15625 : Integer.Sparse Key := [(key2143, 4), (key2025, 4), (key2143, 4), (key2012, -4), (key2126, -4), (key2012, -4), (key2054, -4), (key2227, -4), (key2054, -4), (key2041, 12)]

def rawRow15626 : Integer.Sparse Key := [(key2143, 4), (key2143, 4), (key2025, 4), (key2126, -4), (key2012, -4), (key2012, -4), (key2227, -4), (key2054, -4), (key2054, -4), (key2041, 12)]

def rawRow15627 : Integer.Sparse Key := [(key2025, 4), (key2054, 4), (key2054, 4), (key2143, -4), (key2143, -4), (key2227, -4), (key2012, -4), (key2012, -4), (key2041, -4), (key2126, 12)]

def rawRow15628 : Integer.Sparse Key := [(key2054, 4), (key2025, 4), (key2054, 4), (key2143, -4), (key2227, -4), (key2143, -4), (key2012, -4), (key2041, -4), (key2012, -4), (key2126, 12)]

def rawRow15629 : Integer.Sparse Key := [(key2054, 4), (key2054, 4), (key2025, 4), (key2227, -4), (key2143, -4), (key2143, -4), (key2041, -4), (key2012, -4), (key2012, -4), (key2126, 12)]

def rawRow15630 : Integer.Sparse Key := [(key2025, 4), (key2143, 4), (key2143, 4), (key2054, -4), (key2054, -4), (key2227, -4), (key2012, -4), (key2012, -4), (key2126, -4), (key2041, 12)]

def rawRow15631 : Integer.Sparse Key := [(key2143, 4), (key2025, 4), (key2143, 4), (key2054, -4), (key2227, -4), (key2054, -4), (key2012, -4), (key2126, -4), (key2012, -4), (key2041, 12)]

def rawRow15632 : Integer.Sparse Key := [(key2143, 4), (key2143, 4), (key2025, 4), (key2227, -4), (key2054, -4), (key2054, -4), (key2126, -4), (key2012, -4), (key2012, -4), (key2041, 12)]

def rawRow15645 : Integer.Sparse Key := [(key1364, -2), (key1364, -2), (key1374, -2), (key1358, 6), (key1937, -2), (key1937, -2), (key1940, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1484, -2), (key1710, -2), (key1710, -2), (key1949, 6), (key1513, -2), (key1741, -2), (key1741, -2)]

def rawRow15646 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1364, -2), (key1358, 6), (key1937, -2), (key1940, -2), (key1937, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1710, -2), (key1484, -2), (key1710, -2), (key1949, 6), (key1741, -2), (key1513, -2), (key1741, -2)]

def rawRow15647 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1364, -2), (key1358, 6), (key1940, -2), (key1937, -2), (key1937, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1710, -2), (key1710, -2), (key1484, -2), (key1949, 6), (key1741, -2), (key1741, -2), (key1513, -2)]

def rawRow15648 : Integer.Sparse Key := [(key1490, -2), (key1490, -2), (key1513, -2), (key1484, 6), (key1937, -2), (key1937, -2), (key1949, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1358, -2), (key1710, -2), (key1710, -2), (key1940, 6), (key1374, -2), (key1723, -2), (key1723, -2)]

def rawRow15649 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1490, -2), (key1484, 6), (key1937, -2), (key1949, -2), (key1937, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1710, -2), (key1358, -2), (key1710, -2), (key1940, 6), (key1723, -2), (key1374, -2), (key1723, -2)]

def rawRow15650 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1490, -2), (key1484, 6), (key1949, -2), (key1937, -2), (key1937, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1710, -2), (key1710, -2), (key1358, -2), (key1940, 6), (key1723, -2), (key1723, -2), (key1374, -2)]

def rawRow15651 : Integer.Sparse Key := [(key1937, -2), (key1937, -2), (key1940, -2), (key1949, 6), (key1364, -2), (key1364, -2), (key1374, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1513, -2), (key1741, -2), (key1741, -2), (key1358, 6), (key1484, -2), (key1710, -2), (key1710, -2)]

def rawRow15652 : Integer.Sparse Key := [(key1937, -2), (key1940, -2), (key1937, -2), (key1949, 6), (key1364, -2), (key1374, -2), (key1364, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, -2), (key1513, -2), (key1741, -2), (key1358, 6), (key1710, -2), (key1484, -2), (key1710, -2)]

def rawRow15653 : Integer.Sparse Key := [(key1940, -2), (key1937, -2), (key1937, -2), (key1949, 6), (key1374, -2), (key1364, -2), (key1364, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1741, -2), (key1741, -2), (key1513, -2), (key1358, 6), (key1710, -2), (key1710, -2), (key1484, -2)]

def rawRow15654 : Integer.Sparse Key := [(key1937, -2), (key1937, -2), (key1949, -2), (key1940, 6), (key1490, -2), (key1490, -2), (key1513, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1374, -2), (key1723, -2), (key1723, -2), (key1484, 6), (key1358, -2), (key1710, -2), (key1710, -2)]

def rawRow15655 : Integer.Sparse Key := [(key1937, -2), (key1949, -2), (key1937, -2), (key1940, 6), (key1490, -2), (key1513, -2), (key1490, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1723, -2), (key1374, -2), (key1723, -2), (key1484, 6), (key1710, -2), (key1358, -2), (key1710, -2)]

def rawRow15656 : Integer.Sparse Key := [(key1949, -2), (key1937, -2), (key1937, -2), (key1940, 6), (key1513, -2), (key1490, -2), (key1490, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1723, -2), (key1723, -2), (key1374, -2), (key1484, 6), (key1710, -2), (key1710, -2), (key1358, -2)]

def rawRow15735 : Integer.Sparse Key := [(key994, -2), (key999, -2), (key1013, -2), (key999, 6), (key1107, -2), (key1112, -2), (key1121, -2), (key1029, 2), (key1034, 2), (key1107, 2), (key1191, 2), (key1121, 2), (key1197, 2), (key1034, -2), (key1112, -2), (key1191, -2), (key1148, 6), (key1069, -2), (key1148, -2), (key1210, -2)]

def rawRow15736 : Integer.Sparse Key := [(key999, -2), (key994, -2), (key1013, -2), (key999, 6), (key1112, -2), (key1107, -2), (key1121, -2), (key1034, 2), (key1029, 2), (key1191, 2), (key1107, 2), (key1197, 2), (key1121, 2), (key1034, -2), (key1191, -2), (key1112, -2), (key1148, 6), (key1069, -2), (key1210, -2), (key1148, -2)]

def rawRow15737 : Integer.Sparse Key := [(key994, -2), (key1013, -2), (key999, -2), (key999, 6), (key1107, -2), (key1121, -2), (key1112, -2), (key1107, 2), (key1121, 2), (key1029, 2), (key1197, 2), (key1034, 2), (key1191, 2), (key1112, -2), (key1034, -2), (key1191, -2), (key1148, 6), (key1148, -2), (key1069, -2), (key1210, -2)]

def rawRow15738 : Integer.Sparse Key := [(key1013, -2), (key994, -2), (key999, -2), (key999, 6), (key1121, -2), (key1107, -2), (key1112, -2), (key1121, 2), (key1107, 2), (key1197, 2), (key1029, 2), (key1191, 2), (key1034, 2), (key1112, -2), (key1191, -2), (key1034, -2), (key1148, 6), (key1148, -2), (key1210, -2), (key1069, -2)]

def rawRow15739 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key994, -2), (key999, 6), (key1112, -2), (key1121, -2), (key1107, -2), (key1191, 2), (key1197, 2), (key1034, 2), (key1121, 2), (key1029, 2), (key1107, 2), (key1191, -2), (key1034, -2), (key1112, -2), (key1148, 6), (key1210, -2), (key1069, -2), (key1148, -2)]

def rawRow15740 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key994, -2), (key999, 6), (key1121, -2), (key1112, -2), (key1107, -2), (key1197, 2), (key1191, 2), (key1121, 2), (key1034, 2), (key1107, 2), (key1029, 2), (key1191, -2), (key1112, -2), (key1034, -2), (key1148, 6), (key1210, -2), (key1148, -2), (key1069, -2)]

def rawRow15741 : Integer.Sparse Key := [(key999, -2), (key999, -2), (key1013, -2), (key994, 6), (key1191, -2), (key1191, -2), (key1197, -2), (key1034, 2), (key1034, 2), (key1112, 2), (key1112, 2), (key1121, 2), (key1121, 2), (key1029, -2), (key1107, -2), (key1107, -2), (key1210, 6), (key1069, -2), (key1148, -2), (key1148, -2)]

def rawRow15742 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key999, -2), (key994, 6), (key1191, -2), (key1197, -2), (key1191, -2), (key1112, 2), (key1121, 2), (key1034, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1107, -2), (key1029, -2), (key1107, -2), (key1210, 6), (key1148, -2), (key1069, -2), (key1148, -2)]

def rawRow15743 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key999, -2), (key994, 6), (key1197, -2), (key1191, -2), (key1191, -2), (key1121, 2), (key1112, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1034, 2), (key1107, -2), (key1107, -2), (key1029, -2), (key1210, 6), (key1148, -2), (key1148, -2), (key1069, -2)]

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

def rawRow15744 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1121, -2), (key1148, 6), (key994, -2), (key999, -2), (key1013, -2), (key1029, 2), (key1034, 2), (key1107, 2), (key1191, 2), (key1121, 2), (key1197, 2), (key1069, -2), (key1148, -2), (key1210, -2), (key999, 6), (key1034, -2), (key1112, -2), (key1191, -2)]

def rawRow15745 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1121, -2), (key1148, 6), (key999, -2), (key994, -2), (key1013, -2), (key1034, 2), (key1029, 2), (key1191, 2), (key1107, 2), (key1197, 2), (key1121, 2), (key1069, -2), (key1210, -2), (key1148, -2), (key999, 6), (key1034, -2), (key1191, -2), (key1112, -2)]

def rawRow15746 : Integer.Sparse Key := [(key1107, -2), (key1121, -2), (key1112, -2), (key1148, 6), (key994, -2), (key1013, -2), (key999, -2), (key1107, 2), (key1121, 2), (key1029, 2), (key1197, 2), (key1034, 2), (key1191, 2), (key1148, -2), (key1069, -2), (key1210, -2), (key999, 6), (key1112, -2), (key1034, -2), (key1191, -2)]

def rawRow15747 : Integer.Sparse Key := [(key1121, -2), (key1107, -2), (key1112, -2), (key1148, 6), (key1013, -2), (key994, -2), (key999, -2), (key1121, 2), (key1107, 2), (key1197, 2), (key1029, 2), (key1191, 2), (key1034, 2), (key1148, -2), (key1210, -2), (key1069, -2), (key999, 6), (key1112, -2), (key1191, -2), (key1034, -2)]

def rawRow15748 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1107, -2), (key1148, 6), (key999, -2), (key1013, -2), (key994, -2), (key1191, 2), (key1197, 2), (key1034, 2), (key1121, 2), (key1029, 2), (key1107, 2), (key1210, -2), (key1069, -2), (key1148, -2), (key999, 6), (key1191, -2), (key1034, -2), (key1112, -2)]

def rawRow15749 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1107, -2), (key1148, 6), (key1013, -2), (key999, -2), (key994, -2), (key1197, 2), (key1191, 2), (key1121, 2), (key1034, 2), (key1107, 2), (key1029, 2), (key1210, -2), (key1148, -2), (key1069, -2), (key999, 6), (key1191, -2), (key1112, -2), (key1034, -2)]

def rawRow15750 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1197, -2), (key1210, 6), (key999, -2), (key999, -2), (key1013, -2), (key1034, 2), (key1034, 2), (key1112, 2), (key1112, 2), (key1121, 2), (key1121, 2), (key1069, -2), (key1148, -2), (key1148, -2), (key994, 6), (key1029, -2), (key1107, -2), (key1107, -2)]

def rawRow15751 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1191, -2), (key1210, 6), (key999, -2), (key1013, -2), (key999, -2), (key1112, 2), (key1121, 2), (key1034, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1148, -2), (key1069, -2), (key1148, -2), (key994, 6), (key1107, -2), (key1029, -2), (key1107, -2)]

def rawRow15752 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1191, -2), (key1210, 6), (key1013, -2), (key999, -2), (key999, -2), (key1121, 2), (key1112, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1034, 2), (key1148, -2), (key1148, -2), (key1069, -2), (key994, 6), (key1107, -2), (key1107, -2), (key1029, -2)]

def rawRow15753 : Integer.Sparse Key := [(key2371, -2), (key2375, -2), (key2387, -2), (key2375, 6), (key2465, -2), (key2469, -2), (key2477, -2), (key2399, 2), (key2403, 2), (key2465, 2), (key2536, 2), (key2477, 2), (key2541, 2), (key2403, -2), (key2469, -2), (key2536, -2), (key2500, 6), (key2434, -2), (key2500, -2), (key2552, -2)]

def rawRow15754 : Integer.Sparse Key := [(key2375, -2), (key2371, -2), (key2387, -2), (key2375, 6), (key2469, -2), (key2465, -2), (key2477, -2), (key2403, 2), (key2399, 2), (key2536, 2), (key2465, 2), (key2541, 2), (key2477, 2), (key2403, -2), (key2536, -2), (key2469, -2), (key2500, 6), (key2434, -2), (key2552, -2), (key2500, -2)]

def rawRow15755 : Integer.Sparse Key := [(key2371, -2), (key2387, -2), (key2375, -2), (key2375, 6), (key2465, -2), (key2477, -2), (key2469, -2), (key2465, 2), (key2477, 2), (key2399, 2), (key2541, 2), (key2403, 2), (key2536, 2), (key2469, -2), (key2403, -2), (key2536, -2), (key2500, 6), (key2500, -2), (key2434, -2), (key2552, -2)]

def rawRow15756 : Integer.Sparse Key := [(key2387, -2), (key2371, -2), (key2375, -2), (key2375, 6), (key2477, -2), (key2465, -2), (key2469, -2), (key2477, 2), (key2465, 2), (key2541, 2), (key2399, 2), (key2536, 2), (key2403, 2), (key2469, -2), (key2536, -2), (key2403, -2), (key2500, 6), (key2500, -2), (key2552, -2), (key2434, -2)]

def rawRow15757 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2371, -2), (key2375, 6), (key2469, -2), (key2477, -2), (key2465, -2), (key2536, 2), (key2541, 2), (key2403, 2), (key2477, 2), (key2399, 2), (key2465, 2), (key2536, -2), (key2403, -2), (key2469, -2), (key2500, 6), (key2552, -2), (key2434, -2), (key2500, -2)]

def rawRow15758 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2371, -2), (key2375, 6), (key2477, -2), (key2469, -2), (key2465, -2), (key2541, 2), (key2536, 2), (key2477, 2), (key2403, 2), (key2465, 2), (key2399, 2), (key2536, -2), (key2469, -2), (key2403, -2), (key2500, 6), (key2552, -2), (key2500, -2), (key2434, -2)]

def rawRow15759 : Integer.Sparse Key := [(key2375, -2), (key2375, -2), (key2387, -2), (key2371, 6), (key2536, -2), (key2536, -2), (key2541, -2), (key2403, 2), (key2403, 2), (key2469, 2), (key2469, 2), (key2477, 2), (key2477, 2), (key2399, -2), (key2465, -2), (key2465, -2), (key2552, 6), (key2434, -2), (key2500, -2), (key2500, -2)]

def rawRow15760 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2375, -2), (key2371, 6), (key2536, -2), (key2541, -2), (key2536, -2), (key2469, 2), (key2477, 2), (key2403, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2465, -2), (key2399, -2), (key2465, -2), (key2552, 6), (key2500, -2), (key2434, -2), (key2500, -2)]

def rawRow15761 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2375, -2), (key2371, 6), (key2541, -2), (key2536, -2), (key2536, -2), (key2477, 2), (key2469, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2403, 2), (key2465, -2), (key2465, -2), (key2399, -2), (key2552, 6), (key2500, -2), (key2500, -2), (key2434, -2)]

def rawRow15762 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2477, -2), (key2500, 6), (key2371, -2), (key2375, -2), (key2387, -2), (key2399, 2), (key2403, 2), (key2465, 2), (key2536, 2), (key2477, 2), (key2541, 2), (key2434, -2), (key2500, -2), (key2552, -2), (key2375, 6), (key2403, -2), (key2469, -2), (key2536, -2)]

def rawRow15763 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2477, -2), (key2500, 6), (key2375, -2), (key2371, -2), (key2387, -2), (key2403, 2), (key2399, 2), (key2536, 2), (key2465, 2), (key2541, 2), (key2477, 2), (key2434, -2), (key2552, -2), (key2500, -2), (key2375, 6), (key2403, -2), (key2536, -2), (key2469, -2)]

def rawRow15764 : Integer.Sparse Key := [(key2465, -2), (key2477, -2), (key2469, -2), (key2500, 6), (key2371, -2), (key2387, -2), (key2375, -2), (key2465, 2), (key2477, 2), (key2399, 2), (key2541, 2), (key2403, 2), (key2536, 2), (key2500, -2), (key2434, -2), (key2552, -2), (key2375, 6), (key2469, -2), (key2403, -2), (key2536, -2)]

def rawRow15765 : Integer.Sparse Key := [(key2477, -2), (key2465, -2), (key2469, -2), (key2500, 6), (key2387, -2), (key2371, -2), (key2375, -2), (key2477, 2), (key2465, 2), (key2541, 2), (key2399, 2), (key2536, 2), (key2403, 2), (key2500, -2), (key2552, -2), (key2434, -2), (key2375, 6), (key2469, -2), (key2536, -2), (key2403, -2)]

def rawRow15766 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2465, -2), (key2500, 6), (key2375, -2), (key2387, -2), (key2371, -2), (key2536, 2), (key2541, 2), (key2403, 2), (key2477, 2), (key2399, 2), (key2465, 2), (key2552, -2), (key2434, -2), (key2500, -2), (key2375, 6), (key2536, -2), (key2403, -2), (key2469, -2)]

def rawRow15767 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2465, -2), (key2500, 6), (key2387, -2), (key2375, -2), (key2371, -2), (key2541, 2), (key2536, 2), (key2477, 2), (key2403, 2), (key2465, 2), (key2399, 2), (key2552, -2), (key2500, -2), (key2434, -2), (key2375, 6), (key2536, -2), (key2469, -2), (key2403, -2)]

def rawRow15768 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2541, -2), (key2552, 6), (key2375, -2), (key2375, -2), (key2387, -2), (key2403, 2), (key2403, 2), (key2469, 2), (key2469, 2), (key2477, 2), (key2477, 2), (key2434, -2), (key2500, -2), (key2500, -2), (key2371, 6), (key2399, -2), (key2465, -2), (key2465, -2)]

def rawRow15769 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2536, -2), (key2552, 6), (key2375, -2), (key2387, -2), (key2375, -2), (key2469, 2), (key2477, 2), (key2403, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2500, -2), (key2434, -2), (key2500, -2), (key2371, 6), (key2465, -2), (key2399, -2), (key2465, -2)]

def rawRow15770 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2536, -2), (key2552, 6), (key2387, -2), (key2375, -2), (key2375, -2), (key2477, 2), (key2469, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2403, 2), (key2500, -2), (key2500, -2), (key2434, -2), (key2371, 6), (key2465, -2), (key2465, -2), (key2399, -2)]

def rawRow15771 : Integer.Sparse Key := [(key2623, 6), (key2607, -2), (key2623, -2), (key2634, -2), (key2697, 6), (key2662, -2), (key2697, -2), (key2720, -2), (key2800, -2), (key2850, -2), (key2854, -2), (key2777, -2), (key2850, -2), (key2864, -2), (key2777, 2), (key2788, 2), (key2800, 2), (key2823, 2), (key2854, 2), (key2864, 2)]

def rawRow15772 : Integer.Sparse Key := [(key2623, 6), (key2607, -2), (key2634, -2), (key2623, -2), (key2697, 6), (key2662, -2), (key2720, -2), (key2697, -2), (key2800, -2), (key2854, -2), (key2850, -2), (key2777, -2), (key2864, -2), (key2850, -2), (key2788, 2), (key2777, 2), (key2823, 2), (key2800, 2), (key2864, 2), (key2854, 2)]

def rawRow15773 : Integer.Sparse Key := [(key2623, 6), (key2623, -2), (key2607, -2), (key2634, -2), (key2697, 6), (key2697, -2), (key2662, -2), (key2720, -2), (key2850, -2), (key2800, -2), (key2854, -2), (key2850, -2), (key2777, -2), (key2864, -2), (key2800, 2), (key2854, 2), (key2777, 2), (key2864, 2), (key2788, 2), (key2823, 2)]

def rawRow15774 : Integer.Sparse Key := [(key2623, 6), (key2623, -2), (key2634, -2), (key2607, -2), (key2697, 6), (key2697, -2), (key2720, -2), (key2662, -2), (key2850, -2), (key2854, -2), (key2800, -2), (key2850, -2), (key2864, -2), (key2777, -2), (key2854, 2), (key2800, 2), (key2864, 2), (key2777, 2), (key2823, 2), (key2788, 2)]

def rawRow15775 : Integer.Sparse Key := [(key2623, 6), (key2634, -2), (key2607, -2), (key2623, -2), (key2697, 6), (key2720, -2), (key2662, -2), (key2697, -2), (key2854, -2), (key2800, -2), (key2850, -2), (key2864, -2), (key2777, -2), (key2850, -2), (key2823, 2), (key2864, 2), (key2788, 2), (key2854, 2), (key2777, 2), (key2800, 2)]

def rawRow15776 : Integer.Sparse Key := [(key2623, 6), (key2634, -2), (key2623, -2), (key2607, -2), (key2697, 6), (key2720, -2), (key2697, -2), (key2662, -2), (key2854, -2), (key2850, -2), (key2800, -2), (key2864, -2), (key2850, -2), (key2777, -2), (key2864, 2), (key2823, 2), (key2854, 2), (key2788, 2), (key2800, 2), (key2777, 2)]

def rawRow15777 : Integer.Sparse Key := [(key2634, 6), (key2607, -2), (key2623, -2), (key2623, -2), (key2720, 6), (key2662, -2), (key2697, -2), (key2697, -2), (key2823, -2), (key2864, -2), (key2864, -2), (key2788, -2), (key2854, -2), (key2854, -2), (key2777, 2), (key2777, 2), (key2800, 2), (key2800, 2), (key2850, 2), (key2850, 2)]

def rawRow15778 : Integer.Sparse Key := [(key2634, 6), (key2623, -2), (key2607, -2), (key2623, -2), (key2720, 6), (key2697, -2), (key2662, -2), (key2697, -2), (key2864, -2), (key2823, -2), (key2864, -2), (key2854, -2), (key2788, -2), (key2854, -2), (key2800, 2), (key2850, 2), (key2777, 2), (key2850, 2), (key2777, 2), (key2800, 2)]

def rawRow15779 : Integer.Sparse Key := [(key2634, 6), (key2623, -2), (key2623, -2), (key2607, -2), (key2720, 6), (key2697, -2), (key2697, -2), (key2662, -2), (key2864, -2), (key2864, -2), (key2823, -2), (key2854, -2), (key2854, -2), (key2788, -2), (key2850, 2), (key2800, 2), (key2850, 2), (key2777, 2), (key2800, 2), (key2777, 2)]

def rawRow15780 : Integer.Sparse Key := [(key2697, 6), (key2800, -2), (key2850, -2), (key2854, -2), (key2623, 6), (key2777, -2), (key2850, -2), (key2864, -2), (key2607, -2), (key2623, -2), (key2634, -2), (key2662, -2), (key2697, -2), (key2720, -2), (key2777, 2), (key2788, 2), (key2800, 2), (key2823, 2), (key2854, 2), (key2864, 2)]

def rawRow15781 : Integer.Sparse Key := [(key2697, 6), (key2800, -2), (key2854, -2), (key2850, -2), (key2623, 6), (key2777, -2), (key2864, -2), (key2850, -2), (key2607, -2), (key2634, -2), (key2623, -2), (key2662, -2), (key2720, -2), (key2697, -2), (key2788, 2), (key2777, 2), (key2823, 2), (key2800, 2), (key2864, 2), (key2854, 2)]

def rawRow15782 : Integer.Sparse Key := [(key2697, 6), (key2850, -2), (key2800, -2), (key2854, -2), (key2623, 6), (key2850, -2), (key2777, -2), (key2864, -2), (key2623, -2), (key2607, -2), (key2634, -2), (key2697, -2), (key2662, -2), (key2720, -2), (key2800, 2), (key2854, 2), (key2777, 2), (key2864, 2), (key2788, 2), (key2823, 2)]

def rawRow15783 : Integer.Sparse Key := [(key2697, 6), (key2850, -2), (key2854, -2), (key2800, -2), (key2623, 6), (key2850, -2), (key2864, -2), (key2777, -2), (key2623, -2), (key2634, -2), (key2607, -2), (key2697, -2), (key2720, -2), (key2662, -2), (key2854, 2), (key2800, 2), (key2864, 2), (key2777, 2), (key2823, 2), (key2788, 2)]

def rawRow15784 : Integer.Sparse Key := [(key2697, 6), (key2854, -2), (key2800, -2), (key2850, -2), (key2623, 6), (key2864, -2), (key2777, -2), (key2850, -2), (key2634, -2), (key2607, -2), (key2623, -2), (key2720, -2), (key2662, -2), (key2697, -2), (key2823, 2), (key2864, 2), (key2788, 2), (key2854, 2), (key2777, 2), (key2800, 2)]

def rawRow15785 : Integer.Sparse Key := [(key2697, 6), (key2854, -2), (key2850, -2), (key2800, -2), (key2623, 6), (key2864, -2), (key2850, -2), (key2777, -2), (key2634, -2), (key2623, -2), (key2607, -2), (key2720, -2), (key2697, -2), (key2662, -2), (key2864, 2), (key2823, 2), (key2854, 2), (key2788, 2), (key2800, 2), (key2777, 2)]

def rawRow15786 : Integer.Sparse Key := [(key2720, 6), (key2823, -2), (key2864, -2), (key2864, -2), (key2634, 6), (key2788, -2), (key2854, -2), (key2854, -2), (key2607, -2), (key2623, -2), (key2623, -2), (key2662, -2), (key2697, -2), (key2697, -2), (key2777, 2), (key2777, 2), (key2800, 2), (key2800, 2), (key2850, 2), (key2850, 2)]

def rawRow15787 : Integer.Sparse Key := [(key2720, 6), (key2864, -2), (key2823, -2), (key2864, -2), (key2634, 6), (key2854, -2), (key2788, -2), (key2854, -2), (key2623, -2), (key2607, -2), (key2623, -2), (key2697, -2), (key2662, -2), (key2697, -2), (key2800, 2), (key2850, 2), (key2777, 2), (key2850, 2), (key2777, 2), (key2800, 2)]

def rawRow15788 : Integer.Sparse Key := [(key2720, 6), (key2864, -2), (key2864, -2), (key2823, -2), (key2634, 6), (key2854, -2), (key2854, -2), (key2788, -2), (key2623, -2), (key2623, -2), (key2607, -2), (key2697, -2), (key2697, -2), (key2662, -2), (key2850, 2), (key2800, 2), (key2850, 2), (key2777, 2), (key2800, 2), (key2777, 2)]

def rawRow15789 : Integer.Sparse Key := [(key993, -2), (key997, -2), (key1012, -2), (key997, 6), (key1106, -2), (key1110, -2), (key1120, -2), (key1028, 2), (key1032, 2), (key1106, 2), (key1189, 2), (key1120, 2), (key1196, 2), (key1032, -2), (key1110, -2), (key1189, -2), (key1147, 6), (key1068, -2), (key1147, -2), (key1209, -2)]

def rawRow15790 : Integer.Sparse Key := [(key997, -2), (key993, -2), (key1012, -2), (key997, 6), (key1110, -2), (key1106, -2), (key1120, -2), (key1032, 2), (key1028, 2), (key1189, 2), (key1106, 2), (key1196, 2), (key1120, 2), (key1032, -2), (key1189, -2), (key1110, -2), (key1147, 6), (key1068, -2), (key1209, -2), (key1147, -2)]

def rawRow15791 : Integer.Sparse Key := [(key993, -2), (key1012, -2), (key997, -2), (key997, 6), (key1106, -2), (key1120, -2), (key1110, -2), (key1106, 2), (key1120, 2), (key1028, 2), (key1196, 2), (key1032, 2), (key1189, 2), (key1110, -2), (key1032, -2), (key1189, -2), (key1147, 6), (key1147, -2), (key1068, -2), (key1209, -2)]

def rawRow15792 : Integer.Sparse Key := [(key1012, -2), (key993, -2), (key997, -2), (key997, 6), (key1120, -2), (key1106, -2), (key1110, -2), (key1120, 2), (key1106, 2), (key1196, 2), (key1028, 2), (key1189, 2), (key1032, 2), (key1110, -2), (key1189, -2), (key1032, -2), (key1147, 6), (key1147, -2), (key1209, -2), (key1068, -2)]

def rawRow15793 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key993, -2), (key997, 6), (key1110, -2), (key1120, -2), (key1106, -2), (key1189, 2), (key1196, 2), (key1032, 2), (key1120, 2), (key1028, 2), (key1106, 2), (key1189, -2), (key1032, -2), (key1110, -2), (key1147, 6), (key1209, -2), (key1068, -2), (key1147, -2)]

def rawRow15794 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key993, -2), (key997, 6), (key1120, -2), (key1110, -2), (key1106, -2), (key1196, 2), (key1189, 2), (key1120, 2), (key1032, 2), (key1106, 2), (key1028, 2), (key1189, -2), (key1110, -2), (key1032, -2), (key1147, 6), (key1209, -2), (key1147, -2), (key1068, -2)]

def rawRow15795 : Integer.Sparse Key := [(key997, -2), (key997, -2), (key1012, -2), (key993, 6), (key1189, -2), (key1189, -2), (key1196, -2), (key1032, 2), (key1032, 2), (key1110, 2), (key1110, 2), (key1120, 2), (key1120, 2), (key1028, -2), (key1106, -2), (key1106, -2), (key1209, 6), (key1068, -2), (key1147, -2), (key1147, -2)]

def rawRow15796 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key997, -2), (key993, 6), (key1189, -2), (key1196, -2), (key1189, -2), (key1110, 2), (key1120, 2), (key1032, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1106, -2), (key1028, -2), (key1106, -2), (key1209, 6), (key1147, -2), (key1068, -2), (key1147, -2)]

def rawRow15797 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key997, -2), (key993, 6), (key1196, -2), (key1189, -2), (key1189, -2), (key1120, 2), (key1110, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1032, 2), (key1106, -2), (key1106, -2), (key1028, -2), (key1209, 6), (key1147, -2), (key1147, -2), (key1068, -2)]

def rawRow15798 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1120, -2), (key1147, 6), (key993, -2), (key997, -2), (key1012, -2), (key1028, 2), (key1032, 2), (key1106, 2), (key1189, 2), (key1120, 2), (key1196, 2), (key1068, -2), (key1147, -2), (key1209, -2), (key997, 6), (key1032, -2), (key1110, -2), (key1189, -2)]

def rawRow15799 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1120, -2), (key1147, 6), (key997, -2), (key993, -2), (key1012, -2), (key1032, 2), (key1028, 2), (key1189, 2), (key1106, 2), (key1196, 2), (key1120, 2), (key1068, -2), (key1209, -2), (key1147, -2), (key997, 6), (key1032, -2), (key1189, -2), (key1110, -2)]

def rawRow15800 : Integer.Sparse Key := [(key1106, -2), (key1120, -2), (key1110, -2), (key1147, 6), (key993, -2), (key1012, -2), (key997, -2), (key1106, 2), (key1120, 2), (key1028, 2), (key1196, 2), (key1032, 2), (key1189, 2), (key1147, -2), (key1068, -2), (key1209, -2), (key997, 6), (key1110, -2), (key1032, -2), (key1189, -2)]

def rawRow15801 : Integer.Sparse Key := [(key1120, -2), (key1106, -2), (key1110, -2), (key1147, 6), (key1012, -2), (key993, -2), (key997, -2), (key1120, 2), (key1106, 2), (key1196, 2), (key1028, 2), (key1189, 2), (key1032, 2), (key1147, -2), (key1209, -2), (key1068, -2), (key997, 6), (key1110, -2), (key1189, -2), (key1032, -2)]

def rawRow15802 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1106, -2), (key1147, 6), (key997, -2), (key1012, -2), (key993, -2), (key1189, 2), (key1196, 2), (key1032, 2), (key1120, 2), (key1028, 2), (key1106, 2), (key1209, -2), (key1068, -2), (key1147, -2), (key997, 6), (key1189, -2), (key1032, -2), (key1110, -2)]

def rawRow15803 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1106, -2), (key1147, 6), (key1012, -2), (key997, -2), (key993, -2), (key1196, 2), (key1189, 2), (key1120, 2), (key1032, 2), (key1106, 2), (key1028, 2), (key1209, -2), (key1147, -2), (key1068, -2), (key997, 6), (key1189, -2), (key1110, -2), (key1032, -2)]

def rawRow15804 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1196, -2), (key1209, 6), (key997, -2), (key997, -2), (key1012, -2), (key1032, 2), (key1032, 2), (key1110, 2), (key1110, 2), (key1120, 2), (key1120, 2), (key1068, -2), (key1147, -2), (key1147, -2), (key993, 6), (key1028, -2), (key1106, -2), (key1106, -2)]

def rawRow15805 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1189, -2), (key1209, 6), (key997, -2), (key1012, -2), (key997, -2), (key1110, 2), (key1120, 2), (key1032, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1147, -2), (key1068, -2), (key1147, -2), (key993, 6), (key1106, -2), (key1028, -2), (key1106, -2)]

def rawRow15806 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1189, -2), (key1209, 6), (key1012, -2), (key997, -2), (key997, -2), (key1120, 2), (key1110, 2), (key1120, 2), (key1032, 2), (key1110, 2), (key1032, 2), (key1147, -2), (key1147, -2), (key1068, -2), (key993, 6), (key1106, -2), (key1106, -2), (key1028, -2)]

def rawRow15807 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1200, 4), (key1038, -2), (key1042, -2), (key1116, -2), (key1194, -2), (key1128, -2), (key1200, -2), (key1073, -2), (key1077, -2), (key1152, -2), (key1213, -2), (key1172, -2), (key1223, -2), (key1077, 4), (key1156, 4), (key1213, 4)]

def rawRow15808 : Integer.Sparse Key := [(key1038, 4), (key1200, 4), (key1125, 4), (key1042, -2), (key1038, -2), (key1194, -2), (key1116, -2), (key1200, -2), (key1128, -2), (key1077, -2), (key1073, -2), (key1213, -2), (key1152, -2), (key1223, -2), (key1172, -2), (key1077, 4), (key1213, 4), (key1156, 4)]

def rawRow15809 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1200, 4), (key1116, -2), (key1128, -2), (key1038, -2), (key1200, -2), (key1042, -2), (key1194, -2), (key1152, -2), (key1172, -2), (key1073, -2), (key1223, -2), (key1077, -2), (key1213, -2), (key1156, 4), (key1077, 4), (key1213, 4)]

def rawRow15810 : Integer.Sparse Key := [(key1125, 4), (key1200, 4), (key1038, 4), (key1128, -2), (key1116, -2), (key1200, -2), (key1038, -2), (key1194, -2), (key1042, -2), (key1172, -2), (key1152, -2), (key1223, -2), (key1073, -2), (key1213, -2), (key1077, -2), (key1156, 4), (key1213, 4), (key1077, 4)]

def rawRow15811 : Integer.Sparse Key := [(key1200, 4), (key1038, 4), (key1125, 4), (key1194, -2), (key1200, -2), (key1042, -2), (key1128, -2), (key1038, -2), (key1116, -2), (key1213, -2), (key1223, -2), (key1077, -2), (key1172, -2), (key1073, -2), (key1152, -2), (key1213, 4), (key1077, 4), (key1156, 4)]

def rawRow15812 : Integer.Sparse Key := [(key1200, 4), (key1125, 4), (key1038, 4), (key1200, -2), (key1194, -2), (key1128, -2), (key1042, -2), (key1116, -2), (key1038, -2), (key1223, -2), (key1213, -2), (key1172, -2), (key1077, -2), (key1152, -2), (key1073, -2), (key1213, 4), (key1156, 4), (key1077, 4)]

def rawRow15813 : Integer.Sparse Key := [(key1042, 4), (key1128, 4), (key1128, 4), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1077, -2), (key1077, -2), (key1156, -2), (key1156, -2), (key1172, -2), (key1172, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

def rawRow15814 : Integer.Sparse Key := [(key1128, 4), (key1042, 4), (key1128, 4), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1156, -2), (key1172, -2), (key1077, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

def rawRow15815 : Integer.Sparse Key := [(key1128, 4), (key1128, 4), (key1042, 4), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1172, -2), (key1156, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1077, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

def rawRow15816 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1200, 4), (key1073, -2), (key1077, -2), (key1152, -2), (key1213, -2), (key1172, -2), (key1223, -2), (key1038, -2), (key1042, -2), (key1116, -2), (key1194, -2), (key1128, -2), (key1200, -2), (key1077, 4), (key1156, 4), (key1213, 4)]

def rawRow15817 : Integer.Sparse Key := [(key1038, 4), (key1200, 4), (key1125, 4), (key1077, -2), (key1073, -2), (key1213, -2), (key1152, -2), (key1223, -2), (key1172, -2), (key1042, -2), (key1038, -2), (key1194, -2), (key1116, -2), (key1200, -2), (key1128, -2), (key1077, 4), (key1213, 4), (key1156, 4)]

def rawRow15818 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1200, 4), (key1152, -2), (key1172, -2), (key1073, -2), (key1223, -2), (key1077, -2), (key1213, -2), (key1116, -2), (key1128, -2), (key1038, -2), (key1200, -2), (key1042, -2), (key1194, -2), (key1156, 4), (key1077, 4), (key1213, 4)]

def rawRow15819 : Integer.Sparse Key := [(key1125, 4), (key1200, 4), (key1038, 4), (key1172, -2), (key1152, -2), (key1223, -2), (key1073, -2), (key1213, -2), (key1077, -2), (key1128, -2), (key1116, -2), (key1200, -2), (key1038, -2), (key1194, -2), (key1042, -2), (key1156, 4), (key1213, 4), (key1077, 4)]

def rawRow15820 : Integer.Sparse Key := [(key1200, 4), (key1038, 4), (key1125, 4), (key1213, -2), (key1223, -2), (key1077, -2), (key1172, -2), (key1073, -2), (key1152, -2), (key1194, -2), (key1200, -2), (key1042, -2), (key1128, -2), (key1038, -2), (key1116, -2), (key1213, 4), (key1077, 4), (key1156, 4)]

def rawRow15821 : Integer.Sparse Key := [(key1200, 4), (key1125, 4), (key1038, 4), (key1223, -2), (key1213, -2), (key1172, -2), (key1077, -2), (key1152, -2), (key1073, -2), (key1200, -2), (key1194, -2), (key1128, -2), (key1042, -2), (key1116, -2), (key1038, -2), (key1213, 4), (key1156, 4), (key1077, 4)]

def rawRow15822 : Integer.Sparse Key := [(key1042, 4), (key1128, 4), (key1128, 4), (key1077, -2), (key1077, -2), (key1156, -2), (key1156, -2), (key1172, -2), (key1172, -2), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1073, 4), (key1152, 4), (key1152, 4)]

def rawRow15823 : Integer.Sparse Key := [(key1128, 4), (key1042, 4), (key1128, 4), (key1156, -2), (key1172, -2), (key1077, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, 4), (key1073, 4), (key1152, 4)]

def rawRow15824 : Integer.Sparse Key := [(key1128, 4), (key1128, 4), (key1042, 4), (key1172, -2), (key1156, -2), (key1172, -2), (key1077, -2), (key1156, -2), (key1077, -2), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1152, 4), (key1152, 4), (key1073, 4)]

def rawRow15843 : Integer.Sparse Key := [(key2678, 4), (key2709, 4), (key2713, 4), (key2678, -4), (key2687, -4), (key2713, -4), (key2812, -4), (key2816, -4), (key2862, -4), (key2816, 12)]

def rawRow15844 : Integer.Sparse Key := [(key2678, 4), (key2713, 4), (key2709, 4), (key2687, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2812, -4), (key2862, -4), (key2816, 12)]

def rawRow15845 : Integer.Sparse Key := [(key2709, 4), (key2678, 4), (key2713, 4), (key2678, -4), (key2713, -4), (key2687, -4), (key2812, -4), (key2862, -4), (key2816, -4), (key2816, 12)]

def rawRow15846 : Integer.Sparse Key := [(key2709, 4), (key2713, 4), (key2678, 4), (key2713, -4), (key2678, -4), (key2687, -4), (key2862, -4), (key2812, -4), (key2816, -4), (key2816, 12)]

def rawRow15847 : Integer.Sparse Key := [(key2713, 4), (key2678, 4), (key2709, 4), (key2687, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2862, -4), (key2812, -4), (key2816, 12)]

def rawRow15848 : Integer.Sparse Key := [(key2713, 4), (key2709, 4), (key2678, 4), (key2713, -4), (key2687, -4), (key2678, -4), (key2862, -4), (key2816, -4), (key2812, -4), (key2816, 12)]

def rawRow15849 : Integer.Sparse Key := [(key2687, 4), (key2713, 4), (key2713, 4), (key2678, -4), (key2678, -4), (key2709, -4), (key2816, -4), (key2816, -4), (key2862, -4), (key2812, 12)]

def rawRow15850 : Integer.Sparse Key := [(key2713, 4), (key2687, 4), (key2713, 4), (key2678, -4), (key2709, -4), (key2678, -4), (key2816, -4), (key2862, -4), (key2816, -4), (key2812, 12)]

def rawRow15851 : Integer.Sparse Key := [(key2713, 4), (key2713, 4), (key2687, 4), (key2709, -4), (key2678, -4), (key2678, -4), (key2862, -4), (key2816, -4), (key2816, -4), (key2812, 12)]

def rawRow15852 : Integer.Sparse Key := [(key2678, 4), (key2709, 4), (key2713, 4), (key2812, -4), (key2816, -4), (key2862, -4), (key2678, -4), (key2687, -4), (key2713, -4), (key2816, 12)]

def rawRow15853 : Integer.Sparse Key := [(key2678, 4), (key2713, 4), (key2709, 4), (key2816, -4), (key2812, -4), (key2862, -4), (key2687, -4), (key2678, -4), (key2713, -4), (key2816, 12)]

def rawRow15854 : Integer.Sparse Key := [(key2709, 4), (key2678, 4), (key2713, 4), (key2812, -4), (key2862, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2687, -4), (key2816, 12)]

def rawRow15855 : Integer.Sparse Key := [(key2709, 4), (key2713, 4), (key2678, 4), (key2862, -4), (key2812, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2687, -4), (key2816, 12)]

def rawRow15856 : Integer.Sparse Key := [(key2713, 4), (key2678, 4), (key2709, 4), (key2816, -4), (key2862, -4), (key2812, -4), (key2687, -4), (key2713, -4), (key2678, -4), (key2816, 12)]

def rawRow15857 : Integer.Sparse Key := [(key2713, 4), (key2709, 4), (key2678, 4), (key2862, -4), (key2816, -4), (key2812, -4), (key2713, -4), (key2687, -4), (key2678, -4), (key2816, 12)]

def rawRow15858 : Integer.Sparse Key := [(key2687, 4), (key2713, 4), (key2713, 4), (key2816, -4), (key2816, -4), (key2862, -4), (key2678, -4), (key2678, -4), (key2709, -4), (key2812, 12)]

def rawRow15859 : Integer.Sparse Key := [(key2713, 4), (key2687, 4), (key2713, 4), (key2816, -4), (key2862, -4), (key2816, -4), (key2678, -4), (key2709, -4), (key2678, -4), (key2812, 12)]

def rawRow15860 : Integer.Sparse Key := [(key2713, 4), (key2713, 4), (key2687, 4), (key2862, -4), (key2816, -4), (key2816, -4), (key2709, -4), (key2678, -4), (key2678, -4), (key2812, 12)]

def rawRow15861 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2373, 6), (key2839, -2), (key2842, -2), (key2886, -2), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2765, -2), (key2842, -2), (key2874, -2), (key2965, 6), (key2928, -2), (key2965, -2), (key2987, -2)]

def rawRow15862 : Integer.Sparse Key := [(key2373, -2), (key2370, -2), (key2386, -2), (key2373, 6), (key2842, -2), (key2839, -2), (key2886, -2), (key2765, 2), (key2762, 2), (key2874, 2), (key2839, 2), (key2908, 2), (key2886, 2), (key2765, -2), (key2874, -2), (key2842, -2), (key2965, 6), (key2928, -2), (key2987, -2), (key2965, -2)]

def rawRow15863 : Integer.Sparse Key := [(key2370, -2), (key2386, -2), (key2373, -2), (key2373, 6), (key2839, -2), (key2886, -2), (key2842, -2), (key2839, 2), (key2886, 2), (key2762, 2), (key2908, 2), (key2765, 2), (key2874, 2), (key2842, -2), (key2765, -2), (key2874, -2), (key2965, 6), (key2965, -2), (key2928, -2), (key2987, -2)]

def rawRow15864 : Integer.Sparse Key := [(key2386, -2), (key2370, -2), (key2373, -2), (key2373, 6), (key2886, -2), (key2839, -2), (key2842, -2), (key2886, 2), (key2839, 2), (key2908, 2), (key2762, 2), (key2874, 2), (key2765, 2), (key2842, -2), (key2874, -2), (key2765, -2), (key2965, 6), (key2965, -2), (key2987, -2), (key2928, -2)]

def rawRow15865 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2370, -2), (key2373, 6), (key2842, -2), (key2886, -2), (key2839, -2), (key2874, 2), (key2908, 2), (key2765, 2), (key2886, 2), (key2762, 2), (key2839, 2), (key2874, -2), (key2765, -2), (key2842, -2), (key2965, 6), (key2987, -2), (key2928, -2), (key2965, -2)]

def rawRow15866 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2370, -2), (key2373, 6), (key2886, -2), (key2842, -2), (key2839, -2), (key2908, 2), (key2874, 2), (key2886, 2), (key2765, 2), (key2839, 2), (key2762, 2), (key2874, -2), (key2842, -2), (key2765, -2), (key2965, 6), (key2987, -2), (key2965, -2), (key2928, -2)]

def rawRow15867 : Integer.Sparse Key := [(key2373, -2), (key2373, -2), (key2386, -2), (key2370, 6), (key2874, -2), (key2874, -2), (key2908, -2), (key2765, 2), (key2765, 2), (key2842, 2), (key2842, 2), (key2886, 2), (key2886, 2), (key2762, -2), (key2839, -2), (key2839, -2), (key2987, 6), (key2928, -2), (key2965, -2), (key2965, -2)]

def rawRow15868 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2373, -2), (key2370, 6), (key2874, -2), (key2908, -2), (key2874, -2), (key2842, 2), (key2886, 2), (key2765, 2), (key2886, 2), (key2765, 2), (key2842, 2), (key2839, -2), (key2762, -2), (key2839, -2), (key2987, 6), (key2965, -2), (key2928, -2), (key2965, -2)]

def rawRow15869 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2373, -2), (key2370, 6), (key2908, -2), (key2874, -2), (key2874, -2), (key2886, 2), (key2842, 2), (key2886, 2), (key2765, 2), (key2842, 2), (key2765, 2), (key2839, -2), (key2839, -2), (key2762, -2), (key2987, 6), (key2965, -2), (key2965, -2), (key2928, -2)]

def rawRow15870 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2370, -2), (key2373, -2), (key2386, -2), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, -2), (key2965, -2), (key2987, -2), (key2586, 6), (key2765, -2), (key2842, -2), (key2874, -2)]

def rawRow15871 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2476, -2), (key2499, 6), (key2373, -2), (key2370, -2), (key2386, -2), (key2765, 2), (key2762, 2), (key2874, 2), (key2839, 2), (key2908, 2), (key2886, 2), (key2928, -2), (key2987, -2), (key2965, -2), (key2586, 6), (key2765, -2), (key2874, -2), (key2842, -2)]

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

def rawRow15872 : Integer.Sparse Key := [(key2464, -2), (key2476, -2), (key2467, -2), (key2499, 6), (key2370, -2), (key2386, -2), (key2373, -2), (key2839, 2), (key2886, 2), (key2762, 2), (key2908, 2), (key2765, 2), (key2874, 2), (key2965, -2), (key2928, -2), (key2987, -2), (key2586, 6), (key2842, -2), (key2765, -2), (key2874, -2)]

def rawRow15873 : Integer.Sparse Key := [(key2476, -2), (key2464, -2), (key2467, -2), (key2499, 6), (key2386, -2), (key2370, -2), (key2373, -2), (key2886, 2), (key2839, 2), (key2908, 2), (key2762, 2), (key2874, 2), (key2765, 2), (key2965, -2), (key2987, -2), (key2928, -2), (key2586, 6), (key2842, -2), (key2874, -2), (key2765, -2)]

def rawRow15874 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2464, -2), (key2499, 6), (key2373, -2), (key2386, -2), (key2370, -2), (key2874, 2), (key2908, 2), (key2765, 2), (key2886, 2), (key2762, 2), (key2839, 2), (key2987, -2), (key2928, -2), (key2965, -2), (key2586, 6), (key2874, -2), (key2765, -2), (key2842, -2)]

def rawRow15875 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2464, -2), (key2499, 6), (key2386, -2), (key2373, -2), (key2370, -2), (key2908, 2), (key2874, 2), (key2886, 2), (key2765, 2), (key2839, 2), (key2762, 2), (key2987, -2), (key2965, -2), (key2928, -2), (key2586, 6), (key2874, -2), (key2842, -2), (key2765, -2)]

def rawRow15876 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2540, -2), (key2551, 6), (key2373, -2), (key2373, -2), (key2386, -2), (key2401, 2), (key2401, 2), (key2467, 2), (key2467, 2), (key2476, 2), (key2476, 2), (key2433, -2), (key2499, -2), (key2499, -2), (key2370, 6), (key2762, -2), (key2839, -2), (key2839, -2)]

def rawRow15877 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2534, -2), (key2551, 6), (key2373, -2), (key2386, -2), (key2373, -2), (key2467, 2), (key2476, 2), (key2401, 2), (key2476, 2), (key2401, 2), (key2467, 2), (key2499, -2), (key2433, -2), (key2499, -2), (key2370, 6), (key2839, -2), (key2762, -2), (key2839, -2)]

def rawRow15878 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2534, -2), (key2551, 6), (key2386, -2), (key2373, -2), (key2373, -2), (key2476, 2), (key2467, 2), (key2476, 2), (key2401, 2), (key2467, 2), (key2401, 2), (key2499, -2), (key2499, -2), (key2433, -2), (key2370, 6), (key2839, -2), (key2839, -2), (key2762, -2)]

def rawRow15879 : Integer.Sparse Key := [(key2011, 4), (key2040, 4), (key2048, 4), (key2011, -4), (key2020, -4), (key2048, -4), (key2125, -4), (key2135, -4), (key2220, -4), (key2135, 12)]

def rawRow15880 : Integer.Sparse Key := [(key2011, 4), (key2048, 4), (key2040, 4), (key2020, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2125, -4), (key2220, -4), (key2135, 12)]

def rawRow15881 : Integer.Sparse Key := [(key2040, 4), (key2011, 4), (key2048, 4), (key2011, -4), (key2048, -4), (key2020, -4), (key2125, -4), (key2220, -4), (key2135, -4), (key2135, 12)]

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

def rawRow1493 : Integer.Sparse Key := [(key2999, -2), (key2899, -2), (key2739, -2), (key3004, 1), (key3001, 1), (key2915, 1), (key2751, 1), (key2906, 1), (key2749, 1), (key2946, 2), (key2797, 2), (key2675, 2), (key2994, -1), (key2964, -1), (key2915, -1), (key2751, -1), (key2833, -1), (key2730, -1), (key2749, -1), (key2730, -1), (key2739, -1), (key2675, -1), (key2707, -1), (key2672, -1), (key2906, 1), (key2833, 1), (key2899, 1), (key2797, 1), (key2810, 1), (key2787, 1)]

def rawRow1495 : Integer.Sparse Key := [(key1314, -6), (key1335, 2), (key1294, 2), (key1335, 2), (key1544, 6), (key1770, -2), (key1389, -2), (key1770, -2), (key1653, -2), (key1571, -2), (key1653, -2), (key1811, 2), (key1422, 2), (key1811, 2)]

def rawRow1496 : Integer.Sparse Key := [(key1314, -6), (key1335, 2), (key1335, 2), (key1294, 2), (key1544, 6), (key1770, -2), (key1770, -2), (key1389, -2), (key1653, -2), (key1653, -2), (key1571, -2), (key1811, 2), (key1811, 2), (key1422, 2)]

def rawRow1497 : Integer.Sparse Key := [(key1335, -6), (key1294, 2), (key1314, 2), (key1335, 2), (key1770, 6), (key1389, -2), (key1544, -2), (key1770, -2), (key1786, -2), (key1811, -2), (key1838, -2), (key1453, 2), (key1653, 2), (key1838, 2)]

def rawRow1498 : Integer.Sparse Key := [(key1335, -6), (key1294, 2), (key1335, 2), (key1314, 2), (key1770, 6), (key1389, -2), (key1770, -2), (key1544, -2), (key1786, -2), (key1838, -2), (key1811, -2), (key1453, 2), (key1838, 2), (key1653, 2)]

def rawRow1499 : Integer.Sparse Key := [(key1335, -6), (key1314, 2), (key1294, 2), (key1335, 2), (key1770, 6), (key1544, -2), (key1389, -2), (key1770, -2), (key1811, -2), (key1786, -2), (key1838, -2), (key1653, 2), (key1453, 2), (key1838, 2)]

def rawRow1500 : Integer.Sparse Key := [(key1335, -6), (key1314, 2), (key1335, 2), (key1294, 2), (key1770, 6), (key1544, -2), (key1770, -2), (key1389, -2), (key1811, -2), (key1838, -2), (key1786, -2), (key1653, 2), (key1838, 2), (key1453, 2)]

def rawRow1501 : Integer.Sparse Key := [(key1335, -6), (key1335, 2), (key1294, 2), (key1314, 2), (key1770, 6), (key1770, -2), (key1389, -2), (key1544, -2), (key1838, -2), (key1786, -2), (key1811, -2), (key1838, 2), (key1453, 2), (key1653, 2)]

def rawRow1502 : Integer.Sparse Key := [(key1335, -6), (key1335, 2), (key1314, 2), (key1294, 2), (key1770, 6), (key1770, -2), (key1544, -2), (key1389, -2), (key1838, -2), (key1811, -2), (key1786, -2), (key1838, 2), (key1653, 2), (key1453, 2)]

def rawRow1503 : Integer.Sparse Key := [(key1544, -6), (key1571, 2), (key1653, 2), (key1653, 2), (key1314, 6), (key1422, -2), (key1811, -2), (key1811, -2), (key1294, -2), (key1335, -2), (key1335, -2), (key1389, 2), (key1770, 2), (key1770, 2)]

def rawRow1504 : Integer.Sparse Key := [(key1544, -6), (key1653, 2), (key1571, 2), (key1653, 2), (key1314, 6), (key1811, -2), (key1422, -2), (key1811, -2), (key1335, -2), (key1294, -2), (key1335, -2), (key1770, 2), (key1389, 2), (key1770, 2)]

def rawRow1505 : Integer.Sparse Key := [(key1544, -6), (key1653, 2), (key1653, 2), (key1571, 2), (key1314, 6), (key1811, -2), (key1811, -2), (key1422, -2), (key1335, -2), (key1335, -2), (key1294, -2), (key1770, 2), (key1770, 2), (key1389, 2)]

def rawRow1506 : Integer.Sparse Key := [(key1653, -6), (key1544, 2), (key1571, 2), (key1653, 2), (key1811, 6), (key1314, -2), (key1422, -2), (key1811, -2), (key1770, -2), (key1786, -2), (key1838, -2), (key1335, 2), (key1453, 2), (key1838, 2)]

def rawRow1507 : Integer.Sparse Key := [(key1653, -6), (key1544, 2), (key1653, 2), (key1571, 2), (key1811, 6), (key1314, -2), (key1811, -2), (key1422, -2), (key1770, -2), (key1838, -2), (key1786, -2), (key1335, 2), (key1838, 2), (key1453, 2)]

def rawRow1508 : Integer.Sparse Key := [(key1653, -6), (key1571, 2), (key1544, 2), (key1653, 2), (key1811, 6), (key1422, -2), (key1314, -2), (key1811, -2), (key1786, -2), (key1770, -2), (key1838, -2), (key1453, 2), (key1335, 2), (key1838, 2)]

def rawRow1509 : Integer.Sparse Key := [(key1653, -6), (key1571, 2), (key1653, 2), (key1544, 2), (key1811, 6), (key1422, -2), (key1811, -2), (key1314, -2), (key1786, -2), (key1838, -2), (key1770, -2), (key1453, 2), (key1838, 2), (key1335, 2)]

def rawRow1510 : Integer.Sparse Key := [(key1653, -6), (key1653, 2), (key1544, 2), (key1571, 2), (key1811, 6), (key1811, -2), (key1314, -2), (key1422, -2), (key1838, -2), (key1770, -2), (key1786, -2), (key1838, 2), (key1335, 2), (key1453, 2)]

def rawRow1511 : Integer.Sparse Key := [(key1653, -6), (key1653, 2), (key1571, 2), (key1544, 2), (key1811, 6), (key1811, -2), (key1422, -2), (key1314, -2), (key1838, -2), (key1786, -2), (key1770, -2), (key1838, 2), (key1453, 2), (key1335, 2)]

def rawRow1512 : Integer.Sparse Key := [(key1770, -6), (key1786, 2), (key1811, 2), (key1838, 2), (key1335, 6), (key1453, -2), (key1653, -2), (key1838, -2), (key1294, -2), (key1314, -2), (key1335, -2), (key1389, 2), (key1544, 2), (key1770, 2)]

def rawRow1513 : Integer.Sparse Key := [(key1770, -6), (key1786, 2), (key1838, 2), (key1811, 2), (key1335, 6), (key1453, -2), (key1838, -2), (key1653, -2), (key1294, -2), (key1335, -2), (key1314, -2), (key1389, 2), (key1770, 2), (key1544, 2)]

def rawRow1514 : Integer.Sparse Key := [(key1770, -6), (key1811, 2), (key1786, 2), (key1838, 2), (key1335, 6), (key1653, -2), (key1453, -2), (key1838, -2), (key1314, -2), (key1294, -2), (key1335, -2), (key1544, 2), (key1389, 2), (key1770, 2)]

def rawRow1515 : Integer.Sparse Key := [(key1770, -6), (key1811, 2), (key1838, 2), (key1786, 2), (key1335, 6), (key1653, -2), (key1838, -2), (key1453, -2), (key1314, -2), (key1335, -2), (key1294, -2), (key1544, 2), (key1770, 2), (key1389, 2)]

def rawRow1516 : Integer.Sparse Key := [(key1770, -6), (key1838, 2), (key1786, 2), (key1811, 2), (key1335, 6), (key1838, -2), (key1453, -2), (key1653, -2), (key1335, -2), (key1294, -2), (key1314, -2), (key1770, 2), (key1389, 2), (key1544, 2)]

def rawRow1517 : Integer.Sparse Key := [(key1770, -6), (key1838, 2), (key1811, 2), (key1786, 2), (key1335, 6), (key1838, -2), (key1653, -2), (key1453, -2), (key1335, -2), (key1314, -2), (key1294, -2), (key1770, 2), (key1544, 2), (key1389, 2)]

def rawRow1518 : Integer.Sparse Key := [(key1811, -6), (key1770, 2), (key1786, 2), (key1838, 2), (key1653, 6), (key1335, -2), (key1453, -2), (key1838, -2), (key1544, -2), (key1571, -2), (key1653, -2), (key1314, 2), (key1422, 2), (key1811, 2)]

def rawRow1519 : Integer.Sparse Key := [(key1811, -6), (key1770, 2), (key1838, 2), (key1786, 2), (key1653, 6), (key1335, -2), (key1838, -2), (key1453, -2), (key1544, -2), (key1653, -2), (key1571, -2), (key1314, 2), (key1811, 2), (key1422, 2)]

def rawRow1520 : Integer.Sparse Key := [(key1811, -6), (key1786, 2), (key1770, 2), (key1838, 2), (key1653, 6), (key1453, -2), (key1335, -2), (key1838, -2), (key1571, -2), (key1544, -2), (key1653, -2), (key1422, 2), (key1314, 2), (key1811, 2)]

def rawRow1521 : Integer.Sparse Key := [(key1811, -6), (key1786, 2), (key1838, 2), (key1770, 2), (key1653, 6), (key1453, -2), (key1838, -2), (key1335, -2), (key1571, -2), (key1653, -2), (key1544, -2), (key1422, 2), (key1811, 2), (key1314, 2)]

def rawRow1522 : Integer.Sparse Key := [(key1811, -6), (key1838, 2), (key1770, 2), (key1786, 2), (key1653, 6), (key1838, -2), (key1335, -2), (key1453, -2), (key1653, -2), (key1544, -2), (key1571, -2), (key1811, 2), (key1314, 2), (key1422, 2)]

def rawRow1523 : Integer.Sparse Key := [(key1811, -6), (key1838, 2), (key1786, 2), (key1770, 2), (key1653, 6), (key1838, -2), (key1453, -2), (key1335, -2), (key1653, -2), (key1571, -2), (key1544, -2), (key1811, 2), (key1422, 2), (key1314, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1554 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1019, -2), (key1006, 6), (key1111, 2), (key1111, 2), (key1127, 2), (key1041, -2), (key1193, -2), (key1193, -2), (key1155, -6), (key1076, 2), (key1212, 2), (key1212, 2)]

def rawRow1555 : Integer.Sparse Key := [(key998, -2), (key1019, -2), (key998, -2), (key1006, 6), (key1111, 2), (key1127, 2), (key1111, 2), (key1193, -2), (key1041, -2), (key1193, -2), (key1155, -6), (key1212, 2), (key1076, 2), (key1212, 2)]

def rawRow1556 : Integer.Sparse Key := [(key1019, -2), (key998, -2), (key998, -2), (key1006, 6), (key1127, 2), (key1111, 2), (key1111, 2), (key1193, -2), (key1193, -2), (key1041, -2), (key1155, -6), (key1212, 2), (key1212, 2), (key1076, 2)]

def rawRow1557 : Integer.Sparse Key := [(key998, -2), (key1006, -2), (key1019, -2), (key998, 6), (key1190, 2), (key1193, 2), (key1199, 2), (key1033, -2), (key1111, -2), (key1190, -2), (key1212, -6), (key1076, 2), (key1155, 2), (key1212, 2)]

def rawRow1558 : Integer.Sparse Key := [(key1006, -2), (key998, -2), (key1019, -2), (key998, 6), (key1193, 2), (key1190, 2), (key1199, 2), (key1033, -2), (key1190, -2), (key1111, -2), (key1212, -6), (key1076, 2), (key1212, 2), (key1155, 2)]

def rawRow1559 : Integer.Sparse Key := [(key998, -2), (key1019, -2), (key1006, -2), (key998, 6), (key1190, 2), (key1199, 2), (key1193, 2), (key1111, -2), (key1033, -2), (key1190, -2), (key1212, -6), (key1155, 2), (key1076, 2), (key1212, 2)]

def rawRow1560 : Integer.Sparse Key := [(key1019, -2), (key998, -2), (key1006, -2), (key998, 6), (key1199, 2), (key1190, 2), (key1193, 2), (key1111, -2), (key1190, -2), (key1033, -2), (key1212, -6), (key1155, 2), (key1212, 2), (key1076, 2)]

def rawRow1561 : Integer.Sparse Key := [(key1006, -2), (key1019, -2), (key998, -2), (key998, 6), (key1193, 2), (key1199, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key1111, -2), (key1212, -6), (key1212, 2), (key1076, 2), (key1155, 2)]

def rawRow1562 : Integer.Sparse Key := [(key1019, -2), (key1006, -2), (key998, -2), (key998, 6), (key1199, 2), (key1193, 2), (key1190, 2), (key1190, -2), (key1111, -2), (key1033, -2), (key1212, -6), (key1212, 2), (key1155, 2), (key1076, 2)]

def rawRow1563 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1127, -2), (key1155, 6), (key998, 2), (key998, 2), (key1019, 2), (key1076, -2), (key1212, -2), (key1212, -2), (key1006, -6), (key1041, 2), (key1193, 2), (key1193, 2)]

def rawRow1564 : Integer.Sparse Key := [(key1111, -2), (key1127, -2), (key1111, -2), (key1155, 6), (key998, 2), (key1019, 2), (key998, 2), (key1212, -2), (key1076, -2), (key1212, -2), (key1006, -6), (key1193, 2), (key1041, 2), (key1193, 2)]

def rawRow1565 : Integer.Sparse Key := [(key1127, -2), (key1111, -2), (key1111, -2), (key1155, 6), (key1019, 2), (key998, 2), (key998, 2), (key1212, -2), (key1212, -2), (key1076, -2), (key1006, -6), (key1193, 2), (key1193, 2), (key1041, 2)]

def rawRow1566 : Integer.Sparse Key := [(key1111, -2), (key1127, -2), (key1155, -2), (key1111, 6), (key1190, 2), (key1199, 2), (key1212, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1193, -6), (key1006, 2), (key1041, 2), (key1193, 2)]

def rawRow1567 : Integer.Sparse Key := [(key1127, -2), (key1111, -2), (key1155, -2), (key1111, 6), (key1199, 2), (key1190, 2), (key1212, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1193, -6), (key1006, 2), (key1193, 2), (key1041, 2)]

def rawRow1568 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1127, -2), (key1111, 6), (key1190, 2), (key1212, 2), (key1199, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1193, -6), (key1041, 2), (key1006, 2), (key1193, 2)]

def rawRow1569 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1127, -2), (key1111, 6), (key1212, 2), (key1190, 2), (key1199, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1193, -6), (key1041, 2), (key1193, 2), (key1006, 2)]

def rawRow1570 : Integer.Sparse Key := [(key1127, -2), (key1155, -2), (key1111, -2), (key1111, 6), (key1199, 2), (key1212, 2), (key1190, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1193, -6), (key1193, 2), (key1006, 2), (key1041, 2)]

def rawRow1571 : Integer.Sparse Key := [(key1155, -2), (key1127, -2), (key1111, -2), (key1111, 6), (key1212, 2), (key1199, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1193, -6), (key1193, 2), (key1041, 2), (key1006, 2)]

def rawRow1572 : Integer.Sparse Key := [(key1190, -2), (key1193, -2), (key1199, -2), (key1212, 6), (key998, 2), (key1006, 2), (key1019, 2), (key1076, -2), (key1155, -2), (key1212, -2), (key998, -6), (key1033, 2), (key1111, 2), (key1190, 2)]

def rawRow1573 : Integer.Sparse Key := [(key1193, -2), (key1190, -2), (key1199, -2), (key1212, 6), (key1006, 2), (key998, 2), (key1019, 2), (key1076, -2), (key1212, -2), (key1155, -2), (key998, -6), (key1033, 2), (key1190, 2), (key1111, 2)]

def rawRow1574 : Integer.Sparse Key := [(key1190, -2), (key1199, -2), (key1193, -2), (key1212, 6), (key998, 2), (key1019, 2), (key1006, 2), (key1155, -2), (key1076, -2), (key1212, -2), (key998, -6), (key1111, 2), (key1033, 2), (key1190, 2)]

def rawRow1575 : Integer.Sparse Key := [(key1199, -2), (key1190, -2), (key1193, -2), (key1212, 6), (key1019, 2), (key998, 2), (key1006, 2), (key1155, -2), (key1212, -2), (key1076, -2), (key998, -6), (key1111, 2), (key1190, 2), (key1033, 2)]

def rawRow1576 : Integer.Sparse Key := [(key1193, -2), (key1199, -2), (key1190, -2), (key1212, 6), (key1006, 2), (key1019, 2), (key998, 2), (key1212, -2), (key1076, -2), (key1155, -2), (key998, -6), (key1190, 2), (key1033, 2), (key1111, 2)]

def rawRow1577 : Integer.Sparse Key := [(key1199, -2), (key1193, -2), (key1190, -2), (key1212, 6), (key1019, 2), (key1006, 2), (key998, 2), (key1212, -2), (key1155, -2), (key1076, -2), (key998, -6), (key1190, 2), (key1111, 2), (key1033, 2)]

def rawRow1578 : Integer.Sparse Key := [(key1190, -2), (key1199, -2), (key1212, -2), (key1193, 6), (key1111, 2), (key1127, 2), (key1155, 2), (key1006, -2), (key1041, -2), (key1193, -2), (key1111, -6), (key998, 2), (key1033, 2), (key1190, 2)]

def rawRow1579 : Integer.Sparse Key := [(key1199, -2), (key1190, -2), (key1212, -2), (key1193, 6), (key1127, 2), (key1111, 2), (key1155, 2), (key1006, -2), (key1193, -2), (key1041, -2), (key1111, -6), (key998, 2), (key1190, 2), (key1033, 2)]

def rawRow1580 : Integer.Sparse Key := [(key1190, -2), (key1212, -2), (key1199, -2), (key1193, 6), (key1111, 2), (key1155, 2), (key1127, 2), (key1041, -2), (key1006, -2), (key1193, -2), (key1111, -6), (key1033, 2), (key998, 2), (key1190, 2)]

def rawRow1581 : Integer.Sparse Key := [(key1212, -2), (key1190, -2), (key1199, -2), (key1193, 6), (key1155, 2), (key1111, 2), (key1127, 2), (key1041, -2), (key1193, -2), (key1006, -2), (key1111, -6), (key1033, 2), (key1190, 2), (key998, 2)]

def rawRow1582 : Integer.Sparse Key := [(key1199, -2), (key1212, -2), (key1190, -2), (key1193, 6), (key1127, 2), (key1155, 2), (key1111, 2), (key1193, -2), (key1006, -2), (key1041, -2), (key1111, -6), (key1190, 2), (key998, 2), (key1033, 2)]

def rawRow1583 : Integer.Sparse Key := [(key1212, -2), (key1199, -2), (key1190, -2), (key1193, 6), (key1155, 2), (key1127, 2), (key1111, 2), (key1193, -2), (key1041, -2), (key1006, -2), (key1111, -6), (key1190, 2), (key1033, 2), (key998, 2)]

def rawRow1584 : Integer.Sparse Key := [(key2631, -6), (key2615, 2), (key2639, 2), (key2639, 2), (key2705, 6), (key2670, -2), (key2725, -2), (key2725, -2), (key2808, -2), (key2859, -2), (key2859, -2), (key2785, 2), (key2869, 2), (key2869, 2)]

def rawRow1585 : Integer.Sparse Key := [(key2631, -6), (key2639, 2), (key2615, 2), (key2639, 2), (key2705, 6), (key2725, -2), (key2670, -2), (key2725, -2), (key2859, -2), (key2808, -2), (key2859, -2), (key2869, 2), (key2785, 2), (key2869, 2)]

def rawRow1586 : Integer.Sparse Key := [(key2631, -6), (key2639, 2), (key2639, 2), (key2615, 2), (key2705, 6), (key2725, -2), (key2725, -2), (key2670, -2), (key2859, -2), (key2859, -2), (key2808, -2), (key2869, 2), (key2869, 2), (key2785, 2)]

def rawRow1587 : Integer.Sparse Key := [(key2639, -6), (key2615, 2), (key2631, 2), (key2639, 2), (key2725, 6), (key2670, -2), (key2705, -2), (key2725, -2), (key2828, -2), (key2869, -2), (key2879, -2), (key2793, 2), (key2859, 2), (key2879, 2)]

def rawRow1588 : Integer.Sparse Key := [(key2639, -6), (key2615, 2), (key2639, 2), (key2631, 2), (key2725, 6), (key2670, -2), (key2725, -2), (key2705, -2), (key2828, -2), (key2879, -2), (key2869, -2), (key2793, 2), (key2879, 2), (key2859, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined273_part2 : Sparse := [([1, 2, -1, 0, 1, -1, -1], 9)]

end MUB6.TaoCertificate

end OAI
end


