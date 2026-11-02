-- Prove2me | Definitions.Def_OAIQ106D096
-- name    : OAIQ106D096
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:01:09.078629+00:00
-- url     : https://prove2.me/theorems/4375eb4b-1426-424a-b26d-dc64ee58abba
-- title:
--   Definitions bundle OAIQ106D096 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 425 declarations of OpenAI's Lean: 425 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow12181`, `OAI.MUB6.Certificate.GramRows.rawRow12182`, `OAI.MUB6.Certificate.GramRows.rawRow12183`, `OAI.MUB6.Certificate.GramRows.rawRow12184`, `OAI.MUB6.Certificate.GramRows.rawRow12185`, `OAI.MUB6.Certificate.GramRows.rawRow12186`, `OAI.MUB6.Certificate.GramRows.rawRow12187`, `OAI.MUB6.Certificate.GramRows.rawRow128`, `OAI.MUB6.Certificate.GramRows.rawRow133`, `OAI.MUB6.Certificate.GramRows.rawRow13594`, `OAI.MUB6.Certificate.GramRows.rawRow13595`, `OAI.MUB6.Certificate.GramRows.rawRow13596`, `OAI.MUB6.Certificate.GramRows.rawRow13597`, `OAI.MUB6.Certificate.GramRows.rawRow13598`, `OAI.MUB6.Certificate.GramRows.rawRow13599`, `OAI.MUB6.Certificate.GramRows.rawRow13600`, `OAI.MUB6.Certificate.GramRows.rawRow13601`, `OAI.MUB6.Certificate.GramRows.rawRow13602`, `OAI.MUB6.Certificate.GramRows.rawRow13603`, `OAI.MUB6.Certificate.GramRows.rawRow13604`, `OAI.MUB6.Certificate.GramRows.rawRow13605`, `OAI.MUB6.Certificate.GramRows.rawRow13606`, `OAI.MUB6.Certificate.GramRows.rawRow13607`, `OAI.MUB6.Certificate.GramRows.rawRow13608`, `OAI.MUB6.Certificate.GramRows.rawRow13609`, `OAI.MUB6.Certificate.GramRows.rawRow13610`, `OAI.MUB6.Certificate.GramRows.rawRow13611`, `OAI.MUB6.Certificate.GramRows.rawRow13612`, `OAI.MUB6.Certificate.GramRows.rawRow13613`, `OAI.MUB6.Certificate.GramRows.rawRow13614`, `OAI.MUB6.Certificate.GramRows.rawRow13615`, `OAI.MUB6.Certificate.GramRows.rawRow13616`, `OAI.MUB6.Certificate.GramRows.rawRow13617`, `OAI.MUB6.Certificate.GramRows.rawRow13618`, `OAI.MUB6.Certificate.GramRows.rawRow13619`, `OAI.MUB6.Certificate.GramRows.rawRow13620`, `OAI.MUB6.Certificate.GramRows.rawRow13621`, `OAI.MUB6.Certificate.GramRows.rawRow13622`, `OAI.MUB6.Certificate.GramRows.rawRow13623`, `OAI.MUB6.Certificate.GramRows.rawRow13624` and 385 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block1`, `MutuallyUnbiased_GramRows_Block119`, `MutuallyUnbiased_GramRows_Block130`, `MutuallyUnbiased_GramRows_Block131`, `MutuallyUnbiased_GramRows_Block132`, `MutuallyUnbiased_GramRows_Block134`, `MutuallyUnbiased_GramRows_Block135`, `MutuallyUnbiased_GramRows_Block136`, `MutuallyUnbiased_GramRows_Block137`, `MutuallyUnbiased_GramRows_Block138`, `MutuallyUnbiased_GramRows_Block139`, `MutuallyUnbiased_GramRows_Block140`, `MutuallyUnbiased_GramRows_Block141`, `MutuallyUnbiased_GramRows_Block142`, `MutuallyUnbiased_GramRows_Block143`, `MutuallyUnbiased_GramRows_Block144`, `MutuallyUnbiased_GramRows_Block145`, `MutuallyUnbiased_GramRows_Block35`, `MutuallyUnbiased_GramRows_Block36`, `MutuallyUnbiased_MixedData_Source0`.
--
--   **Imports.** It imports the bundles `OAIQ106D000` and `OAIQ106D001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D186`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15 : Integer.Sparse Key := [(key319, -1), (key328, -1), (key316, 2), (key335, 1), (key340, 1), (key302, -1), (key316, -1), (key335, -2), (key305, 1), (key319, 1), (key409, 1), (key418, 1), (key406, -2), (key578, -1), (key583, -1), (key236, 1), (key406, 1), (key418, 2), (key239, -1), (key409, -1), (key442, -1), (key595, -1), (key316, 1), (key435, 1), (key450, 1), (key601, 1), (key248, -1), (key435, -1), (key328, -1), (key450, -1), (key260, 1), (key442, 1), (key469, 2), (key335, -1), (key467, -1), (key475, -2), (key267, 1), (key467, 1), (key340, 1), (key475, 1), (key271, -1), (key469, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow128 : Integer.Sparse Key := [(key1298, -1), (key1298, -1), (key1292, 2), (key1351, 1), (key1351, 1), (key1312, -1), (key1312, -1), (key1354, -2), (key1326, 1), (key1326, 1), (key1393, 1), (key1393, 1), (key1387, -2), (key1896, -1), (key1896, -1), (key1542, 1), (key1542, 1), (key1899, 2), (key1556, -1), (key1556, -1), (key1472, -1), (key1472, -1), (key1420, 1), (key1420, 1), (key1903, 1), (key1903, 1), (key1569, -1), (key1569, -1), (key1920, -1), (key1920, -1), (key1683, 1), (key1683, 1), (key1480, 2), (key1444, -1), (key1444, -1), (key1911, -2), (key1593, 1), (key1593, 1), (key1926, 1), (key1926, 1), (key1689, -1), (key1689, -1)]

def rawRow133 : Integer.Sparse Key := [(key1351, -1), (key1351, -1), (key1354, 2), (key1298, 1), (key1298, 1), (key1326, -1), (key1326, -1), (key1292, -2), (key1312, 1), (key1312, 1), (key1896, 1), (key1896, 1), (key1899, -2), (key1393, -1), (key1393, -1), (key1556, 1), (key1556, 1), (key1387, 2), (key1542, -1), (key1542, -1), (key1903, -1), (key1903, -1), (key1920, 1), (key1920, 1), (key1472, 1), (key1472, 1), (key1683, -1), (key1683, -1), (key1420, -1), (key1420, -1), (key1569, 1), (key1569, 1), (key1911, 2), (key1926, -1), (key1926, -1), (key1480, -2), (key1689, 1), (key1689, 1), (key1444, 1), (key1444, 1), (key1593, -1), (key1593, -1)]

def rawRow138 : Integer.Sparse Key := [(key1393, -1), (key1393, -1), (key1387, 2), (key1472, 1), (key1472, 1), (key1420, -1), (key1420, -1), (key1480, -2), (key1444, 1), (key1444, 1), (key1298, 1), (key1298, 1), (key1292, -2), (key1903, -1), (key1903, -1), (key1569, 1), (key1569, 1), (key1911, 2), (key1593, -1), (key1593, -1), (key1351, -1), (key1351, -1), (key1312, 1), (key1312, 1), (key1896, 1), (key1896, 1), (key1542, -1), (key1542, -1), (key1926, -1), (key1926, -1), (key1689, 1), (key1689, 1), (key1354, 2), (key1326, -1), (key1326, -1), (key1899, -2), (key1556, 1), (key1556, 1), (key1920, 1), (key1920, 1), (key1683, -1), (key1683, -1)]

def rawRow143 : Integer.Sparse Key := [(key1472, -1), (key1472, -1), (key1480, 2), (key1393, 1), (key1393, 1), (key1444, -1), (key1444, -1), (key1387, -2), (key1420, 1), (key1420, 1), (key1903, 1), (key1903, 1), (key1911, -2), (key1298, -1), (key1298, -1), (key1593, 1), (key1593, 1), (key1292, 2), (key1569, -1), (key1569, -1), (key1896, -1), (key1896, -1), (key1926, 1), (key1926, 1), (key1351, 1), (key1351, 1), (key1689, -1), (key1689, -1), (key1312, -1), (key1312, -1), (key1542, 1), (key1542, 1), (key1899, 2), (key1920, -1), (key1920, -1), (key1354, -2), (key1683, 1), (key1683, 1), (key1326, 1), (key1326, 1), (key1556, -1), (key1556, -1)]

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

def rawRow12181 : Integer.Sparse Key := [(key2538, -2), (key2472, -2), (key2472, -2), (key2554, -2), (key2503, -2), (key2554, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2506, -2), (key2506, -2), (key2381, -2), (key2543, 1), (key2480, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2406, 1), (key2554, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2563, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2390, 1), (key2522, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2440, 1), (key2392, 1)]

def rawRow12182 : Integer.Sparse Key := [(key2503, -2), (key2506, -2), (key2554, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2506, -2), (key2538, -2), (key2554, -2), (key2378, -2), (key2472, -2), (key2503, -2), (key2437, 1), (key2440, 1), (key2503, 1), (key2522, 1), (key2554, 1), (key2563, 1), (key2390, 1), (key2392, 1), (key2480, 1), (key2522, 1), (key2543, 1), (key2563, 1), (key2378, 1), (key2392, 1), (key2406, 1), (key2440, 1), (key2543, 1), (key2554, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1)]

def rawRow12183 : Integer.Sparse Key := [(key2506, -2), (key2503, -2), (key2554, -2), (key2381, -2), (key2378, -2), (key2506, -2), (key2472, -2), (key2554, -2), (key2538, -2), (key2378, -2), (key2503, -2), (key2472, -2), (key2440, 1), (key2437, 1), (key2522, 1), (key2503, 1), (key2563, 1), (key2554, 1), (key2392, 1), (key2390, 1), (key2522, 1), (key2480, 1), (key2563, 1), (key2543, 1), (key2392, 1), (key2378, 1), (key2440, 1), (key2406, 1), (key2554, 1), (key2543, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1)]

def rawRow12184 : Integer.Sparse Key := [(key2503, -2), (key2554, -2), (key2506, -2), (key2472, -2), (key2538, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2472, -2), (key2378, -2), (key2503, -2), (key2503, 1), (key2554, 1), (key2437, 1), (key2563, 1), (key2440, 1), (key2522, 1), (key2480, 1), (key2543, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2522, 1), (key2406, 1), (key2543, 1), (key2378, 1), (key2554, 1), (key2392, 1), (key2440, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1)]

def rawRow12185 : Integer.Sparse Key := [(key2554, -2), (key2503, -2), (key2506, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2554, 1), (key2503, 1), (key2563, 1), (key2437, 1), (key2522, 1), (key2440, 1), (key2543, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2522, 1), (key2392, 1), (key2543, 1), (key2406, 1), (key2554, 1), (key2378, 1), (key2440, 1), (key2392, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1)]

def rawRow12186 : Integer.Sparse Key := [(key2506, -2), (key2554, -2), (key2503, -2), (key2506, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2378, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2522, 1), (key2563, 1), (key2440, 1), (key2554, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2563, 1), (key2392, 1), (key2543, 1), (key2390, 1), (key2480, 1), (key2440, 1), (key2554, 1), (key2392, 1), (key2543, 1), (key2378, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1)]

def rawRow12187 : Integer.Sparse Key := [(key2554, -2), (key2506, -2), (key2503, -2), (key2554, -2), (key2506, -2), (key2538, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2503, -2), (key2472, -2), (key2378, -2), (key2563, 1), (key2522, 1), (key2554, 1), (key2440, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2522, 1), (key2543, 1), (key2392, 1), (key2480, 1), (key2390, 1), (key2554, 1), (key2440, 1), (key2543, 1), (key2392, 1), (key2406, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

end MUB6.Certificate.GramRows

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

def rawRow13594 : Integer.Sparse Key := [(key2587, 4), (key2989, 4), (key2966, 4), (key2593, -2), (key2587, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2968, -2), (key2600, -2), (key2598, -2), (key2910, -2), (key2887, -2), (key3002, -2), (key2995, -2), (key2600, 4), (key2910, 4), (key2889, 4)]

def rawRow13595 : Integer.Sparse Key := [(key2966, 4), (key2587, 4), (key2989, 4), (key2843, -2), (key2968, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2887, -2), (key2995, -2), (key2598, -2), (key3002, -2), (key2600, -2), (key2910, -2), (key2889, 4), (key2600, 4), (key2910, 4)]

def rawRow13596 : Integer.Sparse Key := [(key2966, 4), (key2989, 4), (key2587, 4), (key2968, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2880, -2), (key2593, -2), (key2995, -2), (key2887, -2), (key3002, -2), (key2598, -2), (key2910, -2), (key2600, -2), (key2889, 4), (key2910, 4), (key2600, 4)]

def rawRow13597 : Integer.Sparse Key := [(key2989, 4), (key2587, 4), (key2966, 4), (key2880, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2587, -2), (key2843, -2), (key2910, -2), (key3002, -2), (key2600, -2), (key2995, -2), (key2598, -2), (key2887, -2), (key2910, 4), (key2600, 4), (key2889, 4)]

def rawRow13598 : Integer.Sparse Key := [(key2989, 4), (key2966, 4), (key2587, 4), (key2989, -2), (key2880, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key3002, -2), (key2910, -2), (key2995, -2), (key2600, -2), (key2887, -2), (key2598, -2), (key2910, 4), (key2889, 4), (key2600, 4)]

def rawRow13599 : Integer.Sparse Key := [(key2593, 4), (key2968, 4), (key2968, 4), (key2587, -2), (key2587, -2), (key2843, -2), (key2843, -2), (key2966, -2), (key2966, -2), (key2600, -2), (key2600, -2), (key2889, -2), (key2889, -2), (key2995, -2), (key2995, -2), (key2598, 4), (key2887, 4), (key2887, 4)]

def rawRow13600 : Integer.Sparse Key := [(key2968, 4), (key2593, 4), (key2968, 4), (key2843, -2), (key2966, -2), (key2587, -2), (key2966, -2), (key2587, -2), (key2843, -2), (key2889, -2), (key2995, -2), (key2600, -2), (key2995, -2), (key2600, -2), (key2889, -2), (key2887, 4), (key2598, 4), (key2887, 4)]

def rawRow13601 : Integer.Sparse Key := [(key2968, 4), (key2968, 4), (key2593, 4), (key2966, -2), (key2843, -2), (key2966, -2), (key2587, -2), (key2843, -2), (key2587, -2), (key2995, -2), (key2889, -2), (key2995, -2), (key2600, -2), (key2889, -2), (key2600, -2), (key2887, 4), (key2887, 4), (key2598, 4)]

def rawRow13602 : Integer.Sparse Key := [(key2587, 4), (key2966, 4), (key2989, 4), (key2598, -2), (key2600, -2), (key2887, -2), (key2910, -2), (key2995, -2), (key3002, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2880, -2), (key2968, -2), (key2989, -2), (key2600, 4), (key2889, 4), (key2910, 4)]

def rawRow13603 : Integer.Sparse Key := [(key2587, 4), (key2989, 4), (key2966, 4), (key2600, -2), (key2598, -2), (key2910, -2), (key2887, -2), (key3002, -2), (key2995, -2), (key2593, -2), (key2587, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2968, -2), (key2600, 4), (key2910, 4), (key2889, 4)]

def rawRow13604 : Integer.Sparse Key := [(key2966, 4), (key2587, 4), (key2989, 4), (key2887, -2), (key2995, -2), (key2598, -2), (key3002, -2), (key2600, -2), (key2910, -2), (key2843, -2), (key2968, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2889, 4), (key2600, 4), (key2910, 4)]

def rawRow13605 : Integer.Sparse Key := [(key2966, 4), (key2989, 4), (key2587, 4), (key2995, -2), (key2887, -2), (key3002, -2), (key2598, -2), (key2910, -2), (key2600, -2), (key2968, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2880, -2), (key2593, -2), (key2889, 4), (key2910, 4), (key2600, 4)]

def rawRow13606 : Integer.Sparse Key := [(key2989, 4), (key2587, 4), (key2966, 4), (key2910, -2), (key3002, -2), (key2600, -2), (key2995, -2), (key2598, -2), (key2887, -2), (key2880, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2587, -2), (key2843, -2), (key2910, 4), (key2600, 4), (key2889, 4)]

def rawRow13607 : Integer.Sparse Key := [(key2989, 4), (key2966, 4), (key2587, 4), (key3002, -2), (key2910, -2), (key2995, -2), (key2600, -2), (key2887, -2), (key2598, -2), (key2989, -2), (key2880, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key2910, 4), (key2889, 4), (key2600, 4)]

def rawRow13608 : Integer.Sparse Key := [(key2390, 4), (key2929, 4), (key3002, 4), (key2587, -2), (key2600, -2), (key2766, -2), (key2910, -2), (key2931, -2), (key2989, -2), (key2587, -2), (key2600, -2), (key2766, -2), (key2910, -2), (key2931, -2), (key2989, -2), (key2593, 4), (key2772, 4), (key2880, 4)]

def rawRow13609 : Integer.Sparse Key := [(key2390, 4), (key3002, 4), (key2929, 4), (key2600, -2), (key2587, -2), (key2910, -2), (key2766, -2), (key2989, -2), (key2931, -2), (key2600, -2), (key2587, -2), (key2910, -2), (key2766, -2), (key2989, -2), (key2931, -2), (key2593, 4), (key2880, 4), (key2772, 4)]

def rawRow13610 : Integer.Sparse Key := [(key2437, 4), (key2598, 4), (key3002, 4), (key2766, -2), (key2931, -2), (key2587, -2), (key2989, -2), (key2600, -2), (key2910, -2), (key2766, -2), (key2931, -2), (key2587, -2), (key2989, -2), (key2600, -2), (key2910, -2), (key2772, 4), (key2593, 4), (key2880, 4)]

def rawRow13611 : Integer.Sparse Key := [(key2437, 4), (key3002, 4), (key2598, 4), (key2931, -2), (key2766, -2), (key2989, -2), (key2587, -2), (key2910, -2), (key2600, -2), (key2931, -2), (key2766, -2), (key2989, -2), (key2587, -2), (key2910, -2), (key2600, -2), (key2772, 4), (key2880, 4), (key2593, 4)]

def rawRow13612 : Integer.Sparse Key := [(key2580, 4), (key2390, 4), (key2437, 4), (key2910, -2), (key2989, -2), (key2600, -2), (key2931, -2), (key2587, -2), (key2766, -2), (key2910, -2), (key2989, -2), (key2600, -2), (key2931, -2), (key2587, -2), (key2766, -2), (key2880, 4), (key2593, 4), (key2772, 4)]

def rawRow13613 : Integer.Sparse Key := [(key2580, 4), (key2437, 4), (key2390, 4), (key2989, -2), (key2910, -2), (key2931, -2), (key2600, -2), (key2766, -2), (key2587, -2), (key2989, -2), (key2910, -2), (key2931, -2), (key2600, -2), (key2766, -2), (key2587, -2), (key2880, 4), (key2772, 4), (key2593, 4)]

def rawRow13614 : Integer.Sparse Key := [(key2394, 4), (key2443, 4), (key2524, 4), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2889, -2), (key2931, -2), (key2968, -2), (key2587, 4), (key2766, 4), (key2843, 4)]

def rawRow13615 : Integer.Sparse Key := [(key2394, 4), (key2524, 4), (key2443, 4), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2600, -2), (key2593, -2), (key2889, -2), (key2772, -2), (key2968, -2), (key2931, -2), (key2587, 4), (key2843, 4), (key2766, 4)]

def rawRow13616 : Integer.Sparse Key := [(key2443, 4), (key2394, 4), (key2524, 4), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2772, -2), (key2931, -2), (key2593, -2), (key2968, -2), (key2600, -2), (key2889, -2), (key2766, 4), (key2587, 4), (key2843, 4)]

def rawRow13617 : Integer.Sparse Key := [(key2443, 4), (key2524, 4), (key2394, 4), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2931, -2), (key2772, -2), (key2968, -2), (key2593, -2), (key2889, -2), (key2600, -2), (key2766, 4), (key2843, 4), (key2587, 4)]

def rawRow13618 : Integer.Sparse Key := [(key2524, 4), (key2394, 4), (key2443, 4), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2889, -2), (key2968, -2), (key2600, -2), (key2931, -2), (key2593, -2), (key2772, -2), (key2843, 4), (key2587, 4), (key2766, 4)]

def rawRow13619 : Integer.Sparse Key := [(key2524, 4), (key2443, 4), (key2394, 4), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2968, -2), (key2889, -2), (key2931, -2), (key2600, -2), (key2772, -2), (key2593, -2), (key2843, 4), (key2766, 4), (key2587, 4)]

def rawRow13620 : Integer.Sparse Key := [(key2383, 4), (key2509, 4), (key2509, 4), (key2394, -2), (key2394, -2), (key2484, -2), (key2484, -2), (key2524, -2), (key2524, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow13621 : Integer.Sparse Key := [(key2509, 4), (key2383, 4), (key2509, 4), (key2484, -2), (key2524, -2), (key2394, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow13622 : Integer.Sparse Key := [(key2509, 4), (key2509, 4), (key2383, 4), (key2524, -2), (key2484, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2394, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow13623 : Integer.Sparse Key := [(key2394, 4), (key2443, 4), (key2524, 4), (key2383, -2), (key2394, -2), (key2411, -2), (key2484, -2), (key2443, -2), (key2509, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, 4), (key2406, 4), (key2472, 4)]

def rawRow13624 : Integer.Sparse Key := [(key2394, 4), (key2524, 4), (key2443, 4), (key2394, -2), (key2383, -2), (key2484, -2), (key2411, -2), (key2509, -2), (key2443, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, 4), (key2472, 4), (key2406, 4)]

def rawRow13625 : Integer.Sparse Key := [(key2443, 4), (key2394, 4), (key2524, 4), (key2411, -2), (key2443, -2), (key2383, -2), (key2509, -2), (key2394, -2), (key2484, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, 4), (key2378, 4), (key2472, 4)]

def rawRow13626 : Integer.Sparse Key := [(key2443, 4), (key2524, 4), (key2394, 4), (key2443, -2), (key2411, -2), (key2509, -2), (key2383, -2), (key2484, -2), (key2394, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, 4), (key2472, 4), (key2378, 4)]

def rawRow13627 : Integer.Sparse Key := [(key2524, 4), (key2394, 4), (key2443, 4), (key2484, -2), (key2509, -2), (key2394, -2), (key2443, -2), (key2383, -2), (key2411, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, 4), (key2378, 4), (key2406, 4)]

def rawRow13628 : Integer.Sparse Key := [(key2524, 4), (key2443, 4), (key2394, 4), (key2509, -2), (key2484, -2), (key2443, -2), (key2394, -2), (key2411, -2), (key2383, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, 4), (key2406, 4), (key2378, 4)]

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

def rawRow13809 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2614, 2), (key2807, 2), (key2827, 2), (key2624, -1), (key2630, -1), (key2851, -1), (key2868, -1), (key3021, -1), (key3025, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, -1), (key2868, -1), (key2657, 2), (key2918, 2), (key2922, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2757, -1), (key2919, -1), (key2922, -1)]

def rawRow13810 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2614, 2), (key2827, 2), (key2807, 2), (key2630, -1), (key2624, -1), (key2868, -1), (key2851, -1), (key3025, -1), (key3021, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, -1), (key2858, -1), (key2657, 2), (key2922, 2), (key2918, 2), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, -1), (key2919, -1)]

def rawRow13811 : Integer.Sparse Key := [(key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2807, 2), (key2614, 2), (key2827, 2), (key2851, -1), (key3021, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2918, 2), (key2657, 2), (key2922, 2), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2757, -1)]

def rawRow13812 : Integer.Sparse Key := [(key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key2807, 2), (key2827, 2), (key2614, 2), (key3021, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key2868, -1), (key2630, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, -1), (key2638, -1), (key2918, 2), (key2922, 2), (key2657, 2), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, -1), (key2659, -1)]

def rawRow13813 : Integer.Sparse Key := [(key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2827, 2), (key2614, 2), (key2807, 2), (key2868, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2624, -1), (key2851, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2724, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2630, -1), (key2704, -1), (key2922, 2), (key2657, 2), (key2918, 2), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, -1), (key2752, -1)]

def rawRow13814 : Integer.Sparse Key := [(key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key2827, 2), (key2807, 2), (key2614, 2), (key3025, -1), (key2868, -1), (key3021, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2868, -1), (key2724, -1), (key2858, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2922, 2), (key2918, 2), (key2657, 2), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, -1), (key2657, -1)]

def rawRow13815 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2638, -1), (key2638, -1), (key2858, -1), (key2858, -1), (key3022, -1), (key3022, -1), (key2630, 2), (key2630, 2), (key2704, 2), (key2704, 2), (key3021, 2), (key3021, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2659, 2), (key2919, 2), (key2919, 2), (key2657, -1), (key2657, -1), (key2752, -1), (key2752, -1), (key2918, -1), (key2918, -1)]

def rawRow13816 : Integer.Sparse Key := [(key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2858, -1), (key3022, -1), (key2638, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2704, 2), (key3021, 2), (key2630, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2919, 2), (key2659, 2), (key2919, 2), (key2752, -1), (key2918, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2752, -1)]

def rawRow13817 : Integer.Sparse Key := [(key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key3022, -1), (key2858, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key3021, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2630, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2919, 2), (key2919, 2), (key2659, 2), (key2918, -1), (key2752, -1), (key2918, -1), (key2657, -1), (key2752, -1), (key2657, -1)]

def rawRow13818 : Integer.Sparse Key := [(key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2638, 2), (key2858, 2), (key3022, 2), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2757, -1), (key2919, -1), (key2922, -1), (key2614, 2), (key2807, 2), (key2827, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, -1), (key2868, -1)]

def rawRow13819 : Integer.Sparse Key := [(key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2638, 2), (key3022, 2), (key2858, 2), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, -1), (key2919, -1), (key2614, 2), (key2827, 2), (key2807, 2), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, -1), (key2858, -1)]

def rawRow13820 : Integer.Sparse Key := [(key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2858, 2), (key2638, 2), (key3022, 2), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2807, 2), (key2614, 2), (key2827, 2), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2724, -1)]

def rawRow13821 : Integer.Sparse Key := [(key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2858, 2), (key3022, 2), (key2638, 2), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, -1), (key2659, -1), (key2807, 2), (key2827, 2), (key2614, 2), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, -1), (key2638, -1)]

def rawRow13822 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key3022, 2), (key2638, 2), (key2858, 2), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, -1), (key2752, -1), (key2827, 2), (key2614, 2), (key2807, 2), (key2724, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2630, -1), (key2704, -1)]

def rawRow13823 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3022, 2), (key2858, 2), (key2638, 2), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2827, 2), (key2807, 2), (key2614, 2), (key2868, -1), (key2724, -1), (key2858, -1), (key2638, -1), (key2704, -1), (key2630, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow13824 : Integer.Sparse Key := [(key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2630, 2), (key2704, 2), (key3021, 2), (key2624, -1), (key2638, -1), (key2698, -1), (key3022, -1), (key2724, -1), (key3025, -1), (key2608, 2), (key2659, 2), (key2663, 2), (key2757, 2), (key3009, 2), (key3016, 2), (key2614, -1), (key2638, -1), (key2669, -1), (key2724, -1), (key2792, -1), (key2827, -1), (key2630, 2), (key2784, 2), (key2868, 2), (key2614, -1), (key2638, -1), (key2669, -1), (key2724, -1), (key2792, -1), (key2827, -1)]

def rawRow13825 : Integer.Sparse Key := [(key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2630, 2), (key3021, 2), (key2704, 2), (key2638, -1), (key2624, -1), (key3022, -1), (key2698, -1), (key3025, -1), (key2724, -1), (key2659, 2), (key2608, 2), (key2757, 2), (key2663, 2), (key3016, 2), (key3009, 2), (key2638, -1), (key2614, -1), (key2724, -1), (key2669, -1), (key2827, -1), (key2792, -1), (key2630, 2), (key2868, 2), (key2784, 2), (key2638, -1), (key2614, -1), (key2724, -1), (key2669, -1), (key2827, -1), (key2792, -1)]

def rawRow13826 : Integer.Sparse Key := [(key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2704, 2), (key2630, 2), (key3021, 2), (key2698, -1), (key2724, -1), (key2624, -1), (key3025, -1), (key2638, -1), (key3022, -1), (key2663, 2), (key2757, 2), (key2608, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2669, -1), (key2792, -1), (key2614, -1), (key2827, -1), (key2638, -1), (key2724, -1), (key2784, 2), (key2630, 2), (key2868, 2), (key2669, -1), (key2792, -1), (key2614, -1), (key2827, -1), (key2638, -1), (key2724, -1)]

def rawRow13827 : Integer.Sparse Key := [(key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2704, 2), (key3021, 2), (key2630, 2), (key2724, -1), (key2698, -1), (key3025, -1), (key2624, -1), (key3022, -1), (key2638, -1), (key2757, 2), (key2663, 2), (key3016, 2), (key2608, 2), (key2757, 2), (key2659, 2), (key2792, -1), (key2669, -1), (key2827, -1), (key2614, -1), (key2724, -1), (key2638, -1), (key2784, 2), (key2868, 2), (key2630, 2), (key2792, -1), (key2669, -1), (key2827, -1), (key2614, -1), (key2724, -1), (key2638, -1)]

def rawRow13828 : Integer.Sparse Key := [(key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key3021, 2), (key2630, 2), (key2704, 2), (key3022, -1), (key3025, -1), (key2638, -1), (key2724, -1), (key2624, -1), (key2698, -1), (key3009, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2608, 2), (key2663, 2), (key2724, -1), (key2827, -1), (key2638, -1), (key2792, -1), (key2614, -1), (key2669, -1), (key2868, 2), (key2630, 2), (key2784, 2), (key2724, -1), (key2827, -1), (key2638, -1), (key2792, -1), (key2614, -1), (key2669, -1)]

def rawRow13829 : Integer.Sparse Key := [(key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key3021, 2), (key2704, 2), (key2630, 2), (key3025, -1), (key3022, -1), (key2724, -1), (key2638, -1), (key2698, -1), (key2624, -1), (key3016, 2), (key3009, 2), (key2757, 2), (key2659, 2), (key2663, 2), (key2608, 2), (key2827, -1), (key2724, -1), (key2792, -1), (key2638, -1), (key2669, -1), (key2614, -1), (key2868, 2), (key2784, 2), (key2630, 2), (key2827, -1), (key2724, -1), (key2792, -1), (key2638, -1), (key2669, -1), (key2614, -1)]

def rawRow13830 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2614, 2), (key2638, 2), (key2669, 2), (key2792, 2), (key2724, 2), (key2827, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2638, 2), (key2792, 2), (key2858, 2), (key2614, -1), (key2630, -1), (key2669, -1), (key2704, -1), (key2784, -1), (key2807, -1)]

def rawRow13831 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2638, 2), (key2614, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2724, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2638, 2), (key2858, 2), (key2792, 2), (key2630, -1), (key2614, -1), (key2704, -1), (key2669, -1), (key2807, -1), (key2784, -1)]

def rawRow13832 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2669, 2), (key2724, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2792, 2), (key2638, 2), (key2858, 2), (key2669, -1), (key2784, -1), (key2614, -1), (key2807, -1), (key2630, -1), (key2704, -1)]

def rawRow13833 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2724, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2792, 2), (key2638, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2792, 2), (key2858, 2), (key2638, 2), (key2784, -1), (key2669, -1), (key2807, -1), (key2614, -1), (key2704, -1), (key2630, -1)]

def rawRow13834 : Integer.Sparse Key := [(key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2792, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2614, 2), (key2669, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2858, 2), (key2638, 2), (key2792, 2), (key2704, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2614, -1), (key2669, -1)]

def rawRow13835 : Integer.Sparse Key := [(key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2827, 2), (key2792, 2), (key2724, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2858, 2), (key2792, 2), (key2638, 2), (key2807, -1), (key2704, -1), (key2784, -1), (key2630, -1), (key2669, -1), (key2614, -1)]

def rawRow13836 : Integer.Sparse Key := [(key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2659, 2), (key2919, 2), (key2919, 2), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2630, 2), (key2630, 2), (key2784, 2), (key2784, 2), (key2868, 2), (key2868, 2), (key2638, -1), (key2638, -1), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1)]

def rawRow13837 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2919, 2), (key2659, 2), (key2919, 2), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2784, 2), (key2868, 2), (key2630, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2792, -1), (key2858, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1)]

def rawRow13838 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2919, 2), (key2919, 2), (key2659, 2), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2868, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2630, 2), (key2858, -1), (key2792, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2638, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1)]

def rawRow13839 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2657, 2), (key2752, 2), (key2918, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key2614, 2), (key2638, 2), (key2669, 2), (key2792, 2), (key2724, 2), (key2827, 2), (key2614, -1), (key2630, -1), (key2669, -1), (key2784, -1), (key2704, -1), (key2807, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1)]

def rawRow13840 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2657, 2), (key2918, 2), (key2752, 2), (key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key2638, 2), (key2614, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2724, 2), (key2630, -1), (key2614, -1), (key2784, -1), (key2669, -1), (key2807, -1), (key2704, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1)]

def rawRow13841 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2752, 2), (key2657, 2), (key2918, 2), (key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2669, 2), (key2724, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2669, -1), (key2704, -1), (key2614, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1)]

def rawRow13842 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2752, 2), (key2918, 2), (key2657, 2), (key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key2724, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2792, 2), (key2638, 2), (key2704, -1), (key2669, -1), (key2807, -1), (key2614, -1), (key2784, -1), (key2630, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1)]

def rawRow13843 : Integer.Sparse Key := [(key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2918, 2), (key2657, 2), (key2752, 2), (key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key2792, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2614, 2), (key2669, 2), (key2784, -1), (key2807, -1), (key2630, -1), (key2704, -1), (key2614, -1), (key2669, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1)]

def rawRow13844 : Integer.Sparse Key := [(key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2918, 2), (key2752, 2), (key2657, 2), (key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2827, 2), (key2792, 2), (key2724, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2807, -1), (key2784, -1), (key2704, -1), (key2630, -1), (key2669, -1), (key2614, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14205 : Integer.Sparse Key := [(key2378, 4), (key2503, 4), (key2554, 4), (key2378, -2), (key2381, -2), (key2472, -2), (key2538, -2), (key2506, -2), (key2554, -2), (key2390, -2), (key2392, -2), (key2480, -2), (key2543, -2), (key2522, -2), (key2563, -2), (key2392, 4), (key2482, 4), (key2543, 4)]

def rawRow14206 : Integer.Sparse Key := [(key2378, 4), (key2554, 4), (key2503, 4), (key2381, -2), (key2378, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2506, -2), (key2392, -2), (key2390, -2), (key2543, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2392, 4), (key2543, 4), (key2482, 4)]

def rawRow14207 : Integer.Sparse Key := [(key2503, 4), (key2378, 4), (key2554, 4), (key2472, -2), (key2506, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2480, -2), (key2522, -2), (key2390, -2), (key2563, -2), (key2392, -2), (key2543, -2), (key2482, 4), (key2392, 4), (key2543, 4)]

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

def rawRow14208 : Integer.Sparse Key := [(key2503, 4), (key2554, 4), (key2378, 4), (key2506, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2538, -2), (key2381, -2), (key2522, -2), (key2480, -2), (key2563, -2), (key2390, -2), (key2543, -2), (key2392, -2), (key2482, 4), (key2543, 4), (key2392, 4)]

def rawRow14209 : Integer.Sparse Key := [(key2554, 4), (key2378, 4), (key2503, 4), (key2538, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2378, -2), (key2472, -2), (key2543, -2), (key2563, -2), (key2392, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2543, 4), (key2392, 4), (key2482, 4)]

def rawRow14210 : Integer.Sparse Key := [(key2554, 4), (key2503, 4), (key2378, 4), (key2554, -2), (key2538, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2563, -2), (key2543, -2), (key2522, -2), (key2392, -2), (key2480, -2), (key2390, -2), (key2543, 4), (key2482, 4), (key2392, 4)]

def rawRow14211 : Integer.Sparse Key := [(key2381, 4), (key2506, 4), (key2506, 4), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2392, -2), (key2392, -2), (key2482, -2), (key2482, -2), (key2522, -2), (key2522, -2), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow14212 : Integer.Sparse Key := [(key2506, 4), (key2381, 4), (key2506, 4), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow14213 : Integer.Sparse Key := [(key2506, 4), (key2506, 4), (key2381, 4), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2522, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2392, -2), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow14214 : Integer.Sparse Key := [(key2378, 4), (key2503, 4), (key2554, 4), (key2390, -2), (key2392, -2), (key2480, -2), (key2543, -2), (key2522, -2), (key2563, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2538, -2), (key2506, -2), (key2554, -2), (key2392, 4), (key2482, 4), (key2543, 4)]

def rawRow14215 : Integer.Sparse Key := [(key2378, 4), (key2554, 4), (key2503, 4), (key2392, -2), (key2390, -2), (key2543, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2381, -2), (key2378, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2506, -2), (key2392, 4), (key2543, 4), (key2482, 4)]

def rawRow14216 : Integer.Sparse Key := [(key2503, 4), (key2378, 4), (key2554, 4), (key2480, -2), (key2522, -2), (key2390, -2), (key2563, -2), (key2392, -2), (key2543, -2), (key2472, -2), (key2506, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2482, 4), (key2392, 4), (key2543, 4)]

def rawRow14217 : Integer.Sparse Key := [(key2503, 4), (key2554, 4), (key2378, 4), (key2522, -2), (key2480, -2), (key2563, -2), (key2390, -2), (key2543, -2), (key2392, -2), (key2506, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2538, -2), (key2381, -2), (key2482, 4), (key2543, 4), (key2392, 4)]

def rawRow14218 : Integer.Sparse Key := [(key2554, 4), (key2378, 4), (key2503, 4), (key2543, -2), (key2563, -2), (key2392, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2538, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2378, -2), (key2472, -2), (key2543, 4), (key2392, 4), (key2482, 4)]

def rawRow14219 : Integer.Sparse Key := [(key2554, 4), (key2503, 4), (key2378, 4), (key2563, -2), (key2543, -2), (key2522, -2), (key2392, -2), (key2480, -2), (key2390, -2), (key2554, -2), (key2538, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2543, 4), (key2482, 4), (key2392, 4)]

def rawRow14220 : Integer.Sparse Key := [(key2390, 4), (key2437, 4), (key2563, 4), (key2378, -2), (key2392, -2), (key2406, -2), (key2543, -2), (key2440, -2), (key2554, -2), (key2378, -2), (key2392, -2), (key2406, -2), (key2543, -2), (key2440, -2), (key2554, -2), (key2381, 4), (key2409, 4), (key2538, 4)]

def rawRow14221 : Integer.Sparse Key := [(key2390, 4), (key2563, 4), (key2437, 4), (key2392, -2), (key2378, -2), (key2543, -2), (key2406, -2), (key2554, -2), (key2440, -2), (key2392, -2), (key2378, -2), (key2543, -2), (key2406, -2), (key2554, -2), (key2440, -2), (key2381, 4), (key2538, 4), (key2409, 4)]

def rawRow14222 : Integer.Sparse Key := [(key2437, 4), (key2390, 4), (key2563, 4), (key2406, -2), (key2440, -2), (key2378, -2), (key2554, -2), (key2392, -2), (key2543, -2), (key2406, -2), (key2440, -2), (key2378, -2), (key2554, -2), (key2392, -2), (key2543, -2), (key2409, 4), (key2381, 4), (key2538, 4)]

def rawRow14223 : Integer.Sparse Key := [(key2437, 4), (key2563, 4), (key2390, 4), (key2440, -2), (key2406, -2), (key2554, -2), (key2378, -2), (key2543, -2), (key2392, -2), (key2440, -2), (key2406, -2), (key2554, -2), (key2378, -2), (key2543, -2), (key2392, -2), (key2409, 4), (key2538, 4), (key2381, 4)]

def rawRow14224 : Integer.Sparse Key := [(key2563, 4), (key2390, 4), (key2437, 4), (key2543, -2), (key2554, -2), (key2392, -2), (key2440, -2), (key2378, -2), (key2406, -2), (key2543, -2), (key2554, -2), (key2392, -2), (key2440, -2), (key2378, -2), (key2406, -2), (key2538, 4), (key2381, 4), (key2409, 4)]

def rawRow14225 : Integer.Sparse Key := [(key2563, 4), (key2437, 4), (key2390, 4), (key2554, -2), (key2543, -2), (key2440, -2), (key2392, -2), (key2406, -2), (key2378, -2), (key2554, -2), (key2543, -2), (key2440, -2), (key2392, -2), (key2406, -2), (key2378, -2), (key2538, 4), (key2409, 4), (key2381, 4)]

def rawRow14226 : Integer.Sparse Key := [(key2392, 4), (key2440, 4), (key2522, 4), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2381, -2), (key2392, -2), (key2409, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2378, 4), (key2406, 4), (key2472, 4)]

def rawRow14227 : Integer.Sparse Key := [(key2392, 4), (key2522, 4), (key2440, 4), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2392, -2), (key2381, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2440, -2), (key2378, 4), (key2472, 4), (key2406, 4)]

def rawRow14228 : Integer.Sparse Key := [(key2440, 4), (key2392, 4), (key2522, 4), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2409, -2), (key2440, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2406, 4), (key2378, 4), (key2472, 4)]

def rawRow14229 : Integer.Sparse Key := [(key2440, 4), (key2522, 4), (key2392, 4), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2440, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2482, -2), (key2392, -2), (key2406, 4), (key2472, 4), (key2378, 4)]

def rawRow14230 : Integer.Sparse Key := [(key2522, 4), (key2392, 4), (key2440, 4), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2482, -2), (key2506, -2), (key2392, -2), (key2440, -2), (key2381, -2), (key2409, -2), (key2472, 4), (key2378, 4), (key2406, 4)]

def rawRow14231 : Integer.Sparse Key := [(key2522, 4), (key2440, 4), (key2392, 4), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2506, -2), (key2482, -2), (key2440, -2), (key2392, -2), (key2409, -2), (key2381, -2), (key2472, 4), (key2406, 4), (key2378, 4)]

def rawRow14232 : Integer.Sparse Key := [(key2381, 4), (key2506, 4), (key2506, 4), (key2392, -2), (key2392, -2), (key2482, -2), (key2482, -2), (key2522, -2), (key2522, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, 4), (key2480, 4), (key2480, 4)]

def rawRow14233 : Integer.Sparse Key := [(key2506, 4), (key2381, 4), (key2506, 4), (key2482, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, 4), (key2390, 4), (key2480, 4)]

def rawRow14234 : Integer.Sparse Key := [(key2506, 4), (key2506, 4), (key2381, 4), (key2522, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2392, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, 4), (key2480, 4), (key2390, 4)]

def rawRow14235 : Integer.Sparse Key := [(key2392, 4), (key2440, 4), (key2522, 4), (key2381, -2), (key2392, -2), (key2409, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, 4), (key2406, 4), (key2472, 4)]

def rawRow14236 : Integer.Sparse Key := [(key2392, 4), (key2522, 4), (key2440, 4), (key2392, -2), (key2381, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2440, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, 4), (key2472, 4), (key2406, 4)]

def rawRow14237 : Integer.Sparse Key := [(key2440, 4), (key2392, 4), (key2522, 4), (key2409, -2), (key2440, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, 4), (key2378, 4), (key2472, 4)]

def rawRow14238 : Integer.Sparse Key := [(key2440, 4), (key2522, 4), (key2392, 4), (key2440, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2482, -2), (key2392, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, 4), (key2472, 4), (key2378, 4)]

def rawRow14239 : Integer.Sparse Key := [(key2522, 4), (key2392, 4), (key2440, 4), (key2482, -2), (key2506, -2), (key2392, -2), (key2440, -2), (key2381, -2), (key2409, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, 4), (key2378, 4), (key2406, 4)]

def rawRow14240 : Integer.Sparse Key := [(key2522, 4), (key2440, 4), (key2392, 4), (key2506, -2), (key2482, -2), (key2440, -2), (key2392, -2), (key2409, -2), (key2381, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, 4), (key2406, 4), (key2378, 4)]

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

def rawRow14421 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2613, 2), (key2806, 2), (key2949, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2), (key2629, -1), (key2647, -1), (key2783, -1), (key2937, -1), (key2894, -1), (key2973, -1), (key2637, 2), (key2857, 2), (key2975, 2), (key2637, -1), (key2652, -1), (key2791, -1), (key2942, -1), (key2896, -1), (key2975, -1)]

def rawRow14422 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2613, 2), (key2949, 2), (key2806, 2), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2), (key2647, -1), (key2629, -1), (key2937, -1), (key2783, -1), (key2973, -1), (key2894, -1), (key2637, 2), (key2975, 2), (key2857, 2), (key2652, -1), (key2637, -1), (key2942, -1), (key2791, -1), (key2975, -1), (key2896, -1)]

def rawRow14423 : Integer.Sparse Key := [(key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2806, 2), (key2613, 2), (key2949, 2), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2), (key2783, -1), (key2894, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2937, -1), (key2857, 2), (key2637, 2), (key2975, 2), (key2791, -1), (key2896, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2942, -1)]

def rawRow14424 : Integer.Sparse Key := [(key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2806, 2), (key2949, 2), (key2613, 2), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2), (key2894, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2937, -1), (key2647, -1), (key2857, 2), (key2975, 2), (key2637, 2), (key2896, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2942, -1), (key2652, -1)]

def rawRow14425 : Integer.Sparse Key := [(key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2949, 2), (key2613, 2), (key2806, 2), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2), (key2937, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2629, -1), (key2783, -1), (key2975, 2), (key2637, 2), (key2857, 2), (key2942, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2637, -1), (key2791, -1)]

def rawRow14426 : Integer.Sparse Key := [(key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2949, 2), (key2806, 2), (key2613, 2), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2), (key2973, -1), (key2937, -1), (key2894, -1), (key2647, -1), (key2783, -1), (key2629, -1), (key2975, 2), (key2857, 2), (key2637, 2), (key2975, -1), (key2942, -1), (key2896, -1), (key2652, -1), (key2791, -1), (key2637, -1)]

def rawRow14427 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2), (key2625, -1), (key2625, -1), (key2779, -1), (key2779, -1), (key2852, -1), (key2852, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2637, -1), (key2637, -1), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1)]

def rawRow14428 : Integer.Sparse Key := [(key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2779, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2791, -1), (key2857, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2791, -1)]

def rawRow14429 : Integer.Sparse Key := [(key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2), (key2852, -1), (key2779, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2625, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2857, -1), (key2791, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2637, -1)]

def rawRow14430 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2637, 2), (key2857, 2), (key2975, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2), (key2637, -1), (key2652, -1), (key2791, -1), (key2942, -1), (key2896, -1), (key2975, -1), (key2613, 2), (key2806, 2), (key2949, 2), (key2629, -1), (key2647, -1), (key2783, -1), (key2937, -1), (key2894, -1), (key2973, -1)]

def rawRow14431 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2637, 2), (key2975, 2), (key2857, 2), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2), (key2652, -1), (key2637, -1), (key2942, -1), (key2791, -1), (key2975, -1), (key2896, -1), (key2613, 2), (key2949, 2), (key2806, 2), (key2647, -1), (key2629, -1), (key2937, -1), (key2783, -1), (key2973, -1), (key2894, -1)]

def rawRow14432 : Integer.Sparse Key := [(key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2857, 2), (key2637, 2), (key2975, 2), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2), (key2791, -1), (key2896, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2942, -1), (key2806, 2), (key2613, 2), (key2949, 2), (key2783, -1), (key2894, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2937, -1)]

def rawRow14433 : Integer.Sparse Key := [(key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2857, 2), (key2975, 2), (key2637, 2), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2), (key2896, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2942, -1), (key2652, -1), (key2806, 2), (key2949, 2), (key2613, 2), (key2894, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2937, -1), (key2647, -1)]

def rawRow14434 : Integer.Sparse Key := [(key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2975, 2), (key2637, 2), (key2857, 2), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2), (key2942, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2637, -1), (key2791, -1), (key2949, 2), (key2613, 2), (key2806, 2), (key2937, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2629, -1), (key2783, -1)]

def rawRow14435 : Integer.Sparse Key := [(key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2975, 2), (key2857, 2), (key2637, 2), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2), (key2975, -1), (key2942, -1), (key2896, -1), (key2652, -1), (key2791, -1), (key2637, -1), (key2949, 2), (key2806, 2), (key2613, 2), (key2973, -1), (key2937, -1), (key2894, -1), (key2647, -1), (key2783, -1), (key2629, -1)]

def rawRow14436 : Integer.Sparse Key := [(key2625, -1), (key2637, -1), (key2699, -1), (key2975, -1), (key2723, -1), (key2982, -1), (key2629, 2), (key2703, 2), (key2973, 2), (key2625, -1), (key2637, -1), (key2699, -1), (key2975, -1), (key2723, -1), (key2982, -1), (key2609, 2), (key2652, 2), (key2664, 2), (key2942, 2), (key2746, 2), (key2959, 2), (key2613, -1), (key2647, -1), (key2668, -1), (key2937, -1), (key2736, -1), (key2949, -1), (key2629, 2), (key2703, 2), (key2973, 2), (key2613, -1), (key2647, -1), (key2668, -1), (key2937, -1), (key2736, -1), (key2949, -1)]

def rawRow14437 : Integer.Sparse Key := [(key2637, -1), (key2625, -1), (key2975, -1), (key2699, -1), (key2982, -1), (key2723, -1), (key2629, 2), (key2973, 2), (key2703, 2), (key2637, -1), (key2625, -1), (key2975, -1), (key2699, -1), (key2982, -1), (key2723, -1), (key2652, 2), (key2609, 2), (key2942, 2), (key2664, 2), (key2959, 2), (key2746, 2), (key2647, -1), (key2613, -1), (key2937, -1), (key2668, -1), (key2949, -1), (key2736, -1), (key2629, 2), (key2973, 2), (key2703, 2), (key2647, -1), (key2613, -1), (key2937, -1), (key2668, -1), (key2949, -1), (key2736, -1)]

def rawRow14438 : Integer.Sparse Key := [(key2699, -1), (key2723, -1), (key2625, -1), (key2982, -1), (key2637, -1), (key2975, -1), (key2703, 2), (key2629, 2), (key2973, 2), (key2699, -1), (key2723, -1), (key2625, -1), (key2982, -1), (key2637, -1), (key2975, -1), (key2664, 2), (key2746, 2), (key2609, 2), (key2959, 2), (key2652, 2), (key2942, 2), (key2668, -1), (key2736, -1), (key2613, -1), (key2949, -1), (key2647, -1), (key2937, -1), (key2703, 2), (key2629, 2), (key2973, 2), (key2668, -1), (key2736, -1), (key2613, -1), (key2949, -1), (key2647, -1), (key2937, -1)]

def rawRow14439 : Integer.Sparse Key := [(key2723, -1), (key2699, -1), (key2982, -1), (key2625, -1), (key2975, -1), (key2637, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2723, -1), (key2699, -1), (key2982, -1), (key2625, -1), (key2975, -1), (key2637, -1), (key2746, 2), (key2664, 2), (key2959, 2), (key2609, 2), (key2942, 2), (key2652, 2), (key2736, -1), (key2668, -1), (key2949, -1), (key2613, -1), (key2937, -1), (key2647, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2736, -1), (key2668, -1), (key2949, -1), (key2613, -1), (key2937, -1), (key2647, -1)]

def rawRow14440 : Integer.Sparse Key := [(key2975, -1), (key2982, -1), (key2637, -1), (key2723, -1), (key2625, -1), (key2699, -1), (key2973, 2), (key2629, 2), (key2703, 2), (key2975, -1), (key2982, -1), (key2637, -1), (key2723, -1), (key2625, -1), (key2699, -1), (key2942, 2), (key2959, 2), (key2652, 2), (key2746, 2), (key2609, 2), (key2664, 2), (key2937, -1), (key2949, -1), (key2647, -1), (key2736, -1), (key2613, -1), (key2668, -1), (key2973, 2), (key2629, 2), (key2703, 2), (key2937, -1), (key2949, -1), (key2647, -1), (key2736, -1), (key2613, -1), (key2668, -1)]

def rawRow14441 : Integer.Sparse Key := [(key2982, -1), (key2975, -1), (key2723, -1), (key2637, -1), (key2699, -1), (key2625, -1), (key2973, 2), (key2703, 2), (key2629, 2), (key2982, -1), (key2975, -1), (key2723, -1), (key2637, -1), (key2699, -1), (key2625, -1), (key2959, 2), (key2942, 2), (key2746, 2), (key2652, 2), (key2664, 2), (key2609, 2), (key2949, -1), (key2937, -1), (key2736, -1), (key2647, -1), (key2668, -1), (key2613, -1), (key2973, 2), (key2703, 2), (key2629, 2), (key2949, -1), (key2937, -1), (key2736, -1), (key2647, -1), (key2668, -1), (key2613, -1)]

def rawRow14442 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2625, 2), (key2699, 2), (key2852, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2613, 2), (key2637, 2), (key2668, 2), (key2791, 2), (key2723, 2), (key2826, 2), (key2609, -1), (key2625, -1), (key2664, -1), (key2779, -1), (key2699, -1), (key2802, -1), (key2647, 2), (key2736, 2), (key2894, 2), (key2613, -1), (key2629, -1), (key2668, -1), (key2783, -1), (key2703, -1), (key2806, -1)]

def rawRow14443 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2625, 2), (key2852, 2), (key2699, 2), (key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2637, 2), (key2613, 2), (key2791, 2), (key2668, 2), (key2826, 2), (key2723, 2), (key2625, -1), (key2609, -1), (key2779, -1), (key2664, -1), (key2802, -1), (key2699, -1), (key2647, 2), (key2894, 2), (key2736, 2), (key2629, -1), (key2613, -1), (key2783, -1), (key2668, -1), (key2806, -1), (key2703, -1)]

def rawRow14444 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2699, 2), (key2625, 2), (key2852, 2), (key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2668, 2), (key2723, 2), (key2613, 2), (key2826, 2), (key2637, 2), (key2791, 2), (key2664, -1), (key2699, -1), (key2609, -1), (key2802, -1), (key2625, -1), (key2779, -1), (key2736, 2), (key2647, 2), (key2894, 2), (key2668, -1), (key2703, -1), (key2613, -1), (key2806, -1), (key2629, -1), (key2783, -1)]

def rawRow14445 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2699, 2), (key2852, 2), (key2625, 2), (key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2723, 2), (key2668, 2), (key2826, 2), (key2613, 2), (key2791, 2), (key2637, 2), (key2699, -1), (key2664, -1), (key2802, -1), (key2609, -1), (key2779, -1), (key2625, -1), (key2736, 2), (key2894, 2), (key2647, 2), (key2703, -1), (key2668, -1), (key2806, -1), (key2613, -1), (key2783, -1), (key2629, -1)]

def rawRow14446 : Integer.Sparse Key := [(key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2852, 2), (key2625, 2), (key2699, 2), (key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2791, 2), (key2826, 2), (key2637, 2), (key2723, 2), (key2613, 2), (key2668, 2), (key2779, -1), (key2802, -1), (key2625, -1), (key2699, -1), (key2609, -1), (key2664, -1), (key2894, 2), (key2647, 2), (key2736, 2), (key2783, -1), (key2806, -1), (key2629, -1), (key2703, -1), (key2613, -1), (key2668, -1)]

def rawRow14447 : Integer.Sparse Key := [(key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2852, 2), (key2699, 2), (key2625, 2), (key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2826, 2), (key2791, 2), (key2723, 2), (key2637, 2), (key2668, 2), (key2613, 2), (key2802, -1), (key2779, -1), (key2699, -1), (key2625, -1), (key2664, -1), (key2609, -1), (key2894, 2), (key2736, 2), (key2647, 2), (key2806, -1), (key2783, -1), (key2703, -1), (key2629, -1), (key2668, -1), (key2613, -1)]

def rawRow14448 : Integer.Sparse Key := [(key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2), (key2637, -1), (key2637, -1), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2625, -1), (key2625, -1), (key2779, -1), (key2779, -1), (key2852, -1), (key2852, -1)]

def rawRow14449 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2791, -1), (key2857, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2779, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2779, -1)]

def rawRow14450 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2), (key2857, -1), (key2791, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2637, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2852, -1), (key2779, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2625, -1)]

def rawRow14451 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2647, 2), (key2736, 2), (key2894, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2613, 2), (key2637, 2), (key2668, 2), (key2791, 2), (key2723, 2), (key2826, 2), (key2613, -1), (key2629, -1), (key2668, -1), (key2783, -1), (key2703, -1), (key2806, -1), (key2625, 2), (key2699, 2), (key2852, 2), (key2609, -1), (key2625, -1), (key2664, -1), (key2779, -1), (key2699, -1), (key2802, -1)]

def rawRow14452 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2647, 2), (key2894, 2), (key2736, 2), (key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2637, 2), (key2613, 2), (key2791, 2), (key2668, 2), (key2826, 2), (key2723, 2), (key2629, -1), (key2613, -1), (key2783, -1), (key2668, -1), (key2806, -1), (key2703, -1), (key2625, 2), (key2852, 2), (key2699, 2), (key2625, -1), (key2609, -1), (key2779, -1), (key2664, -1), (key2802, -1), (key2699, -1)]

def rawRow14453 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2736, 2), (key2647, 2), (key2894, 2), (key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2668, 2), (key2723, 2), (key2613, 2), (key2826, 2), (key2637, 2), (key2791, 2), (key2668, -1), (key2703, -1), (key2613, -1), (key2806, -1), (key2629, -1), (key2783, -1), (key2699, 2), (key2625, 2), (key2852, 2), (key2664, -1), (key2699, -1), (key2609, -1), (key2802, -1), (key2625, -1), (key2779, -1)]

def rawRow14454 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2736, 2), (key2894, 2), (key2647, 2), (key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2723, 2), (key2668, 2), (key2826, 2), (key2613, 2), (key2791, 2), (key2637, 2), (key2703, -1), (key2668, -1), (key2806, -1), (key2613, -1), (key2783, -1), (key2629, -1), (key2699, 2), (key2852, 2), (key2625, 2), (key2699, -1), (key2664, -1), (key2802, -1), (key2609, -1), (key2779, -1), (key2625, -1)]

def rawRow14455 : Integer.Sparse Key := [(key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2894, 2), (key2647, 2), (key2736, 2), (key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2791, 2), (key2826, 2), (key2637, 2), (key2723, 2), (key2613, 2), (key2668, 2), (key2783, -1), (key2806, -1), (key2629, -1), (key2703, -1), (key2613, -1), (key2668, -1), (key2852, 2), (key2625, 2), (key2699, 2), (key2779, -1), (key2802, -1), (key2625, -1), (key2699, -1), (key2609, -1), (key2664, -1)]

def rawRow14456 : Integer.Sparse Key := [(key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2894, 2), (key2736, 2), (key2647, 2), (key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2826, 2), (key2791, 2), (key2723, 2), (key2637, 2), (key2668, 2), (key2613, 2), (key2806, -1), (key2783, -1), (key2703, -1), (key2629, -1), (key2668, -1), (key2613, -1), (key2852, 2), (key2699, 2), (key2625, 2), (key2802, -1), (key2779, -1), (key2699, -1), (key2625, -1), (key2664, -1), (key2609, -1)]

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

def rawRow14565 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2611, 2), (key2804, 2), (key2825, 2), (key2624, -1), (key2627, -1), (key2851, -1), (key2866, -1), (key2971, -1), (key2981, -1), (key2624, 2), (key2636, 2), (key2698, 2), (key2722, 2), (key2974, 2), (key2981, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2722, -1), (key2856, -1), (key2866, -1), (key2645, 2), (key2892, 2), (key2902, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2745, -1), (key2895, -1), (key2902, -1)]

def rawRow14566 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2611, 2), (key2825, 2), (key2804, 2), (key2627, -1), (key2624, -1), (key2866, -1), (key2851, -1), (key2981, -1), (key2971, -1), (key2636, 2), (key2624, 2), (key2722, 2), (key2698, 2), (key2981, 2), (key2974, 2), (key2636, -1), (key2627, -1), (key2722, -1), (key2701, -1), (key2866, -1), (key2856, -1), (key2645, 2), (key2902, 2), (key2892, 2), (key2651, -1), (key2645, -1), (key2745, -1), (key2734, -1), (key2902, -1), (key2895, -1)]

def rawRow14567 : Integer.Sparse Key := [(key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2804, 2), (key2611, 2), (key2825, 2), (key2851, -1), (key2971, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2698, 2), (key2974, 2), (key2624, 2), (key2981, 2), (key2636, 2), (key2722, 2), (key2701, -1), (key2856, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2892, 2), (key2645, 2), (key2902, 2), (key2734, -1), (key2895, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2745, -1)]

def rawRow14568 : Integer.Sparse Key := [(key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2804, 2), (key2825, 2), (key2611, 2), (key2971, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2866, -1), (key2627, -1), (key2974, 2), (key2698, 2), (key2981, 2), (key2624, 2), (key2722, 2), (key2636, 2), (key2856, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2722, -1), (key2636, -1), (key2892, 2), (key2902, 2), (key2645, 2), (key2895, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2745, -1), (key2651, -1)]

def rawRow14569 : Integer.Sparse Key := [(key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2825, 2), (key2611, 2), (key2804, 2), (key2866, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2624, -1), (key2851, -1), (key2722, 2), (key2981, 2), (key2636, 2), (key2974, 2), (key2624, 2), (key2698, 2), (key2722, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2627, -1), (key2701, -1), (key2902, 2), (key2645, 2), (key2892, 2), (key2745, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2645, -1), (key2734, -1)]

def rawRow14570 : Integer.Sparse Key := [(key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2825, 2), (key2804, 2), (key2611, 2), (key2981, -1), (key2866, -1), (key2971, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2981, 2), (key2722, 2), (key2974, 2), (key2636, 2), (key2698, 2), (key2624, 2), (key2866, -1), (key2722, -1), (key2856, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2902, 2), (key2892, 2), (key2645, 2), (key2902, -1), (key2745, -1), (key2895, -1), (key2651, -1), (key2734, -1), (key2645, -1)]

def rawRow14571 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2636, -1), (key2636, -1), (key2856, -1), (key2856, -1), (key2974, -1), (key2974, -1), (key2627, 2), (key2627, 2), (key2701, 2), (key2701, 2), (key2971, 2), (key2971, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2651, 2), (key2895, 2), (key2895, 2), (key2645, -1), (key2645, -1), (key2734, -1), (key2734, -1), (key2892, -1), (key2892, -1)]

def rawRow14572 : Integer.Sparse Key := [(key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2856, -1), (key2974, -1), (key2636, -1), (key2974, -1), (key2636, -1), (key2856, -1), (key2701, 2), (key2971, 2), (key2627, 2), (key2971, 2), (key2627, 2), (key2701, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2895, 2), (key2651, 2), (key2895, 2), (key2734, -1), (key2892, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2734, -1)]

def rawRow14573 : Integer.Sparse Key := [(key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2974, -1), (key2856, -1), (key2974, -1), (key2636, -1), (key2856, -1), (key2636, -1), (key2971, 2), (key2701, 2), (key2971, 2), (key2627, 2), (key2701, 2), (key2627, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2895, 2), (key2895, 2), (key2651, 2), (key2892, -1), (key2734, -1), (key2892, -1), (key2645, -1), (key2734, -1), (key2645, -1)]

def rawRow14574 : Integer.Sparse Key := [(key2624, -1), (key2627, -1), (key2851, -1), (key2971, -1), (key2866, -1), (key2981, -1), (key2636, 2), (key2856, 2), (key2974, 2), (key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2624, 2), (key2636, 2), (key2698, 2), (key2722, 2), (key2974, 2), (key2981, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2745, -1), (key2895, -1), (key2902, -1), (key2611, 2), (key2804, 2), (key2825, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2722, -1), (key2856, -1), (key2866, -1)]

def rawRow14575 : Integer.Sparse Key := [(key2627, -1), (key2624, -1), (key2971, -1), (key2851, -1), (key2981, -1), (key2866, -1), (key2636, 2), (key2974, 2), (key2856, 2), (key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2636, 2), (key2624, 2), (key2722, 2), (key2698, 2), (key2981, 2), (key2974, 2), (key2651, -1), (key2645, -1), (key2745, -1), (key2734, -1), (key2902, -1), (key2895, -1), (key2611, 2), (key2825, 2), (key2804, 2), (key2636, -1), (key2627, -1), (key2722, -1), (key2701, -1), (key2866, -1), (key2856, -1)]

def rawRow14576 : Integer.Sparse Key := [(key2851, -1), (key2866, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2856, 2), (key2636, 2), (key2974, 2), (key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2698, 2), (key2974, 2), (key2624, 2), (key2981, 2), (key2636, 2), (key2722, 2), (key2734, -1), (key2895, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2804, 2), (key2611, 2), (key2825, 2), (key2701, -1), (key2856, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2722, -1)]

def rawRow14577 : Integer.Sparse Key := [(key2866, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2971, -1), (key2627, -1), (key2856, 2), (key2974, 2), (key2636, 2), (key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2974, 2), (key2698, 2), (key2981, 2), (key2624, 2), (key2722, 2), (key2636, 2), (key2895, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2745, -1), (key2651, -1), (key2804, 2), (key2825, 2), (key2611, 2), (key2856, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2722, -1), (key2636, -1)]

def rawRow14578 : Integer.Sparse Key := [(key2971, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2624, -1), (key2851, -1), (key2974, 2), (key2636, 2), (key2856, 2), (key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2722, 2), (key2981, 2), (key2636, 2), (key2974, 2), (key2624, 2), (key2698, 2), (key2745, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2645, -1), (key2734, -1), (key2825, 2), (key2611, 2), (key2804, 2), (key2722, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2627, -1), (key2701, -1)]

def rawRow14579 : Integer.Sparse Key := [(key2981, -1), (key2971, -1), (key2866, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2974, 2), (key2856, 2), (key2636, 2), (key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2981, 2), (key2722, 2), (key2974, 2), (key2636, 2), (key2698, 2), (key2624, 2), (key2902, -1), (key2745, -1), (key2895, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2825, 2), (key2804, 2), (key2611, 2), (key2866, -1), (key2722, -1), (key2856, -1), (key2636, -1), (key2701, -1), (key2627, -1)]

def rawRow14580 : Integer.Sparse Key := [(key2624, -1), (key2636, -1), (key2698, -1), (key2974, -1), (key2722, -1), (key2981, -1), (key2627, 2), (key2701, 2), (key2971, 2), (key2624, -1), (key2636, -1), (key2698, -1), (key2974, -1), (key2722, -1), (key2981, -1), (key2608, 2), (key2651, 2), (key2663, 2), (key2745, 2), (key2941, 2), (key2958, 2), (key2611, -1), (key2636, -1), (key2666, -1), (key2722, -1), (key2790, -1), (key2825, -1), (key2627, 2), (key2781, 2), (key2866, 2), (key2611, -1), (key2636, -1), (key2666, -1), (key2722, -1), (key2790, -1), (key2825, -1)]

def rawRow14581 : Integer.Sparse Key := [(key2636, -1), (key2624, -1), (key2974, -1), (key2698, -1), (key2981, -1), (key2722, -1), (key2627, 2), (key2971, 2), (key2701, 2), (key2636, -1), (key2624, -1), (key2974, -1), (key2698, -1), (key2981, -1), (key2722, -1), (key2651, 2), (key2608, 2), (key2745, 2), (key2663, 2), (key2958, 2), (key2941, 2), (key2636, -1), (key2611, -1), (key2722, -1), (key2666, -1), (key2825, -1), (key2790, -1), (key2627, 2), (key2866, 2), (key2781, 2), (key2636, -1), (key2611, -1), (key2722, -1), (key2666, -1), (key2825, -1), (key2790, -1)]

def rawRow14582 : Integer.Sparse Key := [(key2698, -1), (key2722, -1), (key2624, -1), (key2981, -1), (key2636, -1), (key2974, -1), (key2701, 2), (key2627, 2), (key2971, 2), (key2698, -1), (key2722, -1), (key2624, -1), (key2981, -1), (key2636, -1), (key2974, -1), (key2663, 2), (key2745, 2), (key2608, 2), (key2958, 2), (key2651, 2), (key2745, 2), (key2666, -1), (key2790, -1), (key2611, -1), (key2825, -1), (key2636, -1), (key2722, -1), (key2781, 2), (key2627, 2), (key2866, 2), (key2666, -1), (key2790, -1), (key2611, -1), (key2825, -1), (key2636, -1), (key2722, -1)]

def rawRow14583 : Integer.Sparse Key := [(key2722, -1), (key2698, -1), (key2981, -1), (key2624, -1), (key2974, -1), (key2636, -1), (key2701, 2), (key2971, 2), (key2627, 2), (key2722, -1), (key2698, -1), (key2981, -1), (key2624, -1), (key2974, -1), (key2636, -1), (key2745, 2), (key2663, 2), (key2958, 2), (key2608, 2), (key2745, 2), (key2651, 2), (key2790, -1), (key2666, -1), (key2825, -1), (key2611, -1), (key2722, -1), (key2636, -1), (key2781, 2), (key2866, 2), (key2627, 2), (key2790, -1), (key2666, -1), (key2825, -1), (key2611, -1), (key2722, -1), (key2636, -1)]

def rawRow14584 : Integer.Sparse Key := [(key2974, -1), (key2981, -1), (key2636, -1), (key2722, -1), (key2624, -1), (key2698, -1), (key2971, 2), (key2627, 2), (key2701, 2), (key2974, -1), (key2981, -1), (key2636, -1), (key2722, -1), (key2624, -1), (key2698, -1), (key2941, 2), (key2958, 2), (key2651, 2), (key2745, 2), (key2608, 2), (key2663, 2), (key2722, -1), (key2825, -1), (key2636, -1), (key2790, -1), (key2611, -1), (key2666, -1), (key2866, 2), (key2627, 2), (key2781, 2), (key2722, -1), (key2825, -1), (key2636, -1), (key2790, -1), (key2611, -1), (key2666, -1)]

def rawRow14585 : Integer.Sparse Key := [(key2981, -1), (key2974, -1), (key2722, -1), (key2636, -1), (key2698, -1), (key2624, -1), (key2971, 2), (key2701, 2), (key2627, 2), (key2981, -1), (key2974, -1), (key2722, -1), (key2636, -1), (key2698, -1), (key2624, -1), (key2958, 2), (key2941, 2), (key2745, 2), (key2651, 2), (key2663, 2), (key2608, 2), (key2825, -1), (key2722, -1), (key2790, -1), (key2636, -1), (key2666, -1), (key2611, -1), (key2866, 2), (key2781, 2), (key2627, 2), (key2825, -1), (key2722, -1), (key2790, -1), (key2636, -1), (key2666, -1), (key2611, -1)]

def rawRow14586 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2611, 2), (key2636, 2), (key2666, 2), (key2790, 2), (key2722, 2), (key2825, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2636, 2), (key2790, 2), (key2856, 2), (key2611, -1), (key2627, -1), (key2666, -1), (key2701, -1), (key2781, -1), (key2804, -1)]

def rawRow14587 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2636, 2), (key2611, 2), (key2790, 2), (key2666, 2), (key2825, 2), (key2722, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2636, 2), (key2856, 2), (key2790, 2), (key2627, -1), (key2611, -1), (key2701, -1), (key2666, -1), (key2804, -1), (key2781, -1)]

def rawRow14588 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2666, 2), (key2722, 2), (key2611, 2), (key2825, 2), (key2636, 2), (key2790, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2790, 2), (key2636, 2), (key2856, 2), (key2666, -1), (key2781, -1), (key2611, -1), (key2804, -1), (key2627, -1), (key2701, -1)]

def rawRow14589 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2722, 2), (key2666, 2), (key2825, 2), (key2611, 2), (key2790, 2), (key2636, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2790, 2), (key2856, 2), (key2636, 2), (key2781, -1), (key2666, -1), (key2804, -1), (key2611, -1), (key2701, -1), (key2627, -1)]

def rawRow14590 : Integer.Sparse Key := [(key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2790, 2), (key2825, 2), (key2636, 2), (key2722, 2), (key2611, 2), (key2666, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2856, 2), (key2636, 2), (key2790, 2), (key2701, -1), (key2804, -1), (key2627, -1), (key2781, -1), (key2611, -1), (key2666, -1)]

def rawRow14591 : Integer.Sparse Key := [(key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2825, 2), (key2790, 2), (key2722, 2), (key2636, 2), (key2666, 2), (key2611, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2856, 2), (key2790, 2), (key2636, 2), (key2804, -1), (key2701, -1), (key2781, -1), (key2627, -1), (key2666, -1), (key2611, -1)]

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

def rawRow14592 : Integer.Sparse Key := [(key2645, -1), (key2645, -1), (key2892, -1), (key2892, -1), (key2902, -1), (key2902, -1), (key2651, 2), (key2895, 2), (key2895, 2), (key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2627, 2), (key2627, 2), (key2781, 2), (key2781, 2), (key2866, 2), (key2866, 2), (key2636, -1), (key2636, -1), (key2790, -1), (key2790, -1), (key2856, -1), (key2856, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1)]

def rawRow14593 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2645, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2895, 2), (key2651, 2), (key2895, 2), (key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2781, 2), (key2866, 2), (key2627, 2), (key2866, 2), (key2627, 2), (key2781, 2), (key2790, -1), (key2856, -1), (key2636, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1)]

def rawRow14594 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2895, 2), (key2895, 2), (key2651, 2), (key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2866, 2), (key2781, 2), (key2866, 2), (key2627, 2), (key2781, 2), (key2627, 2), (key2856, -1), (key2790, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2636, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1)]

def rawRow14595 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2645, 2), (key2734, 2), (key2892, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2611, 2), (key2636, 2), (key2666, 2), (key2790, 2), (key2722, 2), (key2825, 2), (key2611, -1), (key2627, -1), (key2666, -1), (key2781, -1), (key2701, -1), (key2804, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1)]

def rawRow14596 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2645, 2), (key2892, 2), (key2734, 2), (key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2636, 2), (key2611, 2), (key2790, 2), (key2666, 2), (key2825, 2), (key2722, 2), (key2627, -1), (key2611, -1), (key2781, -1), (key2666, -1), (key2804, -1), (key2701, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1)]

def rawRow14597 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2734, 2), (key2645, 2), (key2892, 2), (key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2666, 2), (key2722, 2), (key2611, 2), (key2825, 2), (key2636, 2), (key2790, 2), (key2666, -1), (key2701, -1), (key2611, -1), (key2804, -1), (key2627, -1), (key2781, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1)]

def rawRow14598 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2734, 2), (key2892, 2), (key2645, 2), (key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2722, 2), (key2666, 2), (key2825, 2), (key2611, 2), (key2790, 2), (key2636, 2), (key2701, -1), (key2666, -1), (key2804, -1), (key2611, -1), (key2781, -1), (key2627, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1)]

def rawRow14599 : Integer.Sparse Key := [(key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2892, 2), (key2645, 2), (key2734, 2), (key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2790, 2), (key2825, 2), (key2636, 2), (key2722, 2), (key2611, 2), (key2666, 2), (key2781, -1), (key2804, -1), (key2627, -1), (key2701, -1), (key2611, -1), (key2666, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1)]

def rawRow14600 : Integer.Sparse Key := [(key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2892, 2), (key2734, 2), (key2645, 2), (key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2825, 2), (key2790, 2), (key2722, 2), (key2636, 2), (key2666, 2), (key2611, 2), (key2804, -1), (key2781, -1), (key2701, -1), (key2627, -1), (key2666, -1), (key2611, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1)]

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

def rawRow14841 : Integer.Sparse Key := [(key2457, 4), (key2521, 4), (key2521, 4), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2525, -2), (key2525, -2), (key2532, -2), (key2532, -2), (key2562, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2533, 4), (key2564, 4), (key2564, 4)]

def rawRow14842 : Integer.Sparse Key := [(key2521, 4), (key2457, 4), (key2521, 4), (key2521, -2), (key2525, -2), (key2460, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow14843 : Integer.Sparse Key := [(key2521, 4), (key2521, 4), (key2457, 4), (key2525, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2460, -2), (key2564, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow14844 : Integer.Sparse Key := [(key2460, 4), (key2460, 4), (key2525, 4), (key2457, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2532, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2564, -2), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow14845 : Integer.Sparse Key := [(key2460, 4), (key2525, 4), (key2460, 4), (key2460, -2), (key2457, -2), (key2521, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow14846 : Integer.Sparse Key := [(key2525, 4), (key2460, 4), (key2460, 4), (key2521, -2), (key2521, -2), (key2460, -2), (key2460, -2), (key2457, -2), (key2457, -2), (key2564, -2), (key2564, -2), (key2533, -2), (key2533, -2), (key2532, -2), (key2532, -2), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow14847 : Integer.Sparse Key := [(key2457, 4), (key2521, 4), (key2521, 4), (key2532, -2), (key2532, -2), (key2562, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2525, -2), (key2525, -2), (key2533, 4), (key2564, 4), (key2564, 4)]

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

def rawRow14848 : Integer.Sparse Key := [(key2521, 4), (key2457, 4), (key2521, 4), (key2562, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow14849 : Integer.Sparse Key := [(key2521, 4), (key2521, 4), (key2457, 4), (key2564, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2525, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2460, -2), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow14850 : Integer.Sparse Key := [(key2460, 4), (key2460, 4), (key2533, 4), (key2521, -2), (key2525, -2), (key2521, -2), (key2564, -2), (key2525, -2), (key2564, -2), (key2457, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow14851 : Integer.Sparse Key := [(key2460, 4), (key2533, 4), (key2460, 4), (key2525, -2), (key2521, -2), (key2564, -2), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow14852 : Integer.Sparse Key := [(key2533, 4), (key2460, 4), (key2460, 4), (key2564, -2), (key2564, -2), (key2525, -2), (key2525, -2), (key2521, -2), (key2521, -2), (key2521, -2), (key2521, -2), (key2460, -2), (key2460, -2), (key2457, -2), (key2457, -2), (key2562, 4), (key2532, 4), (key2532, 4)]

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

def rawRow14988 : Integer.Sparse Key := [(key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2443, -1), (key2443, -1), (key2411, 2), (key2443, 2), (key2443, 2), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2509, -1), (key2509, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2484, -1), (key2484, -1), (key2509, -1), (key2509, -1), (key2524, -1), (key2524, -1), (key2569, 2), (key2576, 2), (key2576, 2), (key2571, -1), (key2571, -1), (key2576, -1), (key2576, -1), (key2580, -1), (key2580, -1)]

def rawRow14989 : Integer.Sparse Key := [(key2437, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2443, 2), (key2411, 2), (key2443, 2), (key2503, -1), (key2509, -1), (key2472, -1), (key2509, -1), (key2472, -1), (key2503, -1), (key2503, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2509, -1), (key2524, -1), (key2484, -1), (key2524, -1), (key2484, -1), (key2509, -1), (key2576, 2), (key2569, 2), (key2576, 2), (key2576, -1), (key2580, -1), (key2571, -1), (key2580, -1), (key2571, -1), (key2576, -1)]

def rawRow14990 : Integer.Sparse Key := [(key2443, -1), (key2437, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2443, 2), (key2443, 2), (key2411, 2), (key2509, -1), (key2503, -1), (key2509, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2524, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2524, -1), (key2509, -1), (key2524, -1), (key2484, -1), (key2509, -1), (key2484, -1), (key2576, 2), (key2576, 2), (key2569, 2), (key2580, -1), (key2576, -1), (key2580, -1), (key2571, -1), (key2576, -1), (key2571, -1)]

def rawRow14991 : Integer.Sparse Key := [(key2406, -1), (key2411, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2443, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2480, -1), (key2484, -1), (key2480, -1), (key2524, -1), (key2484, -1), (key2524, -1), (key2472, 2), (key2484, 2), (key2472, 2), (key2509, 2), (key2484, 2), (key2509, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1), (key2571, 2), (key2571, 2), (key2580, 2), (key2569, -1), (key2571, -1), (key2569, -1), (key2576, -1), (key2571, -1), (key2576, -1)]

def rawRow14992 : Integer.Sparse Key := [(key2411, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2484, -1), (key2480, -1), (key2524, -1), (key2480, -1), (key2524, -1), (key2484, -1), (key2484, 2), (key2472, 2), (key2509, 2), (key2472, 2), (key2509, 2), (key2484, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2571, 2), (key2580, 2), (key2571, 2), (key2571, -1), (key2569, -1), (key2576, -1), (key2569, -1), (key2576, -1), (key2571, -1)]

def rawRow14993 : Integer.Sparse Key := [(key2443, -1), (key2443, -1), (key2411, -1), (key2411, -1), (key2406, -1), (key2406, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2524, -1), (key2524, -1), (key2484, -1), (key2484, -1), (key2480, -1), (key2480, -1), (key2509, 2), (key2509, 2), (key2484, 2), (key2484, 2), (key2472, 2), (key2472, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1), (key2580, 2), (key2571, 2), (key2571, 2), (key2576, -1), (key2576, -1), (key2571, -1), (key2571, -1), (key2569, -1), (key2569, -1)]

def rawRow14994 : Integer.Sparse Key := [(key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2968, -1), (key2968, -1), (key2880, 2), (key2989, 2), (key2989, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2443, -1), (key2443, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2571, -1), (key2571, -1), (key2576, -1), (key2576, -1), (key2580, -1), (key2580, -1), (key2411, 2), (key2443, 2), (key2443, 2), (key2484, -1), (key2484, -1), (key2509, -1), (key2509, -1), (key2524, -1), (key2524, -1)]

def rawRow14995 : Integer.Sparse Key := [(key2966, -1), (key2968, -1), (key2843, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2989, 2), (key2880, 2), (key2989, 2), (key2437, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2503, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2576, -1), (key2580, -1), (key2571, -1), (key2580, -1), (key2571, -1), (key2576, -1), (key2443, 2), (key2411, 2), (key2443, 2), (key2509, -1), (key2524, -1), (key2484, -1), (key2524, -1), (key2484, -1), (key2509, -1)]

def rawRow14996 : Integer.Sparse Key := [(key2968, -1), (key2966, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2843, -1), (key2989, 2), (key2989, 2), (key2880, 2), (key2443, -1), (key2437, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2524, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2580, -1), (key2576, -1), (key2580, -1), (key2571, -1), (key2576, -1), (key2571, -1), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, -1), (key2509, -1), (key2524, -1), (key2484, -1), (key2509, -1), (key2484, -1)]

def rawRow14997 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2843, -1), (key2968, -1), (key2880, -1), (key2989, -1), (key2587, 2), (key2843, 2), (key2966, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2995, -1), (key2910, -1), (key3002, -1), (key2587, 2), (key2600, 2), (key2766, 2), (key2931, 2), (key2910, 2), (key2989, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1), (key2394, 2), (key2484, 2), (key2524, 2), (key2383, -1), (key2394, -1), (key2411, -1), (key2443, -1), (key2484, -1), (key2509, -1)]

def rawRow14998 : Integer.Sparse Key := [(key2593, -1), (key2587, -1), (key2968, -1), (key2843, -1), (key2989, -1), (key2880, -1), (key2587, 2), (key2966, 2), (key2843, 2), (key2600, -1), (key2598, -1), (key2995, -1), (key2887, -1), (key3002, -1), (key2910, -1), (key2600, 2), (key2587, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2910, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1), (key2394, 2), (key2524, 2), (key2484, 2), (key2394, -1), (key2383, -1), (key2443, -1), (key2411, -1), (key2509, -1), (key2484, -1)]

def rawRow14999 : Integer.Sparse Key := [(key2843, -1), (key2880, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2843, 2), (key2587, 2), (key2966, 2), (key2887, -1), (key2910, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2766, 2), (key2910, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2484, 2), (key2394, 2), (key2524, 2), (key2411, -1), (key2484, -1), (key2383, -1), (key2509, -1), (key2394, -1), (key2443, -1)]

def rawRow15000 : Integer.Sparse Key := [(key2880, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2968, -1), (key2593, -1), (key2843, 2), (key2966, 2), (key2587, 2), (key2910, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2995, -1), (key2600, -1), (key2910, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2931, 2), (key2600, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1), (key2484, 2), (key2524, 2), (key2394, 2), (key2484, -1), (key2411, -1), (key2509, -1), (key2383, -1), (key2443, -1), (key2394, -1)]

def rawRow15001 : Integer.Sparse Key := [(key2968, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2587, -1), (key2843, -1), (key2966, 2), (key2587, 2), (key2843, 2), (key2995, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2598, -1), (key2887, -1), (key2931, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2587, 2), (key2766, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1), (key2524, 2), (key2394, 2), (key2484, 2), (key2443, -1), (key2509, -1), (key2394, -1), (key2484, -1), (key2383, -1), (key2411, -1)]

def rawRow15002 : Integer.Sparse Key := [(key2989, -1), (key2968, -1), (key2880, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2966, 2), (key2843, 2), (key2587, 2), (key3002, -1), (key2995, -1), (key2910, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2989, 2), (key2931, 2), (key2910, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2524, 2), (key2484, 2), (key2394, 2), (key2509, -1), (key2443, -1), (key2484, -1), (key2394, -1), (key2411, -1), (key2383, -1)]

def rawRow15003 : Integer.Sparse Key := [(key2887, -1), (key2889, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2995, -1), (key2910, 2), (key2910, 2), (key3002, 2), (key2766, -1), (key2772, -1), (key2766, -1), (key2931, -1), (key2772, -1), (key2931, -1), (key2843, 2), (key2889, 2), (key2843, 2), (key2968, 2), (key2889, 2), (key2968, 2), (key2880, -1), (key2910, -1), (key2880, -1), (key2989, -1), (key2910, -1), (key2989, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1)]

def rawRow15004 : Integer.Sparse Key := [(key2889, -1), (key2887, -1), (key2995, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2910, 2), (key3002, 2), (key2910, 2), (key2772, -1), (key2766, -1), (key2931, -1), (key2766, -1), (key2931, -1), (key2772, -1), (key2889, 2), (key2843, 2), (key2968, 2), (key2843, 2), (key2968, 2), (key2889, 2), (key2910, -1), (key2880, -1), (key2989, -1), (key2880, -1), (key2989, -1), (key2910, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1)]

def rawRow15005 : Integer.Sparse Key := [(key2995, -1), (key2995, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key3002, 2), (key2910, 2), (key2910, 2), (key2931, -1), (key2931, -1), (key2772, -1), (key2772, -1), (key2766, -1), (key2766, -1), (key2968, 2), (key2968, 2), (key2889, 2), (key2889, 2), (key2843, 2), (key2843, 2), (key2989, -1), (key2989, -1), (key2910, -1), (key2910, -1), (key2880, -1), (key2880, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1)]

def rawRow15006 : Integer.Sparse Key := [(key2598, -1), (key2600, -1), (key2887, -1), (key2995, -1), (key2910, -1), (key3002, -1), (key2600, 2), (key2889, 2), (key2995, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2968, -1), (key2880, -1), (key2989, -1), (key2587, 2), (key2600, 2), (key2766, 2), (key2931, 2), (key2910, 2), (key2989, 2), (key2593, -1), (key2600, -1), (key2772, -1), (key2931, -1), (key2889, -1), (key2968, -1), (key2378, 2), (key2472, 2), (key2503, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1)]

def rawRow15007 : Integer.Sparse Key := [(key2600, -1), (key2598, -1), (key2995, -1), (key2887, -1), (key3002, -1), (key2910, -1), (key2600, 2), (key2995, 2), (key2889, 2), (key2593, -1), (key2587, -1), (key2968, -1), (key2843, -1), (key2989, -1), (key2880, -1), (key2600, 2), (key2587, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2910, 2), (key2600, -1), (key2593, -1), (key2931, -1), (key2772, -1), (key2968, -1), (key2889, -1), (key2378, 2), (key2503, 2), (key2472, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1)]

def rawRow15008 : Integer.Sparse Key := [(key2887, -1), (key2910, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2889, 2), (key2600, 2), (key2995, 2), (key2843, -1), (key2880, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2766, 2), (key2910, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2772, -1), (key2889, -1), (key2593, -1), (key2968, -1), (key2600, -1), (key2931, -1), (key2472, 2), (key2378, 2), (key2503, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1)]

def rawRow15009 : Integer.Sparse Key := [(key2910, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2995, -1), (key2600, -1), (key2889, 2), (key2995, 2), (key2600, 2), (key2880, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2968, -1), (key2593, -1), (key2910, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2931, 2), (key2600, 2), (key2889, -1), (key2772, -1), (key2968, -1), (key2593, -1), (key2931, -1), (key2600, -1), (key2472, 2), (key2503, 2), (key2378, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1)]

def rawRow15010 : Integer.Sparse Key := [(key2995, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2598, -1), (key2887, -1), (key2995, 2), (key2600, 2), (key2889, 2), (key2968, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2587, -1), (key2843, -1), (key2931, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2587, 2), (key2766, 2), (key2931, -1), (key2968, -1), (key2600, -1), (key2889, -1), (key2593, -1), (key2772, -1), (key2503, 2), (key2378, 2), (key2472, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1)]

def rawRow15011 : Integer.Sparse Key := [(key3002, -1), (key2995, -1), (key2910, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2995, 2), (key2889, 2), (key2600, 2), (key2989, -1), (key2968, -1), (key2880, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2989, 2), (key2931, 2), (key2910, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2968, -1), (key2931, -1), (key2889, -1), (key2600, -1), (key2772, -1), (key2593, -1), (key2503, 2), (key2472, 2), (key2378, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1)]

def rawRow15012 : Integer.Sparse Key := [(key2600, -1), (key2600, -1), (key2889, -1), (key2889, -1), (key2910, -1), (key2910, -1), (key2598, 2), (key2887, 2), (key2887, 2), (key2600, -1), (key2600, -1), (key2889, -1), (key2889, -1), (key2910, -1), (key2910, -1), (key2593, 2), (key2593, 2), (key2772, 2), (key2772, 2), (key2880, 2), (key2880, 2), (key2587, -1), (key2587, -1), (key2766, -1), (key2766, -1), (key2843, -1), (key2843, -1), (key2390, 2), (key2480, 2), (key2480, 2), (key2378, -1), (key2378, -1), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1)]

def rawRow15013 : Integer.Sparse Key := [(key2889, -1), (key2910, -1), (key2600, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2887, 2), (key2598, 2), (key2887, 2), (key2889, -1), (key2910, -1), (key2600, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2772, 2), (key2880, 2), (key2593, 2), (key2880, 2), (key2593, 2), (key2772, 2), (key2766, -1), (key2843, -1), (key2587, -1), (key2843, -1), (key2587, -1), (key2766, -1), (key2480, 2), (key2390, 2), (key2480, 2), (key2406, -1), (key2472, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2406, -1)]

def rawRow15014 : Integer.Sparse Key := [(key2910, -1), (key2889, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2600, -1), (key2887, 2), (key2887, 2), (key2598, 2), (key2910, -1), (key2889, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2600, -1), (key2880, 2), (key2772, 2), (key2880, 2), (key2593, 2), (key2772, 2), (key2593, 2), (key2843, -1), (key2766, -1), (key2843, -1), (key2587, -1), (key2766, -1), (key2587, -1), (key2480, 2), (key2480, 2), (key2390, 2), (key2472, -1), (key2406, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2378, -1)]

def rawRow15096 : Integer.Sparse Key := [(key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2440, -1), (key2440, -1), (key2409, 2), (key2440, 2), (key2440, 2), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2506, -1), (key2506, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2522, 2), (key2522, 2), (key2482, -1), (key2482, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2538, 2), (key2554, 2), (key2554, 2), (key2543, -1), (key2543, -1), (key2554, -1), (key2554, -1), (key2563, -1), (key2563, -1)]

def rawRow15097 : Integer.Sparse Key := [(key2437, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2440, 2), (key2409, 2), (key2440, 2), (key2503, -1), (key2506, -1), (key2472, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2503, 2), (key2522, 2), (key2480, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2506, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2482, -1), (key2506, -1), (key2554, 2), (key2538, 2), (key2554, 2), (key2554, -1), (key2563, -1), (key2543, -1), (key2563, -1), (key2543, -1), (key2554, -1)]

def rawRow15098 : Integer.Sparse Key := [(key2440, -1), (key2437, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2440, 2), (key2440, 2), (key2409, 2), (key2506, -1), (key2503, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2522, 2), (key2503, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2482, -1), (key2506, -1), (key2482, -1), (key2554, 2), (key2554, 2), (key2538, 2), (key2563, -1), (key2554, -1), (key2563, -1), (key2543, -1), (key2554, -1), (key2543, -1)]

def rawRow15099 : Integer.Sparse Key := [(key2406, -1), (key2409, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2440, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2480, -1), (key2482, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2472, 2), (key2482, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2506, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1), (key2543, 2), (key2543, 2), (key2563, 2), (key2538, -1), (key2543, -1), (key2538, -1), (key2554, -1), (key2543, -1), (key2554, -1)]

def rawRow15100 : Integer.Sparse Key := [(key2409, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2482, -1), (key2480, -1), (key2522, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2482, 2), (key2472, 2), (key2506, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2543, 2), (key2563, 2), (key2543, 2), (key2543, -1), (key2538, -1), (key2554, -1), (key2538, -1), (key2554, -1), (key2543, -1)]

def rawRow15101 : Integer.Sparse Key := [(key2440, -1), (key2440, -1), (key2409, -1), (key2409, -1), (key2406, -1), (key2406, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2522, -1), (key2522, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2506, 2), (key2506, 2), (key2482, 2), (key2482, 2), (key2472, 2), (key2472, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1), (key2563, 2), (key2543, 2), (key2543, 2), (key2554, -1), (key2554, -1), (key2543, -1), (key2543, -1), (key2538, -1), (key2538, -1)]

def rawRow15102 : Integer.Sparse Key := [(key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2506, -1), (key2506, -1), (key2538, 2), (key2554, 2), (key2554, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2440, -1), (key2440, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2522, 2), (key2522, 2), (key2543, -1), (key2543, -1), (key2554, -1), (key2554, -1), (key2563, -1), (key2563, -1), (key2409, 2), (key2440, 2), (key2440, 2), (key2482, -1), (key2482, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1)]

def rawRow15103 : Integer.Sparse Key := [(key2503, -1), (key2506, -1), (key2472, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2554, 2), (key2538, 2), (key2554, 2), (key2437, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2503, 2), (key2522, 2), (key2480, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2554, -1), (key2563, -1), (key2543, -1), (key2563, -1), (key2543, -1), (key2554, -1), (key2440, 2), (key2409, 2), (key2440, 2), (key2506, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2482, -1), (key2506, -1)]

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

def rawRow15104 : Integer.Sparse Key := [(key2506, -1), (key2503, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2554, 2), (key2554, 2), (key2538, 2), (key2440, -1), (key2437, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2522, 2), (key2503, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2563, -1), (key2554, -1), (key2563, -1), (key2543, -1), (key2554, -1), (key2543, -1), (key2440, 2), (key2440, 2), (key2409, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2482, -1), (key2506, -1), (key2482, -1)]

def rawRow15105 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2472, -1), (key2506, -1), (key2538, -1), (key2554, -1), (key2378, 2), (key2472, 2), (key2503, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2522, -1), (key2543, -1), (key2563, -1), (key2378, 2), (key2392, 2), (key2406, 2), (key2440, 2), (key2543, 2), (key2554, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1), (key2392, 2), (key2482, 2), (key2522, 2), (key2381, -1), (key2392, -1), (key2409, -1), (key2440, -1), (key2482, -1), (key2506, -1)]

def rawRow15106 : Integer.Sparse Key := [(key2381, -1), (key2378, -1), (key2506, -1), (key2472, -1), (key2554, -1), (key2538, -1), (key2378, 2), (key2503, 2), (key2472, 2), (key2392, -1), (key2390, -1), (key2522, -1), (key2480, -1), (key2563, -1), (key2543, -1), (key2392, 2), (key2378, 2), (key2440, 2), (key2406, 2), (key2554, 2), (key2543, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1), (key2392, 2), (key2522, 2), (key2482, 2), (key2392, -1), (key2381, -1), (key2440, -1), (key2409, -1), (key2506, -1), (key2482, -1)]

def rawRow15107 : Integer.Sparse Key := [(key2472, -1), (key2538, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2472, 2), (key2378, 2), (key2503, 2), (key2480, -1), (key2543, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2406, 2), (key2543, 2), (key2378, 2), (key2554, 2), (key2392, 2), (key2440, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2482, 2), (key2392, 2), (key2522, 2), (key2409, -1), (key2482, -1), (key2381, -1), (key2506, -1), (key2392, -1), (key2440, -1)]

def rawRow15108 : Integer.Sparse Key := [(key2538, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2506, -1), (key2381, -1), (key2472, 2), (key2503, 2), (key2378, 2), (key2543, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2522, -1), (key2392, -1), (key2543, 2), (key2406, 2), (key2554, 2), (key2378, 2), (key2440, 2), (key2392, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1), (key2482, 2), (key2522, 2), (key2392, 2), (key2482, -1), (key2409, -1), (key2506, -1), (key2381, -1), (key2440, -1), (key2392, -1)]

def rawRow15109 : Integer.Sparse Key := [(key2506, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2378, -1), (key2472, -1), (key2503, 2), (key2378, 2), (key2472, 2), (key2522, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2390, -1), (key2480, -1), (key2440, 2), (key2554, 2), (key2392, 2), (key2543, 2), (key2378, 2), (key2406, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1), (key2522, 2), (key2392, 2), (key2482, 2), (key2440, -1), (key2506, -1), (key2392, -1), (key2482, -1), (key2381, -1), (key2409, -1)]

def rawRow15110 : Integer.Sparse Key := [(key2554, -1), (key2506, -1), (key2538, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2503, 2), (key2472, 2), (key2378, 2), (key2563, -1), (key2522, -1), (key2543, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2554, 2), (key2440, 2), (key2543, 2), (key2392, 2), (key2406, 2), (key2378, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2522, 2), (key2482, 2), (key2392, 2), (key2506, -1), (key2440, -1), (key2482, -1), (key2392, -1), (key2409, -1), (key2381, -1)]

def rawRow15111 : Integer.Sparse Key := [(key2480, -1), (key2482, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2543, 2), (key2543, 2), (key2563, 2), (key2406, -1), (key2409, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2440, -1), (key2472, 2), (key2482, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2506, 2), (key2538, -1), (key2543, -1), (key2538, -1), (key2554, -1), (key2543, -1), (key2554, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1)]

def rawRow15112 : Integer.Sparse Key := [(key2482, -1), (key2480, -1), (key2522, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2543, 2), (key2563, 2), (key2543, 2), (key2409, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2482, 2), (key2472, 2), (key2506, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2543, -1), (key2538, -1), (key2554, -1), (key2538, -1), (key2554, -1), (key2543, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1)]

def rawRow15113 : Integer.Sparse Key := [(key2522, -1), (key2522, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2563, 2), (key2543, 2), (key2543, 2), (key2440, -1), (key2440, -1), (key2409, -1), (key2409, -1), (key2406, -1), (key2406, -1), (key2506, 2), (key2506, 2), (key2482, 2), (key2482, 2), (key2472, 2), (key2472, 2), (key2554, -1), (key2554, -1), (key2543, -1), (key2543, -1), (key2538, -1), (key2538, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1)]

def rawRow15114 : Integer.Sparse Key := [(key2390, -1), (key2392, -1), (key2480, -1), (key2522, -1), (key2543, -1), (key2563, -1), (key2392, 2), (key2482, 2), (key2522, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2506, -1), (key2538, -1), (key2554, -1), (key2378, 2), (key2392, 2), (key2406, 2), (key2440, 2), (key2543, 2), (key2554, 2), (key2381, -1), (key2392, -1), (key2409, -1), (key2440, -1), (key2482, -1), (key2506, -1), (key2378, 2), (key2472, 2), (key2503, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1)]

def rawRow15115 : Integer.Sparse Key := [(key2392, -1), (key2390, -1), (key2522, -1), (key2480, -1), (key2563, -1), (key2543, -1), (key2392, 2), (key2522, 2), (key2482, 2), (key2381, -1), (key2378, -1), (key2506, -1), (key2472, -1), (key2554, -1), (key2538, -1), (key2392, 2), (key2378, 2), (key2440, 2), (key2406, 2), (key2554, 2), (key2543, 2), (key2392, -1), (key2381, -1), (key2440, -1), (key2409, -1), (key2506, -1), (key2482, -1), (key2378, 2), (key2503, 2), (key2472, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1)]

def rawRow15116 : Integer.Sparse Key := [(key2480, -1), (key2543, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2482, 2), (key2392, 2), (key2522, 2), (key2472, -1), (key2538, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2406, 2), (key2543, 2), (key2378, 2), (key2554, 2), (key2392, 2), (key2440, 2), (key2409, -1), (key2482, -1), (key2381, -1), (key2506, -1), (key2392, -1), (key2440, -1), (key2472, 2), (key2378, 2), (key2503, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1)]

def rawRow15117 : Integer.Sparse Key := [(key2543, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2522, -1), (key2392, -1), (key2482, 2), (key2522, 2), (key2392, 2), (key2538, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2506, -1), (key2381, -1), (key2543, 2), (key2406, 2), (key2554, 2), (key2378, 2), (key2440, 2), (key2392, 2), (key2482, -1), (key2409, -1), (key2506, -1), (key2381, -1), (key2440, -1), (key2392, -1), (key2472, 2), (key2503, 2), (key2378, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1)]

def rawRow15118 : Integer.Sparse Key := [(key2522, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2390, -1), (key2480, -1), (key2522, 2), (key2392, 2), (key2482, 2), (key2506, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2378, -1), (key2472, -1), (key2440, 2), (key2554, 2), (key2392, 2), (key2543, 2), (key2378, 2), (key2406, 2), (key2440, -1), (key2506, -1), (key2392, -1), (key2482, -1), (key2381, -1), (key2409, -1), (key2503, 2), (key2378, 2), (key2472, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1)]

def rawRow15119 : Integer.Sparse Key := [(key2563, -1), (key2522, -1), (key2543, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2522, 2), (key2482, 2), (key2392, 2), (key2554, -1), (key2506, -1), (key2538, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2554, 2), (key2440, 2), (key2543, 2), (key2392, 2), (key2406, 2), (key2378, 2), (key2506, -1), (key2440, -1), (key2482, -1), (key2392, -1), (key2409, -1), (key2381, -1), (key2503, 2), (key2472, 2), (key2378, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1)]

def rawRow15120 : Integer.Sparse Key := [(key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2543, -1), (key2543, -1), (key2390, 2), (key2480, 2), (key2480, 2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2543, -1), (key2543, -1), (key2381, 2), (key2381, 2), (key2409, 2), (key2409, 2), (key2538, 2), (key2538, 2), (key2378, -1), (key2378, -1), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2390, 2), (key2480, 2), (key2480, 2), (key2378, -1), (key2378, -1), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1)]

def rawRow15121 : Integer.Sparse Key := [(key2482, -1), (key2543, -1), (key2392, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2480, 2), (key2390, 2), (key2480, 2), (key2482, -1), (key2543, -1), (key2392, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2409, 2), (key2538, 2), (key2381, 2), (key2538, 2), (key2381, 2), (key2409, 2), (key2406, -1), (key2472, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2480, 2), (key2390, 2), (key2480, 2), (key2406, -1), (key2472, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2406, -1)]

def rawRow15122 : Integer.Sparse Key := [(key2543, -1), (key2482, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2480, 2), (key2480, 2), (key2390, 2), (key2543, -1), (key2482, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2538, 2), (key2409, 2), (key2538, 2), (key2381, 2), (key2409, 2), (key2381, 2), (key2472, -1), (key2406, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2378, -1), (key2480, 2), (key2480, 2), (key2390, 2), (key2472, -1), (key2406, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2378, -1)]

def rawRow15177 : Integer.Sparse Key := [(key2843, 4), (key2843, 4), (key2880, 4), (key2887, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2989, -2), (key2995, 4), (key2995, 4), (key3002, 4)]

def rawRow15178 : Integer.Sparse Key := [(key2843, 4), (key2880, 4), (key2843, 4), (key2889, -2), (key2887, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2995, 4), (key3002, 4), (key2995, 4)]

def rawRow15179 : Integer.Sparse Key := [(key2880, 4), (key2843, 4), (key2843, 4), (key2910, -2), (key2910, -2), (key2889, -2), (key2889, -2), (key2887, -2), (key2887, -2), (key2989, -2), (key2989, -2), (key2968, -2), (key2968, -2), (key2966, -2), (key2966, -2), (key3002, 4), (key2995, 4), (key2995, 4)]

def rawRow15180 : Integer.Sparse Key := [(key2766, 4), (key2887, 4), (key2910, 4), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -2), (key2966, -2), (key2989, -2), (key2995, -2), (key3002, -2), (key2931, 4), (key2968, 4), (key2989, 4)]

def rawRow15181 : Integer.Sparse Key := [(key2766, 4), (key2910, 4), (key2887, 4), (key2772, -2), (key2766, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2889, -2), (key2931, -2), (key2929, -2), (key2989, -2), (key2966, -2), (key3002, -2), (key2995, -2), (key2931, 4), (key2989, 4), (key2968, 4)]

def rawRow15182 : Integer.Sparse Key := [(key2887, 4), (key2766, 4), (key2910, 4), (key2843, -2), (key2889, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2966, -2), (key2995, -2), (key2929, -2), (key3002, -2), (key2931, -2), (key2989, -2), (key2968, 4), (key2931, 4), (key2989, 4)]

def rawRow15183 : Integer.Sparse Key := [(key2887, 4), (key2910, 4), (key2766, 4), (key2889, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2880, -2), (key2772, -2), (key2995, -2), (key2966, -2), (key3002, -2), (key2929, -2), (key2989, -2), (key2931, -2), (key2968, 4), (key2989, 4), (key2931, 4)]

def rawRow15184 : Integer.Sparse Key := [(key2910, 4), (key2766, 4), (key2887, 4), (key2880, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2766, -2), (key2843, -2), (key2989, -2), (key3002, -2), (key2931, -2), (key2995, -2), (key2929, -2), (key2966, -2), (key2989, 4), (key2931, 4), (key2968, 4)]

def rawRow15185 : Integer.Sparse Key := [(key2910, 4), (key2887, 4), (key2766, 4), (key2910, -2), (key2880, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key3002, -2), (key2989, -2), (key2995, -2), (key2931, -2), (key2966, -2), (key2929, -2), (key2989, 4), (key2968, 4), (key2931, 4)]

def rawRow15186 : Integer.Sparse Key := [(key2843, 4), (key2843, 4), (key2880, 4), (key2966, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2989, -2), (key2887, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2910, -2), (key2995, 4), (key2995, 4), (key3002, 4)]

def rawRow15187 : Integer.Sparse Key := [(key2843, 4), (key2880, 4), (key2843, 4), (key2968, -2), (key2966, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2995, 4), (key3002, 4), (key2995, 4)]

def rawRow15188 : Integer.Sparse Key := [(key2880, 4), (key2843, 4), (key2843, 4), (key2989, -2), (key2989, -2), (key2968, -2), (key2968, -2), (key2966, -2), (key2966, -2), (key2910, -2), (key2910, -2), (key2889, -2), (key2889, -2), (key2887, -2), (key2887, -2), (key3002, 4), (key2995, 4), (key2995, 4)]

def rawRow15189 : Integer.Sparse Key := [(key2766, 4), (key2887, 4), (key2910, 4), (key2929, -2), (key2931, -2), (key2966, -2), (key2989, -2), (key2995, -2), (key3002, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, 4), (key2968, 4), (key2989, 4)]

def rawRow15190 : Integer.Sparse Key := [(key2766, 4), (key2910, 4), (key2887, 4), (key2931, -2), (key2929, -2), (key2989, -2), (key2966, -2), (key3002, -2), (key2995, -2), (key2772, -2), (key2766, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2889, -2), (key2931, 4), (key2989, 4), (key2968, 4)]

def rawRow15191 : Integer.Sparse Key := [(key2887, 4), (key2766, 4), (key2910, 4), (key2966, -2), (key2995, -2), (key2929, -2), (key3002, -2), (key2931, -2), (key2989, -2), (key2843, -2), (key2889, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2968, 4), (key2931, 4), (key2989, 4)]

def rawRow15192 : Integer.Sparse Key := [(key2887, 4), (key2910, 4), (key2766, 4), (key2995, -2), (key2966, -2), (key3002, -2), (key2929, -2), (key2989, -2), (key2931, -2), (key2889, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2880, -2), (key2772, -2), (key2968, 4), (key2989, 4), (key2931, 4)]

def rawRow15193 : Integer.Sparse Key := [(key2910, 4), (key2766, 4), (key2887, 4), (key2989, -2), (key3002, -2), (key2931, -2), (key2995, -2), (key2929, -2), (key2966, -2), (key2880, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2766, -2), (key2843, -2), (key2989, 4), (key2931, 4), (key2968, 4)]

def rawRow15194 : Integer.Sparse Key := [(key2910, 4), (key2887, 4), (key2766, 4), (key3002, -2), (key2989, -2), (key2995, -2), (key2931, -2), (key2966, -2), (key2929, -2), (key2910, -2), (key2880, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key2989, 4), (key2968, 4), (key2931, 4)]

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

def rawRow15285 : Integer.Sparse Key := [(key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2752, 2), (key2752, 2), (key2757, 2), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key2918, -1), (key2919, -1), (key2918, -1), (key2922, -1), (key2919, -1), (key2922, -1), (key3011, 2), (key3011, 2), (key3016, 2), (key3021, -1), (key3022, -1), (key3021, -1), (key3025, -1), (key3022, -1), (key3025, -1)]

def rawRow15286 : Integer.Sparse Key := [(key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2752, 2), (key2757, 2), (key2752, 2), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2919, -1), (key2918, -1), (key2922, -1), (key2918, -1), (key2922, -1), (key2919, -1), (key3011, 2), (key3016, 2), (key3011, 2), (key3022, -1), (key3021, -1), (key3025, -1), (key3021, -1), (key3025, -1), (key3022, -1)]

def rawRow15287 : Integer.Sparse Key := [(key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2757, 2), (key2752, 2), (key2752, 2), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key2922, -1), (key2922, -1), (key2919, -1), (key2919, -1), (key2918, -1), (key2918, -1), (key3016, 2), (key3011, 2), (key3011, 2), (key3025, -1), (key3025, -1), (key3022, -1), (key3022, -1), (key3021, -1), (key3021, -1)]

def rawRow15288 : Integer.Sparse Key := [(key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2669, 2), (key2704, 2), (key2724, 2), (key2778, -1), (key2784, -1), (key2851, -1), (key2868, -1), (key2918, -1), (key2922, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2858, -1), (key2868, -1), (key3007, 2), (key3021, 2), (key3025, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, -1)]

def rawRow15289 : Integer.Sparse Key := [(key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2669, 2), (key2724, 2), (key2704, 2), (key2784, -1), (key2778, -1), (key2868, -1), (key2851, -1), (key2922, -1), (key2918, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key2792, -1), (key2784, -1), (key2827, -1), (key2807, -1), (key2868, -1), (key2858, -1), (key3007, 2), (key3025, 2), (key3021, 2), (key3009, -1), (key3007, -1), (key3016, -1), (key3011, -1), (key3025, -1), (key3022, -1)]

def rawRow15290 : Integer.Sparse Key := [(key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2704, 2), (key2669, 2), (key2724, 2), (key2851, -1), (key2918, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key2807, -1), (key2858, -1), (key2784, -1), (key2868, -1), (key2792, -1), (key2827, -1), (key3021, 2), (key3007, 2), (key3025, 2), (key3011, -1), (key3022, -1), (key3007, -1), (key3025, -1), (key3009, -1), (key3016, -1)]

def rawRow15291 : Integer.Sparse Key := [(key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2704, 2), (key2724, 2), (key2669, 2), (key2918, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2868, -1), (key2784, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key2858, -1), (key2807, -1), (key2868, -1), (key2784, -1), (key2827, -1), (key2792, -1), (key3021, 2), (key3025, 2), (key3007, 2), (key3022, -1), (key3011, -1), (key3025, -1), (key3007, -1), (key3016, -1), (key3009, -1)]

def rawRow15292 : Integer.Sparse Key := [(key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2724, 2), (key2669, 2), (key2704, 2), (key2868, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2778, -1), (key2851, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key2827, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2784, -1), (key2807, -1), (key3025, 2), (key3007, 2), (key3021, 2), (key3016, -1), (key3025, -1), (key3009, -1), (key3022, -1), (key3007, -1), (key3011, -1)]

def rawRow15293 : Integer.Sparse Key := [(key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2724, 2), (key2704, 2), (key2669, 2), (key2922, -1), (key2868, -1), (key2918, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key2868, -1), (key2827, -1), (key2858, -1), (key2792, -1), (key2807, -1), (key2784, -1), (key3025, 2), (key3021, 2), (key3007, 2), (key3025, -1), (key3016, -1), (key3022, -1), (key3009, -1), (key3011, -1), (key3007, -1)]

def rawRow15294 : Integer.Sparse Key := [(key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key3011, 2), (key3011, 2), (key3016, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key3021, -1), (key3022, -1), (key3021, -1), (key3025, -1), (key3022, -1), (key3025, -1), (key2752, 2), (key2752, 2), (key2757, 2), (key2918, -1), (key2919, -1), (key2918, -1), (key2922, -1), (key2919, -1), (key2922, -1)]

def rawRow15295 : Integer.Sparse Key := [(key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key3011, 2), (key3016, 2), (key3011, 2), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key3022, -1), (key3021, -1), (key3025, -1), (key3021, -1), (key3025, -1), (key3022, -1), (key2752, 2), (key2757, 2), (key2752, 2), (key2919, -1), (key2918, -1), (key2922, -1), (key2918, -1), (key2922, -1), (key2919, -1)]

def rawRow15296 : Integer.Sparse Key := [(key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key3016, 2), (key3011, 2), (key3011, 2), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key3025, -1), (key3025, -1), (key3022, -1), (key3022, -1), (key3021, -1), (key3021, -1), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, -1), (key2922, -1), (key2919, -1), (key2919, -1), (key2918, -1), (key2918, -1)]

def rawRow15297 : Integer.Sparse Key := [(key2698, -1), (key2704, -1), (key2851, -1), (key3021, -1), (key2858, -1), (key3022, -1), (key2724, 2), (key2868, 2), (key3025, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, -1), (key2669, 2), (key2704, 2), (key2724, 2), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2858, -1), (key2868, -1)]

def rawRow15298 : Integer.Sparse Key := [(key2704, -1), (key2698, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2858, -1), (key2724, 2), (key3025, 2), (key2868, 2), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key3009, -1), (key3007, -1), (key3016, -1), (key3011, -1), (key3025, -1), (key3022, -1), (key2669, 2), (key2724, 2), (key2704, 2), (key2792, -1), (key2784, -1), (key2827, -1), (key2807, -1), (key2868, -1), (key2858, -1)]

def rawRow15299 : Integer.Sparse Key := [(key2851, -1), (key2858, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2868, 2), (key2724, 2), (key3025, 2), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key3011, -1), (key3022, -1), (key3007, -1), (key3025, -1), (key3009, -1), (key3016, -1), (key2704, 2), (key2669, 2), (key2724, 2), (key2807, -1), (key2858, -1), (key2784, -1), (key2868, -1), (key2792, -1), (key2827, -1)]

def rawRow15300 : Integer.Sparse Key := [(key2858, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key3021, -1), (key2704, -1), (key2868, 2), (key3025, 2), (key2724, 2), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key3022, -1), (key3011, -1), (key3025, -1), (key3007, -1), (key3016, -1), (key3009, -1), (key2704, 2), (key2724, 2), (key2669, 2), (key2858, -1), (key2807, -1), (key2868, -1), (key2784, -1), (key2827, -1), (key2792, -1)]

def rawRow15301 : Integer.Sparse Key := [(key3021, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key3025, 2), (key2724, 2), (key2868, 2), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key3016, -1), (key3025, -1), (key3009, -1), (key3022, -1), (key3007, -1), (key3011, -1), (key2724, 2), (key2669, 2), (key2704, 2), (key2827, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2784, -1), (key2807, -1)]

def rawRow15302 : Integer.Sparse Key := [(key3022, -1), (key3021, -1), (key2858, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, 2), (key2868, 2), (key2724, 2), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key3025, -1), (key3016, -1), (key3022, -1), (key3009, -1), (key3011, -1), (key3007, -1), (key2724, 2), (key2704, 2), (key2669, 2), (key2868, -1), (key2827, -1), (key2858, -1), (key2792, -1), (key2807, -1), (key2784, -1)]

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

def rawRow15411 : Integer.Sparse Key := [(key2699, -1), (key2703, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2736, 2), (key2736, 2), (key2746, 2), (key2802, -1), (key2806, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2826, -1), (key2852, 2), (key2857, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2867, 2), (key2894, -1), (key2896, -1), (key2894, -1), (key2903, -1), (key2896, -1), (key2903, -1), (key2949, 2), (key2949, 2), (key2959, 2), (key2973, -1), (key2975, -1), (key2973, -1), (key2982, -1), (key2975, -1), (key2982, -1)]

def rawRow15412 : Integer.Sparse Key := [(key2703, -1), (key2699, -1), (key2723, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2736, 2), (key2746, 2), (key2736, 2), (key2806, -1), (key2802, -1), (key2826, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2857, 2), (key2852, 2), (key2867, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2896, -1), (key2894, -1), (key2903, -1), (key2894, -1), (key2903, -1), (key2896, -1), (key2949, 2), (key2959, 2), (key2949, 2), (key2975, -1), (key2973, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2975, -1)]

def rawRow15413 : Integer.Sparse Key := [(key2723, -1), (key2723, -1), (key2703, -1), (key2703, -1), (key2699, -1), (key2699, -1), (key2746, 2), (key2736, 2), (key2736, 2), (key2826, -1), (key2826, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2867, 2), (key2867, 2), (key2857, 2), (key2857, 2), (key2852, 2), (key2852, 2), (key2903, -1), (key2903, -1), (key2896, -1), (key2896, -1), (key2894, -1), (key2894, -1), (key2959, 2), (key2949, 2), (key2949, 2), (key2982, -1), (key2982, -1), (key2975, -1), (key2975, -1), (key2973, -1), (key2973, -1)]

def rawRow15414 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2699, -1), (key2723, -1), (key2736, -1), (key2746, -1), (key2668, 2), (key2703, 2), (key2723, 2), (key2779, -1), (key2783, -1), (key2852, -1), (key2867, -1), (key2894, -1), (key2903, -1), (key2779, 2), (key2791, 2), (key2802, 2), (key2826, 2), (key2896, 2), (key2903, 2), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2857, -1), (key2867, -1), (key2937, 2), (key2973, 2), (key2982, 2), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2975, -1), (key2982, -1)]

def rawRow15415 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2736, -1), (key2668, 2), (key2723, 2), (key2703, 2), (key2783, -1), (key2779, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2894, -1), (key2791, 2), (key2779, 2), (key2826, 2), (key2802, 2), (key2903, 2), (key2896, 2), (key2791, -1), (key2783, -1), (key2826, -1), (key2806, -1), (key2867, -1), (key2857, -1), (key2937, 2), (key2982, 2), (key2973, 2), (key2942, -1), (key2937, -1), (key2959, -1), (key2949, -1), (key2982, -1), (key2975, -1)]

def rawRow15416 : Integer.Sparse Key := [(key2699, -1), (key2736, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2703, 2), (key2668, 2), (key2723, 2), (key2852, -1), (key2894, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2802, 2), (key2896, 2), (key2779, 2), (key2903, 2), (key2791, 2), (key2826, 2), (key2806, -1), (key2857, -1), (key2783, -1), (key2867, -1), (key2791, -1), (key2826, -1), (key2973, 2), (key2937, 2), (key2982, 2), (key2949, -1), (key2975, -1), (key2937, -1), (key2982, -1), (key2942, -1), (key2959, -1)]

def rawRow15417 : Integer.Sparse Key := [(key2736, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2723, -1), (key2668, -1), (key2703, 2), (key2723, 2), (key2668, 2), (key2894, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2867, -1), (key2783, -1), (key2896, 2), (key2802, 2), (key2903, 2), (key2779, 2), (key2826, 2), (key2791, 2), (key2857, -1), (key2806, -1), (key2867, -1), (key2783, -1), (key2826, -1), (key2791, -1), (key2973, 2), (key2982, 2), (key2937, 2), (key2975, -1), (key2949, -1), (key2982, -1), (key2937, -1), (key2959, -1), (key2942, -1)]

def rawRow15418 : Integer.Sparse Key := [(key2723, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2664, -1), (key2699, -1), (key2723, 2), (key2668, 2), (key2703, 2), (key2867, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2779, -1), (key2852, -1), (key2826, 2), (key2903, 2), (key2791, 2), (key2896, 2), (key2779, 2), (key2802, 2), (key2826, -1), (key2867, -1), (key2791, -1), (key2857, -1), (key2783, -1), (key2806, -1), (key2982, 2), (key2937, 2), (key2973, 2), (key2959, -1), (key2982, -1), (key2942, -1), (key2975, -1), (key2937, -1), (key2949, -1)]

def rawRow15419 : Integer.Sparse Key := [(key2746, -1), (key2723, -1), (key2736, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2723, 2), (key2703, 2), (key2668, 2), (key2903, -1), (key2867, -1), (key2894, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2903, 2), (key2826, 2), (key2896, 2), (key2791, 2), (key2802, 2), (key2779, 2), (key2867, -1), (key2826, -1), (key2857, -1), (key2791, -1), (key2806, -1), (key2783, -1), (key2982, 2), (key2973, 2), (key2937, 2), (key2982, -1), (key2959, -1), (key2975, -1), (key2942, -1), (key2949, -1), (key2937, -1)]

def rawRow15420 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2826, -1), (key2949, 2), (key2949, 2), (key2959, 2), (key2699, -1), (key2703, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2852, 2), (key2857, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2867, 2), (key2973, -1), (key2975, -1), (key2973, -1), (key2982, -1), (key2975, -1), (key2982, -1), (key2736, 2), (key2736, 2), (key2746, 2), (key2894, -1), (key2896, -1), (key2894, -1), (key2903, -1), (key2896, -1), (key2903, -1)]

def rawRow15421 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2826, -1), (key2802, -1), (key2826, -1), (key2806, -1), (key2949, 2), (key2959, 2), (key2949, 2), (key2703, -1), (key2699, -1), (key2723, -1), (key2699, -1), (key2723, -1), (key2703, -1), (key2857, 2), (key2852, 2), (key2867, 2), (key2852, 2), (key2867, 2), (key2857, 2), (key2975, -1), (key2973, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2975, -1), (key2736, 2), (key2746, 2), (key2736, 2), (key2896, -1), (key2894, -1), (key2903, -1), (key2894, -1), (key2903, -1), (key2896, -1)]

def rawRow15422 : Integer.Sparse Key := [(key2826, -1), (key2826, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2959, 2), (key2949, 2), (key2949, 2), (key2723, -1), (key2723, -1), (key2703, -1), (key2703, -1), (key2699, -1), (key2699, -1), (key2867, 2), (key2867, 2), (key2857, 2), (key2857, 2), (key2852, 2), (key2852, 2), (key2982, -1), (key2982, -1), (key2975, -1), (key2975, -1), (key2973, -1), (key2973, -1), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, -1), (key2903, -1), (key2896, -1), (key2896, -1), (key2894, -1), (key2894, -1)]

def rawRow15423 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2802, -1), (key2826, -1), (key2949, -1), (key2959, -1), (key2613, 2), (key2806, 2), (key2826, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2867, -1), (key2973, -1), (key2982, -1), (key2625, 2), (key2637, 2), (key2699, 2), (key2723, 2), (key2975, 2), (key2982, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2723, -1), (key2857, -1), (key2867, -1), (key2647, 2), (key2894, 2), (key2903, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2746, -1), (key2896, -1), (key2903, -1)]

def rawRow15424 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2949, -1), (key2613, 2), (key2826, 2), (key2806, 2), (key2629, -1), (key2625, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2973, -1), (key2637, 2), (key2625, 2), (key2723, 2), (key2699, 2), (key2982, 2), (key2975, 2), (key2637, -1), (key2629, -1), (key2723, -1), (key2703, -1), (key2867, -1), (key2857, -1), (key2647, 2), (key2903, 2), (key2894, 2), (key2652, -1), (key2647, -1), (key2746, -1), (key2736, -1), (key2903, -1), (key2896, -1)]

def rawRow15425 : Integer.Sparse Key := [(key2802, -1), (key2949, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2806, 2), (key2613, 2), (key2826, 2), (key2852, -1), (key2973, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2699, 2), (key2975, 2), (key2625, 2), (key2982, 2), (key2637, 2), (key2723, 2), (key2703, -1), (key2857, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2894, 2), (key2647, 2), (key2903, 2), (key2736, -1), (key2896, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2746, -1)]

def rawRow15426 : Integer.Sparse Key := [(key2949, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2826, -1), (key2613, -1), (key2806, 2), (key2826, 2), (key2613, 2), (key2973, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2867, -1), (key2629, -1), (key2975, 2), (key2699, 2), (key2982, 2), (key2625, 2), (key2723, 2), (key2637, 2), (key2857, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2723, -1), (key2637, -1), (key2894, 2), (key2903, 2), (key2647, 2), (key2896, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2746, -1), (key2652, -1)]

def rawRow15427 : Integer.Sparse Key := [(key2826, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2609, -1), (key2802, -1), (key2826, 2), (key2613, 2), (key2806, 2), (key2867, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2625, -1), (key2852, -1), (key2723, 2), (key2982, 2), (key2637, 2), (key2975, 2), (key2625, 2), (key2699, 2), (key2723, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2629, -1), (key2703, -1), (key2903, 2), (key2647, 2), (key2894, 2), (key2746, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2647, -1), (key2736, -1)]

def rawRow15428 : Integer.Sparse Key := [(key2959, -1), (key2826, -1), (key2949, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2826, 2), (key2806, 2), (key2613, 2), (key2982, -1), (key2867, -1), (key2973, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2982, 2), (key2723, 2), (key2975, 2), (key2637, 2), (key2699, 2), (key2625, 2), (key2867, -1), (key2723, -1), (key2857, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2903, 2), (key2894, 2), (key2647, 2), (key2903, -1), (key2746, -1), (key2896, -1), (key2652, -1), (key2736, -1), (key2647, -1)]

def rawRow15429 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2852, -1), (key2867, -1), (key2894, -1), (key2903, -1), (key2937, 2), (key2973, 2), (key2982, 2), (key2664, -1), (key2668, -1), (key2699, -1), (key2723, -1), (key2736, -1), (key2746, -1), (key2779, 2), (key2791, 2), (key2802, 2), (key2826, 2), (key2896, 2), (key2903, 2), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2975, -1), (key2982, -1), (key2668, 2), (key2703, 2), (key2723, 2), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2857, -1), (key2867, -1)]

def rawRow15430 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2894, -1), (key2937, 2), (key2982, 2), (key2973, 2), (key2668, -1), (key2664, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2736, -1), (key2791, 2), (key2779, 2), (key2826, 2), (key2802, 2), (key2903, 2), (key2896, 2), (key2942, -1), (key2937, -1), (key2959, -1), (key2949, -1), (key2982, -1), (key2975, -1), (key2668, 2), (key2723, 2), (key2703, 2), (key2791, -1), (key2783, -1), (key2826, -1), (key2806, -1), (key2867, -1), (key2857, -1)]

def rawRow15431 : Integer.Sparse Key := [(key2852, -1), (key2894, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2973, 2), (key2937, 2), (key2982, 2), (key2699, -1), (key2736, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2802, 2), (key2896, 2), (key2779, 2), (key2903, 2), (key2791, 2), (key2826, 2), (key2949, -1), (key2975, -1), (key2937, -1), (key2982, -1), (key2942, -1), (key2959, -1), (key2703, 2), (key2668, 2), (key2723, 2), (key2806, -1), (key2857, -1), (key2783, -1), (key2867, -1), (key2791, -1), (key2826, -1)]

def rawRow15432 : Integer.Sparse Key := [(key2894, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2867, -1), (key2783, -1), (key2973, 2), (key2982, 2), (key2937, 2), (key2736, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2723, -1), (key2668, -1), (key2896, 2), (key2802, 2), (key2903, 2), (key2779, 2), (key2826, 2), (key2791, 2), (key2975, -1), (key2949, -1), (key2982, -1), (key2937, -1), (key2959, -1), (key2942, -1), (key2703, 2), (key2723, 2), (key2668, 2), (key2857, -1), (key2806, -1), (key2867, -1), (key2783, -1), (key2826, -1), (key2791, -1)]

def rawRow15433 : Integer.Sparse Key := [(key2867, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2779, -1), (key2852, -1), (key2982, 2), (key2937, 2), (key2973, 2), (key2723, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2664, -1), (key2699, -1), (key2826, 2), (key2903, 2), (key2791, 2), (key2896, 2), (key2779, 2), (key2802, 2), (key2959, -1), (key2982, -1), (key2942, -1), (key2975, -1), (key2937, -1), (key2949, -1), (key2723, 2), (key2668, 2), (key2703, 2), (key2826, -1), (key2867, -1), (key2791, -1), (key2857, -1), (key2783, -1), (key2806, -1)]

def rawRow15434 : Integer.Sparse Key := [(key2903, -1), (key2867, -1), (key2894, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, 2), (key2973, 2), (key2937, 2), (key2746, -1), (key2723, -1), (key2736, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2903, 2), (key2826, 2), (key2896, 2), (key2791, 2), (key2802, 2), (key2779, 2), (key2982, -1), (key2959, -1), (key2975, -1), (key2942, -1), (key2949, -1), (key2937, -1), (key2723, 2), (key2703, 2), (key2668, 2), (key2867, -1), (key2826, -1), (key2857, -1), (key2791, -1), (key2806, -1), (key2783, -1)]

def rawRow15435 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2852, -1), (key2867, -1), (key2973, -1), (key2982, -1), (key2647, 2), (key2894, 2), (key2903, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2826, -1), (key2949, -1), (key2959, -1), (key2625, 2), (key2637, 2), (key2699, 2), (key2723, 2), (key2975, 2), (key2982, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2746, -1), (key2896, -1), (key2903, -1), (key2613, 2), (key2806, 2), (key2826, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2723, -1), (key2857, -1), (key2867, -1)]

def rawRow15436 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2973, -1), (key2647, 2), (key2903, 2), (key2894, 2), (key2613, -1), (key2609, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2949, -1), (key2637, 2), (key2625, 2), (key2723, 2), (key2699, 2), (key2982, 2), (key2975, 2), (key2652, -1), (key2647, -1), (key2746, -1), (key2736, -1), (key2903, -1), (key2896, -1), (key2613, 2), (key2826, 2), (key2806, 2), (key2637, -1), (key2629, -1), (key2723, -1), (key2703, -1), (key2867, -1), (key2857, -1)]

def rawRow15437 : Integer.Sparse Key := [(key2852, -1), (key2973, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2894, 2), (key2647, 2), (key2903, 2), (key2802, -1), (key2949, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2699, 2), (key2975, 2), (key2625, 2), (key2982, 2), (key2637, 2), (key2723, 2), (key2736, -1), (key2896, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2806, 2), (key2613, 2), (key2826, 2), (key2703, -1), (key2857, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2723, -1)]

def rawRow15438 : Integer.Sparse Key := [(key2973, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2867, -1), (key2629, -1), (key2894, 2), (key2903, 2), (key2647, 2), (key2949, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2826, -1), (key2613, -1), (key2975, 2), (key2699, 2), (key2982, 2), (key2625, 2), (key2723, 2), (key2637, 2), (key2896, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2746, -1), (key2652, -1), (key2806, 2), (key2826, 2), (key2613, 2), (key2857, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2723, -1), (key2637, -1)]

def rawRow15439 : Integer.Sparse Key := [(key2867, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2625, -1), (key2852, -1), (key2903, 2), (key2647, 2), (key2894, 2), (key2826, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2609, -1), (key2802, -1), (key2723, 2), (key2982, 2), (key2637, 2), (key2975, 2), (key2625, 2), (key2699, 2), (key2746, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2647, -1), (key2736, -1), (key2826, 2), (key2613, 2), (key2806, 2), (key2723, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2629, -1), (key2703, -1)]

def rawRow15440 : Integer.Sparse Key := [(key2982, -1), (key2867, -1), (key2973, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2903, 2), (key2894, 2), (key2647, 2), (key2959, -1), (key2826, -1), (key2949, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2982, 2), (key2723, 2), (key2975, 2), (key2637, 2), (key2699, 2), (key2625, 2), (key2903, -1), (key2746, -1), (key2896, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2826, 2), (key2806, 2), (key2613, 2), (key2867, -1), (key2723, -1), (key2857, -1), (key2637, -1), (key2703, -1), (key2629, -1)]

def rawRow15441 : Integer.Sparse Key := [(key2625, -1), (key2647, -1), (key2779, -1), (key2903, -1), (key2937, -1), (key2982, -1), (key2629, 2), (key2783, 2), (key2867, 2), (key2625, -1), (key2647, -1), (key2779, -1), (key2903, -1), (key2937, -1), (key2982, -1), (key2609, 2), (key2652, 2), (key2664, 2), (key2746, 2), (key2942, 2), (key2959, 2), (key2613, -1), (key2637, -1), (key2668, -1), (key2723, -1), (key2791, -1), (key2826, -1), (key2629, 2), (key2783, 2), (key2867, 2), (key2613, -1), (key2637, -1), (key2668, -1), (key2723, -1), (key2791, -1), (key2826, -1)]

def rawRow15442 : Integer.Sparse Key := [(key2647, -1), (key2625, -1), (key2903, -1), (key2779, -1), (key2982, -1), (key2937, -1), (key2629, 2), (key2867, 2), (key2783, 2), (key2647, -1), (key2625, -1), (key2903, -1), (key2779, -1), (key2982, -1), (key2937, -1), (key2652, 2), (key2609, 2), (key2746, 2), (key2664, 2), (key2959, 2), (key2942, 2), (key2637, -1), (key2613, -1), (key2723, -1), (key2668, -1), (key2826, -1), (key2791, -1), (key2629, 2), (key2867, 2), (key2783, 2), (key2637, -1), (key2613, -1), (key2723, -1), (key2668, -1), (key2826, -1), (key2791, -1)]

def rawRow15443 : Integer.Sparse Key := [(key2779, -1), (key2937, -1), (key2625, -1), (key2982, -1), (key2647, -1), (key2903, -1), (key2783, 2), (key2629, 2), (key2867, 2), (key2779, -1), (key2937, -1), (key2625, -1), (key2982, -1), (key2647, -1), (key2903, -1), (key2664, 2), (key2942, 2), (key2609, 2), (key2959, 2), (key2652, 2), (key2746, 2), (key2668, -1), (key2791, -1), (key2613, -1), (key2826, -1), (key2637, -1), (key2723, -1), (key2783, 2), (key2629, 2), (key2867, 2), (key2668, -1), (key2791, -1), (key2613, -1), (key2826, -1), (key2637, -1), (key2723, -1)]

def rawRow15444 : Integer.Sparse Key := [(key2937, -1), (key2779, -1), (key2982, -1), (key2625, -1), (key2903, -1), (key2647, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2937, -1), (key2779, -1), (key2982, -1), (key2625, -1), (key2903, -1), (key2647, -1), (key2942, 2), (key2664, 2), (key2959, 2), (key2609, 2), (key2746, 2), (key2652, 2), (key2791, -1), (key2668, -1), (key2826, -1), (key2613, -1), (key2723, -1), (key2637, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2791, -1), (key2668, -1), (key2826, -1), (key2613, -1), (key2723, -1), (key2637, -1)]

def rawRow15445 : Integer.Sparse Key := [(key2903, -1), (key2982, -1), (key2647, -1), (key2937, -1), (key2625, -1), (key2779, -1), (key2867, 2), (key2629, 2), (key2783, 2), (key2903, -1), (key2982, -1), (key2647, -1), (key2937, -1), (key2625, -1), (key2779, -1), (key2746, 2), (key2959, 2), (key2652, 2), (key2942, 2), (key2609, 2), (key2664, 2), (key2723, -1), (key2826, -1), (key2637, -1), (key2791, -1), (key2613, -1), (key2668, -1), (key2867, 2), (key2629, 2), (key2783, 2), (key2723, -1), (key2826, -1), (key2637, -1), (key2791, -1), (key2613, -1), (key2668, -1)]

def rawRow15446 : Integer.Sparse Key := [(key2982, -1), (key2903, -1), (key2937, -1), (key2647, -1), (key2779, -1), (key2625, -1), (key2867, 2), (key2783, 2), (key2629, 2), (key2982, -1), (key2903, -1), (key2937, -1), (key2647, -1), (key2779, -1), (key2625, -1), (key2959, 2), (key2746, 2), (key2942, 2), (key2652, 2), (key2664, 2), (key2609, 2), (key2826, -1), (key2723, -1), (key2791, -1), (key2637, -1), (key2668, -1), (key2613, -1), (key2867, 2), (key2783, 2), (key2629, 2), (key2826, -1), (key2723, -1), (key2791, -1), (key2637, -1), (key2668, -1), (key2613, -1)]

def rawRow15483 : Integer.Sparse Key := [(key2378, 2), (key2378, 2), (key2383, 2), (key2390, -2), (key2394, -2), (key2394, -2), (key2766, 2), (key2766, 2), (key2772, 2), (key2887, -1), (key2889, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2910, -1), (key2929, -2), (key2931, -2), (key2931, -2), (key2966, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2989, -1), (key2995, 4), (key2995, 4), (key3002, 4)]

def rawRow15484 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2378, 2), (key2394, -2), (key2390, -2), (key2394, -2), (key2766, 2), (key2772, 2), (key2766, 2), (key2889, -1), (key2887, -1), (key2910, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2931, -2), (key2929, -2), (key2931, -2), (key2968, -1), (key2966, -1), (key2989, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2995, 4), (key3002, 4), (key2995, 4)]

def rawRow15485 : Integer.Sparse Key := [(key2383, 2), (key2378, 2), (key2378, 2), (key2394, -2), (key2394, -2), (key2390, -2), (key2772, 2), (key2766, 2), (key2766, 2), (key2910, -1), (key2910, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key2931, -2), (key2931, -2), (key2929, -2), (key2989, -1), (key2989, -1), (key2968, -1), (key2968, -1), (key2966, -1), (key2966, -1), (key3002, 4), (key2995, 4), (key2995, 4)]

def rawRow15486 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2378, -2), (key2383, -2), (key2394, -2), (key2843, 2), (key2887, 2), (key2889, 2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2966, -2), (key2968, -2), (key2995, -2), (key2929, -1), (key2931, -1), (key2966, -1), (key2989, -1), (key2995, -1), (key3002, -1), (key2931, 4), (key2968, 4), (key2989, 4)]

def rawRow15487 : Integer.Sparse Key := [(key2378, 2), (key2394, 2), (key2390, 2), (key2383, -2), (key2378, -2), (key2394, -2), (key2843, 2), (key2889, 2), (key2887, 2), (key2772, -1), (key2766, -1), (key2880, -1), (key2843, -1), (key2910, -1), (key2889, -1), (key2968, -2), (key2966, -2), (key2995, -2), (key2931, -1), (key2929, -1), (key2989, -1), (key2966, -1), (key3002, -1), (key2995, -1), (key2931, 4), (key2989, 4), (key2968, 4)]

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

def rawRow15488 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2394, 2), (key2378, -2), (key2394, -2), (key2383, -2), (key2887, 2), (key2843, 2), (key2889, 2), (key2843, -1), (key2889, -1), (key2766, -1), (key2910, -1), (key2772, -1), (key2880, -1), (key2966, -2), (key2995, -2), (key2968, -2), (key2966, -1), (key2995, -1), (key2929, -1), (key3002, -1), (key2931, -1), (key2989, -1), (key2968, 4), (key2931, 4), (key2989, 4)]

def rawRow15489 : Integer.Sparse Key := [(key2390, 2), (key2394, 2), (key2378, 2), (key2394, -2), (key2378, -2), (key2383, -2), (key2887, 2), (key2889, 2), (key2843, 2), (key2889, -1), (key2843, -1), (key2910, -1), (key2766, -1), (key2880, -1), (key2772, -1), (key2995, -2), (key2966, -2), (key2968, -2), (key2995, -1), (key2966, -1), (key3002, -1), (key2929, -1), (key2989, -1), (key2931, -1), (key2968, 4), (key2989, 4), (key2931, 4)]

def rawRow15490 : Integer.Sparse Key := [(key2394, 2), (key2378, 2), (key2390, 2), (key2383, -2), (key2394, -2), (key2378, -2), (key2889, 2), (key2843, 2), (key2887, 2), (key2880, -1), (key2910, -1), (key2772, -1), (key2889, -1), (key2766, -1), (key2843, -1), (key2968, -2), (key2995, -2), (key2966, -2), (key2989, -1), (key3002, -1), (key2931, -1), (key2995, -1), (key2929, -1), (key2966, -1), (key2989, 4), (key2931, 4), (key2968, 4)]

def rawRow15491 : Integer.Sparse Key := [(key2394, 2), (key2390, 2), (key2378, 2), (key2394, -2), (key2383, -2), (key2378, -2), (key2889, 2), (key2887, 2), (key2843, 2), (key2910, -1), (key2880, -1), (key2889, -1), (key2772, -1), (key2843, -1), (key2766, -1), (key2995, -2), (key2968, -2), (key2966, -2), (key3002, -1), (key2989, -1), (key2995, -1), (key2931, -1), (key2966, -1), (key2929, -1), (key2989, 4), (key2968, 4), (key2931, 4)]

def rawRow15492 : Integer.Sparse Key := [(key2406, 2), (key2406, 2), (key2411, 2), (key2437, -2), (key2443, -2), (key2443, -2), (key2587, 2), (key2587, 2), (key2593, 2), (key2966, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2989, -1), (key2598, -2), (key2600, -2), (key2600, -2), (key2887, -1), (key2889, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2910, -1), (key2995, 4), (key2995, 4), (key3002, 4)]

def rawRow15493 : Integer.Sparse Key := [(key2406, 2), (key2411, 2), (key2406, 2), (key2443, -2), (key2437, -2), (key2443, -2), (key2587, 2), (key2593, 2), (key2587, 2), (key2968, -1), (key2966, -1), (key2989, -1), (key2966, -1), (key2989, -1), (key2968, -1), (key2600, -2), (key2598, -2), (key2600, -2), (key2889, -1), (key2887, -1), (key2910, -1), (key2887, -1), (key2910, -1), (key2889, -1), (key2995, 4), (key3002, 4), (key2995, 4)]

def rawRow15494 : Integer.Sparse Key := [(key2411, 2), (key2406, 2), (key2406, 2), (key2443, -2), (key2443, -2), (key2437, -2), (key2593, 2), (key2587, 2), (key2587, 2), (key2989, -1), (key2989, -1), (key2968, -1), (key2968, -1), (key2966, -1), (key2966, -1), (key2600, -2), (key2600, -2), (key2598, -2), (key2910, -1), (key2910, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key3002, 4), (key2995, 4), (key2995, 4)]

def rawRow15495 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2406, -2), (key2411, -2), (key2443, -2), (key2843, 2), (key2966, 2), (key2968, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2880, -1), (key2968, -1), (key2989, -1), (key2887, -2), (key2889, -2), (key2995, -2), (key2598, -1), (key2600, -1), (key2887, -1), (key2910, -1), (key2995, -1), (key3002, -1), (key2600, 4), (key2889, 4), (key2910, 4)]

def rawRow15496 : Integer.Sparse Key := [(key2406, 2), (key2443, 2), (key2437, 2), (key2411, -2), (key2406, -2), (key2443, -2), (key2843, 2), (key2968, 2), (key2966, 2), (key2593, -1), (key2587, -1), (key2880, -1), (key2843, -1), (key2989, -1), (key2968, -1), (key2889, -2), (key2887, -2), (key2995, -2), (key2600, -1), (key2598, -1), (key2910, -1), (key2887, -1), (key3002, -1), (key2995, -1), (key2600, 4), (key2910, 4), (key2889, 4)]

def rawRow15497 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2443, 2), (key2406, -2), (key2443, -2), (key2411, -2), (key2966, 2), (key2843, 2), (key2968, 2), (key2843, -1), (key2968, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2887, -2), (key2995, -2), (key2889, -2), (key2887, -1), (key2995, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2889, 4), (key2600, 4), (key2910, 4)]

def rawRow15498 : Integer.Sparse Key := [(key2437, 2), (key2443, 2), (key2406, 2), (key2443, -2), (key2406, -2), (key2411, -2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2880, -1), (key2593, -1), (key2995, -2), (key2887, -2), (key2889, -2), (key2995, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2910, -1), (key2600, -1), (key2889, 4), (key2910, 4), (key2600, 4)]

def rawRow15499 : Integer.Sparse Key := [(key2443, 2), (key2406, 2), (key2437, 2), (key2411, -2), (key2443, -2), (key2406, -2), (key2968, 2), (key2843, 2), (key2966, 2), (key2880, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2587, -1), (key2843, -1), (key2889, -2), (key2995, -2), (key2887, -2), (key2910, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2598, -1), (key2887, -1), (key2910, 4), (key2600, 4), (key2889, 4)]

def rawRow15500 : Integer.Sparse Key := [(key2443, 2), (key2437, 2), (key2406, 2), (key2443, -2), (key2411, -2), (key2406, -2), (key2968, 2), (key2966, 2), (key2843, 2), (key2989, -1), (key2880, -1), (key2968, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2995, -2), (key2889, -2), (key2887, -2), (key3002, -1), (key2910, -1), (key2995, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2910, 4), (key2889, 4), (key2600, 4)]

def rawRow15501 : Integer.Sparse Key := [(key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2378, 2), (key2390, 2), (key2394, 2), (key2929, -1), (key2931, -1), (key2966, -1), (key2989, -1), (key2995, -1), (key3002, -1), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2931, 4), (key2968, 4), (key2989, 4)]

def rawRow15502 : Integer.Sparse Key := [(key2472, 2), (key2484, 2), (key2480, 2), (key2509, -2), (key2503, -2), (key2524, -2), (key2378, 2), (key2394, 2), (key2390, 2), (key2931, -1), (key2929, -1), (key2989, -1), (key2966, -1), (key3002, -1), (key2995, -1), (key2593, -2), (key2587, -2), (key2600, -2), (key2772, -1), (key2766, -1), (key2880, -1), (key2843, -1), (key2910, -1), (key2889, -1), (key2931, 4), (key2989, 4), (key2968, 4)]

def rawRow15503 : Integer.Sparse Key := [(key2480, 2), (key2472, 2), (key2484, 2), (key2503, -2), (key2524, -2), (key2509, -2), (key2390, 2), (key2378, 2), (key2394, 2), (key2966, -1), (key2995, -1), (key2929, -1), (key3002, -1), (key2931, -1), (key2989, -1), (key2587, -2), (key2600, -2), (key2593, -2), (key2843, -1), (key2889, -1), (key2766, -1), (key2910, -1), (key2772, -1), (key2880, -1), (key2968, 4), (key2931, 4), (key2989, 4)]

def rawRow15504 : Integer.Sparse Key := [(key2480, 2), (key2484, 2), (key2472, 2), (key2524, -2), (key2503, -2), (key2509, -2), (key2390, 2), (key2394, 2), (key2378, 2), (key2995, -1), (key2966, -1), (key3002, -1), (key2929, -1), (key2989, -1), (key2931, -1), (key2600, -2), (key2587, -2), (key2593, -2), (key2889, -1), (key2843, -1), (key2910, -1), (key2766, -1), (key2880, -1), (key2772, -1), (key2968, 4), (key2989, 4), (key2931, 4)]

def rawRow15505 : Integer.Sparse Key := [(key2484, 2), (key2472, 2), (key2480, 2), (key2509, -2), (key2524, -2), (key2503, -2), (key2394, 2), (key2378, 2), (key2390, 2), (key2989, -1), (key3002, -1), (key2931, -1), (key2995, -1), (key2929, -1), (key2966, -1), (key2593, -2), (key2600, -2), (key2587, -2), (key2880, -1), (key2910, -1), (key2772, -1), (key2889, -1), (key2766, -1), (key2843, -1), (key2989, 4), (key2931, 4), (key2968, 4)]

def rawRow15506 : Integer.Sparse Key := [(key2484, 2), (key2480, 2), (key2472, 2), (key2524, -2), (key2509, -2), (key2503, -2), (key2394, 2), (key2390, 2), (key2378, 2), (key3002, -1), (key2989, -1), (key2995, -1), (key2931, -1), (key2966, -1), (key2929, -1), (key2600, -2), (key2593, -2), (key2587, -2), (key2910, -1), (key2880, -1), (key2889, -1), (key2772, -1), (key2843, -1), (key2766, -1), (key2989, 4), (key2968, 4), (key2931, 4)]

def rawRow15507 : Integer.Sparse Key := [(key2472, 2), (key2503, 2), (key2509, 2), (key2480, -2), (key2484, -2), (key2524, -2), (key2406, 2), (key2437, 2), (key2443, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2910, -1), (key2995, -1), (key3002, -1), (key2766, -2), (key2772, -2), (key2931, -2), (key2587, -1), (key2593, -1), (key2843, -1), (key2880, -1), (key2968, -1), (key2989, -1), (key2600, 4), (key2889, 4), (key2910, 4)]

def rawRow15508 : Integer.Sparse Key := [(key2472, 2), (key2509, 2), (key2503, 2), (key2484, -2), (key2480, -2), (key2524, -2), (key2406, 2), (key2443, 2), (key2437, 2), (key2600, -1), (key2598, -1), (key2910, -1), (key2887, -1), (key3002, -1), (key2995, -1), (key2772, -2), (key2766, -2), (key2931, -2), (key2593, -1), (key2587, -1), (key2880, -1), (key2843, -1), (key2989, -1), (key2968, -1), (key2600, 4), (key2910, 4), (key2889, 4)]

def rawRow15509 : Integer.Sparse Key := [(key2503, 2), (key2472, 2), (key2509, 2), (key2480, -2), (key2524, -2), (key2484, -2), (key2437, 2), (key2406, 2), (key2443, 2), (key2887, -1), (key2995, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2766, -2), (key2931, -2), (key2772, -2), (key2843, -1), (key2968, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2889, 4), (key2600, 4), (key2910, 4)]

def rawRow15510 : Integer.Sparse Key := [(key2503, 2), (key2509, 2), (key2472, 2), (key2524, -2), (key2480, -2), (key2484, -2), (key2437, 2), (key2443, 2), (key2406, 2), (key2995, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2910, -1), (key2600, -1), (key2931, -2), (key2766, -2), (key2772, -2), (key2968, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2880, -1), (key2593, -1), (key2889, 4), (key2910, 4), (key2600, 4)]

def rawRow15511 : Integer.Sparse Key := [(key2509, 2), (key2472, 2), (key2503, 2), (key2484, -2), (key2524, -2), (key2480, -2), (key2443, 2), (key2406, 2), (key2437, 2), (key2910, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2598, -1), (key2887, -1), (key2772, -2), (key2931, -2), (key2766, -2), (key2880, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2587, -1), (key2843, -1), (key2910, 4), (key2600, 4), (key2889, 4)]

def rawRow15512 : Integer.Sparse Key := [(key2509, 2), (key2503, 2), (key2472, 2), (key2524, -2), (key2484, -2), (key2480, -2), (key2443, 2), (key2437, 2), (key2406, 2), (key3002, -1), (key2910, -1), (key2995, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2931, -2), (key2772, -2), (key2766, -2), (key2989, -1), (key2880, -1), (key2968, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2910, 4), (key2889, 4), (key2600, 4)]

def rawRow15513 : Integer.Sparse Key := [(key2480, 2), (key2503, 2), (key2524, 2), (key2472, -2), (key2484, -2), (key2509, -2), (key2480, 2), (key2503, 2), (key2524, 2), (key2587, -1), (key2600, -1), (key2766, -1), (key2910, -1), (key2931, -1), (key2989, -1), (key2843, -2), (key2889, -2), (key2968, -2), (key2587, -1), (key2600, -1), (key2766, -1), (key2910, -1), (key2931, -1), (key2989, -1), (key2593, 4), (key2772, 4), (key2880, 4)]

def rawRow15514 : Integer.Sparse Key := [(key2480, 2), (key2524, 2), (key2503, 2), (key2484, -2), (key2472, -2), (key2509, -2), (key2480, 2), (key2524, 2), (key2503, 2), (key2600, -1), (key2587, -1), (key2910, -1), (key2766, -1), (key2989, -1), (key2931, -1), (key2889, -2), (key2843, -2), (key2968, -2), (key2600, -1), (key2587, -1), (key2910, -1), (key2766, -1), (key2989, -1), (key2931, -1), (key2593, 4), (key2880, 4), (key2772, 4)]

def rawRow15515 : Integer.Sparse Key := [(key2503, 2), (key2480, 2), (key2524, 2), (key2472, -2), (key2509, -2), (key2484, -2), (key2503, 2), (key2480, 2), (key2524, 2), (key2766, -1), (key2931, -1), (key2587, -1), (key2989, -1), (key2600, -1), (key2910, -1), (key2843, -2), (key2968, -2), (key2889, -2), (key2766, -1), (key2931, -1), (key2587, -1), (key2989, -1), (key2600, -1), (key2910, -1), (key2772, 4), (key2593, 4), (key2880, 4)]

def rawRow15516 : Integer.Sparse Key := [(key2503, 2), (key2524, 2), (key2480, 2), (key2509, -2), (key2472, -2), (key2484, -2), (key2503, 2), (key2524, 2), (key2480, 2), (key2931, -1), (key2766, -1), (key2989, -1), (key2587, -1), (key2910, -1), (key2600, -1), (key2968, -2), (key2843, -2), (key2889, -2), (key2931, -1), (key2766, -1), (key2989, -1), (key2587, -1), (key2910, -1), (key2600, -1), (key2772, 4), (key2880, 4), (key2593, 4)]

def rawRow15517 : Integer.Sparse Key := [(key2524, 2), (key2480, 2), (key2503, 2), (key2484, -2), (key2509, -2), (key2472, -2), (key2524, 2), (key2480, 2), (key2503, 2), (key2910, -1), (key2989, -1), (key2600, -1), (key2931, -1), (key2587, -1), (key2766, -1), (key2889, -2), (key2968, -2), (key2843, -2), (key2910, -1), (key2989, -1), (key2600, -1), (key2931, -1), (key2587, -1), (key2766, -1), (key2880, 4), (key2593, 4), (key2772, 4)]

def rawRow15518 : Integer.Sparse Key := [(key2524, 2), (key2503, 2), (key2480, 2), (key2509, -2), (key2484, -2), (key2472, -2), (key2524, 2), (key2503, 2), (key2480, 2), (key2989, -1), (key2910, -1), (key2931, -1), (key2600, -1), (key2766, -1), (key2587, -1), (key2968, -2), (key2889, -2), (key2843, -2), (key2989, -1), (key2910, -1), (key2931, -1), (key2600, -1), (key2766, -1), (key2587, -1), (key2880, 4), (key2772, 4), (key2593, 4)]

def rawRow15519 : Integer.Sparse Key := [(key2608, 2), (key2614, 2), (key2614, 2), (key2624, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2663, 2), (key2669, 2), (key2669, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2778, -1), (key2784, -1), (key2778, -1), (key2792, -1), (key2784, -1), (key2792, -1), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2)]

def rawRow15520 : Integer.Sparse Key := [(key2614, 2), (key2608, 2), (key2614, 2), (key2630, -1), (key2624, -1), (key2638, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2669, 2), (key2663, 2), (key2669, 2), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2784, -1), (key2778, -1), (key2792, -1), (key2778, -1), (key2792, -1), (key2784, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2)]

def rawRow15521 : Integer.Sparse Key := [(key2614, 2), (key2614, 2), (key2608, 2), (key2638, -1), (key2638, -1), (key2630, -1), (key2630, -1), (key2624, -1), (key2624, -1), (key2669, 2), (key2669, 2), (key2663, 2), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2792, -1), (key2792, -1), (key2784, -1), (key2784, -1), (key2778, -1), (key2778, -1), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2)]

def rawRow15522 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, 2), (key2752, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, -1), (key2851, -1), (key2858, -1), (key2918, -1), (key2919, -1), (key2778, -1), (key2784, -1), (key2851, -1), (key2868, -1), (key2918, -1), (key2922, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2)]

def rawRow15523 : Integer.Sparse Key := [(key2630, 2), (key2624, 2), (key2638, 2), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2704, 2), (key2698, 2), (key2752, 2), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2807, -1), (key2801, -1), (key2858, -1), (key2851, -1), (key2919, -1), (key2918, -1), (key2784, -1), (key2778, -1), (key2868, -1), (key2851, -1), (key2922, -1), (key2918, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2)]

def rawRow15524 : Integer.Sparse Key := [(key2624, 2), (key2638, 2), (key2630, 2), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, 2), (key2752, 2), (key2704, 2), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2851, -1), (key2918, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2851, -1), (key2918, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2)]

def rawRow15525 : Integer.Sparse Key := [(key2638, 2), (key2624, 2), (key2630, 2), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, 2), (key2698, 2), (key2704, 2), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2858, -1), (key2807, -1), (key2918, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2868, -1), (key2784, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2)]

def rawRow15526 : Integer.Sparse Key := [(key2630, 2), (key2638, 2), (key2624, 2), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2704, 2), (key2752, 2), (key2698, 2), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2858, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2801, -1), (key2851, -1), (key2868, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2778, -1), (key2851, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2)]

def rawRow15527 : Integer.Sparse Key := [(key2638, 2), (key2630, 2), (key2624, 2), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2752, 2), (key2704, 2), (key2698, 2), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2919, -1), (key2858, -1), (key2918, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, -1), (key2868, -1), (key2918, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2)]

def rawRow15528 : Integer.Sparse Key := [(key2663, 2), (key2669, 2), (key2669, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2752, -1), (key2704, -1), (key2752, -1), (key2608, 2), (key2614, 2), (key2614, 2), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2624, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2)]

def rawRow15529 : Integer.Sparse Key := [(key2669, 2), (key2663, 2), (key2669, 2), (key2704, -1), (key2698, -1), (key2752, -1), (key2698, -1), (key2752, -1), (key2704, -1), (key2614, 2), (key2608, 2), (key2614, 2), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2)]

def rawRow15530 : Integer.Sparse Key := [(key2669, 2), (key2669, 2), (key2663, 2), (key2752, -1), (key2752, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2614, 2), (key2614, 2), (key2608, 2), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2638, -1), (key2638, -1), (key2630, -1), (key2630, -1), (key2624, -1), (key2624, -1), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2)]

def rawRow15531 : Integer.Sparse Key := [(key2698, 2), (key2704, 2), (key2724, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2801, 2), (key2807, 2), (key2827, 2), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2698, -1), (key2704, -1), (key2851, -1), (key2858, -1), (key3021, -1), (key3022, -1), (key2624, -1), (key2630, -1), (key2851, -1), (key2868, -1), (key3021, -1), (key3025, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2)]

def rawRow15532 : Integer.Sparse Key := [(key2704, 2), (key2698, 2), (key2724, 2), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2807, 2), (key2801, 2), (key2827, 2), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2704, -1), (key2698, -1), (key2858, -1), (key2851, -1), (key3022, -1), (key3021, -1), (key2630, -1), (key2624, -1), (key2868, -1), (key2851, -1), (key3025, -1), (key3021, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2)]

def rawRow15533 : Integer.Sparse Key := [(key2698, 2), (key2724, 2), (key2704, 2), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, 2), (key2827, 2), (key2807, 2), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2851, -1), (key3021, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2851, -1), (key3021, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2)]

def rawRow15534 : Integer.Sparse Key := [(key2724, 2), (key2698, 2), (key2704, 2), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, 2), (key2801, 2), (key2807, 2), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key2858, -1), (key2704, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key2868, -1), (key2630, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2)]

def rawRow15535 : Integer.Sparse Key := [(key2704, 2), (key2724, 2), (key2698, 2), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key2807, 2), (key2827, 2), (key2801, 2), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2858, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2698, -1), (key2851, -1), (key2868, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2624, -1), (key2851, -1), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2)]

def rawRow15536 : Integer.Sparse Key := [(key2724, 2), (key2704, 2), (key2698, 2), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2827, 2), (key2807, 2), (key2801, 2), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3022, -1), (key2858, -1), (key3021, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, -1), (key2868, -1), (key3021, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2)]

def rawRow15537 : Integer.Sparse Key := [(key2778, 2), (key2784, 2), (key2792, 2), (key2801, -1), (key2807, -1), (key2851, -1), (key2918, -1), (key2858, -1), (key2919, -1), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, -1), (key2704, -1), (key2851, -1), (key3021, -1), (key2858, -1), (key3022, -1), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2)]

def rawRow15538 : Integer.Sparse Key := [(key2784, 2), (key2778, 2), (key2792, 2), (key2807, -1), (key2801, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2858, -1), (key2630, 2), (key2624, 2), (key2638, 2), (key2704, -1), (key2698, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2858, -1), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2)]

def rawRow15539 : Integer.Sparse Key := [(key2778, 2), (key2792, 2), (key2784, 2), (key2851, -1), (key2858, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2624, 2), (key2638, 2), (key2630, 2), (key2851, -1), (key2858, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2)]

def rawRow15540 : Integer.Sparse Key := [(key2792, 2), (key2778, 2), (key2784, 2), (key2858, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2918, -1), (key2807, -1), (key2638, 2), (key2624, 2), (key2630, 2), (key2858, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key3021, -1), (key2704, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2)]

def rawRow15541 : Integer.Sparse Key := [(key2784, 2), (key2792, 2), (key2778, 2), (key2918, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2801, -1), (key2851, -1), (key2630, 2), (key2638, 2), (key2624, 2), (key3021, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2)]

def rawRow15542 : Integer.Sparse Key := [(key2792, 2), (key2784, 2), (key2778, 2), (key2919, -1), (key2918, -1), (key2858, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2638, 2), (key2630, 2), (key2624, 2), (key3022, -1), (key3021, -1), (key2858, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2)]

def rawRow15543 : Integer.Sparse Key := [(key2801, 2), (key2807, 2), (key2827, 2), (key2778, -1), (key2784, -1), (key2851, -1), (key2918, -1), (key2868, -1), (key2922, -1), (key2698, 2), (key2704, 2), (key2724, 2), (key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2)]

def rawRow15544 : Integer.Sparse Key := [(key2807, 2), (key2801, 2), (key2827, 2), (key2784, -1), (key2778, -1), (key2918, -1), (key2851, -1), (key2922, -1), (key2868, -1), (key2704, 2), (key2698, 2), (key2724, 2), (key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2)]

def rawRow15545 : Integer.Sparse Key := [(key2801, 2), (key2827, 2), (key2807, 2), (key2851, -1), (key2868, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2698, 2), (key2724, 2), (key2704, 2), (key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2)]

def rawRow15546 : Integer.Sparse Key := [(key2827, 2), (key2801, 2), (key2807, 2), (key2868, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2918, -1), (key2784, -1), (key2724, 2), (key2698, 2), (key2704, 2), (key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2)]

def rawRow15555 : Integer.Sparse Key := [(key2772, 4), (key2889, 4), (key2889, 4), (key2766, -2), (key2766, -2), (key2843, -2), (key2843, -2), (key2887, -2), (key2887, -2), (key2931, -2), (key2931, -2), (key2968, -2), (key2968, -2), (key2995, -2), (key2995, -2), (key2929, 4), (key2966, 4), (key2966, 4)]

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

def rawRow1524 : Integer.Sparse Key := [(key2628, -2), (key2628, -2), (key2641, -2), (key2612, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2660, 1), (key2660, 1), (key2706, 2), (key2706, 2), (key2753, 2), (key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2758, -1), (key2758, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2920, -1), (key2920, -1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2923, 1), (key2923, 1)]

def rawRow1525 : Integer.Sparse Key := [(key2628, -2), (key2641, -2), (key2628, -2), (key2646, 1), (key2653, 1), (key2612, 1), (key2653, 1), (key2616, 1), (key2640, 1), (key2706, 2), (key2753, 2), (key2706, 2), (key2726, -1), (key2758, -1), (key2671, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2860, -1), (key2920, -1), (key2809, -1), (key2920, -1), (key2809, -1), (key2860, -1), (key2870, 1), (key2923, 1), (key2786, 1), (key2923, 1), (key2786, 1), (key2870, 1)]

def rawRow1526 : Integer.Sparse Key := [(key2641, -2), (key2628, -2), (key2628, -2), (key2653, 1), (key2646, 1), (key2653, 1), (key2612, 1), (key2640, 1), (key2616, 1), (key2753, 2), (key2706, 2), (key2706, 2), (key2758, -1), (key2726, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2920, -1), (key2860, -1), (key2920, -1), (key2809, -1), (key2860, -1), (key2809, -1), (key2923, 1), (key2870, 1), (key2923, 1), (key2786, 1), (key2870, 1), (key2786, 1)]

def rawRow1527 : Integer.Sparse Key := [(key2646, -2), (key2648, -2), (key2653, -2), (key2612, 1), (key2618, 1), (key2628, 1), (key2648, 1), (key2641, 1), (key2653, 1), (key2726, 2), (key2732, 2), (key2758, 2), (key2671, -1), (key2676, -1), (key2706, -1), (key2732, -1), (key2753, -1), (key2758, -1), (key2829, -1), (key2835, -1), (key2870, -1), (key2885, -1), (key2923, -1), (key2927, -1), (key2794, 1), (key2798, 1), (key2860, 1), (key2885, 1), (key2920, 1), (key2927, 1)]

def rawRow1528 : Integer.Sparse Key := [(key2648, -2), (key2646, -2), (key2653, -2), (key2618, 1), (key2612, 1), (key2648, 1), (key2628, 1), (key2653, 1), (key2641, 1), (key2732, 2), (key2726, 2), (key2758, 2), (key2676, -1), (key2671, -1), (key2732, -1), (key2706, -1), (key2758, -1), (key2753, -1), (key2835, -1), (key2829, -1), (key2885, -1), (key2870, -1), (key2927, -1), (key2923, -1), (key2798, 1), (key2794, 1), (key2885, 1), (key2860, 1), (key2927, 1), (key2920, 1)]

def rawRow1529 : Integer.Sparse Key := [(key2646, -2), (key2653, -2), (key2648, -2), (key2628, 1), (key2641, 1), (key2612, 1), (key2653, 1), (key2618, 1), (key2648, 1), (key2726, 2), (key2758, 2), (key2732, 2), (key2706, -1), (key2753, -1), (key2671, -1), (key2758, -1), (key2676, -1), (key2732, -1), (key2870, -1), (key2923, -1), (key2829, -1), (key2927, -1), (key2835, -1), (key2885, -1), (key2860, 1), (key2920, 1), (key2794, 1), (key2927, 1), (key2798, 1), (key2885, 1)]

def rawRow1530 : Integer.Sparse Key := [(key2653, -2), (key2646, -2), (key2648, -2), (key2641, 1), (key2628, 1), (key2653, 1), (key2612, 1), (key2648, 1), (key2618, 1), (key2758, 2), (key2726, 2), (key2732, 2), (key2753, -1), (key2706, -1), (key2758, -1), (key2671, -1), (key2732, -1), (key2676, -1), (key2923, -1), (key2870, -1), (key2927, -1), (key2829, -1), (key2885, -1), (key2835, -1), (key2920, 1), (key2860, 1), (key2927, 1), (key2794, 1), (key2885, 1), (key2798, 1)]

def rawRow1531 : Integer.Sparse Key := [(key2648, -2), (key2653, -2), (key2646, -2), (key2648, 1), (key2653, 1), (key2618, 1), (key2641, 1), (key2612, 1), (key2628, 1), (key2732, 2), (key2758, 2), (key2726, 2), (key2732, -1), (key2758, -1), (key2676, -1), (key2753, -1), (key2671, -1), (key2706, -1), (key2885, -1), (key2927, -1), (key2835, -1), (key2923, -1), (key2829, -1), (key2870, -1), (key2885, 1), (key2927, 1), (key2798, 1), (key2920, 1), (key2794, 1), (key2860, 1)]

def rawRow1532 : Integer.Sparse Key := [(key2653, -2), (key2648, -2), (key2646, -2), (key2653, 1), (key2648, 1), (key2641, 1), (key2618, 1), (key2628, 1), (key2612, 1), (key2758, 2), (key2732, 2), (key2726, 2), (key2758, -1), (key2732, -1), (key2753, -1), (key2676, -1), (key2706, -1), (key2671, -1), (key2927, -1), (key2885, -1), (key2923, -1), (key2835, -1), (key2870, -1), (key2829, -1), (key2927, 1), (key2885, 1), (key2920, 1), (key2798, 1), (key2860, 1), (key2794, 1)]

def rawRow1533 : Integer.Sparse Key := [(key2782, -2), (key2782, -2), (key2795, -2), (key2805, 1), (key2805, 1), (key2893, 1), (key2893, 1), (key2897, 1), (key2897, 1), (key2628, 2), (key2628, 2), (key2641, 2), (key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2976, -1), (key2976, -1), (key2612, -1), (key2616, -1), (key2640, -1), (key2640, -1), (key2660, -1), (key2660, -1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1)]

def rawRow1534 : Integer.Sparse Key := [(key2782, -2), (key2795, -2), (key2782, -2), (key2893, 1), (key2897, 1), (key2805, 1), (key2897, 1), (key2805, 1), (key2893, 1), (key2628, 2), (key2641, 2), (key2628, 2), (key2972, -1), (key2976, -1), (key2702, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2646, -1), (key2653, -1), (key2612, -1), (key2653, -1), (key2616, -1), (key2640, -1), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1)]

def rawRow1535 : Integer.Sparse Key := [(key2795, -2), (key2782, -2), (key2782, -2), (key2897, 1), (key2893, 1), (key2897, 1), (key2805, 1), (key2893, 1), (key2805, 1), (key2641, 2), (key2628, 2), (key2628, 2), (key2976, -1), (key2972, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2702, -1), (key2653, -1), (key2646, -1), (key2653, -1), (key2612, -1), (key2640, -1), (key2616, -1), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1)]

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

def rawRow1536 : Integer.Sparse Key := [(key2893, -2), (key2897, -2), (key2904, -2), (key2782, 1), (key2795, 1), (key2805, 1), (key2897, 1), (key2831, 1), (key2904, 1), (key2972, 2), (key2976, 2), (key2983, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1)]

def rawRow1537 : Integer.Sparse Key := [(key2897, -2), (key2893, -2), (key2904, -2), (key2795, 1), (key2782, 1), (key2897, 1), (key2805, 1), (key2904, 1), (key2831, 1), (key2976, 2), (key2972, 2), (key2983, 2), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1)]

def rawRow1538 : Integer.Sparse Key := [(key2893, -2), (key2904, -2), (key2897, -2), (key2805, 1), (key2831, 1), (key2782, 1), (key2904, 1), (key2795, 1), (key2897, 1), (key2972, 2), (key2983, 2), (key2976, 2), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1)]

def rawRow1539 : Integer.Sparse Key := [(key2904, -2), (key2893, -2), (key2897, -2), (key2831, 1), (key2805, 1), (key2904, 1), (key2782, 1), (key2897, 1), (key2795, 1), (key2983, 2), (key2972, 2), (key2976, 2), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1)]

def rawRow1540 : Integer.Sparse Key := [(key2897, -2), (key2904, -2), (key2893, -2), (key2897, 1), (key2904, 1), (key2795, 1), (key2831, 1), (key2782, 1), (key2805, 1), (key2976, 2), (key2983, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1)]

def rawRow1541 : Integer.Sparse Key := [(key2904, -2), (key2897, -2), (key2893, -2), (key2904, 1), (key2897, 1), (key2831, 1), (key2795, 1), (key2805, 1), (key2782, 1), (key2983, 2), (key2976, 2), (key2972, 2), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1)]

def rawRow1542 : Integer.Sparse Key := [(key2936, -2), (key2938, -2), (key2943, -2), (key2948, 1), (key2950, 1), (key2972, 1), (key2997, 1), (key2976, 1), (key2998, 1), (key2646, 2), (key2648, 2), (key2653, 2), (key2735, -1), (key2737, -1), (key2893, -1), (key2997, -1), (key2897, -1), (key2998, -1), (key2612, -1), (key2618, -1), (key2628, -1), (key2648, -1), (key2641, -1), (key2653, -1), (key2667, 1), (key2673, 1), (key2782, 1), (key2938, 1), (key2795, 1), (key2943, 1)]

def rawRow1543 : Integer.Sparse Key := [(key2938, -2), (key2936, -2), (key2943, -2), (key2950, 1), (key2948, 1), (key2997, 1), (key2972, 1), (key2998, 1), (key2976, 1), (key2648, 2), (key2646, 2), (key2653, 2), (key2737, -1), (key2735, -1), (key2997, -1), (key2893, -1), (key2998, -1), (key2897, -1), (key2618, -1), (key2612, -1), (key2648, -1), (key2628, -1), (key2653, -1), (key2641, -1), (key2673, 1), (key2667, 1), (key2938, 1), (key2782, 1), (key2943, 1), (key2795, 1)]

def rawRow1544 : Integer.Sparse Key := [(key2936, -2), (key2943, -2), (key2938, -2), (key2972, 1), (key2976, 1), (key2948, 1), (key2998, 1), (key2950, 1), (key2997, 1), (key2646, 2), (key2653, 2), (key2648, 2), (key2893, -1), (key2897, -1), (key2735, -1), (key2998, -1), (key2737, -1), (key2997, -1), (key2628, -1), (key2641, -1), (key2612, -1), (key2653, -1), (key2618, -1), (key2648, -1), (key2782, 1), (key2795, 1), (key2667, 1), (key2943, 1), (key2673, 1), (key2938, 1)]

def rawRow1545 : Integer.Sparse Key := [(key2943, -2), (key2936, -2), (key2938, -2), (key2976, 1), (key2972, 1), (key2998, 1), (key2948, 1), (key2997, 1), (key2950, 1), (key2653, 2), (key2646, 2), (key2648, 2), (key2897, -1), (key2893, -1), (key2998, -1), (key2735, -1), (key2997, -1), (key2737, -1), (key2641, -1), (key2628, -1), (key2653, -1), (key2612, -1), (key2648, -1), (key2618, -1), (key2795, 1), (key2782, 1), (key2943, 1), (key2667, 1), (key2938, 1), (key2673, 1)]

def rawRow1546 : Integer.Sparse Key := [(key2938, -2), (key2943, -2), (key2936, -2), (key2997, 1), (key2998, 1), (key2950, 1), (key2976, 1), (key2948, 1), (key2972, 1), (key2648, 2), (key2653, 2), (key2646, 2), (key2997, -1), (key2998, -1), (key2737, -1), (key2897, -1), (key2735, -1), (key2893, -1), (key2648, -1), (key2653, -1), (key2618, -1), (key2641, -1), (key2612, -1), (key2628, -1), (key2938, 1), (key2943, 1), (key2673, 1), (key2795, 1), (key2667, 1), (key2782, 1)]

def rawRow1547 : Integer.Sparse Key := [(key2943, -2), (key2938, -2), (key2936, -2), (key2998, 1), (key2997, 1), (key2976, 1), (key2950, 1), (key2972, 1), (key2948, 1), (key2653, 2), (key2648, 2), (key2646, 2), (key2998, -1), (key2997, -1), (key2897, -1), (key2737, -1), (key2893, -1), (key2735, -1), (key2653, -1), (key2648, -1), (key2641, -1), (key2618, -1), (key2628, -1), (key2612, -1), (key2943, 1), (key2938, 1), (key2795, 1), (key2673, 1), (key2782, 1), (key2667, 1)]

def rawRow1548 : Integer.Sparse Key := [(key2972, -2), (key2976, -2), (key2983, -2), (key2936, 1), (key2943, 1), (key2948, 1), (key2998, 1), (key2960, 1), (key3000, 1), (key2893, 2), (key2897, 2), (key2904, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2976, 1), (key2728, 1), (key2983, 1)]

def rawRow1549 : Integer.Sparse Key := [(key2976, -2), (key2972, -2), (key2983, -2), (key2943, 1), (key2936, 1), (key2998, 1), (key2948, 1), (key3000, 1), (key2960, 1), (key2897, 2), (key2893, 2), (key2904, 2), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2641, 1), (key2628, 1), (key2976, 1), (key2702, 1), (key2983, 1), (key2728, 1)]

def rawRow1550 : Integer.Sparse Key := [(key2972, -2), (key2983, -2), (key2976, -2), (key2948, 1), (key2960, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2893, 2), (key2904, 2), (key2897, 2), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2702, 1), (key2728, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2976, 1)]

def rawRow1551 : Integer.Sparse Key := [(key2983, -2), (key2972, -2), (key2976, -2), (key2960, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2998, 1), (key2943, 1), (key2904, 2), (key2893, 2), (key2897, 2), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2728, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2976, 1), (key2641, 1)]

def rawRow1552 : Integer.Sparse Key := [(key2976, -2), (key2983, -2), (key2972, -2), (key2998, 1), (key3000, 1), (key2943, 1), (key2960, 1), (key2936, 1), (key2948, 1), (key2897, 2), (key2904, 2), (key2893, 2), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, 1), (key2983, 1), (key2641, 1), (key2728, 1), (key2628, 1), (key2702, 1)]

def rawRow1553 : Integer.Sparse Key := [(key2983, -2), (key2976, -2), (key2972, -2), (key3000, 1), (key2998, 1), (key2960, 1), (key2943, 1), (key2948, 1), (key2936, 1), (key2904, 2), (key2897, 2), (key2893, 2), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, 1), (key2976, 1), (key2728, 1), (key2641, 1), (key2702, 1), (key2628, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def row0 : Integer.Sparse (Fin 3237) := [(0, 10), (225, -40), (261, 30), (1620, -540), (1622, -180), (1632, -180), (2160, -540), (2574, -540), (2579, -180), (2704, -1080), (2766, -540)]

end MUB6.Certificate.MixedData

end OAI
end


