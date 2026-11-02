-- Prove2me | Definitions.Def_OAIQ106D157
-- name    : OAIQ106D157
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:05:32.144148+00:00
-- url     : https://prove2.me/theorems/2db67b1b-61f5-4a86-a5ee-48a89bab5b33
-- title:
--   Definitions bundle OAIQ106D157 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 771 declarations of OpenAI's Lean: 771 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow12134`, `OAI.MUB6.Certificate.GramRows.rawRow12135`, `OAI.MUB6.Certificate.GramRows.rawRow12136`, `OAI.MUB6.Certificate.GramRows.rawRow12137`, `OAI.MUB6.Certificate.GramRows.rawRow12138`, `OAI.MUB6.Certificate.GramRows.rawRow12139`, `OAI.MUB6.Certificate.GramRows.rawRow1214`, `OAI.MUB6.Certificate.GramRows.rawRow12140`, `OAI.MUB6.Certificate.GramRows.rawRow12141`, `OAI.MUB6.Certificate.GramRows.rawRow12142`, `OAI.MUB6.Certificate.GramRows.rawRow12143`, `OAI.MUB6.Certificate.GramRows.rawRow12144`, `OAI.MUB6.Certificate.GramRows.rawRow12145`, `OAI.MUB6.Certificate.GramRows.rawRow12146`, `OAI.MUB6.Certificate.GramRows.rawRow12147`, `OAI.MUB6.Certificate.GramRows.rawRow12148`, `OAI.MUB6.Certificate.GramRows.rawRow12149`, `OAI.MUB6.Certificate.GramRows.rawRow1215`, `OAI.MUB6.Certificate.GramRows.rawRow12150`, `OAI.MUB6.Certificate.GramRows.rawRow12151`, `OAI.MUB6.Certificate.GramRows.rawRow1216`, `OAI.MUB6.Certificate.GramRows.rawRow1217`, `OAI.MUB6.Certificate.GramRows.rawRow1218`, `OAI.MUB6.Certificate.GramRows.rawRow12188`, `OAI.MUB6.Certificate.GramRows.rawRow12189`, `OAI.MUB6.Certificate.GramRows.rawRow1219`, `OAI.MUB6.Certificate.GramRows.rawRow12190`, `OAI.MUB6.Certificate.GramRows.rawRow12191`, `OAI.MUB6.Certificate.GramRows.rawRow12192`, `OAI.MUB6.Certificate.GramRows.rawRow12193`, `OAI.MUB6.Certificate.GramRows.rawRow12194`, `OAI.MUB6.Certificate.GramRows.rawRow12195`, `OAI.MUB6.Certificate.GramRows.rawRow12196`, `OAI.MUB6.Certificate.GramRows.rawRow12197`, `OAI.MUB6.Certificate.GramRows.rawRow12198`, `OAI.MUB6.Certificate.GramRows.rawRow12199`, `OAI.MUB6.Certificate.GramRows.rawRow122`, `OAI.MUB6.Certificate.GramRows.rawRow1220`, `OAI.MUB6.Certificate.GramRows.rawRow12200`, `OAI.MUB6.Certificate.GramRows.rawRow12201` and 731 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block118`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block118.lean), [`MutuallyUnbiased_GramRows_Block119`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block119.lean), [`MutuallyUnbiased_GramRows_Block120`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block120.lean), [`MutuallyUnbiased_GramRows_Block121`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block121.lean), [`MutuallyUnbiased_GramRows_Block122`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block122.lean), [`MutuallyUnbiased_GramRows_Block123`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block123.lean), [`MutuallyUnbiased_GramRows_Block124`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block124.lean), [`MutuallyUnbiased_GramRows_Block181`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block181.lean), [`MutuallyUnbiased_GramRows_Block33`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block33.lean), [`MutuallyUnbiased_GramRows_Block34`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block34.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D080`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092`, `OAIQ106D093` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_interpretation`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_23`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow25`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D080
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow122 : Integer.Sparse Key := [(key2978, -2), (key2985, 1), (key2994, 1), (key2945, 2), (key2962, -1), (key3004, -1), (key2940, -1), (key2946, -1), (key2952, 1), (key2999, 1), (key2899, 2), (key2906, -1), (key2915, -1), (key2655, -2), (key2749, 1), (key3004, 1), (key2650, 1), (key2656, 1), (key2739, -1), (key2999, -1), (key2797, -2), (key2833, 1), (key2915, 1), (key2643, 2), (key2730, -1), (key2994, -1), (key2620, -1), (key2656, -1), (key2675, 1), (key2946, 1), (key2787, 1), (key2797, 1), (key2810, -1), (key2899, -1), (key2633, -1), (key2643, -1), (key2707, 1), (key2978, 1), (key2617, 1), (key2655, 1), (key2672, -1), (key2749, -1)]

def rawRow123 : Integer.Sparse Key := [(key2978, -2), (key2994, 1), (key2985, 1), (key2945, 2), (key3004, -1), (key2962, -1), (key2946, -1), (key2940, -1), (key2999, 1), (key2952, 1), (key2899, 2), (key2915, -1), (key2906, -1), (key2655, -2), (key3004, 1), (key2749, 1), (key2656, 1), (key2650, 1), (key2999, -1), (key2739, -1), (key2797, -2), (key2915, 1), (key2833, 1), (key2643, 2), (key2994, -1), (key2730, -1), (key2656, -1), (key2620, -1), (key2946, 1), (key2675, 1), (key2797, 1), (key2787, 1), (key2899, -1), (key2810, -1), (key2643, -1), (key2633, -1), (key2978, 1), (key2707, 1), (key2655, 1), (key2617, 1), (key2749, -1), (key2672, -1)]

def rawRow124 : Integer.Sparse Key := [(key2985, -2), (key2978, 1), (key2994, 1), (key2962, 2), (key2945, -1), (key3004, -1), (key2952, -1), (key2964, -1), (key2940, 1), (key3001, 1), (key2906, 2), (key2899, -1), (key2915, -1), (key2749, -2), (key2655, 1), (key3004, 1), (key2739, 1), (key2751, 1), (key2650, -1), (key3001, -1), (key2833, -2), (key2797, 1), (key2915, 1), (key2730, 2), (key2643, -1), (key2994, -1), (key2675, -1), (key2751, -1), (key2620, 1), (key2964, 1), (key2810, 1), (key2833, 1), (key2787, -1), (key2906, -1), (key2707, -1), (key2730, -1), (key2633, 1), (key2985, 1), (key2672, 1), (key2749, 1), (key2617, -1), (key2962, -1)]

def rawRow125 : Integer.Sparse Key := [(key2985, -2), (key2994, 1), (key2978, 1), (key2962, 2), (key3004, -1), (key2945, -1), (key2964, -1), (key2952, -1), (key3001, 1), (key2940, 1), (key2906, 2), (key2915, -1), (key2899, -1), (key2749, -2), (key3004, 1), (key2655, 1), (key2751, 1), (key2739, 1), (key3001, -1), (key2650, -1), (key2833, -2), (key2915, 1), (key2797, 1), (key2730, 2), (key2994, -1), (key2643, -1), (key2751, -1), (key2675, -1), (key2964, 1), (key2620, 1), (key2833, 1), (key2810, 1), (key2906, -1), (key2787, -1), (key2730, -1), (key2707, -1), (key2985, 1), (key2633, 1), (key2749, 1), (key2672, 1), (key2962, -1), (key2617, -1)]

def rawRow126 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1298, 2), (key1312, 1), (key1318, 1), (key1318, -1), (key1351, -1), (key1326, -2), (key1326, 1), (key1354, 1), (key1387, 1), (key1393, 1), (key1393, -2), (key1542, -1), (key1548, -1), (key1548, 1), (key1896, 1), (key1556, 2), (key1556, -1), (key1899, -1), (key1420, -1), (key1426, -1), (key1426, 1), (key1472, 1), (key1569, 1), (key1575, 1), (key1575, -1), (key1903, -1), (key1624, -1), (key1683, -1), (key1624, 1), (key1920, 1), (key1444, 2), (key1444, -1), (key1480, -1), (key1593, -2), (key1593, 1), (key1911, 1), (key1633, 1), (key1689, 1), (key1633, -1), (key1926, -1)]

def rawRow127 : Integer.Sparse Key := [(key1298, -1), (key1292, -1), (key1298, 2), (key1318, 1), (key1312, 1), (key1351, -1), (key1318, -1), (key1326, -2), (key1354, 1), (key1326, 1), (key1393, 1), (key1387, 1), (key1393, -2), (key1548, -1), (key1542, -1), (key1896, 1), (key1548, 1), (key1556, 2), (key1899, -1), (key1556, -1), (key1426, -1), (key1420, -1), (key1472, 1), (key1426, 1), (key1575, 1), (key1569, 1), (key1903, -1), (key1575, -1), (key1683, -1), (key1624, -1), (key1920, 1), (key1624, 1), (key1444, 2), (key1480, -1), (key1444, -1), (key1593, -2), (key1911, 1), (key1593, 1), (key1689, 1), (key1633, 1), (key1926, -1), (key1633, -1)]

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

def rawRow12134 : Integer.Sparse Key := [(key1851, 6), (key1851, 6), (key1855, 6), (key1855, 6), (key1886, -24)]

def rawRow12135 : Integer.Sparse Key := [(key1851, 6), (key1855, 6), (key1851, 6), (key1855, 6), (key1886, -24)]

def rawRow12136 : Integer.Sparse Key := [(key1855, 6), (key1851, 6), (key1851, 6), (key1855, 6), (key1886, -24)]

def rawRow12137 : Integer.Sparse Key := [(key1851, 6), (key1855, 6), (key1855, 6), (key1851, 6), (key1886, -24)]

def rawRow12138 : Integer.Sparse Key := [(key1855, 6), (key1851, 6), (key1855, 6), (key1851, 6), (key1886, -24)]

def rawRow12139 : Integer.Sparse Key := [(key1855, 6), (key1855, 6), (key1851, 6), (key1851, 6), (key1886, -24)]

def rawRow12140 : Integer.Sparse Key := [(key1851, 6), (key1851, 6), (key1855, 6), (key1886, 6), (key1855, -24)]

def rawRow12141 : Integer.Sparse Key := [(key1851, 6), (key1855, 6), (key1851, 6), (key1886, 6), (key1855, -24)]

def rawRow12142 : Integer.Sparse Key := [(key1855, 6), (key1851, 6), (key1851, 6), (key1886, 6), (key1855, -24)]

def rawRow12143 : Integer.Sparse Key := [(key1851, 6), (key1851, 6), (key1886, 6), (key1855, 6), (key1855, -24)]

def rawRow12144 : Integer.Sparse Key := [(key1851, 6), (key1886, 6), (key1851, 6), (key1855, 6), (key1855, -24)]

def rawRow12145 : Integer.Sparse Key := [(key1886, 6), (key1851, 6), (key1851, 6), (key1855, 6), (key1855, -24)]

def rawRow12146 : Integer.Sparse Key := [(key1851, 6), (key1855, 6), (key1886, 6), (key1851, 6), (key1855, -24)]

def rawRow12147 : Integer.Sparse Key := [(key1855, 6), (key1851, 6), (key1886, 6), (key1851, 6), (key1855, -24)]

def rawRow12148 : Integer.Sparse Key := [(key1851, 6), (key1886, 6), (key1855, 6), (key1851, 6), (key1855, -24)]

def rawRow12149 : Integer.Sparse Key := [(key1886, 6), (key1851, 6), (key1855, 6), (key1851, 6), (key1855, -24)]

def rawRow12150 : Integer.Sparse Key := [(key1855, 6), (key1886, 6), (key1851, 6), (key1851, 6), (key1855, -24)]

def rawRow12151 : Integer.Sparse Key := [(key1886, 6), (key1855, 6), (key1851, 6), (key1851, 6), (key1855, -24)]

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

def rawRow12188 : Integer.Sparse Key := [(key2362, -4), (key2365, -4), (key2365, -4), (key2365, -4), (key2365, -4), (key2367, -4), (key2457, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2525, 2)]

def rawRow12189 : Integer.Sparse Key := [(key2365, -4), (key2362, -4), (key2365, -4), (key2365, -4), (key2367, -4), (key2365, -4), (key2460, 2), (key2457, 2), (key2460, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, 2), (key2460, 2), (key2521, 2)]

def rawRow12190 : Integer.Sparse Key := [(key2365, -4), (key2365, -4), (key2362, -4), (key2367, -4), (key2365, -4), (key2365, -4), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2457, 2), (key2525, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2460, 2)]

def rawRow12191 : Integer.Sparse Key := [(key2365, -4), (key2365, -4), (key2367, -4), (key2362, -4), (key2365, -4), (key2365, -4), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2525, 2), (key2457, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2460, 2), (key2521, 2)]

def rawRow12192 : Integer.Sparse Key := [(key2365, -4), (key2367, -4), (key2365, -4), (key2365, -4), (key2362, -4), (key2365, -4), (key2521, 2), (key2525, 2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2460, 2)]

def rawRow12193 : Integer.Sparse Key := [(key2367, -4), (key2365, -4), (key2365, -4), (key2365, -4), (key2365, -4), (key2362, -4), (key2525, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2457, 2)]

def rawRow12194 : Integer.Sparse Key := [(key2457, -4), (key2460, -4), (key2460, -4), (key2521, -4), (key2521, -4), (key2525, -4), (key2362, 2), (key2365, 2), (key2365, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2532, 2), (key2532, 2), (key2562, 2), (key2562, 2), (key2564, 2), (key2564, 2)]

def rawRow12195 : Integer.Sparse Key := [(key2460, -4), (key2457, -4), (key2460, -4), (key2521, -4), (key2525, -4), (key2521, -4), (key2365, 2), (key2362, 2), (key2365, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2564, 2), (key2532, 2), (key2562, 2)]

def rawRow12196 : Integer.Sparse Key := [(key2460, -4), (key2460, -4), (key2457, -4), (key2525, -4), (key2521, -4), (key2521, -4), (key2365, 2), (key2365, 2), (key2362, 2), (key2521, 2), (key2521, 2), (key2457, 2), (key2564, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, 2)]

def rawRow12197 : Integer.Sparse Key := [(key2457, -4), (key2521, -4), (key2521, -4), (key2460, -4), (key2460, -4), (key2525, -4), (key2457, 2), (key2521, 2), (key2521, 2), (key2362, 2), (key2562, 2), (key2562, 2), (key2365, 2), (key2365, 2), (key2521, 2), (key2521, 2), (key2564, 2), (key2564, 2)]

def rawRow12198 : Integer.Sparse Key := [(key2521, -4), (key2457, -4), (key2521, -4), (key2460, -4), (key2525, -4), (key2460, -4), (key2521, 2), (key2457, 2), (key2521, 2), (key2562, 2), (key2362, 2), (key2562, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2564, 2), (key2365, 2), (key2521, 2)]

def rawRow12199 : Integer.Sparse Key := [(key2521, -4), (key2521, -4), (key2457, -4), (key2525, -4), (key2460, -4), (key2460, -4), (key2521, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2562, 2), (key2362, 2), (key2564, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2365, 2)]

def rawRow12200 : Integer.Sparse Key := [(key2460, -4), (key2521, -4), (key2525, -4), (key2457, -4), (key2460, -4), (key2521, -4), (key2532, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2564, 2), (key2362, 2), (key2365, 2), (key2457, 2), (key2521, 2), (key2532, 2), (key2562, 2)]

def rawRow12201 : Integer.Sparse Key := [(key2460, -4), (key2525, -4), (key2521, -4), (key2460, -4), (key2457, -4), (key2521, -4), (key2532, 2), (key2564, 2), (key2562, 2), (key2365, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2362, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2532, 2)]

def rawRow12202 : Integer.Sparse Key := [(key2521, -4), (key2460, -4), (key2525, -4), (key2457, -4), (key2521, -4), (key2460, -4), (key2562, 2), (key2532, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2457, 2), (key2521, 2), (key2362, 2), (key2562, 2), (key2365, 2), (key2521, 2)]

def rawRow12203 : Integer.Sparse Key := [(key2521, -4), (key2525, -4), (key2460, -4), (key2521, -4), (key2457, -4), (key2460, -4), (key2562, 2), (key2564, 2), (key2532, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2362, 2), (key2521, 2), (key2365, 2)]

def rawRow12204 : Integer.Sparse Key := [(key2525, -4), (key2460, -4), (key2521, -4), (key2460, -4), (key2521, -4), (key2457, -4), (key2564, 2), (key2532, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2365, 2), (key2521, 2), (key2362, 2), (key2457, 2)]

def rawRow12205 : Integer.Sparse Key := [(key2525, -4), (key2521, -4), (key2460, -4), (key2521, -4), (key2460, -4), (key2457, -4), (key2564, 2), (key2562, 2), (key2532, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2562, 2), (key2532, 2), (key2521, 2), (key2365, 2), (key2457, 2), (key2362, 2)]

def rawRow12206 : Integer.Sparse Key := [(key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2)]

def rawRow12207 : Integer.Sparse Key := [(key1277, 2), (key1277, 2), (key1277, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1277, -2), (key1277, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1851, -2), (key1851, -2)]

def rawRow12208 : Integer.Sparse Key := [(key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1277, 2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1700, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1700, -2)]

def rawRow12209 : Integer.Sparse Key := [(key1851, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1277, 2), (key1700, 2), (key1700, -2), (key1851, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1277, -2), (key1700, -2)]

def rawRow12210 : Integer.Sparse Key := [(key1851, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1277, 2), (key1700, 2), (key1277, 2), (key1851, -2), (key1700, -2), (key1700, -2), (key1851, -2), (key1700, -2), (key1851, -2), (key1277, -2), (key1700, -2), (key1277, -2), (key1700, -2), (key1700, -2), (key1277, -2)]

def rawRow12211 : Integer.Sparse Key := [(key219, -24), (key491, 6), (key491, 6), (key491, 6), (key491, 6)]

def rawRow12212 : Integer.Sparse Key := [(key491, -24), (key219, 6), (key491, 6), (key491, 6), (key491, 6)]

def rawRow12213 : Integer.Sparse Key := [(key491, -24), (key491, 6), (key219, 6), (key491, 6), (key491, 6)]

def rawRow12214 : Integer.Sparse Key := [(key491, -24), (key491, 6), (key491, 6), (key219, 6), (key491, 6)]

def rawRow12215 : Integer.Sparse Key := [(key491, -24), (key491, 6), (key491, 6), (key491, 6), (key219, 6)]

def rawRow12216 : Integer.Sparse Key := [(key30, -6), (key30, -6), (key30, -6), (key30, -6), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2)]

def rawRow12217 : Integer.Sparse Key := [(key110, -6), (key110, -6), (key110, -6), (key146, -6), (key30, 2), (key30, 2), (key30, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key110, 2), (key146, 2), (key146, 2), (key146, 2)]

def rawRow12218 : Integer.Sparse Key := [(key110, -6), (key110, -6), (key146, -6), (key110, -6), (key110, 2), (key110, 2), (key146, 2), (key30, 2), (key30, 2), (key110, 2), (key110, 2), (key146, 2), (key146, 2), (key30, 2), (key110, 2), (key110, 2)]

def rawRow12219 : Integer.Sparse Key := [(key110, -6), (key146, -6), (key110, -6), (key110, -6), (key110, 2), (key146, 2), (key110, 2), (key110, 2), (key146, 2), (key30, 2), (key146, 2), (key30, 2), (key110, 2), (key110, 2), (key30, 2), (key110, 2)]

def rawRow12220 : Integer.Sparse Key := [(key146, -6), (key110, -6), (key110, -6), (key110, -6), (key146, 2), (key110, 2), (key110, 2), (key146, 2), (key110, 2), (key146, 2), (key30, 2), (key110, 2), (key30, 2), (key110, 2), (key110, 2), (key30, 2)]

def rawRow12221 : Integer.Sparse Key := [(key1483, -6), (key1483, -6), (key1483, -6), (key1483, -6), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2)]

def rawRow12222 : Integer.Sparse Key := [(key1357, -6), (key1709, -6), (key1709, -6), (key1709, -6), (key1357, 2), (key1357, 2), (key1357, 2), (key1483, 2), (key1483, 2), (key1483, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2), (key1709, 2)]

def rawRow12223 : Integer.Sparse Key := [(key1709, -6), (key1357, -6), (key1709, -6), (key1709, -6), (key1483, 2), (key1709, 2), (key1709, 2), (key1357, 2), (key1709, 2), (key1709, 2), (key1357, 2), (key1357, 2), (key1483, 2), (key1483, 2), (key1709, 2), (key1709, 2)]

def rawRow12224 : Integer.Sparse Key := [(key1709, -6), (key1709, -6), (key1357, -6), (key1709, -6), (key1709, 2), (key1483, 2), (key1709, 2), (key1709, 2), (key1357, 2), (key1709, 2), (key1483, 2), (key1709, 2), (key1357, 2), (key1709, 2), (key1357, 2), (key1483, 2)]

def rawRow12225 : Integer.Sparse Key := [(key1709, -6), (key1709, -6), (key1709, -6), (key1357, -6), (key1709, 2), (key1709, 2), (key1483, 2), (key1709, 2), (key1709, 2), (key1357, 2), (key1709, 2), (key1483, 2), (key1709, 2), (key1357, 2), (key1483, 2), (key1357, 2)]

def rawRow12226 : Integer.Sparse Key := [(key1274, -6), (key1274, -6), (key1274, -6), (key1274, -6), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2)]

def rawRow12227 : Integer.Sparse Key := [(key1697, -6), (key1697, -6), (key1697, -6), (key1932, -6), (key1274, 2), (key1274, 2), (key1274, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1697, 2), (key1932, 2), (key1932, 2), (key1932, 2)]

def rawRow12228 : Integer.Sparse Key := [(key1697, -6), (key1697, -6), (key1932, -6), (key1697, -6), (key1697, 2), (key1697, 2), (key1932, 2), (key1274, 2), (key1274, 2), (key1697, 2), (key1697, 2), (key1932, 2), (key1932, 2), (key1274, 2), (key1697, 2), (key1697, 2)]

def rawRow12229 : Integer.Sparse Key := [(key1697, -6), (key1932, -6), (key1697, -6), (key1697, -6), (key1697, 2), (key1932, 2), (key1697, 2), (key1697, 2), (key1932, 2), (key1274, 2), (key1932, 2), (key1274, 2), (key1697, 2), (key1697, 2), (key1274, 2), (key1697, 2)]

def rawRow12230 : Integer.Sparse Key := [(key1932, -6), (key1697, -6), (key1697, -6), (key1697, -6), (key1932, 2), (key1697, 2), (key1697, 2), (key1932, 2), (key1697, 2), (key1932, 2), (key1274, 2), (key1697, 2), (key1274, 2), (key1697, 2), (key1697, 2), (key1274, 2)]

def rawRow12231 : Integer.Sparse Key := [(key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1)]

def rawRow12232 : Integer.Sparse Key := [(key1359, -2), (key1359, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1)]

def rawRow12233 : Integer.Sparse Key := [(key1711, -2), (key1711, -2), (key1936, -2), (key1359, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1936, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1)]

def rawRow12234 : Integer.Sparse Key := [(key1711, -2), (key1936, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1359, -2), (key1936, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1711, 1), (key1936, 1), (key1485, 1), (key1936, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1359, 1), (key1936, 1), (key1359, 1), (key1711, 1), (key1485, 1), (key1936, 1), (key1359, 1), (key1936, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1359, 1), (key1711, 1), (key1359, 1), (key1485, 1)]

def rawRow12235 : Integer.Sparse Key := [(key1936, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1711, -2), (key1936, -2), (key1359, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1936, 1), (key1711, 1), (key1936, 1), (key1485, 1), (key1711, 1), (key1485, 1), (key1936, 1), (key1711, 1), (key1936, 1), (key1359, 1), (key1711, 1), (key1359, 1), (key1936, 1), (key1485, 1), (key1936, 1), (key1359, 1), (key1485, 1), (key1359, 1), (key1711, 1), (key1485, 1), (key1711, 1), (key1359, 1), (key1485, 1), (key1359, 1)]

def rawRow12236 : Integer.Sparse Key := [(key1272, -24), (key1695, 6), (key1695, 6), (key1695, 6), (key1695, 6)]

def rawRow12237 : Integer.Sparse Key := [(key1695, -24), (key1272, 6), (key1695, 6), (key1695, 6), (key1695, 6)]

def rawRow12238 : Integer.Sparse Key := [(key1695, -24), (key1695, 6), (key1272, 6), (key1695, 6), (key1695, 6)]

def rawRow12239 : Integer.Sparse Key := [(key1695, -24), (key1695, 6), (key1695, 6), (key1272, 6), (key1695, 6)]

def rawRow12240 : Integer.Sparse Key := [(key1695, -24), (key1695, 6), (key1695, 6), (key1695, 6), (key1272, 6)]

def rawRow12241 : Integer.Sparse Key := [(key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1359, -2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2), (key1485, 2)]

def rawRow12242 : Integer.Sparse Key := [(key1485, -2), (key1485, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1359, 2), (key1359, 2), (key1359, 2), (key1711, 2), (key1711, 2), (key1711, 2), (key1711, 2), (key1711, 2), (key1711, 2), (key1936, 2), (key1936, 2), (key1936, 2)]

def rawRow12243 : Integer.Sparse Key := [(key1711, -2), (key1711, -2), (key1936, -2), (key1485, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1936, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1711, 2), (key1711, 2), (key1936, 2), (key1359, 2), (key1359, 2), (key1711, 2), (key1711, 2), (key1936, 2), (key1936, 2), (key1359, 2), (key1711, 2), (key1711, 2)]

def rawRow12244 : Integer.Sparse Key := [(key1711, -2), (key1936, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1485, -2), (key1936, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1485, -2), (key1711, -2), (key1711, 2), (key1936, 2), (key1711, 2), (key1711, 2), (key1936, 2), (key1359, 2), (key1936, 2), (key1359, 2), (key1711, 2), (key1711, 2), (key1359, 2), (key1711, 2)]

def rawRow12245 : Integer.Sparse Key := [(key1936, -2), (key1711, -2), (key1711, -2), (key1936, -2), (key1711, -2), (key1936, -2), (key1485, -2), (key1711, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1485, -2), (key1936, 2), (key1711, 2), (key1711, 2), (key1936, 2), (key1711, 2), (key1936, 2), (key1359, 2), (key1711, 2), (key1359, 2), (key1711, 2), (key1711, 2), (key1359, 2)]

def rawRow12246 : Integer.Sparse Key := [(key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key395, -2), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1)]

def rawRow12247 : Integer.Sparse Key := [(key258, -2), (key258, -2), (key258, -2), (key440, -2), (key440, -2), (key440, -2), (key440, -2), (key440, -2), (key440, -2), (key455, -2), (key455, -2), (key455, -2), (key258, 1), (key258, 1), (key258, 1), (key258, 1), (key258, 1), (key258, 1), (key395, 1), (key395, 1), (key395, 1), (key395, 1), (key395, 1), (key395, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key440, 1), (key455, 1), (key455, 1), (key455, 1), (key455, 1), (key455, 1), (key455, 1)]

def rawRow12248 : Integer.Sparse Key := [(key440, -2), (key440, -2), (key455, -2), (key258, -2), (key258, -2), (key440, -2), (key440, -2), (key455, -2), (key455, -2), (key258, -2), (key440, -2), (key440, -2), (key395, 1), (key395, 1), (key440, 1), (key440, 1), (key455, 1), (key455, 1), (key258, 1), (key258, 1), (key440, 1), (key440, 1), (key455, 1), (key455, 1), (key258, 1), (key258, 1), (key395, 1), (key395, 1), (key455, 1), (key455, 1), (key258, 1), (key258, 1), (key395, 1), (key395, 1), (key440, 1), (key440, 1)]

def rawRow12249 : Integer.Sparse Key := [(key440, -2), (key455, -2), (key440, -2), (key440, -2), (key455, -2), (key258, -2), (key455, -2), (key258, -2), (key440, -2), (key440, -2), (key258, -2), (key440, -2), (key440, 1), (key455, 1), (key395, 1), (key455, 1), (key395, 1), (key440, 1), (key440, 1), (key455, 1), (key258, 1), (key455, 1), (key258, 1), (key440, 1), (key395, 1), (key455, 1), (key258, 1), (key455, 1), (key258, 1), (key395, 1), (key395, 1), (key440, 1), (key258, 1), (key440, 1), (key258, 1), (key395, 1)]

def rawRow12250 : Integer.Sparse Key := [(key455, -2), (key440, -2), (key440, -2), (key455, -2), (key440, -2), (key455, -2), (key258, -2), (key440, -2), (key258, -2), (key440, -2), (key440, -2), (key258, -2), (key455, 1), (key440, 1), (key455, 1), (key395, 1), (key440, 1), (key395, 1), (key455, 1), (key440, 1), (key455, 1), (key258, 1), (key440, 1), (key258, 1), (key455, 1), (key395, 1), (key455, 1), (key258, 1), (key395, 1), (key258, 1), (key440, 1), (key395, 1), (key440, 1), (key258, 1), (key395, 1), (key258, 1)]

def rawRow12251 : Integer.Sparse Key := [(key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2), (key1936, -2)]

def rawRow12252 : Integer.Sparse Key := [(key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1936, 1), (key1359, -2), (key1359, -2), (key1359, -2), (key1485, -2), (key1485, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2), (key1711, -2)]

def rawRow12253 : Integer.Sparse Key := [(key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1936, 1), (key1936, 1), (key1359, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1485, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1359, -2), (key1485, -2), (key1485, -2), (key1711, -2), (key1711, -2)]

def rawRow12254 : Integer.Sparse Key := [(key1711, 1), (key1936, 1), (key1485, 1), (key1936, 1), (key1485, 1), (key1711, 1), (key1711, 1), (key1936, 1), (key1359, 1), (key1936, 1), (key1359, 1), (key1711, 1), (key1485, 1), (key1936, 1), (key1359, 1), (key1936, 1), (key1359, 1), (key1485, 1), (key1485, 1), (key1711, 1), (key1359, 1), (key1711, 1), (key1359, 1), (key1485, 1), (key1711, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1485, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1359, -2), (key1485, -2)]

def rawRow12255 : Integer.Sparse Key := [(key1936, 1), (key1711, 1), (key1936, 1), (key1485, 1), (key1711, 1), (key1485, 1), (key1936, 1), (key1711, 1), (key1936, 1), (key1359, 1), (key1711, 1), (key1359, 1), (key1936, 1), (key1485, 1), (key1936, 1), (key1359, 1), (key1485, 1), (key1359, 1), (key1711, 1), (key1485, 1), (key1711, 1), (key1359, 1), (key1485, 1), (key1359, 1), (key1711, -2), (key1711, -2), (key1485, -2), (key1711, -2), (key1711, -2), (key1359, -2), (key1711, -2), (key1485, -2), (key1711, -2), (key1359, -2), (key1485, -2), (key1359, -2)]

def rawRow12256 : Integer.Sparse Key := [(key348, -6), (key348, -6), (key348, -6), (key348, -6), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2)]

def rawRow12257 : Integer.Sparse Key := [(key279, -6), (key505, -6), (key505, -6), (key505, -6), (key279, 2), (key279, 2), (key279, 2), (key348, 2), (key348, 2), (key348, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2), (key505, 2)]

def rawRow12258 : Integer.Sparse Key := [(key505, -6), (key279, -6), (key505, -6), (key505, -6), (key348, 2), (key505, 2), (key505, 2), (key279, 2), (key505, 2), (key505, 2), (key279, 2), (key279, 2), (key348, 2), (key348, 2), (key505, 2), (key505, 2)]

def rawRow12259 : Integer.Sparse Key := [(key505, -6), (key505, -6), (key279, -6), (key505, -6), (key505, 2), (key348, 2), (key505, 2), (key505, 2), (key279, 2), (key505, 2), (key348, 2), (key505, 2), (key279, 2), (key505, 2), (key279, 2), (key348, 2)]

def rawRow12260 : Integer.Sparse Key := [(key505, -6), (key505, -6), (key505, -6), (key279, -6), (key505, 2), (key505, 2), (key348, 2), (key505, 2), (key505, 2), (key279, 2), (key505, 2), (key348, 2), (key505, 2), (key279, 2), (key348, 2), (key279, 2)]

def rawRow12261 : Integer.Sparse Key := [(key1273, 6), (key1273, 6), (key1273, 6), (key1273, 6), (key1850, -6), (key1850, -6), (key1850, -6), (key1850, -6)]

def rawRow12262 : Integer.Sparse Key := [(key1696, 6), (key1696, 6), (key1696, 6), (key1850, 6), (key1273, -6), (key1696, -6), (key1696, -6), (key1696, -6)]

def rawRow12263 : Integer.Sparse Key := [(key1696, 6), (key1696, 6), (key1850, 6), (key1696, 6), (key1696, -6), (key1273, -6), (key1696, -6), (key1696, -6)]

def rawRow12264 : Integer.Sparse Key := [(key1696, 6), (key1850, 6), (key1696, 6), (key1696, 6), (key1696, -6), (key1696, -6), (key1273, -6), (key1696, -6)]

def rawRow12265 : Integer.Sparse Key := [(key1850, 6), (key1696, 6), (key1696, 6), (key1696, 6), (key1696, -6), (key1696, -6), (key1696, -6), (key1273, -6)]

def rawRow12266 : Integer.Sparse Key := [(key1274, 6), (key1274, 6), (key1274, 6), (key1274, 6), (key1932, -6), (key1932, -6), (key1932, -6), (key1932, -6)]

def rawRow12267 : Integer.Sparse Key := [(key1697, 6), (key1697, 6), (key1697, 6), (key1932, 6), (key1274, -6), (key1697, -6), (key1697, -6), (key1697, -6)]

def rawRow12268 : Integer.Sparse Key := [(key1697, 6), (key1697, 6), (key1932, 6), (key1697, 6), (key1697, -6), (key1274, -6), (key1697, -6), (key1697, -6)]

def rawRow12269 : Integer.Sparse Key := [(key1697, 6), (key1932, 6), (key1697, 6), (key1697, 6), (key1697, -6), (key1697, -6), (key1274, -6), (key1697, -6)]

def rawRow12270 : Integer.Sparse Key := [(key1932, 6), (key1697, 6), (key1697, 6), (key1697, 6), (key1697, -6), (key1697, -6), (key1697, -6), (key1274, -6)]

def rawRow12271 : Integer.Sparse Key := [(key750, -6), (key750, -6), (key750, -6), (key750, -6), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2)]

def rawRow12272 : Integer.Sparse Key := [(key927, -6), (key927, -6), (key927, -6), (key938, -6), (key750, 2), (key750, 2), (key750, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key927, 2), (key938, 2), (key938, 2), (key938, 2)]

def rawRow12273 : Integer.Sparse Key := [(key927, -6), (key927, -6), (key938, -6), (key927, -6), (key927, 2), (key927, 2), (key938, 2), (key750, 2), (key750, 2), (key927, 2), (key927, 2), (key938, 2), (key938, 2), (key750, 2), (key927, 2), (key927, 2)]

def rawRow12274 : Integer.Sparse Key := [(key927, -6), (key938, -6), (key927, -6), (key927, -6), (key927, 2), (key938, 2), (key927, 2), (key927, 2), (key938, 2), (key750, 2), (key938, 2), (key750, 2), (key927, 2), (key927, 2), (key750, 2), (key927, 2)]

def rawRow12275 : Integer.Sparse Key := [(key938, -6), (key927, -6), (key927, -6), (key927, -6), (key938, 2), (key927, 2), (key927, 2), (key938, 2), (key927, 2), (key938, 2), (key750, 2), (key927, 2), (key750, 2), (key927, 2), (key927, 2), (key750, 2)]

def rawRow12276 : Integer.Sparse Key := [(key30, 6), (key30, 6), (key30, 6), (key30, 6), (key146, -6), (key146, -6), (key146, -6), (key146, -6)]

def rawRow12277 : Integer.Sparse Key := [(key110, 6), (key110, 6), (key110, 6), (key146, 6), (key30, -6), (key110, -6), (key110, -6), (key110, -6)]

def rawRow12278 : Integer.Sparse Key := [(key110, 6), (key110, 6), (key146, 6), (key110, 6), (key110, -6), (key30, -6), (key110, -6), (key110, -6)]

def rawRow12279 : Integer.Sparse Key := [(key110, 6), (key146, 6), (key110, 6), (key110, 6), (key110, -6), (key110, -6), (key30, -6), (key110, -6)]

def rawRow12280 : Integer.Sparse Key := [(key146, 6), (key110, 6), (key110, 6), (key110, 6), (key110, -6), (key110, -6), (key110, -6), (key30, -6)]

def rawRow12281 : Integer.Sparse Key := [(key1273, -6), (key1273, -6), (key1273, -6), (key1273, -6), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2)]

def rawRow12282 : Integer.Sparse Key := [(key1696, -6), (key1696, -6), (key1696, -6), (key1850, -6), (key1273, 2), (key1273, 2), (key1273, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1696, 2), (key1850, 2), (key1850, 2), (key1850, 2)]

def rawRow12283 : Integer.Sparse Key := [(key1696, -6), (key1696, -6), (key1850, -6), (key1696, -6), (key1696, 2), (key1696, 2), (key1850, 2), (key1273, 2), (key1273, 2), (key1696, 2), (key1696, 2), (key1850, 2), (key1850, 2), (key1273, 2), (key1696, 2), (key1696, 2)]

def rawRow12284 : Integer.Sparse Key := [(key1696, -6), (key1850, -6), (key1696, -6), (key1696, -6), (key1696, 2), (key1850, 2), (key1696, 2), (key1696, 2), (key1850, 2), (key1273, 2), (key1850, 2), (key1273, 2), (key1696, 2), (key1696, 2), (key1273, 2), (key1696, 2)]

def rawRow12285 : Integer.Sparse Key := [(key1850, -6), (key1696, -6), (key1696, -6), (key1696, -6), (key1850, 2), (key1696, 2), (key1696, 2), (key1850, 2), (key1696, 2), (key1850, 2), (key1273, 2), (key1696, 2), (key1273, 2), (key1696, 2), (key1696, 2), (key1273, 2)]

def rawRow12286 : Integer.Sparse Key := [(key1357, -6), (key1357, -6), (key1357, -6), (key1357, -6), (key1483, 6), (key1483, 6), (key1483, 6), (key1483, 6)]

def rawRow12287 : Integer.Sparse Key := [(key1483, -6), (key1709, -6), (key1709, -6), (key1709, -6), (key1357, 6), (key1709, 6), (key1709, 6), (key1709, 6)]

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

def rawRow12288 : Integer.Sparse Key := [(key1709, -6), (key1483, -6), (key1709, -6), (key1709, -6), (key1709, 6), (key1357, 6), (key1709, 6), (key1709, 6)]

def rawRow12289 : Integer.Sparse Key := [(key1709, -6), (key1709, -6), (key1483, -6), (key1709, -6), (key1709, 6), (key1709, 6), (key1357, 6), (key1709, 6)]

def rawRow12290 : Integer.Sparse Key := [(key1709, -6), (key1709, -6), (key1709, -6), (key1483, -6), (key1709, 6), (key1709, 6), (key1709, 6), (key1357, 6)]

def rawRow12291 : Integer.Sparse Key := [(key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2)]

def rawRow12292 : Integer.Sparse Key := [(key1363, -2), (key1363, -2), (key1363, -2), (key1715, -2), (key1715, -2), (key1715, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1363, 2), (key1363, 2), (key1363, 2), (key1489, 2), (key1489, 2), (key1489, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2)]

def rawRow12293 : Integer.Sparse Key := [(key1715, -2), (key1860, -2), (key1860, -2), (key1363, -2), (key1860, -2), (key1860, -2), (key1363, -2), (key1363, -2), (key1715, -2), (key1715, -2), (key1860, -2), (key1860, -2), (key1489, 2), (key1860, 2), (key1860, 2), (key1363, 2), (key1860, 2), (key1860, 2), (key1363, 2), (key1363, 2), (key1489, 2), (key1489, 2), (key1860, 2), (key1860, 2)]

def rawRow12294 : Integer.Sparse Key := [(key1860, -2), (key1715, -2), (key1860, -2), (key1860, -2), (key1363, -2), (key1860, -2), (key1715, -2), (key1860, -2), (key1363, -2), (key1860, -2), (key1363, -2), (key1715, -2), (key1860, 2), (key1489, 2), (key1860, 2), (key1860, 2), (key1363, 2), (key1860, 2), (key1489, 2), (key1860, 2), (key1363, 2), (key1860, 2), (key1363, 2), (key1489, 2)]

def rawRow12295 : Integer.Sparse Key := [(key1860, -2), (key1860, -2), (key1715, -2), (key1860, -2), (key1860, -2), (key1363, -2), (key1860, -2), (key1715, -2), (key1860, -2), (key1363, -2), (key1715, -2), (key1363, -2), (key1860, 2), (key1860, 2), (key1489, 2), (key1860, 2), (key1860, 2), (key1363, 2), (key1860, 2), (key1489, 2), (key1860, 2), (key1363, 2), (key1489, 2), (key1363, 2)]

def rawRow12296 : Integer.Sparse Key := [(key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2)]

def rawRow12297 : Integer.Sparse Key := [(key38, 2), (key38, 2), (key38, 2), (key118, 2), (key118, 2), (key118, 2), (key155, 2), (key155, 2), (key155, 2), (key155, 2), (key155, 2), (key155, 2), (key38, -2), (key38, -2), (key38, -2), (key118, -2), (key118, -2), (key118, -2), (key118, -2), (key118, -2), (key118, -2), (key155, -2), (key155, -2), (key155, -2)]

def rawRow12298 : Integer.Sparse Key := [(key118, 2), (key155, 2), (key155, 2), (key38, 2), (key155, 2), (key155, 2), (key38, 2), (key38, 2), (key118, 2), (key118, 2), (key155, 2), (key155, 2), (key118, -2), (key118, -2), (key155, -2), (key38, -2), (key38, -2), (key118, -2), (key118, -2), (key155, -2), (key155, -2), (key38, -2), (key118, -2), (key118, -2)]

def rawRow12299 : Integer.Sparse Key := [(key155, 2), (key118, 2), (key155, 2), (key155, 2), (key38, 2), (key155, 2), (key118, 2), (key155, 2), (key38, 2), (key155, 2), (key38, 2), (key118, 2), (key118, -2), (key155, -2), (key118, -2), (key118, -2), (key155, -2), (key38, -2), (key155, -2), (key38, -2), (key118, -2), (key118, -2), (key38, -2), (key118, -2)]

def rawRow12300 : Integer.Sparse Key := [(key155, 2), (key155, 2), (key118, 2), (key155, 2), (key155, 2), (key38, 2), (key155, 2), (key118, 2), (key155, 2), (key38, 2), (key118, 2), (key38, 2), (key155, -2), (key118, -2), (key118, -2), (key155, -2), (key118, -2), (key155, -2), (key38, -2), (key118, -2), (key38, -2), (key118, -2), (key118, -2), (key38, -2)]

def rawRow12301 : Integer.Sparse Key := [(key1498, -4), (key1498, -4), (key1498, -4), (key1498, -4), (key1498, -4), (key1498, -4), (key1730, 6), (key1730, 6), (key1730, 6), (key1730, 6)]

def rawRow12302 : Integer.Sparse Key := [(key1498, -4), (key1498, -4), (key1498, -4), (key1730, -4), (key1730, -4), (key1730, -4), (key1498, 6), (key1498, 6), (key1498, 6), (key1730, 6)]

def rawRow12303 : Integer.Sparse Key := [(key1498, -4), (key1730, -4), (key1730, -4), (key1498, -4), (key1498, -4), (key1730, -4), (key1498, 6), (key1498, 6), (key1730, 6), (key1498, 6)]

def rawRow12304 : Integer.Sparse Key := [(key1730, -4), (key1498, -4), (key1730, -4), (key1498, -4), (key1730, -4), (key1498, -4), (key1498, 6), (key1730, 6), (key1498, 6), (key1498, 6)]

def rawRow12305 : Integer.Sparse Key := [(key1730, -4), (key1730, -4), (key1498, -4), (key1730, -4), (key1498, -4), (key1498, -4), (key1730, 6), (key1498, 6), (key1498, 6), (key1498, 6)]

def rawRow12306 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key670, 6), (key670, 6), (key680, -24)]

def rawRow12307 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key670, 6), (key680, 6), (key670, -24)]

def rawRow12308 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key680, 6), (key670, 6), (key670, -24)]

def rawRow12309 : Integer.Sparse Key := [(key670, 6), (key680, 6), (key670, 6), (key670, 6), (key670, -24)]

def rawRow12310 : Integer.Sparse Key := [(key680, 6), (key670, 6), (key670, 6), (key670, 6), (key670, -24)]

def rawRow12311 : Integer.Sparse Key := [(key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2)]

def rawRow12312 : Integer.Sparse Key := [(key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1358, -2), (key1358, -2), (key1358, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2)]

def rawRow12313 : Integer.Sparse Key := [(key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1484, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1358, -2), (key1484, -2), (key1484, -2), (key1710, -2), (key1710, -2)]

def rawRow12314 : Integer.Sparse Key := [(key1710, 1), (key1859, 1), (key1484, 1), (key1859, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1358, 1), (key1859, 1), (key1358, 1), (key1710, 1), (key1484, 1), (key1859, 1), (key1358, 1), (key1859, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1358, 1), (key1710, 1), (key1358, 1), (key1484, 1), (key1710, -2), (key1484, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1484, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1358, -2), (key1484, -2)]

def rawRow12315 : Integer.Sparse Key := [(key1859, 1), (key1710, 1), (key1859, 1), (key1484, 1), (key1710, 1), (key1484, 1), (key1859, 1), (key1710, 1), (key1859, 1), (key1358, 1), (key1710, 1), (key1358, 1), (key1859, 1), (key1484, 1), (key1859, 1), (key1358, 1), (key1484, 1), (key1358, 1), (key1710, 1), (key1484, 1), (key1710, 1), (key1358, 1), (key1484, 1), (key1358, 1), (key1710, -2), (key1710, -2), (key1484, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1484, -2), (key1710, -2), (key1358, -2), (key1484, -2), (key1358, -2)]

def rawRow12316 : Integer.Sparse Key := [(key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1)]

def rawRow12317 : Integer.Sparse Key := [(key1358, -2), (key1358, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1)]

def rawRow12318 : Integer.Sparse Key := [(key1710, -2), (key1710, -2), (key1859, -2), (key1358, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1859, -2), (key1859, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1)]

def rawRow12319 : Integer.Sparse Key := [(key1710, -2), (key1859, -2), (key1710, -2), (key1710, -2), (key1859, -2), (key1358, -2), (key1859, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1710, 1), (key1859, 1), (key1484, 1), (key1859, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1358, 1), (key1859, 1), (key1358, 1), (key1710, 1), (key1484, 1), (key1859, 1), (key1358, 1), (key1859, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1358, 1), (key1710, 1), (key1358, 1), (key1484, 1)]

def rawRow12320 : Integer.Sparse Key := [(key1859, -2), (key1710, -2), (key1710, -2), (key1859, -2), (key1710, -2), (key1859, -2), (key1358, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1859, 1), (key1710, 1), (key1859, 1), (key1484, 1), (key1710, 1), (key1484, 1), (key1859, 1), (key1710, 1), (key1859, 1), (key1358, 1), (key1710, 1), (key1358, 1), (key1859, 1), (key1484, 1), (key1859, 1), (key1358, 1), (key1484, 1), (key1358, 1), (key1710, 1), (key1484, 1), (key1710, 1), (key1358, 1), (key1484, 1), (key1358, 1)]

def rawRow12321 : Integer.Sparse Key := [(key1277, -4), (key1277, -4), (key1277, -4), (key1277, -4), (key1277, -4), (key1277, -4), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2)]

def rawRow12322 : Integer.Sparse Key := [(key1700, -4), (key1700, -4), (key1700, -4), (key1851, -4), (key1851, -4), (key1851, -4), (key1277, 2), (key1277, 2), (key1277, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2)]

def rawRow12323 : Integer.Sparse Key := [(key1700, -4), (key1851, -4), (key1851, -4), (key1700, -4), (key1700, -4), (key1851, -4), (key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1277, 2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2)]

def rawRow12324 : Integer.Sparse Key := [(key1851, -4), (key1700, -4), (key1851, -4), (key1700, -4), (key1851, -4), (key1700, -4), (key1851, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1277, 2), (key1700, 2)]

def rawRow12325 : Integer.Sparse Key := [(key1851, -4), (key1851, -4), (key1700, -4), (key1851, -4), (key1700, -4), (key1700, -4), (key1851, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1277, 2), (key1700, 2), (key1277, 2)]

def rawRow12326 : Integer.Sparse Key := [(key288, -24), (key513, 6), (key513, 6), (key513, 6), (key513, 6)]

def rawRow12327 : Integer.Sparse Key := [(key513, -24), (key288, 6), (key513, 6), (key513, 6), (key513, 6)]

def rawRow12328 : Integer.Sparse Key := [(key513, -24), (key513, 6), (key288, 6), (key513, 6), (key513, 6)]

def rawRow12329 : Integer.Sparse Key := [(key513, -24), (key513, 6), (key513, 6), (key288, 6), (key513, 6)]

def rawRow12330 : Integer.Sparse Key := [(key513, -24), (key513, 6), (key513, 6), (key513, 6), (key288, 6)]

def rawRow12331 : Integer.Sparse Key := [(key2428, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2556, 2), (key2442, 2), (key2556, 2), (key2421, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2550, -2)]

def rawRow12332 : Integer.Sparse Key := [(key2428, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2556, 2), (key2442, 2), (key2429, -2), (key2421, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2550, -2), (key2429, -2)]

def rawRow12333 : Integer.Sparse Key := [(key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2556, 2), (key2442, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2429, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2429, -2)]

def rawRow12334 : Integer.Sparse Key := [(key2556, 2), (key2556, 2), (key2556, 2), (key2442, 2), (key2442, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2550, -2), (key2550, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2421, -2), (key2421, -2)]

def rawRow12335 : Integer.Sparse Key := [(key2429, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2508, 2), (key2442, 2), (key2508, 2), (key2421, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2496, -2)]

def rawRow12336 : Integer.Sparse Key := [(key2429, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2508, 2), (key2442, 2), (key2428, -2), (key2421, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2496, -2), (key2428, -2)]

def rawRow12337 : Integer.Sparse Key := [(key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2508, 2), (key2442, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2428, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2428, -2)]

def rawRow12338 : Integer.Sparse Key := [(key2508, 2), (key2508, 2), (key2508, 2), (key2442, 2), (key2442, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2496, -2), (key2496, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2421, -2), (key2421, -2)]

def rawRow12339 : Integer.Sparse Key := [(key1132, -24), (key1046, 6), (key1046, 6), (key1046, 6), (key1203, 6)]

def rawRow12340 : Integer.Sparse Key := [(key1132, -24), (key1046, 6), (key1046, 6), (key1203, 6), (key1046, 6)]

def rawRow12341 : Integer.Sparse Key := [(key1132, -24), (key1046, 6), (key1203, 6), (key1046, 6), (key1046, 6)]

def rawRow12342 : Integer.Sparse Key := [(key1132, -24), (key1203, 6), (key1046, 6), (key1046, 6), (key1046, 6)]

def rawRow12343 : Integer.Sparse Key := [(key1203, -24), (key1046, 6), (key1046, 6), (key1046, 6), (key1132, 6)]

def rawRow12344 : Integer.Sparse Key := [(key1203, -24), (key1046, 6), (key1046, 6), (key1132, 6), (key1046, 6)]

def rawRow12345 : Integer.Sparse Key := [(key1203, -24), (key1046, 6), (key1132, 6), (key1046, 6), (key1046, 6)]

def rawRow12346 : Integer.Sparse Key := [(key1203, -24), (key1132, 6), (key1046, 6), (key1046, 6), (key1046, 6)]

def rawRow12347 : Integer.Sparse Key := [(key1135, -6), (key1140, -6), (key1140, -6), (key1140, -6), (key1049, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1207, 2)]

def rawRow12348 : Integer.Sparse Key := [(key1140, -6), (key1135, -6), (key1140, -6), (key1140, -6), (key1060, 2), (key1049, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1207, 2), (key1060, 2)]

def rawRow12349 : Integer.Sparse Key := [(key1140, -6), (key1140, -6), (key1135, -6), (key1140, -6), (key1060, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1060, 2)]

def rawRow12350 : Integer.Sparse Key := [(key1140, -6), (key1140, -6), (key1140, -6), (key1135, -6), (key1207, 2), (key1207, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1049, 2), (key1049, 2)]

def rawRow12351 : Integer.Sparse Key := [(key1205, -6), (key1207, -6), (key1207, -6), (key1207, -6), (key1052, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1140, 2)]

def rawRow12352 : Integer.Sparse Key := [(key1207, -6), (key1205, -6), (key1207, -6), (key1207, -6), (key1060, 2), (key1052, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1140, 2), (key1060, 2)]

def rawRow12353 : Integer.Sparse Key := [(key1207, -6), (key1207, -6), (key1205, -6), (key1207, -6), (key1060, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1060, 2)]

def rawRow12354 : Integer.Sparse Key := [(key1207, -6), (key1207, -6), (key1207, -6), (key1205, -6), (key1140, 2), (key1140, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1052, 2), (key1052, 2)]

def rawRow12355 : Integer.Sparse Key := [(key3060, -6), (key3060, -6), (key3060, -6), (key3125, -6), (key3046, 2), (key3046, 2), (key3064, 2), (key3046, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3064, 2), (key3046, 2), (key3101, 2), (key3064, 2), (key3101, 2)]

def rawRow12356 : Integer.Sparse Key := [(key3060, -6), (key3060, -6), (key3125, -6), (key3060, -6), (key3046, 2), (key3064, 2), (key3046, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3064, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3101, 2), (key3064, 2)]

def rawRow12357 : Integer.Sparse Key := [(key3060, -6), (key3125, -6), (key3060, -6), (key3060, -6), (key3064, 2), (key3046, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3046, 2), (key3101, 2), (key3101, 2), (key3064, 2), (key3064, 2), (key3046, 2), (key3046, 2)]

def rawRow12358 : Integer.Sparse Key := [(key3125, -6), (key3060, -6), (key3060, -6), (key3060, -6), (key3101, 2), (key3101, 2), (key3101, 2), (key3064, 2), (key3064, 2), (key3064, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2)]

def rawRow12359 : Integer.Sparse Key := [(key3064, -6), (key3064, -6), (key3064, -6), (key3123, -6), (key3046, 2), (key3046, 2), (key3060, 2), (key3046, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3060, 2), (key3046, 2), (key3095, 2), (key3060, 2), (key3095, 2)]

def rawRow12360 : Integer.Sparse Key := [(key3064, -6), (key3064, -6), (key3123, -6), (key3064, -6), (key3046, 2), (key3060, 2), (key3046, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3060, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3095, 2), (key3060, 2)]

def rawRow12361 : Integer.Sparse Key := [(key3064, -6), (key3123, -6), (key3064, -6), (key3064, -6), (key3060, 2), (key3046, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3046, 2), (key3095, 2), (key3095, 2), (key3060, 2), (key3060, 2), (key3046, 2), (key3046, 2)]

def rawRow12362 : Integer.Sparse Key := [(key3123, -6), (key3064, -6), (key3064, -6), (key3064, -6), (key3095, 2), (key3095, 2), (key3095, 2), (key3060, 2), (key3060, 2), (key3060, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2)]

def rawRow12363 : Integer.Sparse Key := [(key2488, -6), (key2493, -6), (key2493, -6), (key2493, -6), (key2415, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2549, 2)]

def rawRow12364 : Integer.Sparse Key := [(key2493, -6), (key2488, -6), (key2493, -6), (key2493, -6), (key2425, 2), (key2415, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2549, 2), (key2425, 2)]

def rawRow12365 : Integer.Sparse Key := [(key2493, -6), (key2493, -6), (key2488, -6), (key2493, -6), (key2425, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2425, 2)]

def rawRow12366 : Integer.Sparse Key := [(key2493, -6), (key2493, -6), (key2493, -6), (key2488, -6), (key2549, 2), (key2549, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2415, 2), (key2415, 2)]

def rawRow12367 : Integer.Sparse Key := [(key2547, -6), (key2549, -6), (key2549, -6), (key2549, -6), (key2418, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2493, 2)]

def rawRow12368 : Integer.Sparse Key := [(key2549, -6), (key2547, -6), (key2549, -6), (key2549, -6), (key2425, 2), (key2418, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2493, 2), (key2425, 2)]

def rawRow12369 : Integer.Sparse Key := [(key2549, -6), (key2549, -6), (key2547, -6), (key2549, -6), (key2425, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2425, 2)]

def rawRow12370 : Integer.Sparse Key := [(key2549, -6), (key2549, -6), (key2549, -6), (key2547, -6), (key2493, 2), (key2493, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2418, 2), (key2418, 2)]

def rawRow12371 : Integer.Sparse Key := [(key2711, -2), (key2716, -2), (key2716, -2), (key2711, -2), (key2716, -2), (key2711, -2), (key2980, -2), (key2716, -2), (key2980, -2), (key2716, -2), (key2716, -2), (key2980, -2), (key2680, 1), (key2690, 1), (key2680, 1), (key2743, 1), (key2690, 1), (key2743, 1), (key2680, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2680, 1), (key2743, 1), (key2680, 1), (key2956, 1), (key2743, 1), (key2956, 1), (key2690, 1), (key2743, 1), (key2690, 1), (key2956, 1), (key2743, 1), (key2956, 1)]

def rawRow12372 : Integer.Sparse Key := [(key2716, -2), (key2711, -2), (key2716, -2), (key2716, -2), (key2711, -2), (key2980, -2), (key2711, -2), (key2980, -2), (key2716, -2), (key2716, -2), (key2980, -2), (key2716, -2), (key2690, 1), (key2680, 1), (key2743, 1), (key2680, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2743, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2743, 1)]

def rawRow12373 : Integer.Sparse Key := [(key2716, -2), (key2716, -2), (key2711, -2), (key2980, -2), (key2980, -2), (key2716, -2), (key2716, -2), (key2711, -2), (key2711, -2), (key2980, -2), (key2716, -2), (key2716, -2), (key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1)]

def rawRow12374 : Integer.Sparse Key := [(key2980, -2), (key2980, -2), (key2980, -2), (key2716, -2), (key2716, -2), (key2716, -2), (key2716, -2), (key2716, -2), (key2716, -2), (key2711, -2), (key2711, -2), (key2711, -2), (key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1)]

def rawRow12375 : Integer.Sparse Key := [(key2741, -2), (key2743, -2), (key2743, -2), (key2741, -2), (key2743, -2), (key2741, -2), (key2901, -2), (key2743, -2), (key2901, -2), (key2743, -2), (key2743, -2), (key2901, -2), (key2683, 1), (key2690, 1), (key2683, 1), (key2716, 1), (key2690, 1), (key2716, 1), (key2683, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2683, 1), (key2716, 1), (key2683, 1), (key2819, 1), (key2716, 1), (key2819, 1), (key2690, 1), (key2716, 1), (key2690, 1), (key2819, 1), (key2716, 1), (key2819, 1)]

def rawRow12376 : Integer.Sparse Key := [(key2743, -2), (key2741, -2), (key2743, -2), (key2743, -2), (key2741, -2), (key2901, -2), (key2741, -2), (key2901, -2), (key2743, -2), (key2743, -2), (key2901, -2), (key2743, -2), (key2690, 1), (key2683, 1), (key2716, 1), (key2683, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2716, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2716, 1)]

def rawRow12377 : Integer.Sparse Key := [(key2743, -2), (key2743, -2), (key2741, -2), (key2901, -2), (key2901, -2), (key2743, -2), (key2743, -2), (key2741, -2), (key2741, -2), (key2901, -2), (key2743, -2), (key2743, -2), (key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1)]

def rawRow12378 : Integer.Sparse Key := [(key2901, -2), (key2901, -2), (key2901, -2), (key2743, -2), (key2743, -2), (key2743, -2), (key2743, -2), (key2743, -2), (key2743, -2), (key2741, -2), (key2741, -2), (key2741, -2), (key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1)]

def rawRow12379 : Integer.Sparse Key := [(key3119, -24), (key3032, 6), (key3032, 6), (key3032, 6), (key3127, 6)]

def rawRow12380 : Integer.Sparse Key := [(key3119, -24), (key3032, 6), (key3032, 6), (key3127, 6), (key3032, 6)]

def rawRow12381 : Integer.Sparse Key := [(key3119, -24), (key3032, 6), (key3127, 6), (key3032, 6), (key3032, 6)]

def rawRow12382 : Integer.Sparse Key := [(key3119, -24), (key3127, 6), (key3032, 6), (key3032, 6), (key3032, 6)]

def rawRow12383 : Integer.Sparse Key := [(key3127, -24), (key3032, 6), (key3032, 6), (key3032, 6), (key3119, 6)]

def rawRow12384 : Integer.Sparse Key := [(key3127, -24), (key3032, 6), (key3032, 6), (key3119, 6), (key3032, 6)]

def rawRow12385 : Integer.Sparse Key := [(key3127, -24), (key3032, 6), (key3119, 6), (key3032, 6), (key3032, 6)]

def rawRow12386 : Integer.Sparse Key := [(key3127, -24), (key3119, 6), (key3032, 6), (key3032, 6), (key3032, 6)]

def rawRow12387 : Integer.Sparse Key := [(key2814, -2), (key2819, -2), (key2819, -2), (key2814, -2), (key2819, -2), (key2814, -2), (key2901, -2), (key2819, -2), (key2901, -2), (key2819, -2), (key2819, -2), (key2901, -2), (key2711, 2), (key2716, 2), (key2716, 2), (key2711, 2), (key2716, 2), (key2711, 2), (key2980, 2), (key2716, 2), (key2980, 2), (key2716, 2), (key2716, 2), (key2980, 2)]

def rawRow12388 : Integer.Sparse Key := [(key2819, -2), (key2814, -2), (key2819, -2), (key2819, -2), (key2814, -2), (key2901, -2), (key2814, -2), (key2901, -2), (key2819, -2), (key2819, -2), (key2901, -2), (key2819, -2), (key2716, 2), (key2711, 2), (key2716, 2), (key2716, 2), (key2711, 2), (key2980, 2), (key2711, 2), (key2980, 2), (key2716, 2), (key2716, 2), (key2980, 2), (key2716, 2)]

def rawRow12389 : Integer.Sparse Key := [(key2819, -2), (key2819, -2), (key2814, -2), (key2901, -2), (key2901, -2), (key2819, -2), (key2819, -2), (key2814, -2), (key2814, -2), (key2901, -2), (key2819, -2), (key2819, -2), (key2716, 2), (key2716, 2), (key2711, 2), (key2980, 2), (key2980, 2), (key2716, 2), (key2716, 2), (key2711, 2), (key2711, 2), (key2980, 2), (key2716, 2), (key2716, 2)]

def rawRow12390 : Integer.Sparse Key := [(key2901, -2), (key2901, -2), (key2901, -2), (key2819, -2), (key2819, -2), (key2819, -2), (key2819, -2), (key2819, -2), (key2819, -2), (key2814, -2), (key2814, -2), (key2814, -2), (key2980, 2), (key2980, 2), (key2980, 2), (key2716, 2), (key2716, 2), (key2716, 2), (key2716, 2), (key2716, 2), (key2716, 2), (key2711, 2), (key2711, 2), (key2711, 2)]

def rawRow12391 : Integer.Sparse Key := [(key2954, -2), (key2956, -2), (key2956, -2), (key2954, -2), (key2956, -2), (key2954, -2), (key2980, -2), (key2956, -2), (key2980, -2), (key2956, -2), (key2956, -2), (key2980, -2), (key2741, 2), (key2743, 2), (key2743, 2), (key2741, 2), (key2743, 2), (key2741, 2), (key2901, 2), (key2743, 2), (key2901, 2), (key2743, 2), (key2743, 2), (key2901, 2)]

def rawRow12392 : Integer.Sparse Key := [(key2956, -2), (key2954, -2), (key2956, -2), (key2956, -2), (key2954, -2), (key2980, -2), (key2954, -2), (key2980, -2), (key2956, -2), (key2956, -2), (key2980, -2), (key2956, -2), (key2743, 2), (key2741, 2), (key2743, 2), (key2743, 2), (key2741, 2), (key2901, 2), (key2741, 2), (key2901, 2), (key2743, 2), (key2743, 2), (key2901, 2), (key2743, 2)]

def rawRow12393 : Integer.Sparse Key := [(key2956, -2), (key2956, -2), (key2954, -2), (key2980, -2), (key2980, -2), (key2956, -2), (key2956, -2), (key2954, -2), (key2954, -2), (key2980, -2), (key2956, -2), (key2956, -2), (key2743, 2), (key2743, 2), (key2741, 2), (key2901, 2), (key2901, 2), (key2743, 2), (key2743, 2), (key2741, 2), (key2741, 2), (key2901, 2), (key2743, 2), (key2743, 2)]

def rawRow12394 : Integer.Sparse Key := [(key2980, -2), (key2980, -2), (key2980, -2), (key2956, -2), (key2956, -2), (key2956, -2), (key2956, -2), (key2956, -2), (key2956, -2), (key2954, -2), (key2954, -2), (key2954, -2), (key2901, 2), (key2901, 2), (key2901, 2), (key2743, 2), (key2743, 2), (key2743, 2), (key2743, 2), (key2743, 2), (key2743, 2), (key2741, 2), (key2741, 2), (key2741, 2)]

def rawRow12395 : Integer.Sparse Key := [(key1434, -2), (key1437, -2), (key1437, -2), (key1434, -2), (key1437, -2), (key1434, -2), (key1822, -2), (key1437, -2), (key1822, -2), (key1437, -2), (key1437, -2), (key1822, -2), (key1406, 1), (key1412, 1), (key1406, 1), (key1463, 1), (key1412, 1), (key1463, 1), (key1406, 1), (key1412, 1), (key1406, 1), (key1795, 1), (key1412, 1), (key1795, 1), (key1406, 1), (key1463, 1), (key1406, 1), (key1795, 1), (key1463, 1), (key1795, 1), (key1412, 1), (key1463, 1), (key1412, 1), (key1795, 1), (key1463, 1), (key1795, 1)]

def rawRow12396 : Integer.Sparse Key := [(key1437, -2), (key1434, -2), (key1437, -2), (key1437, -2), (key1434, -2), (key1822, -2), (key1434, -2), (key1822, -2), (key1437, -2), (key1437, -2), (key1822, -2), (key1437, -2), (key1412, 1), (key1406, 1), (key1463, 1), (key1406, 1), (key1463, 1), (key1412, 1), (key1412, 1), (key1406, 1), (key1795, 1), (key1406, 1), (key1795, 1), (key1412, 1), (key1463, 1), (key1406, 1), (key1795, 1), (key1406, 1), (key1795, 1), (key1463, 1), (key1463, 1), (key1412, 1), (key1795, 1), (key1412, 1), (key1795, 1), (key1463, 1)]

def rawRow12397 : Integer.Sparse Key := [(key1437, -2), (key1437, -2), (key1434, -2), (key1822, -2), (key1822, -2), (key1437, -2), (key1437, -2), (key1434, -2), (key1434, -2), (key1822, -2), (key1437, -2), (key1437, -2), (key1463, 1), (key1463, 1), (key1412, 1), (key1412, 1), (key1406, 1), (key1406, 1), (key1795, 1), (key1795, 1), (key1412, 1), (key1412, 1), (key1406, 1), (key1406, 1), (key1795, 1), (key1795, 1), (key1463, 1), (key1463, 1), (key1406, 1), (key1406, 1), (key1795, 1), (key1795, 1), (key1463, 1), (key1463, 1), (key1412, 1), (key1412, 1)]

def rawRow12398 : Integer.Sparse Key := [(key1822, -2), (key1822, -2), (key1822, -2), (key1437, -2), (key1437, -2), (key1437, -2), (key1437, -2), (key1437, -2), (key1437, -2), (key1434, -2), (key1434, -2), (key1434, -2), (key1795, 1), (key1795, 1), (key1795, 1), (key1795, 1), (key1795, 1), (key1795, 1), (key1463, 1), (key1463, 1), (key1463, 1), (key1463, 1), (key1463, 1), (key1463, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1406, 1), (key1406, 1), (key1406, 1), (key1406, 1), (key1406, 1), (key1406, 1)]

def rawRow12399 : Integer.Sparse Key := [(key1462, -2), (key1463, -2), (key1463, -2), (key1462, -2), (key1463, -2), (key1462, -2), (key1664, -2), (key1463, -2), (key1664, -2), (key1463, -2), (key1463, -2), (key1664, -2), (key1408, 1), (key1412, 1), (key1408, 1), (key1437, 1), (key1412, 1), (key1437, 1), (key1408, 1), (key1412, 1), (key1408, 1), (key1586, 1), (key1412, 1), (key1586, 1), (key1408, 1), (key1437, 1), (key1408, 1), (key1586, 1), (key1437, 1), (key1586, 1), (key1412, 1), (key1437, 1), (key1412, 1), (key1586, 1), (key1437, 1), (key1586, 1)]

def rawRow12400 : Integer.Sparse Key := [(key1463, -2), (key1462, -2), (key1463, -2), (key1463, -2), (key1462, -2), (key1664, -2), (key1462, -2), (key1664, -2), (key1463, -2), (key1463, -2), (key1664, -2), (key1463, -2), (key1412, 1), (key1408, 1), (key1437, 1), (key1408, 1), (key1437, 1), (key1412, 1), (key1412, 1), (key1408, 1), (key1586, 1), (key1408, 1), (key1586, 1), (key1412, 1), (key1437, 1), (key1408, 1), (key1586, 1), (key1408, 1), (key1586, 1), (key1437, 1), (key1437, 1), (key1412, 1), (key1586, 1), (key1412, 1), (key1586, 1), (key1437, 1)]

def rawRow12401 : Integer.Sparse Key := [(key1463, -2), (key1463, -2), (key1462, -2), (key1664, -2), (key1664, -2), (key1463, -2), (key1463, -2), (key1462, -2), (key1462, -2), (key1664, -2), (key1463, -2), (key1463, -2), (key1437, 1), (key1437, 1), (key1412, 1), (key1412, 1), (key1408, 1), (key1408, 1), (key1586, 1), (key1586, 1), (key1412, 1), (key1412, 1), (key1408, 1), (key1408, 1), (key1586, 1), (key1586, 1), (key1437, 1), (key1437, 1), (key1408, 1), (key1408, 1), (key1586, 1), (key1586, 1), (key1437, 1), (key1437, 1), (key1412, 1), (key1412, 1)]

def rawRow12402 : Integer.Sparse Key := [(key1664, -2), (key1664, -2), (key1664, -2), (key1463, -2), (key1463, -2), (key1463, -2), (key1463, -2), (key1463, -2), (key1463, -2), (key1462, -2), (key1462, -2), (key1462, -2), (key1586, 1), (key1586, 1), (key1586, 1), (key1586, 1), (key1586, 1), (key1586, 1), (key1437, 1), (key1437, 1), (key1437, 1), (key1437, 1), (key1437, 1), (key1437, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1408, 1), (key1408, 1), (key1408, 1), (key1408, 1), (key1408, 1), (key1408, 1)]

def rawRow12403 : Integer.Sparse Key := [(key2680, 1), (key2690, 1), (key2680, 1), (key2743, 1), (key2690, 1), (key2743, 1), (key2680, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2680, 1), (key2743, 1), (key2680, 1), (key2956, 1), (key2743, 1), (key2956, 1), (key2690, 1), (key2743, 1), (key2690, 1), (key2956, 1), (key2743, 1), (key2956, 1), (key2683, -2), (key2683, -2), (key2741, -2), (key2683, -2), (key2683, -2), (key2954, -2), (key2683, -2), (key2741, -2), (key2683, -2), (key2954, -2), (key2741, -2), (key2954, -2)]

def rawRow12404 : Integer.Sparse Key := [(key2690, 1), (key2680, 1), (key2743, 1), (key2680, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2743, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2743, 1), (key2683, -2), (key2741, -2), (key2683, -2), (key2683, -2), (key2954, -2), (key2683, -2), (key2741, -2), (key2683, -2), (key2954, -2), (key2683, -2), (key2954, -2), (key2741, -2)]

def rawRow12405 : Integer.Sparse Key := [(key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2741, -2), (key2683, -2), (key2683, -2), (key2954, -2), (key2683, -2), (key2683, -2), (key2954, -2), (key2954, -2), (key2741, -2), (key2741, -2), (key2683, -2), (key2683, -2)]

def rawRow12406 : Integer.Sparse Key := [(key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2954, -2), (key2954, -2), (key2954, -2), (key2741, -2), (key2741, -2), (key2741, -2), (key2683, -2), (key2683, -2), (key2683, -2), (key2683, -2), (key2683, -2), (key2683, -2)]

def rawRow12407 : Integer.Sparse Key := [(key2683, 1), (key2690, 1), (key2683, 1), (key2716, 1), (key2690, 1), (key2716, 1), (key2683, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2683, 1), (key2716, 1), (key2683, 1), (key2819, 1), (key2716, 1), (key2819, 1), (key2690, 1), (key2716, 1), (key2690, 1), (key2819, 1), (key2716, 1), (key2819, 1), (key2680, -2), (key2680, -2), (key2711, -2), (key2680, -2), (key2680, -2), (key2814, -2), (key2680, -2), (key2711, -2), (key2680, -2), (key2814, -2), (key2711, -2), (key2814, -2)]

def rawRow12408 : Integer.Sparse Key := [(key2690, 1), (key2683, 1), (key2716, 1), (key2683, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2716, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2716, 1), (key2680, -2), (key2711, -2), (key2680, -2), (key2680, -2), (key2814, -2), (key2680, -2), (key2711, -2), (key2680, -2), (key2814, -2), (key2680, -2), (key2814, -2), (key2711, -2)]

def rawRow12409 : Integer.Sparse Key := [(key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2711, -2), (key2680, -2), (key2680, -2), (key2814, -2), (key2680, -2), (key2680, -2), (key2814, -2), (key2814, -2), (key2711, -2), (key2711, -2), (key2680, -2), (key2680, -2)]

def rawRow12410 : Integer.Sparse Key := [(key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2814, -2), (key2814, -2), (key2814, -2), (key2711, -2), (key2711, -2), (key2711, -2), (key2680, -2), (key2680, -2), (key2680, -2), (key2680, -2), (key2680, -2), (key2680, -2)]

def rawRow12411 : Integer.Sparse Key := [(key1431, -6), (key1431, -6), (key1431, -6), (key1821, -6), (key1403, 2), (key1403, 2), (key1461, 2), (key1403, 2), (key1403, 2), (key1794, 2), (key1403, 2), (key1461, 2), (key1403, 2), (key1794, 2), (key1461, 2), (key1794, 2)]

def rawRow12412 : Integer.Sparse Key := [(key1431, -6), (key1431, -6), (key1821, -6), (key1431, -6), (key1403, 2), (key1461, 2), (key1403, 2), (key1403, 2), (key1794, 2), (key1403, 2), (key1461, 2), (key1403, 2), (key1794, 2), (key1403, 2), (key1794, 2), (key1461, 2)]

def rawRow12413 : Integer.Sparse Key := [(key1431, -6), (key1821, -6), (key1431, -6), (key1431, -6), (key1461, 2), (key1403, 2), (key1403, 2), (key1794, 2), (key1403, 2), (key1403, 2), (key1794, 2), (key1794, 2), (key1461, 2), (key1461, 2), (key1403, 2), (key1403, 2)]

def rawRow12414 : Integer.Sparse Key := [(key1821, -6), (key1431, -6), (key1431, -6), (key1431, -6), (key1794, 2), (key1794, 2), (key1794, 2), (key1461, 2), (key1461, 2), (key1461, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2)]

def rawRow12415 : Integer.Sparse Key := [(key1461, -6), (key1461, -6), (key1461, -6), (key1663, -6), (key1403, 2), (key1403, 2), (key1431, 2), (key1403, 2), (key1403, 2), (key1580, 2), (key1403, 2), (key1431, 2), (key1403, 2), (key1580, 2), (key1431, 2), (key1580, 2)]

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

def rawRow12416 : Integer.Sparse Key := [(key1461, -6), (key1461, -6), (key1663, -6), (key1461, -6), (key1403, 2), (key1431, 2), (key1403, 2), (key1403, 2), (key1580, 2), (key1403, 2), (key1431, 2), (key1403, 2), (key1580, 2), (key1403, 2), (key1580, 2), (key1431, 2)]

def rawRow12417 : Integer.Sparse Key := [(key1461, -6), (key1663, -6), (key1461, -6), (key1461, -6), (key1431, 2), (key1403, 2), (key1403, 2), (key1580, 2), (key1403, 2), (key1403, 2), (key1580, 2), (key1580, 2), (key1431, 2), (key1431, 2), (key1403, 2), (key1403, 2)]

def rawRow12418 : Integer.Sparse Key := [(key1663, -6), (key1461, -6), (key1461, -6), (key1461, -6), (key1580, 2), (key1580, 2), (key1580, 2), (key1431, 2), (key1431, 2), (key1431, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2)]

def rawRow12419 : Integer.Sparse Key := [(key2487, 6), (key2492, 6), (key2492, 6), (key2492, 6), (key3035, -6), (key3035, -6), (key3035, -6), (key3128, -6)]

def rawRow12420 : Integer.Sparse Key := [(key2492, 6), (key2487, 6), (key2492, 6), (key2492, 6), (key3035, -6), (key3035, -6), (key3128, -6), (key3035, -6)]

def rawRow12421 : Integer.Sparse Key := [(key2492, 6), (key2492, 6), (key2487, 6), (key2492, 6), (key3035, -6), (key3128, -6), (key3035, -6), (key3035, -6)]

def rawRow12422 : Integer.Sparse Key := [(key2492, 6), (key2492, 6), (key2492, 6), (key2487, 6), (key3128, -6), (key3035, -6), (key3035, -6), (key3035, -6)]

def rawRow12423 : Integer.Sparse Key := [(key2546, 6), (key2548, 6), (key2548, 6), (key2548, 6), (key2414, -6), (key3033, -6), (key3033, -6), (key3120, -6)]

def rawRow12424 : Integer.Sparse Key := [(key2548, 6), (key2546, 6), (key2548, 6), (key2548, 6), (key2414, -6), (key3033, -6), (key3120, -6), (key3033, -6)]

def rawRow12425 : Integer.Sparse Key := [(key2548, 6), (key2548, 6), (key2546, 6), (key2548, 6), (key2414, -6), (key3120, -6), (key3033, -6), (key3033, -6)]

def rawRow12426 : Integer.Sparse Key := [(key2548, 6), (key2548, 6), (key2548, 6), (key2546, 6), (key2487, -6), (key2414, -6), (key3033, -6), (key3033, -6)]

def rawRow12427 : Integer.Sparse Key := [(key2488, 6), (key2493, 6), (key2493, 6), (key2493, 6), (key2418, -6), (key2418, -6), (key2418, -6), (key2547, -6)]

def rawRow12428 : Integer.Sparse Key := [(key2493, 6), (key2488, 6), (key2493, 6), (key2493, 6), (key2418, -6), (key2418, -6), (key2547, -6), (key2418, -6)]

def rawRow12429 : Integer.Sparse Key := [(key2493, 6), (key2493, 6), (key2488, 6), (key2493, 6), (key2418, -6), (key2547, -6), (key2418, -6), (key2418, -6)]

def rawRow12430 : Integer.Sparse Key := [(key2493, 6), (key2493, 6), (key2493, 6), (key2488, 6), (key2547, -6), (key2418, -6), (key2418, -6), (key2418, -6)]

def rawRow12431 : Integer.Sparse Key := [(key2547, 6), (key2549, 6), (key2549, 6), (key2549, 6), (key2415, -6), (key2415, -6), (key2415, -6), (key2488, -6)]

def rawRow12432 : Integer.Sparse Key := [(key2549, 6), (key2547, 6), (key2549, 6), (key2549, 6), (key2415, -6), (key2415, -6), (key2488, -6), (key2415, -6)]

def rawRow12433 : Integer.Sparse Key := [(key2549, 6), (key2549, 6), (key2547, 6), (key2549, 6), (key2415, -6), (key2488, -6), (key2415, -6), (key2415, -6)]

def rawRow12434 : Integer.Sparse Key := [(key2549, 6), (key2549, 6), (key2549, 6), (key2547, 6), (key2488, -6), (key2415, -6), (key2415, -6), (key2415, -6)]

def rawRow12435 : Integer.Sparse Key := [(key2308, -6), (key2309, -6), (key2309, -6), (key2309, -6), (key2197, 2), (key2199, 2), (key2199, 2), (key2197, 2), (key2199, 2), (key2197, 2), (key2346, 2), (key2199, 2), (key2346, 2), (key2199, 2), (key2199, 2), (key2346, 2)]

def rawRow12436 : Integer.Sparse Key := [(key2309, -6), (key2308, -6), (key2309, -6), (key2309, -6), (key2199, 2), (key2197, 2), (key2199, 2), (key2199, 2), (key2197, 2), (key2346, 2), (key2197, 2), (key2346, 2), (key2199, 2), (key2199, 2), (key2346, 2), (key2199, 2)]

def rawRow12437 : Integer.Sparse Key := [(key2309, -6), (key2309, -6), (key2308, -6), (key2309, -6), (key2199, 2), (key2199, 2), (key2197, 2), (key2346, 2), (key2346, 2), (key2199, 2), (key2199, 2), (key2197, 2), (key2197, 2), (key2346, 2), (key2199, 2), (key2199, 2)]

def rawRow12438 : Integer.Sparse Key := [(key2309, -6), (key2309, -6), (key2309, -6), (key2308, -6), (key2346, 2), (key2346, 2), (key2346, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2197, 2), (key2197, 2), (key2197, 2)]

def rawRow12439 : Integer.Sparse Key := [(key2345, -6), (key2346, -6), (key2346, -6), (key2346, -6), (key2198, 2), (key2199, 2), (key2199, 2), (key2198, 2), (key2199, 2), (key2198, 2), (key2309, 2), (key2199, 2), (key2309, 2), (key2199, 2), (key2199, 2), (key2309, 2)]

def rawRow12440 : Integer.Sparse Key := [(key2346, -6), (key2345, -6), (key2346, -6), (key2346, -6), (key2199, 2), (key2198, 2), (key2199, 2), (key2199, 2), (key2198, 2), (key2309, 2), (key2198, 2), (key2309, 2), (key2199, 2), (key2199, 2), (key2309, 2), (key2199, 2)]

def rawRow12441 : Integer.Sparse Key := [(key2346, -6), (key2346, -6), (key2345, -6), (key2346, -6), (key2199, 2), (key2199, 2), (key2198, 2), (key2309, 2), (key2309, 2), (key2199, 2), (key2199, 2), (key2198, 2), (key2198, 2), (key2309, 2), (key2199, 2), (key2199, 2)]

def rawRow12442 : Integer.Sparse Key := [(key2346, -6), (key2346, -6), (key2346, -6), (key2345, -6), (key2309, 2), (key2309, 2), (key2309, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2199, 2), (key2198, 2), (key2198, 2), (key2198, 2)]

def rawRow12443 : Integer.Sparse Key := [(key1135, 6), (key1140, 6), (key1140, 6), (key1140, 6), (key1052, -6), (key1052, -6), (key1052, -6), (key1205, -6)]

def rawRow12444 : Integer.Sparse Key := [(key1140, 6), (key1135, 6), (key1140, 6), (key1140, 6), (key1052, -6), (key1052, -6), (key1205, -6), (key1052, -6)]

def rawRow12445 : Integer.Sparse Key := [(key1140, 6), (key1140, 6), (key1135, 6), (key1140, 6), (key1052, -6), (key1205, -6), (key1052, -6), (key1052, -6)]

def rawRow12446 : Integer.Sparse Key := [(key1140, 6), (key1140, 6), (key1140, 6), (key1135, 6), (key1205, -6), (key1052, -6), (key1052, -6), (key1052, -6)]

def rawRow12447 : Integer.Sparse Key := [(key1205, 6), (key1207, 6), (key1207, 6), (key1207, 6), (key1049, -6), (key1049, -6), (key1049, -6), (key1135, -6)]

def rawRow12448 : Integer.Sparse Key := [(key1207, 6), (key1205, 6), (key1207, 6), (key1207, 6), (key1049, -6), (key1049, -6), (key1135, -6), (key1049, -6)]

def rawRow12449 : Integer.Sparse Key := [(key1207, 6), (key1207, 6), (key1205, 6), (key1207, 6), (key1049, -6), (key1135, -6), (key1049, -6), (key1049, -6)]

def rawRow12450 : Integer.Sparse Key := [(key1207, 6), (key1207, 6), (key1207, 6), (key1205, 6), (key1135, -6), (key1049, -6), (key1049, -6), (key1049, -6)]

def rawRow12451 : Integer.Sparse Key := [(key2487, -6), (key2492, -6), (key2492, -6), (key2492, -6), (key2414, 2), (key2424, 2), (key2424, 2), (key3033, 2), (key3039, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3138, 2)]

def rawRow12452 : Integer.Sparse Key := [(key2492, -6), (key2487, -6), (key2492, -6), (key2492, -6), (key2424, 2), (key2414, 2), (key2424, 2), (key3039, 2), (key3033, 2), (key3138, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3138, 2), (key3039, 2)]

def rawRow12453 : Integer.Sparse Key := [(key2492, -6), (key2492, -6), (key2487, -6), (key2492, -6), (key2424, 2), (key2424, 2), (key2414, 2), (key3138, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3033, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3039, 2)]

def rawRow12454 : Integer.Sparse Key := [(key2492, -6), (key2492, -6), (key2492, -6), (key2487, -6), (key2548, 2), (key2548, 2), (key2548, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2414, 2), (key3033, 2), (key3033, 2)]

def rawRow12455 : Integer.Sparse Key := [(key2546, -6), (key2548, -6), (key2548, -6), (key2548, -6), (key2417, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2424, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2492, 2)]

def rawRow12456 : Integer.Sparse Key := [(key2548, -6), (key2546, -6), (key2548, -6), (key2548, -6), (key2424, 2), (key2417, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2492, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2492, 2), (key2424, 2)]

def rawRow12457 : Integer.Sparse Key := [(key2548, -6), (key2548, -6), (key2546, -6), (key2548, -6), (key2424, 2), (key2424, 2), (key2417, 2), (key2492, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2424, 2)]

def rawRow12458 : Integer.Sparse Key := [(key2548, -6), (key2548, -6), (key2548, -6), (key2546, -6), (key2492, 2), (key2492, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2417, 2), (key2417, 2)]

def rawRow12459 : Integer.Sparse Key := [(key3095, -6), (key3095, -6), (key3095, -6), (key3123, -6), (key3060, 6), (key3060, 6), (key3060, 6), (key3125, 6)]

def rawRow12460 : Integer.Sparse Key := [(key3095, -6), (key3095, -6), (key3123, -6), (key3095, -6), (key3060, 6), (key3060, 6), (key3125, 6), (key3060, 6)]

def rawRow12461 : Integer.Sparse Key := [(key3095, -6), (key3123, -6), (key3095, -6), (key3095, -6), (key3060, 6), (key3125, 6), (key3060, 6), (key3060, 6)]

def rawRow12462 : Integer.Sparse Key := [(key3123, -6), (key3095, -6), (key3095, -6), (key3095, -6), (key3125, 6), (key3060, 6), (key3060, 6), (key3060, 6)]

def rawRow12463 : Integer.Sparse Key := [(key3101, -6), (key3101, -6), (key3101, -6), (key3125, -6), (key3064, 6), (key3064, 6), (key3064, 6), (key3123, 6)]

def rawRow12464 : Integer.Sparse Key := [(key3101, -6), (key3101, -6), (key3125, -6), (key3101, -6), (key3064, 6), (key3064, 6), (key3123, 6), (key3064, 6)]

def rawRow12465 : Integer.Sparse Key := [(key3101, -6), (key3125, -6), (key3101, -6), (key3101, -6), (key3064, 6), (key3123, 6), (key3064, 6), (key3064, 6)]

def rawRow12466 : Integer.Sparse Key := [(key3125, -6), (key3101, -6), (key3101, -6), (key3101, -6), (key3123, 6), (key3064, 6), (key3064, 6), (key3064, 6)]

def rawRow12467 : Integer.Sparse Key := [(key2719, -2), (key2719, -2), (key2731, -2), (key2719, -2), (key2719, -2), (key2986, -2), (key2719, -2), (key2731, -2), (key2719, -2), (key2986, -2), (key2731, -2), (key2986, -2), (key2693, 2), (key2693, 2), (key2750, 2), (key2693, 2), (key2693, 2), (key2963, 2), (key2693, 2), (key2750, 2), (key2693, 2), (key2963, 2), (key2750, 2), (key2963, 2)]

def rawRow12468 : Integer.Sparse Key := [(key2719, -2), (key2731, -2), (key2719, -2), (key2719, -2), (key2986, -2), (key2719, -2), (key2731, -2), (key2719, -2), (key2986, -2), (key2719, -2), (key2986, -2), (key2731, -2), (key2693, 2), (key2750, 2), (key2693, 2), (key2693, 2), (key2963, 2), (key2693, 2), (key2750, 2), (key2693, 2), (key2963, 2), (key2693, 2), (key2963, 2), (key2750, 2)]

def rawRow12469 : Integer.Sparse Key := [(key2731, -2), (key2719, -2), (key2719, -2), (key2986, -2), (key2719, -2), (key2719, -2), (key2986, -2), (key2986, -2), (key2731, -2), (key2731, -2), (key2719, -2), (key2719, -2), (key2750, 2), (key2693, 2), (key2693, 2), (key2963, 2), (key2693, 2), (key2693, 2), (key2963, 2), (key2963, 2), (key2750, 2), (key2750, 2), (key2693, 2), (key2693, 2)]

def rawRow12470 : Integer.Sparse Key := [(key2986, -2), (key2986, -2), (key2986, -2), (key2731, -2), (key2731, -2), (key2731, -2), (key2719, -2), (key2719, -2), (key2719, -2), (key2719, -2), (key2719, -2), (key2719, -2), (key2963, 2), (key2963, 2), (key2963, 2), (key2750, 2), (key2750, 2), (key2750, 2), (key2693, 2), (key2693, 2), (key2693, 2), (key2693, 2), (key2693, 2), (key2693, 2)]

def rawRow12471 : Integer.Sparse Key := [(key2744, -2), (key2744, -2), (key2750, -2), (key2744, -2), (key2744, -2), (key2907, -2), (key2744, -2), (key2750, -2), (key2744, -2), (key2907, -2), (key2750, -2), (key2907, -2), (key2694, 2), (key2694, 2), (key2731, 2), (key2694, 2), (key2694, 2), (key2834, 2), (key2694, 2), (key2731, 2), (key2694, 2), (key2834, 2), (key2731, 2), (key2834, 2)]

def rawRow12472 : Integer.Sparse Key := [(key2744, -2), (key2750, -2), (key2744, -2), (key2744, -2), (key2907, -2), (key2744, -2), (key2750, -2), (key2744, -2), (key2907, -2), (key2744, -2), (key2907, -2), (key2750, -2), (key2694, 2), (key2731, 2), (key2694, 2), (key2694, 2), (key2834, 2), (key2694, 2), (key2731, 2), (key2694, 2), (key2834, 2), (key2694, 2), (key2834, 2), (key2731, 2)]

def rawRow12473 : Integer.Sparse Key := [(key2750, -2), (key2744, -2), (key2744, -2), (key2907, -2), (key2744, -2), (key2744, -2), (key2907, -2), (key2907, -2), (key2750, -2), (key2750, -2), (key2744, -2), (key2744, -2), (key2731, 2), (key2694, 2), (key2694, 2), (key2834, 2), (key2694, 2), (key2694, 2), (key2834, 2), (key2834, 2), (key2731, 2), (key2731, 2), (key2694, 2), (key2694, 2)]

def rawRow12474 : Integer.Sparse Key := [(key2907, -2), (key2907, -2), (key2907, -2), (key2750, -2), (key2750, -2), (key2750, -2), (key2744, -2), (key2744, -2), (key2744, -2), (key2744, -2), (key2744, -2), (key2744, -2), (key2834, 2), (key2834, 2), (key2834, 2), (key2731, 2), (key2731, 2), (key2731, 2), (key2694, 2), (key2694, 2), (key2694, 2), (key2694, 2), (key2694, 2), (key2694, 2)]

def rawRow12475 : Integer.Sparse Key := [(key1064, 2), (key1064, 2), (key1079, 2), (key1064, 2), (key1064, 2), (key1215, 2), (key1064, 2), (key1079, 2), (key1064, 2), (key1215, 2), (key1079, 2), (key1215, 2), (key1056, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1208, -2)]

def rawRow12476 : Integer.Sparse Key := [(key1064, 2), (key1079, 2), (key1064, 2), (key1064, 2), (key1215, 2), (key1064, 2), (key1079, 2), (key1064, 2), (key1215, 2), (key1064, 2), (key1215, 2), (key1079, 2), (key1065, -2), (key1056, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1208, -2), (key1065, -2)]

def rawRow12477 : Integer.Sparse Key := [(key1079, 2), (key1064, 2), (key1064, 2), (key1215, 2), (key1064, 2), (key1064, 2), (key1215, 2), (key1215, 2), (key1079, 2), (key1079, 2), (key1064, 2), (key1064, 2), (key1065, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1065, -2)]

def rawRow12478 : Integer.Sparse Key := [(key1215, 2), (key1215, 2), (key1215, 2), (key1079, 2), (key1079, 2), (key1079, 2), (key1064, 2), (key1064, 2), (key1064, 2), (key1064, 2), (key1064, 2), (key1064, 2), (key1208, -2), (key1208, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1056, -2), (key1056, -2)]

def rawRow12479 : Integer.Sparse Key := [(key1065, 2), (key1065, 2), (key1079, 2), (key1065, 2), (key1065, 2), (key1158, 2), (key1065, 2), (key1079, 2), (key1065, 2), (key1158, 2), (key1079, 2), (key1158, 2), (key1056, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1144, -2)]

def rawRow12480 : Integer.Sparse Key := [(key1065, 2), (key1079, 2), (key1065, 2), (key1065, 2), (key1158, 2), (key1065, 2), (key1079, 2), (key1065, 2), (key1158, 2), (key1065, 2), (key1158, 2), (key1079, 2), (key1064, -2), (key1056, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1144, -2), (key1064, -2)]

def rawRow12481 : Integer.Sparse Key := [(key1079, 2), (key1065, 2), (key1065, 2), (key1158, 2), (key1065, 2), (key1065, 2), (key1158, 2), (key1158, 2), (key1079, 2), (key1079, 2), (key1065, 2), (key1065, 2), (key1064, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1064, -2)]

def rawRow12482 : Integer.Sparse Key := [(key1158, 2), (key1158, 2), (key1158, 2), (key1079, 2), (key1079, 2), (key1079, 2), (key1065, 2), (key1065, 2), (key1065, 2), (key1065, 2), (key1065, 2), (key1065, 2), (key1144, -2), (key1144, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1056, -2), (key1056, -2)]

def rawRow12483 : Integer.Sparse Key := [(key3085, -4), (key3085, -4), (key3100, -4), (key3085, -4), (key3100, -4), (key3100, -4), (key3080, 6), (key3087, 6), (key3087, 6), (key3087, 6)]

def rawRow12484 : Integer.Sparse Key := [(key3085, -4), (key3100, -4), (key3085, -4), (key3100, -4), (key3085, -4), (key3100, -4), (key3087, 6), (key3080, 6), (key3087, 6), (key3087, 6)]

def rawRow12485 : Integer.Sparse Key := [(key3100, -4), (key3085, -4), (key3085, -4), (key3100, -4), (key3100, -4), (key3085, -4), (key3087, 6), (key3087, 6), (key3080, 6), (key3087, 6)]

def rawRow12486 : Integer.Sparse Key := [(key3100, -4), (key3100, -4), (key3100, -4), (key3085, -4), (key3085, -4), (key3085, -4), (key3087, 6), (key3087, 6), (key3087, 6), (key3080, 6)]

def rawRow12487 : Integer.Sparse Key := [(key3087, -4), (key3087, -4), (key3100, -4), (key3087, -4), (key3100, -4), (key3100, -4), (key3080, 6), (key3085, 6), (key3085, 6), (key3085, 6)]

def rawRow12488 : Integer.Sparse Key := [(key3087, -4), (key3100, -4), (key3087, -4), (key3100, -4), (key3087, -4), (key3100, -4), (key3085, 6), (key3080, 6), (key3085, 6), (key3085, 6)]

def rawRow12489 : Integer.Sparse Key := [(key3100, -4), (key3087, -4), (key3087, -4), (key3100, -4), (key3100, -4), (key3087, -4), (key3085, 6), (key3085, 6), (key3080, 6), (key3085, 6)]

def rawRow12490 : Integer.Sparse Key := [(key3100, -4), (key3100, -4), (key3100, -4), (key3087, -4), (key3087, -4), (key3087, -4), (key3085, 6), (key3085, 6), (key3085, 6), (key3080, 6)]

def rawRow12491 : Integer.Sparse Key := [(key1943, 6), (key1946, 6), (key1946, 6), (key1946, 6), (key1944, -24)]

def rawRow12492 : Integer.Sparse Key := [(key1946, 6), (key1943, 6), (key1946, 6), (key1946, 6), (key1944, -24)]

def rawRow12493 : Integer.Sparse Key := [(key1946, 6), (key1946, 6), (key1943, 6), (key1946, 6), (key1944, -24)]

def rawRow12494 : Integer.Sparse Key := [(key1946, 6), (key1946, 6), (key1946, 6), (key1943, 6), (key1944, -24)]

def rawRow12495 : Integer.Sparse Key := [(key1944, 6), (key1946, 6), (key1946, 6), (key1946, 6), (key1943, -24)]

def rawRow12496 : Integer.Sparse Key := [(key1946, 6), (key1944, 6), (key1946, 6), (key1946, 6), (key1943, -24)]

def rawRow12497 : Integer.Sparse Key := [(key1946, 6), (key1946, 6), (key1944, 6), (key1946, 6), (key1943, -24)]

def rawRow12498 : Integer.Sparse Key := [(key1946, 6), (key1946, 6), (key1946, 6), (key1944, 6), (key1943, -24)]

def rawRow12499 : Integer.Sparse Key := [(key2679, 1), (key2689, 1), (key2679, 1), (key2742, 1), (key2689, 1), (key2742, 1), (key2679, 1), (key2689, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3047, 1), (key3072, 1), (key3047, 1), (key3110, 1), (key3072, 1), (key3110, 1), (key3054, 1), (key3072, 1), (key3054, 1), (key3110, 1), (key3072, 1), (key3110, 1), (key3050, -2), (key3050, -2), (key3066, -2), (key3050, -2), (key3050, -2), (key3103, -2), (key3050, -2), (key3066, -2), (key3050, -2), (key3103, -2), (key3066, -2), (key3103, -2)]

def rawRow12500 : Integer.Sparse Key := [(key2689, 1), (key2679, 1), (key2742, 1), (key2679, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3072, 1), (key3047, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3054, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3072, 1), (key3050, -2), (key3066, -2), (key3050, -2), (key3050, -2), (key3103, -2), (key3050, -2), (key3066, -2), (key3050, -2), (key3103, -2), (key3050, -2), (key3103, -2), (key3066, -2)]

def rawRow12501 : Integer.Sparse Key := [(key2742, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key2679, 1), (key2955, 1), (key2955, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3047, 1), (key3110, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3047, 1), (key3047, 1), (key3110, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3054, 1), (key3054, 1), (key3066, -2), (key3050, -2), (key3050, -2), (key3103, -2), (key3050, -2), (key3050, -2), (key3103, -2), (key3103, -2), (key3066, -2), (key3066, -2), (key3050, -2), (key3050, -2)]

def rawRow12502 : Integer.Sparse Key := [(key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key2679, 1), (key2679, 1), (key3047, 1), (key3047, 1), (key3047, 1), (key3103, -2), (key3103, -2), (key3103, -2), (key3066, -2), (key3066, -2), (key3066, -2), (key3050, -2), (key3050, -2), (key3050, -2), (key3050, -2), (key3050, -2), (key3050, -2)]

def rawRow12503 : Integer.Sparse Key := [(key2682, 1), (key2689, 1), (key2682, 1), (key2715, 1), (key2689, 1), (key2715, 1), (key2682, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2682, 1), (key2715, 1), (key2682, 1), (key2818, 1), (key2715, 1), (key2818, 1), (key2689, 1), (key2715, 1), (key2689, 1), (key2818, 1), (key2715, 1), (key2818, 1), (key2679, -2), (key2679, -2), (key2710, -2), (key2679, -2), (key3047, -2), (key3096, -2), (key3047, -2), (key3061, -2), (key3047, -2), (key3096, -2), (key3061, -2), (key3096, -2)]

def rawRow12504 : Integer.Sparse Key := [(key2689, 1), (key2682, 1), (key2715, 1), (key2682, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2715, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2715, 1), (key2679, -2), (key2710, -2), (key2679, -2), (key2679, -2), (key3096, -2), (key3047, -2), (key3061, -2), (key3047, -2), (key3096, -2), (key3047, -2), (key3096, -2), (key3061, -2)]

def rawRow12505 : Integer.Sparse Key := [(key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2710, -2), (key2679, -2), (key2679, -2), (key2813, -2), (key2679, -2), (key3047, -2), (key3096, -2), (key3096, -2), (key3061, -2), (key3061, -2), (key3047, -2), (key3047, -2)]

def rawRow12506 : Integer.Sparse Key := [(key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2813, -2), (key2813, -2), (key2813, -2), (key2710, -2), (key2710, -2), (key2710, -2), (key2679, -2), (key2679, -2), (key2679, -2), (key3047, -2), (key3047, -2), (key3047, -2)]

def rawRow12507 : Integer.Sparse Key := [(key2710, -2), (key2715, -2), (key2715, -2), (key2710, -2), (key2715, -2), (key2710, -2), (key2979, -2), (key2715, -2), (key2979, -2), (key2715, -2), (key2715, -2), (key2979, -2), (key2679, 1), (key2689, 1), (key2679, 1), (key2742, 1), (key2689, 1), (key2742, 1), (key2679, 1), (key2689, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3047, 1), (key3072, 1), (key3047, 1), (key3110, 1), (key3072, 1), (key3110, 1), (key3054, 1), (key3072, 1), (key3054, 1), (key3110, 1), (key3072, 1), (key3110, 1)]

def rawRow12508 : Integer.Sparse Key := [(key2715, -2), (key2710, -2), (key2715, -2), (key2715, -2), (key2710, -2), (key2979, -2), (key2710, -2), (key2979, -2), (key2715, -2), (key2715, -2), (key2979, -2), (key2715, -2), (key2689, 1), (key2679, 1), (key2742, 1), (key2679, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3072, 1), (key3047, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3054, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3072, 1)]

def rawRow12509 : Integer.Sparse Key := [(key2715, -2), (key2715, -2), (key2710, -2), (key2979, -2), (key2979, -2), (key2715, -2), (key2715, -2), (key2710, -2), (key2710, -2), (key2979, -2), (key2715, -2), (key2715, -2), (key2742, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key2679, 1), (key2955, 1), (key2955, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3047, 1), (key3110, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3047, 1), (key3047, 1), (key3110, 1), (key3110, 1), (key3072, 1), (key3072, 1), (key3054, 1), (key3054, 1)]

def rawRow12510 : Integer.Sparse Key := [(key2979, -2), (key2979, -2), (key2979, -2), (key2715, -2), (key2715, -2), (key2715, -2), (key2715, -2), (key2715, -2), (key2715, -2), (key2710, -2), (key2710, -2), (key2710, -2), (key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2955, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key2679, 1), (key2679, 1), (key3047, 1), (key3047, 1), (key3047, 1)]

def rawRow12511 : Integer.Sparse Key := [(key2740, -2), (key2742, -2), (key2742, -2), (key2740, -2), (key2742, -2), (key2740, -2), (key2900, -2), (key2742, -2), (key2900, -2), (key2742, -2), (key2742, -2), (key2900, -2), (key2682, 1), (key2689, 1), (key2682, 1), (key2715, 1), (key2689, 1), (key2715, 1), (key2682, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2682, 1), (key2715, 1), (key2682, 1), (key2818, 1), (key2715, 1), (key2818, 1), (key2689, 1), (key2715, 1), (key2689, 1), (key2818, 1), (key2715, 1), (key2818, 1)]

def rawRow12512 : Integer.Sparse Key := [(key2742, -2), (key2740, -2), (key2742, -2), (key2742, -2), (key2740, -2), (key2900, -2), (key2740, -2), (key2900, -2), (key2742, -2), (key2742, -2), (key2900, -2), (key2742, -2), (key2689, 1), (key2682, 1), (key2715, 1), (key2682, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2715, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2715, 1)]

def rawRow12513 : Integer.Sparse Key := [(key2742, -2), (key2742, -2), (key2740, -2), (key2900, -2), (key2900, -2), (key2742, -2), (key2742, -2), (key2740, -2), (key2740, -2), (key2900, -2), (key2742, -2), (key2742, -2), (key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2682, 1), (key2682, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1)]

def rawRow12514 : Integer.Sparse Key := [(key2900, -2), (key2900, -2), (key2900, -2), (key2742, -2), (key2742, -2), (key2742, -2), (key2742, -2), (key2742, -2), (key2742, -2), (key2740, -2), (key2740, -2), (key2740, -2), (key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2818, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1), (key2682, 1)]

def rawRow12515 : Integer.Sparse Key := [(key2496, -4), (key2496, -4), (key2508, -4), (key2496, -4), (key2508, -4), (key2508, -4), (key2428, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2556, 2), (key2442, 2), (key2556, 2)]

def rawRow12516 : Integer.Sparse Key := [(key2496, -4), (key2508, -4), (key2496, -4), (key2508, -4), (key2496, -4), (key2508, -4), (key2428, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2556, 2), (key2442, 2)]

def rawRow12517 : Integer.Sparse Key := [(key2508, -4), (key2496, -4), (key2496, -4), (key2508, -4), (key2508, -4), (key2496, -4), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2556, 2), (key2442, 2), (key2442, 2), (key2428, 2), (key2428, 2)]

def rawRow12518 : Integer.Sparse Key := [(key2508, -4), (key2508, -4), (key2508, -4), (key2496, -4), (key2496, -4), (key2496, -4), (key2556, 2), (key2556, 2), (key2556, 2), (key2442, 2), (key2442, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2)]

def rawRow12519 : Integer.Sparse Key := [(key2550, -4), (key2550, -4), (key2556, -4), (key2550, -4), (key2556, -4), (key2556, -4), (key2429, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2508, 2), (key2442, 2), (key2508, 2)]

def rawRow12520 : Integer.Sparse Key := [(key2550, -4), (key2556, -4), (key2550, -4), (key2556, -4), (key2550, -4), (key2556, -4), (key2429, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2508, 2), (key2442, 2)]

def rawRow12521 : Integer.Sparse Key := [(key2556, -4), (key2550, -4), (key2550, -4), (key2556, -4), (key2556, -4), (key2550, -4), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2508, 2), (key2442, 2), (key2442, 2), (key2429, 2), (key2429, 2)]

def rawRow12522 : Integer.Sparse Key := [(key2556, -4), (key2556, -4), (key2556, -4), (key2550, -4), (key2550, -4), (key2550, -4), (key2508, 2), (key2508, 2), (key2508, 2), (key2442, 2), (key2442, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2)]

def rawRow12523 : Integer.Sparse Key := [(key1731, -24), (key1499, 6), (key1499, 6), (key1499, 6), (key1873, 6)]

def rawRow12524 : Integer.Sparse Key := [(key1731, -24), (key1499, 6), (key1499, 6), (key1873, 6), (key1499, 6)]

def rawRow12525 : Integer.Sparse Key := [(key1731, -24), (key1499, 6), (key1873, 6), (key1499, 6), (key1499, 6)]

def rawRow12526 : Integer.Sparse Key := [(key1731, -24), (key1873, 6), (key1499, 6), (key1499, 6), (key1499, 6)]

def rawRow12527 : Integer.Sparse Key := [(key1873, -24), (key1499, 6), (key1499, 6), (key1499, 6), (key1731, 6)]

def rawRow12528 : Integer.Sparse Key := [(key1873, -24), (key1499, 6), (key1499, 6), (key1731, 6), (key1499, 6)]

def rawRow12529 : Integer.Sparse Key := [(key1873, -24), (key1499, 6), (key1731, 6), (key1499, 6), (key1499, 6)]

def rawRow12530 : Integer.Sparse Key := [(key1873, -24), (key1731, 6), (key1499, 6), (key1499, 6), (key1499, 6)]

def rawRow12531 : Integer.Sparse Key := [(key3081, 6), (key3091, 6), (key3091, 6), (key3091, 6), (key3082, -6), (key3088, -6), (key3088, -6), (key3088, -6)]

def rawRow12532 : Integer.Sparse Key := [(key3091, 6), (key3081, 6), (key3091, 6), (key3091, 6), (key3088, -6), (key3082, -6), (key3088, -6), (key3088, -6)]

def rawRow12533 : Integer.Sparse Key := [(key3091, 6), (key3091, 6), (key3081, 6), (key3091, 6), (key3088, -6), (key3088, -6), (key3082, -6), (key3088, -6)]

def rawRow12534 : Integer.Sparse Key := [(key3091, 6), (key3091, 6), (key3091, 6), (key3081, 6), (key3088, -6), (key3088, -6), (key3088, -6), (key3082, -6)]

def rawRow12535 : Integer.Sparse Key := [(key3082, 6), (key3088, 6), (key3088, 6), (key3088, 6), (key3081, -6), (key3086, -6), (key3086, -6), (key3086, -6)]

def rawRow12536 : Integer.Sparse Key := [(key3088, 6), (key3082, 6), (key3088, 6), (key3088, 6), (key3086, -6), (key3081, -6), (key3086, -6), (key3086, -6)]

def rawRow12537 : Integer.Sparse Key := [(key3088, 6), (key3088, 6), (key3082, 6), (key3088, 6), (key3086, -6), (key3086, -6), (key3081, -6), (key3086, -6)]

def rawRow12538 : Integer.Sparse Key := [(key3088, 6), (key3088, 6), (key3088, 6), (key3082, 6), (key3086, -6), (key3086, -6), (key3086, -6), (key3081, -6)]

def rawRow12539 : Integer.Sparse Key := [(key1280, 2), (key1284, 2), (key1284, 2), (key1703, 2), (key1757, 2), (key1757, 2), (key1856, 2), (key1856, 2), (key1887, 2), (key1887, 2), (key1890, 2), (key1890, 2), (key1284, -2), (key1284, -2), (key1286, -2), (key1707, -2), (key1707, -2), (key1757, -2), (key1757, -2), (key1760, -2), (key1760, -2), (key1858, -2), (key1890, -2), (key1890, -2)]

def rawRow12540 : Integer.Sparse Key := [(key1284, 2), (key1280, 2), (key1284, 2), (key1757, 2), (key1703, 2), (key1757, 2), (key1887, 2), (key1890, 2), (key1856, 2), (key1890, 2), (key1856, 2), (key1887, 2), (key1284, -2), (key1286, -2), (key1284, -2), (key1757, -2), (key1760, -2), (key1707, -2), (key1760, -2), (key1707, -2), (key1757, -2), (key1890, -2), (key1858, -2), (key1890, -2)]

def rawRow12541 : Integer.Sparse Key := [(key1284, 2), (key1284, 2), (key1280, 2), (key1757, 2), (key1757, 2), (key1703, 2), (key1890, 2), (key1887, 2), (key1890, 2), (key1856, 2), (key1887, 2), (key1856, 2), (key1286, -2), (key1284, -2), (key1284, -2), (key1760, -2), (key1757, -2), (key1760, -2), (key1707, -2), (key1757, -2), (key1707, -2), (key1890, -2), (key1890, -2), (key1858, -2)]

def rawRow12542 : Integer.Sparse Key := [(key1703, 2), (key1856, 2), (key1856, 2), (key1280, 2), (key1887, 2), (key1887, 2), (key1284, 2), (key1284, 2), (key1757, 2), (key1757, 2), (key1890, 2), (key1890, 2), (key1707, -2), (key1707, -2), (key1858, -2), (key1284, -2), (key1284, -2), (key1757, -2), (key1757, -2), (key1890, -2), (key1890, -2), (key1286, -2), (key1760, -2), (key1760, -2)]

def rawRow12543 : Integer.Sparse Key := [(key1856, 2), (key1703, 2), (key1856, 2), (key1887, 2), (key1280, 2), (key1887, 2), (key1757, 2), (key1890, 2), (key1284, 2), (key1890, 2), (key1284, 2), (key1757, 2), (key1707, -2), (key1858, -2), (key1707, -2), (key1757, -2), (key1890, -2), (key1284, -2), (key1890, -2), (key1284, -2), (key1757, -2), (key1760, -2), (key1286, -2), (key1760, -2)]

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

def rawRow12544 : Integer.Sparse Key := [(key1856, 2), (key1856, 2), (key1703, 2), (key1887, 2), (key1887, 2), (key1280, 2), (key1890, 2), (key1757, 2), (key1890, 2), (key1284, 2), (key1757, 2), (key1284, 2), (key1858, -2), (key1707, -2), (key1707, -2), (key1890, -2), (key1757, -2), (key1890, -2), (key1284, -2), (key1757, -2), (key1284, -2), (key1760, -2), (key1760, -2), (key1286, -2)]

def rawRow12545 : Integer.Sparse Key := [(key1757, 2), (key1887, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1890, 2), (key1280, 2), (key1284, 2), (key1703, 2), (key1757, 2), (key1856, 2), (key1887, 2), (key1757, -2), (key1760, -2), (key1890, -2), (key1284, -2), (key1286, -2), (key1707, -2), (key1760, -2), (key1858, -2), (key1890, -2), (key1284, -2), (key1707, -2), (key1757, -2)]

def rawRow12546 : Integer.Sparse Key := [(key1757, 2), (key1890, 2), (key1887, 2), (key1284, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1280, 2), (key1757, 2), (key1703, 2), (key1887, 2), (key1856, 2), (key1760, -2), (key1757, -2), (key1890, -2), (key1286, -2), (key1284, -2), (key1760, -2), (key1707, -2), (key1890, -2), (key1858, -2), (key1284, -2), (key1757, -2), (key1707, -2)]

def rawRow12547 : Integer.Sparse Key := [(key1887, 2), (key1757, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1703, 2), (key1856, 2), (key1280, 2), (key1887, 2), (key1284, 2), (key1757, 2), (key1757, -2), (key1890, -2), (key1760, -2), (key1707, -2), (key1858, -2), (key1284, -2), (key1890, -2), (key1286, -2), (key1760, -2), (key1707, -2), (key1284, -2), (key1757, -2)]

def rawRow12548 : Integer.Sparse Key := [(key1887, 2), (key1890, 2), (key1757, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1703, 2), (key1887, 2), (key1280, 2), (key1757, 2), (key1284, 2), (key1890, -2), (key1757, -2), (key1760, -2), (key1858, -2), (key1707, -2), (key1890, -2), (key1284, -2), (key1760, -2), (key1286, -2), (key1707, -2), (key1757, -2), (key1284, -2)]

def rawRow12549 : Integer.Sparse Key := [(key1890, 2), (key1757, 2), (key1887, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1757, 2), (key1887, 2), (key1284, 2), (key1856, 2), (key1280, 2), (key1703, 2), (key1760, -2), (key1890, -2), (key1757, -2), (key1760, -2), (key1890, -2), (key1286, -2), (key1858, -2), (key1284, -2), (key1707, -2), (key1757, -2), (key1284, -2), (key1707, -2)]

def rawRow12550 : Integer.Sparse Key := [(key1890, 2), (key1887, 2), (key1757, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1887, 2), (key1757, 2), (key1856, 2), (key1284, 2), (key1703, 2), (key1280, 2), (key1890, -2), (key1760, -2), (key1757, -2), (key1890, -2), (key1760, -2), (key1858, -2), (key1286, -2), (key1707, -2), (key1284, -2), (key1757, -2), (key1707, -2), (key1284, -2)]

def rawRow12551 : Integer.Sparse Key := [(key1284, 2), (key1284, 2), (key1286, 2), (key1707, 2), (key1707, 2), (key1760, 2), (key1856, 2), (key1858, 2), (key1856, 2), (key1890, 2), (key1858, 2), (key1890, 2), (key1280, -2), (key1284, -2), (key1284, -2), (key1703, -2), (key1707, -2), (key1703, -2), (key1757, -2), (key1707, -2), (key1757, -2), (key1856, -2), (key1856, -2), (key1887, -2)]

def rawRow12552 : Integer.Sparse Key := [(key1284, 2), (key1286, 2), (key1284, 2), (key1707, 2), (key1760, 2), (key1707, 2), (key1858, 2), (key1856, 2), (key1890, 2), (key1856, 2), (key1890, 2), (key1858, 2), (key1284, -2), (key1280, -2), (key1284, -2), (key1707, -2), (key1703, -2), (key1757, -2), (key1703, -2), (key1757, -2), (key1707, -2), (key1856, -2), (key1887, -2), (key1856, -2)]

def rawRow12553 : Integer.Sparse Key := [(key1286, 2), (key1284, 2), (key1284, 2), (key1760, 2), (key1707, 2), (key1707, 2), (key1890, 2), (key1890, 2), (key1858, 2), (key1858, 2), (key1856, 2), (key1856, 2), (key1284, -2), (key1284, -2), (key1280, -2), (key1757, -2), (key1757, -2), (key1707, -2), (key1707, -2), (key1703, -2), (key1703, -2), (key1887, -2), (key1856, -2), (key1856, -2)]

def rawRow12554 : Integer.Sparse Key := [(key1707, 2), (key1856, 2), (key1858, 2), (key1284, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1286, 2), (key1707, 2), (key1760, 2), (key1858, 2), (key1890, 2), (key1703, -2), (key1707, -2), (key1856, -2), (key1280, -2), (key1284, -2), (key1703, -2), (key1757, -2), (key1856, -2), (key1887, -2), (key1284, -2), (key1707, -2), (key1757, -2)]

def rawRow12555 : Integer.Sparse Key := [(key1707, 2), (key1858, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1856, 2), (key1286, 2), (key1284, 2), (key1760, 2), (key1707, 2), (key1890, 2), (key1858, 2), (key1707, -2), (key1703, -2), (key1856, -2), (key1284, -2), (key1280, -2), (key1757, -2), (key1703, -2), (key1887, -2), (key1856, -2), (key1284, -2), (key1757, -2), (key1707, -2)]

def rawRow12556 : Integer.Sparse Key := [(key1856, 2), (key1707, 2), (key1858, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1707, 2), (key1858, 2), (key1284, 2), (key1890, 2), (key1286, 2), (key1760, 2), (key1703, -2), (key1856, -2), (key1707, -2), (key1703, -2), (key1856, -2), (key1280, -2), (key1887, -2), (key1284, -2), (key1757, -2), (key1707, -2), (key1284, -2), (key1757, -2)]

def rawRow12557 : Integer.Sparse Key := [(key1856, 2), (key1858, 2), (key1707, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1858, 2), (key1707, 2), (key1890, 2), (key1284, 2), (key1760, 2), (key1286, 2), (key1856, -2), (key1703, -2), (key1707, -2), (key1856, -2), (key1703, -2), (key1887, -2), (key1280, -2), (key1757, -2), (key1284, -2), (key1707, -2), (key1757, -2), (key1284, -2)]

def rawRow12558 : Integer.Sparse Key := [(key1858, 2), (key1707, 2), (key1856, 2), (key1890, 2), (key1284, 2), (key1856, 2), (key1760, 2), (key1890, 2), (key1286, 2), (key1858, 2), (key1284, 2), (key1707, 2), (key1707, -2), (key1856, -2), (key1703, -2), (key1757, -2), (key1887, -2), (key1284, -2), (key1856, -2), (key1280, -2), (key1703, -2), (key1757, -2), (key1284, -2), (key1707, -2)]

def rawRow12559 : Integer.Sparse Key := [(key1858, 2), (key1856, 2), (key1707, 2), (key1890, 2), (key1856, 2), (key1284, 2), (key1890, 2), (key1760, 2), (key1858, 2), (key1286, 2), (key1707, 2), (key1284, 2), (key1856, -2), (key1707, -2), (key1703, -2), (key1887, -2), (key1757, -2), (key1856, -2), (key1284, -2), (key1703, -2), (key1280, -2), (key1757, -2), (key1707, -2), (key1284, -2)]

def rawRow12560 : Integer.Sparse Key := [(key1760, 2), (key1890, 2), (key1890, 2), (key1286, 2), (key1858, 2), (key1858, 2), (key1284, 2), (key1284, 2), (key1707, 2), (key1707, 2), (key1856, 2), (key1856, 2), (key1757, -2), (key1757, -2), (key1887, -2), (key1284, -2), (key1284, -2), (key1707, -2), (key1707, -2), (key1856, -2), (key1856, -2), (key1280, -2), (key1703, -2), (key1703, -2)]

def rawRow12561 : Integer.Sparse Key := [(key1890, 2), (key1760, 2), (key1890, 2), (key1858, 2), (key1286, 2), (key1858, 2), (key1707, 2), (key1856, 2), (key1284, 2), (key1856, 2), (key1284, 2), (key1707, 2), (key1757, -2), (key1887, -2), (key1757, -2), (key1707, -2), (key1856, -2), (key1284, -2), (key1856, -2), (key1284, -2), (key1707, -2), (key1703, -2), (key1280, -2), (key1703, -2)]

def rawRow12562 : Integer.Sparse Key := [(key1890, 2), (key1890, 2), (key1760, 2), (key1858, 2), (key1858, 2), (key1286, 2), (key1856, 2), (key1707, 2), (key1856, 2), (key1284, 2), (key1707, 2), (key1284, 2), (key1887, -2), (key1757, -2), (key1757, -2), (key1856, -2), (key1707, -2), (key1856, -2), (key1284, -2), (key1707, -2), (key1284, -2), (key1703, -2), (key1703, -2), (key1280, -2)]

def rawRow12563 : Integer.Sparse Key := [(key501, -24), (key229, 6), (key501, 6), (key557, 6), (key557, 6)]

def rawRow12564 : Integer.Sparse Key := [(key501, -24), (key229, 6), (key557, 6), (key501, 6), (key557, 6)]

def rawRow12565 : Integer.Sparse Key := [(key501, -24), (key229, 6), (key557, 6), (key557, 6), (key501, 6)]

def rawRow12566 : Integer.Sparse Key := [(key501, -24), (key501, 6), (key229, 6), (key557, 6), (key557, 6)]

def rawRow12567 : Integer.Sparse Key := [(key501, -24), (key501, 6), (key557, 6), (key229, 6), (key557, 6)]

def rawRow12568 : Integer.Sparse Key := [(key501, -24), (key501, 6), (key557, 6), (key557, 6), (key229, 6)]

def rawRow12569 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key229, 6), (key501, 6), (key557, 6)]

def rawRow12570 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key229, 6), (key557, 6), (key501, 6)]

def rawRow12571 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key501, 6), (key229, 6), (key557, 6)]

def rawRow12572 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key501, 6), (key557, 6), (key229, 6)]

def rawRow12573 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key557, 6), (key229, 6), (key501, 6)]

def rawRow12574 : Integer.Sparse Key := [(key501, -24), (key557, 6), (key557, 6), (key501, 6), (key229, 6)]

def rawRow12575 : Integer.Sparse Key := [(key557, -24), (key229, 6), (key501, 6), (key501, 6), (key557, 6)]

def rawRow12576 : Integer.Sparse Key := [(key557, -24), (key229, 6), (key501, 6), (key557, 6), (key501, 6)]

def rawRow12577 : Integer.Sparse Key := [(key557, -24), (key229, 6), (key557, 6), (key501, 6), (key501, 6)]

def rawRow12578 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key229, 6), (key501, 6), (key557, 6)]

def rawRow12579 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key229, 6), (key557, 6), (key501, 6)]

def rawRow12580 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key501, 6), (key229, 6), (key557, 6)]

def rawRow12581 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key501, 6), (key557, 6), (key229, 6)]

def rawRow12582 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key557, 6), (key229, 6), (key501, 6)]

def rawRow12583 : Integer.Sparse Key := [(key557, -24), (key501, 6), (key557, 6), (key501, 6), (key229, 6)]

def rawRow12584 : Integer.Sparse Key := [(key557, -24), (key557, 6), (key229, 6), (key501, 6), (key501, 6)]

def rawRow12585 : Integer.Sparse Key := [(key557, -24), (key557, 6), (key501, 6), (key229, 6), (key501, 6)]

def rawRow12586 : Integer.Sparse Key := [(key557, -24), (key557, 6), (key501, 6), (key501, 6), (key229, 6)]

def rawRow12587 : Integer.Sparse Key := [(key498, -6), (key498, -6), (key504, -6), (key666, -6), (key226, 2), (key226, 2), (key232, 2), (key498, 2), (key498, 2), (key552, 2), (key552, 2), (key562, 2), (key562, 2), (key666, 2), (key683, 2), (key683, 2)]

def rawRow12588 : Integer.Sparse Key := [(key498, -6), (key504, -6), (key498, -6), (key666, -6), (key226, 2), (key232, 2), (key226, 2), (key552, 2), (key562, 2), (key498, 2), (key562, 2), (key498, 2), (key552, 2), (key683, 2), (key666, 2), (key683, 2)]

def rawRow12589 : Integer.Sparse Key := [(key504, -6), (key498, -6), (key498, -6), (key666, -6), (key232, 2), (key226, 2), (key226, 2), (key562, 2), (key552, 2), (key562, 2), (key498, 2), (key552, 2), (key498, 2), (key683, 2), (key683, 2), (key666, 2)]

def rawRow12590 : Integer.Sparse Key := [(key498, -6), (key498, -6), (key666, -6), (key504, -6), (key498, 2), (key498, 2), (key666, 2), (key226, 2), (key226, 2), (key552, 2), (key552, 2), (key683, 2), (key683, 2), (key232, 2), (key562, 2), (key562, 2)]

def rawRow12591 : Integer.Sparse Key := [(key498, -6), (key666, -6), (key498, -6), (key504, -6), (key498, 2), (key666, 2), (key498, 2), (key552, 2), (key683, 2), (key226, 2), (key683, 2), (key226, 2), (key552, 2), (key562, 2), (key232, 2), (key562, 2)]

def rawRow12592 : Integer.Sparse Key := [(key666, -6), (key498, -6), (key498, -6), (key504, -6), (key666, 2), (key498, 2), (key498, 2), (key683, 2), (key552, 2), (key683, 2), (key226, 2), (key552, 2), (key226, 2), (key562, 2), (key562, 2), (key232, 2)]

def rawRow12593 : Integer.Sparse Key := [(key498, -6), (key504, -6), (key666, -6), (key498, -6), (key552, 2), (key562, 2), (key683, 2), (key226, 2), (key232, 2), (key498, 2), (key562, 2), (key666, 2), (key683, 2), (key226, 2), (key498, 2), (key552, 2)]

def rawRow12594 : Integer.Sparse Key := [(key504, -6), (key498, -6), (key666, -6), (key498, -6), (key562, 2), (key552, 2), (key683, 2), (key232, 2), (key226, 2), (key562, 2), (key498, 2), (key683, 2), (key666, 2), (key226, 2), (key552, 2), (key498, 2)]

def rawRow12595 : Integer.Sparse Key := [(key498, -6), (key666, -6), (key504, -6), (key498, -6), (key552, 2), (key683, 2), (key562, 2), (key498, 2), (key666, 2), (key226, 2), (key683, 2), (key232, 2), (key562, 2), (key498, 2), (key226, 2), (key552, 2)]

def rawRow12596 : Integer.Sparse Key := [(key666, -6), (key498, -6), (key504, -6), (key498, -6), (key683, 2), (key552, 2), (key562, 2), (key666, 2), (key498, 2), (key683, 2), (key226, 2), (key562, 2), (key232, 2), (key498, 2), (key552, 2), (key226, 2)]

def rawRow12597 : Integer.Sparse Key := [(key504, -6), (key666, -6), (key498, -6), (key498, -6), (key562, 2), (key683, 2), (key552, 2), (key562, 2), (key683, 2), (key232, 2), (key666, 2), (key226, 2), (key498, 2), (key552, 2), (key226, 2), (key498, 2)]

def rawRow12598 : Integer.Sparse Key := [(key666, -6), (key504, -6), (key498, -6), (key498, -6), (key683, 2), (key562, 2), (key552, 2), (key683, 2), (key562, 2), (key666, 2), (key232, 2), (key498, 2), (key226, 2), (key552, 2), (key498, 2), (key226, 2)]

def rawRow12599 : Integer.Sparse Key := [(key552, -6), (key562, -6), (key562, -6), (key683, -6), (key226, 2), (key232, 2), (key232, 2), (key498, 2), (key504, 2), (key498, 2), (key562, 2), (key504, 2), (key562, 2), (key666, 2), (key666, 2), (key683, 2)]

def rawRow12600 : Integer.Sparse Key := [(key562, -6), (key552, -6), (key562, -6), (key683, -6), (key232, 2), (key226, 2), (key232, 2), (key504, 2), (key498, 2), (key562, 2), (key498, 2), (key562, 2), (key504, 2), (key666, 2), (key683, 2), (key666, 2)]

def rawRow12601 : Integer.Sparse Key := [(key562, -6), (key562, -6), (key552, -6), (key683, -6), (key232, 2), (key232, 2), (key226, 2), (key562, 2), (key562, 2), (key504, 2), (key504, 2), (key498, 2), (key498, 2), (key683, 2), (key666, 2), (key666, 2)]

def rawRow12602 : Integer.Sparse Key := [(key552, -6), (key562, -6), (key683, -6), (key562, -6), (key498, 2), (key504, 2), (key666, 2), (key226, 2), (key232, 2), (key498, 2), (key562, 2), (key666, 2), (key683, 2), (key232, 2), (key504, 2), (key562, 2)]

def rawRow12603 : Integer.Sparse Key := [(key562, -6), (key552, -6), (key683, -6), (key562, -6), (key504, 2), (key498, 2), (key666, 2), (key232, 2), (key226, 2), (key562, 2), (key498, 2), (key683, 2), (key666, 2), (key232, 2), (key562, 2), (key504, 2)]

def rawRow12604 : Integer.Sparse Key := [(key552, -6), (key683, -6), (key562, -6), (key562, -6), (key498, 2), (key666, 2), (key504, 2), (key498, 2), (key666, 2), (key226, 2), (key683, 2), (key232, 2), (key562, 2), (key504, 2), (key232, 2), (key562, 2)]

def rawRow12605 : Integer.Sparse Key := [(key683, -6), (key552, -6), (key562, -6), (key562, -6), (key666, 2), (key498, 2), (key504, 2), (key666, 2), (key498, 2), (key683, 2), (key226, 2), (key562, 2), (key232, 2), (key504, 2), (key562, 2), (key232, 2)]

def rawRow12606 : Integer.Sparse Key := [(key562, -6), (key683, -6), (key552, -6), (key562, -6), (key504, 2), (key666, 2), (key498, 2), (key562, 2), (key683, 2), (key232, 2), (key666, 2), (key226, 2), (key498, 2), (key562, 2), (key232, 2), (key504, 2)]

def rawRow12607 : Integer.Sparse Key := [(key683, -6), (key562, -6), (key552, -6), (key562, -6), (key666, 2), (key504, 2), (key498, 2), (key683, 2), (key562, 2), (key666, 2), (key232, 2), (key498, 2), (key226, 2), (key562, 2), (key504, 2), (key232, 2)]

def rawRow12608 : Integer.Sparse Key := [(key562, -6), (key562, -6), (key683, -6), (key552, -6), (key562, 2), (key562, 2), (key683, 2), (key232, 2), (key232, 2), (key504, 2), (key504, 2), (key666, 2), (key666, 2), (key226, 2), (key498, 2), (key498, 2)]

def rawRow12609 : Integer.Sparse Key := [(key562, -6), (key683, -6), (key562, -6), (key552, -6), (key562, 2), (key683, 2), (key562, 2), (key504, 2), (key666, 2), (key232, 2), (key666, 2), (key232, 2), (key504, 2), (key498, 2), (key226, 2), (key498, 2)]

def rawRow12610 : Integer.Sparse Key := [(key683, -6), (key562, -6), (key562, -6), (key552, -6), (key683, 2), (key562, 2), (key562, 2), (key666, 2), (key504, 2), (key666, 2), (key232, 2), (key504, 2), (key232, 2), (key498, 2), (key498, 2), (key226, 2)]

def rawRow12611 : Integer.Sparse Key := [(key1368, -6), (key1720, -6), (key1744, -6), (key1744, -6), (key1368, 2), (key1377, 2), (key1377, 2), (key1494, 2), (key1516, 2), (key1516, 2), (key1726, 2), (key1726, 2), (key1744, 2), (key1744, 2), (key1755, 2), (key1755, 2)]

def rawRow12612 : Integer.Sparse Key := [(key1368, -6), (key1744, -6), (key1720, -6), (key1744, -6), (key1377, 2), (key1368, 2), (key1377, 2), (key1516, 2), (key1494, 2), (key1516, 2), (key1744, 2), (key1755, 2), (key1726, 2), (key1755, 2), (key1726, 2), (key1744, 2)]

def rawRow12613 : Integer.Sparse Key := [(key1368, -6), (key1744, -6), (key1744, -6), (key1720, -6), (key1377, 2), (key1377, 2), (key1368, 2), (key1516, 2), (key1516, 2), (key1494, 2), (key1755, 2), (key1744, 2), (key1755, 2), (key1726, 2), (key1744, 2), (key1726, 2)]

def rawRow12614 : Integer.Sparse Key := [(key1720, -6), (key1368, -6), (key1744, -6), (key1744, -6), (key1494, 2), (key1726, 2), (key1726, 2), (key1368, 2), (key1744, 2), (key1744, 2), (key1377, 2), (key1377, 2), (key1516, 2), (key1516, 2), (key1755, 2), (key1755, 2)]

def rawRow12615 : Integer.Sparse Key := [(key1720, -6), (key1744, -6), (key1368, -6), (key1744, -6), (key1726, 2), (key1494, 2), (key1726, 2), (key1744, 2), (key1368, 2), (key1744, 2), (key1516, 2), (key1755, 2), (key1377, 2), (key1755, 2), (key1377, 2), (key1516, 2)]

def rawRow12616 : Integer.Sparse Key := [(key1720, -6), (key1744, -6), (key1744, -6), (key1368, -6), (key1726, 2), (key1726, 2), (key1494, 2), (key1744, 2), (key1744, 2), (key1368, 2), (key1755, 2), (key1516, 2), (key1755, 2), (key1377, 2), (key1516, 2), (key1377, 2)]

def rawRow12617 : Integer.Sparse Key := [(key1744, -6), (key1368, -6), (key1720, -6), (key1744, -6), (key1516, 2), (key1744, 2), (key1755, 2), (key1377, 2), (key1726, 2), (key1755, 2), (key1368, 2), (key1377, 2), (key1494, 2), (key1516, 2), (key1726, 2), (key1744, 2)]

def rawRow12618 : Integer.Sparse Key := [(key1744, -6), (key1368, -6), (key1744, -6), (key1720, -6), (key1516, 2), (key1755, 2), (key1744, 2), (key1377, 2), (key1755, 2), (key1726, 2), (key1377, 2), (key1368, 2), (key1516, 2), (key1494, 2), (key1744, 2), (key1726, 2)]

def rawRow12619 : Integer.Sparse Key := [(key1744, -6), (key1720, -6), (key1368, -6), (key1744, -6), (key1744, 2), (key1516, 2), (key1755, 2), (key1726, 2), (key1377, 2), (key1755, 2), (key1494, 2), (key1726, 2), (key1368, 2), (key1744, 2), (key1377, 2), (key1516, 2)]

def rawRow12620 : Integer.Sparse Key := [(key1744, -6), (key1720, -6), (key1744, -6), (key1368, -6), (key1744, 2), (key1755, 2), (key1516, 2), (key1726, 2), (key1755, 2), (key1377, 2), (key1726, 2), (key1494, 2), (key1744, 2), (key1368, 2), (key1516, 2), (key1377, 2)]

def rawRow12621 : Integer.Sparse Key := [(key1744, -6), (key1744, -6), (key1368, -6), (key1720, -6), (key1755, 2), (key1516, 2), (key1744, 2), (key1755, 2), (key1377, 2), (key1726, 2), (key1516, 2), (key1744, 2), (key1377, 2), (key1726, 2), (key1368, 2), (key1494, 2)]

def rawRow12622 : Integer.Sparse Key := [(key1744, -6), (key1744, -6), (key1720, -6), (key1368, -6), (key1755, 2), (key1744, 2), (key1516, 2), (key1755, 2), (key1726, 2), (key1377, 2), (key1744, 2), (key1516, 2), (key1726, 2), (key1377, 2), (key1494, 2), (key1368, 2)]

def rawRow12623 : Integer.Sparse Key := [(key1377, -6), (key1726, -6), (key1726, -6), (key1755, -6), (key1368, 2), (key1368, 2), (key1377, 2), (key1494, 2), (key1494, 2), (key1516, 2), (key1720, 2), (key1726, 2), (key1720, 2), (key1744, 2), (key1726, 2), (key1744, 2)]

def rawRow12624 : Integer.Sparse Key := [(key1377, -6), (key1726, -6), (key1755, -6), (key1726, -6), (key1368, 2), (key1377, 2), (key1368, 2), (key1494, 2), (key1516, 2), (key1494, 2), (key1726, 2), (key1720, 2), (key1744, 2), (key1720, 2), (key1744, 2), (key1726, 2)]

def rawRow12625 : Integer.Sparse Key := [(key1377, -6), (key1755, -6), (key1726, -6), (key1726, -6), (key1377, 2), (key1368, 2), (key1368, 2), (key1516, 2), (key1494, 2), (key1494, 2), (key1744, 2), (key1744, 2), (key1726, 2), (key1726, 2), (key1720, 2), (key1720, 2)]

def rawRow12626 : Integer.Sparse Key := [(key1726, -6), (key1377, -6), (key1726, -6), (key1755, -6), (key1494, 2), (key1720, 2), (key1726, 2), (key1368, 2), (key1720, 2), (key1744, 2), (key1368, 2), (key1377, 2), (key1494, 2), (key1516, 2), (key1726, 2), (key1744, 2)]

def rawRow12627 : Integer.Sparse Key := [(key1726, -6), (key1377, -6), (key1755, -6), (key1726, -6), (key1494, 2), (key1726, 2), (key1720, 2), (key1368, 2), (key1744, 2), (key1720, 2), (key1377, 2), (key1368, 2), (key1516, 2), (key1494, 2), (key1744, 2), (key1726, 2)]

def rawRow12628 : Integer.Sparse Key := [(key1726, -6), (key1726, -6), (key1377, -6), (key1755, -6), (key1720, 2), (key1494, 2), (key1726, 2), (key1720, 2), (key1368, 2), (key1744, 2), (key1494, 2), (key1726, 2), (key1368, 2), (key1744, 2), (key1377, 2), (key1516, 2)]

def rawRow12629 : Integer.Sparse Key := [(key1726, -6), (key1726, -6), (key1755, -6), (key1377, -6), (key1720, 2), (key1726, 2), (key1494, 2), (key1720, 2), (key1744, 2), (key1368, 2), (key1726, 2), (key1494, 2), (key1744, 2), (key1368, 2), (key1516, 2), (key1377, 2)]

def rawRow12630 : Integer.Sparse Key := [(key1726, -6), (key1755, -6), (key1377, -6), (key1726, -6), (key1726, 2), (key1494, 2), (key1720, 2), (key1744, 2), (key1368, 2), (key1720, 2), (key1516, 2), (key1744, 2), (key1377, 2), (key1726, 2), (key1368, 2), (key1494, 2)]

def rawRow12631 : Integer.Sparse Key := [(key1726, -6), (key1755, -6), (key1726, -6), (key1377, -6), (key1726, 2), (key1720, 2), (key1494, 2), (key1744, 2), (key1720, 2), (key1368, 2), (key1744, 2), (key1516, 2), (key1726, 2), (key1377, 2), (key1494, 2), (key1368, 2)]

def rawRow12632 : Integer.Sparse Key := [(key1755, -6), (key1377, -6), (key1726, -6), (key1726, -6), (key1516, 2), (key1744, 2), (key1744, 2), (key1377, 2), (key1726, 2), (key1726, 2), (key1368, 2), (key1368, 2), (key1494, 2), (key1494, 2), (key1720, 2), (key1720, 2)]

def rawRow12633 : Integer.Sparse Key := [(key1755, -6), (key1726, -6), (key1377, -6), (key1726, -6), (key1744, 2), (key1516, 2), (key1744, 2), (key1726, 2), (key1377, 2), (key1726, 2), (key1494, 2), (key1720, 2), (key1368, 2), (key1720, 2), (key1368, 2), (key1494, 2)]

def rawRow12634 : Integer.Sparse Key := [(key1755, -6), (key1726, -6), (key1726, -6), (key1377, -6), (key1744, 2), (key1744, 2), (key1516, 2), (key1726, 2), (key1726, 2), (key1377, 2), (key1720, 2), (key1494, 2), (key1720, 2), (key1368, 2), (key1494, 2), (key1368, 2)]

def rawRow12635 : Integer.Sparse Key := [(key1702, -6), (key1702, -6), (key1708, -6), (key1935, -6), (key1279, 2), (key1279, 2), (key1285, 2), (key1702, 2), (key1702, 2), (key1752, 2), (key1752, 2), (key1758, 2), (key1758, 2), (key1935, 2), (key1955, 2), (key1955, 2)]

def rawRow12636 : Integer.Sparse Key := [(key1702, -6), (key1708, -6), (key1702, -6), (key1935, -6), (key1279, 2), (key1285, 2), (key1279, 2), (key1752, 2), (key1758, 2), (key1702, 2), (key1758, 2), (key1702, 2), (key1752, 2), (key1955, 2), (key1935, 2), (key1955, 2)]

def rawRow12637 : Integer.Sparse Key := [(key1708, -6), (key1702, -6), (key1702, -6), (key1935, -6), (key1285, 2), (key1279, 2), (key1279, 2), (key1758, 2), (key1752, 2), (key1758, 2), (key1702, 2), (key1752, 2), (key1702, 2), (key1955, 2), (key1955, 2), (key1935, 2)]

def rawRow12638 : Integer.Sparse Key := [(key1702, -6), (key1702, -6), (key1935, -6), (key1708, -6), (key1702, 2), (key1702, 2), (key1935, 2), (key1279, 2), (key1279, 2), (key1752, 2), (key1752, 2), (key1955, 2), (key1955, 2), (key1285, 2), (key1758, 2), (key1758, 2)]

def rawRow12639 : Integer.Sparse Key := [(key1702, -6), (key1935, -6), (key1702, -6), (key1708, -6), (key1702, 2), (key1935, 2), (key1702, 2), (key1752, 2), (key1955, 2), (key1279, 2), (key1955, 2), (key1279, 2), (key1752, 2), (key1758, 2), (key1285, 2), (key1758, 2)]

def rawRow12640 : Integer.Sparse Key := [(key1935, -6), (key1702, -6), (key1702, -6), (key1708, -6), (key1935, 2), (key1702, 2), (key1702, 2), (key1955, 2), (key1752, 2), (key1955, 2), (key1279, 2), (key1752, 2), (key1279, 2), (key1758, 2), (key1758, 2), (key1285, 2)]

def rawRow12641 : Integer.Sparse Key := [(key1702, -6), (key1708, -6), (key1935, -6), (key1702, -6), (key1752, 2), (key1758, 2), (key1955, 2), (key1279, 2), (key1285, 2), (key1702, 2), (key1758, 2), (key1935, 2), (key1955, 2), (key1279, 2), (key1702, 2), (key1752, 2)]

def rawRow12642 : Integer.Sparse Key := [(key1708, -6), (key1702, -6), (key1935, -6), (key1702, -6), (key1758, 2), (key1752, 2), (key1955, 2), (key1285, 2), (key1279, 2), (key1758, 2), (key1702, 2), (key1955, 2), (key1935, 2), (key1279, 2), (key1752, 2), (key1702, 2)]

def rawRow12643 : Integer.Sparse Key := [(key1702, -6), (key1935, -6), (key1708, -6), (key1702, -6), (key1752, 2), (key1955, 2), (key1758, 2), (key1702, 2), (key1935, 2), (key1279, 2), (key1955, 2), (key1285, 2), (key1758, 2), (key1702, 2), (key1279, 2), (key1752, 2)]

def rawRow12644 : Integer.Sparse Key := [(key1935, -6), (key1702, -6), (key1708, -6), (key1702, -6), (key1955, 2), (key1752, 2), (key1758, 2), (key1935, 2), (key1702, 2), (key1955, 2), (key1279, 2), (key1758, 2), (key1285, 2), (key1702, 2), (key1752, 2), (key1279, 2)]

def rawRow12645 : Integer.Sparse Key := [(key1708, -6), (key1935, -6), (key1702, -6), (key1702, -6), (key1758, 2), (key1955, 2), (key1752, 2), (key1758, 2), (key1955, 2), (key1285, 2), (key1935, 2), (key1279, 2), (key1702, 2), (key1752, 2), (key1279, 2), (key1702, 2)]

def rawRow12646 : Integer.Sparse Key := [(key1935, -6), (key1708, -6), (key1702, -6), (key1702, -6), (key1955, 2), (key1758, 2), (key1752, 2), (key1955, 2), (key1758, 2), (key1935, 2), (key1285, 2), (key1702, 2), (key1279, 2), (key1752, 2), (key1702, 2), (key1279, 2)]

def rawRow12647 : Integer.Sparse Key := [(key1752, -6), (key1758, -6), (key1758, -6), (key1955, -6), (key1279, 2), (key1285, 2), (key1285, 2), (key1702, 2), (key1708, 2), (key1702, 2), (key1758, 2), (key1708, 2), (key1758, 2), (key1935, 2), (key1935, 2), (key1955, 2)]

def rawRow12648 : Integer.Sparse Key := [(key1758, -6), (key1752, -6), (key1758, -6), (key1955, -6), (key1285, 2), (key1279, 2), (key1285, 2), (key1708, 2), (key1702, 2), (key1758, 2), (key1702, 2), (key1758, 2), (key1708, 2), (key1935, 2), (key1955, 2), (key1935, 2)]

def rawRow12649 : Integer.Sparse Key := [(key1758, -6), (key1758, -6), (key1752, -6), (key1955, -6), (key1285, 2), (key1285, 2), (key1279, 2), (key1758, 2), (key1758, 2), (key1708, 2), (key1708, 2), (key1702, 2), (key1702, 2), (key1955, 2), (key1935, 2), (key1935, 2)]

def rawRow12650 : Integer.Sparse Key := [(key1752, -6), (key1758, -6), (key1955, -6), (key1758, -6), (key1702, 2), (key1708, 2), (key1935, 2), (key1279, 2), (key1285, 2), (key1702, 2), (key1758, 2), (key1935, 2), (key1955, 2), (key1285, 2), (key1708, 2), (key1758, 2)]

def rawRow12651 : Integer.Sparse Key := [(key1758, -6), (key1752, -6), (key1955, -6), (key1758, -6), (key1708, 2), (key1702, 2), (key1935, 2), (key1285, 2), (key1279, 2), (key1758, 2), (key1702, 2), (key1955, 2), (key1935, 2), (key1285, 2), (key1758, 2), (key1708, 2)]

def rawRow12652 : Integer.Sparse Key := [(key1752, -6), (key1955, -6), (key1758, -6), (key1758, -6), (key1702, 2), (key1935, 2), (key1708, 2), (key1702, 2), (key1935, 2), (key1279, 2), (key1955, 2), (key1285, 2), (key1758, 2), (key1708, 2), (key1285, 2), (key1758, 2)]

def rawRow12653 : Integer.Sparse Key := [(key1955, -6), (key1752, -6), (key1758, -6), (key1758, -6), (key1935, 2), (key1702, 2), (key1708, 2), (key1935, 2), (key1702, 2), (key1955, 2), (key1279, 2), (key1758, 2), (key1285, 2), (key1708, 2), (key1758, 2), (key1285, 2)]

def rawRow12654 : Integer.Sparse Key := [(key1758, -6), (key1955, -6), (key1752, -6), (key1758, -6), (key1708, 2), (key1935, 2), (key1702, 2), (key1758, 2), (key1955, 2), (key1285, 2), (key1935, 2), (key1279, 2), (key1702, 2), (key1758, 2), (key1285, 2), (key1708, 2)]

def rawRow12655 : Integer.Sparse Key := [(key1955, -6), (key1758, -6), (key1752, -6), (key1758, -6), (key1935, 2), (key1708, 2), (key1702, 2), (key1955, 2), (key1758, 2), (key1935, 2), (key1285, 2), (key1702, 2), (key1279, 2), (key1758, 2), (key1708, 2), (key1285, 2)]

def rawRow12656 : Integer.Sparse Key := [(key1758, -6), (key1758, -6), (key1955, -6), (key1752, -6), (key1758, 2), (key1758, 2), (key1955, 2), (key1285, 2), (key1285, 2), (key1708, 2), (key1708, 2), (key1935, 2), (key1935, 2), (key1279, 2), (key1702, 2), (key1702, 2)]

def rawRow12657 : Integer.Sparse Key := [(key1758, -6), (key1955, -6), (key1758, -6), (key1752, -6), (key1758, 2), (key1955, 2), (key1758, 2), (key1708, 2), (key1935, 2), (key1285, 2), (key1935, 2), (key1285, 2), (key1708, 2), (key1702, 2), (key1279, 2), (key1702, 2)]

def rawRow12658 : Integer.Sparse Key := [(key1955, -6), (key1758, -6), (key1758, -6), (key1752, -6), (key1955, 2), (key1758, 2), (key1758, 2), (key1935, 2), (key1708, 2), (key1935, 2), (key1285, 2), (key1708, 2), (key1285, 2), (key1702, 2), (key1702, 2), (key1279, 2)]

def rawRow12659 : Integer.Sparse Key := [(key1365, -2), (key1365, -2), (key1371, -2), (key1717, -2), (key1717, -2), (key1742, -2), (key1742, -2), (key1748, -2), (key1748, -2), (key1939, -2), (key1951, -2), (key1951, -2), (key1365, 1), (key1365, 1), (key1375, 1), (key1375, 1), (key1380, 1), (key1380, 1), (key1491, 1), (key1491, 1), (key1514, 1), (key1514, 1), (key1520, 1), (key1520, 1), (key1724, 1), (key1724, 1), (key1742, 1), (key1742, 1), (key1759, 1), (key1759, 1), (key1942, 1), (key1942, 1), (key1951, 1), (key1951, 1), (key1956, 1), (key1956, 1)]

def rawRow12660 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1365, -2), (key1742, -2), (key1748, -2), (key1717, -2), (key1748, -2), (key1717, -2), (key1742, -2), (key1951, -2), (key1939, -2), (key1951, -2), (key1375, 1), (key1380, 1), (key1365, 1), (key1380, 1), (key1365, 1), (key1375, 1), (key1514, 1), (key1520, 1), (key1491, 1), (key1520, 1), (key1491, 1), (key1514, 1), (key1742, 1), (key1759, 1), (key1724, 1), (key1759, 1), (key1724, 1), (key1742, 1), (key1951, 1), (key1956, 1), (key1942, 1), (key1956, 1), (key1942, 1), (key1951, 1)]

def rawRow12661 : Integer.Sparse Key := [(key1371, -2), (key1365, -2), (key1365, -2), (key1748, -2), (key1742, -2), (key1748, -2), (key1717, -2), (key1742, -2), (key1717, -2), (key1951, -2), (key1951, -2), (key1939, -2), (key1380, 1), (key1375, 1), (key1380, 1), (key1365, 1), (key1375, 1), (key1365, 1), (key1520, 1), (key1514, 1), (key1520, 1), (key1491, 1), (key1514, 1), (key1491, 1), (key1759, 1), (key1742, 1), (key1759, 1), (key1724, 1), (key1742, 1), (key1724, 1), (key1956, 1), (key1951, 1), (key1956, 1), (key1942, 1), (key1951, 1), (key1942, 1)]

def rawRow12662 : Integer.Sparse Key := [(key1717, -2), (key1717, -2), (key1939, -2), (key1365, -2), (key1365, -2), (key1742, -2), (key1742, -2), (key1951, -2), (key1951, -2), (key1371, -2), (key1748, -2), (key1748, -2), (key1491, 1), (key1491, 1), (key1724, 1), (key1724, 1), (key1942, 1), (key1942, 1), (key1365, 1), (key1365, 1), (key1742, 1), (key1742, 1), (key1951, 1), (key1951, 1), (key1375, 1), (key1375, 1), (key1514, 1), (key1514, 1), (key1956, 1), (key1956, 1), (key1380, 1), (key1380, 1), (key1520, 1), (key1520, 1), (key1759, 1), (key1759, 1)]

def rawRow12663 : Integer.Sparse Key := [(key1717, -2), (key1939, -2), (key1717, -2), (key1742, -2), (key1951, -2), (key1365, -2), (key1951, -2), (key1365, -2), (key1742, -2), (key1748, -2), (key1371, -2), (key1748, -2), (key1724, 1), (key1942, 1), (key1491, 1), (key1942, 1), (key1491, 1), (key1724, 1), (key1742, 1), (key1951, 1), (key1365, 1), (key1951, 1), (key1365, 1), (key1742, 1), (key1514, 1), (key1956, 1), (key1375, 1), (key1956, 1), (key1375, 1), (key1514, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1759, 1), (key1380, 1), (key1520, 1)]

def rawRow12664 : Integer.Sparse Key := [(key1939, -2), (key1717, -2), (key1717, -2), (key1951, -2), (key1742, -2), (key1951, -2), (key1365, -2), (key1742, -2), (key1365, -2), (key1748, -2), (key1748, -2), (key1371, -2), (key1942, 1), (key1724, 1), (key1942, 1), (key1491, 1), (key1724, 1), (key1491, 1), (key1951, 1), (key1742, 1), (key1951, 1), (key1365, 1), (key1742, 1), (key1365, 1), (key1956, 1), (key1514, 1), (key1956, 1), (key1375, 1), (key1514, 1), (key1375, 1), (key1759, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1380, 1)]

def rawRow12665 : Integer.Sparse Key := [(key1742, -2), (key1748, -2), (key1951, -2), (key1365, -2), (key1371, -2), (key1717, -2), (key1748, -2), (key1939, -2), (key1951, -2), (key1365, -2), (key1717, -2), (key1742, -2), (key1514, 1), (key1520, 1), (key1742, 1), (key1759, 1), (key1951, 1), (key1956, 1), (key1375, 1), (key1380, 1), (key1724, 1), (key1759, 1), (key1942, 1), (key1956, 1), (key1365, 1), (key1380, 1), (key1491, 1), (key1520, 1), (key1942, 1), (key1951, 1), (key1365, 1), (key1375, 1), (key1491, 1), (key1514, 1), (key1724, 1), (key1742, 1)]

def rawRow12666 : Integer.Sparse Key := [(key1748, -2), (key1742, -2), (key1951, -2), (key1371, -2), (key1365, -2), (key1748, -2), (key1717, -2), (key1951, -2), (key1939, -2), (key1365, -2), (key1742, -2), (key1717, -2), (key1520, 1), (key1514, 1), (key1759, 1), (key1742, 1), (key1956, 1), (key1951, 1), (key1380, 1), (key1375, 1), (key1759, 1), (key1724, 1), (key1956, 1), (key1942, 1), (key1380, 1), (key1365, 1), (key1520, 1), (key1491, 1), (key1951, 1), (key1942, 1), (key1375, 1), (key1365, 1), (key1514, 1), (key1491, 1), (key1742, 1), (key1724, 1)]

def rawRow12667 : Integer.Sparse Key := [(key1742, -2), (key1951, -2), (key1748, -2), (key1717, -2), (key1939, -2), (key1365, -2), (key1951, -2), (key1371, -2), (key1748, -2), (key1717, -2), (key1365, -2), (key1742, -2), (key1742, 1), (key1951, 1), (key1514, 1), (key1956, 1), (key1520, 1), (key1759, 1), (key1724, 1), (key1942, 1), (key1375, 1), (key1956, 1), (key1380, 1), (key1759, 1), (key1491, 1), (key1942, 1), (key1365, 1), (key1951, 1), (key1380, 1), (key1520, 1), (key1491, 1), (key1724, 1), (key1365, 1), (key1742, 1), (key1375, 1), (key1514, 1)]

def rawRow12668 : Integer.Sparse Key := [(key1951, -2), (key1742, -2), (key1748, -2), (key1939, -2), (key1717, -2), (key1951, -2), (key1365, -2), (key1748, -2), (key1371, -2), (key1717, -2), (key1742, -2), (key1365, -2), (key1951, 1), (key1742, 1), (key1956, 1), (key1514, 1), (key1759, 1), (key1520, 1), (key1942, 1), (key1724, 1), (key1956, 1), (key1375, 1), (key1759, 1), (key1380, 1), (key1942, 1), (key1491, 1), (key1951, 1), (key1365, 1), (key1520, 1), (key1380, 1), (key1724, 1), (key1491, 1), (key1742, 1), (key1365, 1), (key1514, 1), (key1375, 1)]

def rawRow12669 : Integer.Sparse Key := [(key1748, -2), (key1951, -2), (key1742, -2), (key1748, -2), (key1951, -2), (key1371, -2), (key1939, -2), (key1365, -2), (key1717, -2), (key1742, -2), (key1365, -2), (key1717, -2), (key1759, 1), (key1956, 1), (key1520, 1), (key1951, 1), (key1514, 1), (key1742, 1), (key1759, 1), (key1956, 1), (key1380, 1), (key1942, 1), (key1375, 1), (key1724, 1), (key1520, 1), (key1951, 1), (key1380, 1), (key1942, 1), (key1365, 1), (key1491, 1), (key1514, 1), (key1742, 1), (key1375, 1), (key1724, 1), (key1365, 1), (key1491, 1)]

def rawRow12670 : Integer.Sparse Key := [(key1951, -2), (key1748, -2), (key1742, -2), (key1951, -2), (key1748, -2), (key1939, -2), (key1371, -2), (key1717, -2), (key1365, -2), (key1742, -2), (key1717, -2), (key1365, -2), (key1956, 1), (key1759, 1), (key1951, 1), (key1520, 1), (key1742, 1), (key1514, 1), (key1956, 1), (key1759, 1), (key1942, 1), (key1380, 1), (key1724, 1), (key1375, 1), (key1951, 1), (key1520, 1), (key1942, 1), (key1380, 1), (key1491, 1), (key1365, 1), (key1742, 1), (key1514, 1), (key1724, 1), (key1375, 1), (key1491, 1), (key1365, 1)]

def rawRow12671 : Integer.Sparse Key := [(key1375, -2), (key1380, -2), (key1380, -2), (key1724, -2), (key1729, -2), (key1724, -2), (key1759, -2), (key1729, -2), (key1759, -2), (key1942, -2), (key1942, -2), (key1956, -2), (key1365, 1), (key1371, 1), (key1365, 1), (key1380, 1), (key1371, 1), (key1380, 1), (key1491, 1), (key1497, 1), (key1491, 1), (key1520, 1), (key1497, 1), (key1520, 1), (key1717, 1), (key1729, 1), (key1717, 1), (key1748, 1), (key1729, 1), (key1748, 1), (key1939, 1), (key1942, 1), (key1939, 1), (key1951, 1), (key1942, 1), (key1951, 1)]

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

def rawRow12672 : Integer.Sparse Key := [(key1380, -2), (key1375, -2), (key1380, -2), (key1729, -2), (key1724, -2), (key1759, -2), (key1724, -2), (key1759, -2), (key1729, -2), (key1942, -2), (key1956, -2), (key1942, -2), (key1371, 1), (key1365, 1), (key1380, 1), (key1365, 1), (key1380, 1), (key1371, 1), (key1497, 1), (key1491, 1), (key1520, 1), (key1491, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1717, 1), (key1748, 1), (key1717, 1), (key1748, 1), (key1729, 1), (key1942, 1), (key1939, 1), (key1951, 1), (key1939, 1), (key1951, 1), (key1942, 1)]

def rawRow12673 : Integer.Sparse Key := [(key1380, -2), (key1380, -2), (key1375, -2), (key1759, -2), (key1759, -2), (key1729, -2), (key1729, -2), (key1724, -2), (key1724, -2), (key1956, -2), (key1942, -2), (key1942, -2), (key1380, 1), (key1380, 1), (key1371, 1), (key1371, 1), (key1365, 1), (key1365, 1), (key1520, 1), (key1520, 1), (key1497, 1), (key1497, 1), (key1491, 1), (key1491, 1), (key1748, 1), (key1748, 1), (key1729, 1), (key1729, 1), (key1717, 1), (key1717, 1), (key1951, 1), (key1951, 1), (key1942, 1), (key1942, 1), (key1939, 1), (key1939, 1)]

def rawRow12674 : Integer.Sparse Key := [(key1724, -2), (key1729, -2), (key1942, -2), (key1375, -2), (key1380, -2), (key1724, -2), (key1759, -2), (key1942, -2), (key1956, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1491, 1), (key1497, 1), (key1717, 1), (key1729, 1), (key1939, 1), (key1942, 1), (key1365, 1), (key1371, 1), (key1717, 1), (key1748, 1), (key1939, 1), (key1951, 1), (key1365, 1), (key1380, 1), (key1491, 1), (key1520, 1), (key1942, 1), (key1951, 1), (key1371, 1), (key1380, 1), (key1497, 1), (key1520, 1), (key1729, 1), (key1748, 1)]

def rawRow12675 : Integer.Sparse Key := [(key1729, -2), (key1724, -2), (key1942, -2), (key1380, -2), (key1375, -2), (key1759, -2), (key1724, -2), (key1956, -2), (key1942, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1497, 1), (key1491, 1), (key1729, 1), (key1717, 1), (key1942, 1), (key1939, 1), (key1371, 1), (key1365, 1), (key1748, 1), (key1717, 1), (key1951, 1), (key1939, 1), (key1380, 1), (key1365, 1), (key1520, 1), (key1491, 1), (key1951, 1), (key1942, 1), (key1380, 1), (key1371, 1), (key1520, 1), (key1497, 1), (key1748, 1), (key1729, 1)]

def rawRow12676 : Integer.Sparse Key := [(key1724, -2), (key1942, -2), (key1729, -2), (key1724, -2), (key1942, -2), (key1375, -2), (key1956, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1759, -2), (key1717, 1), (key1939, 1), (key1491, 1), (key1942, 1), (key1497, 1), (key1729, 1), (key1717, 1), (key1939, 1), (key1365, 1), (key1951, 1), (key1371, 1), (key1748, 1), (key1491, 1), (key1942, 1), (key1365, 1), (key1951, 1), (key1380, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1371, 1), (key1748, 1), (key1380, 1), (key1520, 1)]

def rawRow12677 : Integer.Sparse Key := [(key1942, -2), (key1724, -2), (key1729, -2), (key1942, -2), (key1724, -2), (key1956, -2), (key1375, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1380, -2), (key1939, 1), (key1717, 1), (key1942, 1), (key1491, 1), (key1729, 1), (key1497, 1), (key1939, 1), (key1717, 1), (key1951, 1), (key1365, 1), (key1748, 1), (key1371, 1), (key1942, 1), (key1491, 1), (key1951, 1), (key1365, 1), (key1520, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1748, 1), (key1371, 1), (key1520, 1), (key1380, 1)]

def rawRow12678 : Integer.Sparse Key := [(key1729, -2), (key1942, -2), (key1724, -2), (key1759, -2), (key1956, -2), (key1380, -2), (key1942, -2), (key1375, -2), (key1724, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1729, 1), (key1942, 1), (key1497, 1), (key1939, 1), (key1491, 1), (key1717, 1), (key1748, 1), (key1951, 1), (key1371, 1), (key1939, 1), (key1365, 1), (key1717, 1), (key1520, 1), (key1951, 1), (key1380, 1), (key1942, 1), (key1365, 1), (key1491, 1), (key1520, 1), (key1748, 1), (key1380, 1), (key1729, 1), (key1371, 1), (key1497, 1)]

def rawRow12679 : Integer.Sparse Key := [(key1942, -2), (key1729, -2), (key1724, -2), (key1956, -2), (key1759, -2), (key1942, -2), (key1380, -2), (key1724, -2), (key1375, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1942, 1), (key1729, 1), (key1939, 1), (key1497, 1), (key1717, 1), (key1491, 1), (key1951, 1), (key1748, 1), (key1939, 1), (key1371, 1), (key1717, 1), (key1365, 1), (key1951, 1), (key1520, 1), (key1942, 1), (key1380, 1), (key1491, 1), (key1365, 1), (key1748, 1), (key1520, 1), (key1729, 1), (key1380, 1), (key1497, 1), (key1371, 1)]

def rawRow12680 : Integer.Sparse Key := [(key1759, -2), (key1759, -2), (key1956, -2), (key1380, -2), (key1380, -2), (key1729, -2), (key1729, -2), (key1942, -2), (key1942, -2), (key1375, -2), (key1724, -2), (key1724, -2), (key1520, 1), (key1520, 1), (key1748, 1), (key1748, 1), (key1951, 1), (key1951, 1), (key1380, 1), (key1380, 1), (key1729, 1), (key1729, 1), (key1942, 1), (key1942, 1), (key1371, 1), (key1371, 1), (key1497, 1), (key1497, 1), (key1939, 1), (key1939, 1), (key1365, 1), (key1365, 1), (key1491, 1), (key1491, 1), (key1717, 1), (key1717, 1)]

def rawRow12681 : Integer.Sparse Key := [(key1759, -2), (key1956, -2), (key1759, -2), (key1729, -2), (key1942, -2), (key1380, -2), (key1942, -2), (key1380, -2), (key1729, -2), (key1724, -2), (key1375, -2), (key1724, -2), (key1748, 1), (key1951, 1), (key1520, 1), (key1951, 1), (key1520, 1), (key1748, 1), (key1729, 1), (key1942, 1), (key1380, 1), (key1942, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1939, 1), (key1371, 1), (key1939, 1), (key1371, 1), (key1497, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1717, 1), (key1365, 1), (key1491, 1)]

def rawRow12682 : Integer.Sparse Key := [(key1956, -2), (key1759, -2), (key1759, -2), (key1942, -2), (key1729, -2), (key1942, -2), (key1380, -2), (key1729, -2), (key1380, -2), (key1724, -2), (key1724, -2), (key1375, -2), (key1951, 1), (key1748, 1), (key1951, 1), (key1520, 1), (key1748, 1), (key1520, 1), (key1942, 1), (key1729, 1), (key1942, 1), (key1380, 1), (key1729, 1), (key1380, 1), (key1939, 1), (key1497, 1), (key1939, 1), (key1371, 1), (key1497, 1), (key1371, 1), (key1717, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1491, 1), (key1365, 1)]

def rawRow12683 : Integer.Sparse Key := [(key1705, -24), (key1282, 6), (key1705, 6), (key1754, 6), (key1754, 6)]

def rawRow12684 : Integer.Sparse Key := [(key1705, -24), (key1282, 6), (key1754, 6), (key1705, 6), (key1754, 6)]

def rawRow12685 : Integer.Sparse Key := [(key1705, -24), (key1282, 6), (key1754, 6), (key1754, 6), (key1705, 6)]

def rawRow12686 : Integer.Sparse Key := [(key1705, -24), (key1705, 6), (key1282, 6), (key1754, 6), (key1754, 6)]

def rawRow12687 : Integer.Sparse Key := [(key1705, -24), (key1705, 6), (key1754, 6), (key1282, 6), (key1754, 6)]

def rawRow12688 : Integer.Sparse Key := [(key1705, -24), (key1705, 6), (key1754, 6), (key1754, 6), (key1282, 6)]

def rawRow12689 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1282, 6), (key1705, 6), (key1754, 6)]

def rawRow12690 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1282, 6), (key1754, 6), (key1705, 6)]

def rawRow12691 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1705, 6), (key1282, 6), (key1754, 6)]

def rawRow12692 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1705, 6), (key1754, 6), (key1282, 6)]

def rawRow12693 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1754, 6), (key1282, 6), (key1705, 6)]

def rawRow12694 : Integer.Sparse Key := [(key1705, -24), (key1754, 6), (key1754, 6), (key1705, 6), (key1282, 6)]

def rawRow12695 : Integer.Sparse Key := [(key1754, -24), (key1282, 6), (key1705, 6), (key1705, 6), (key1754, 6)]

def rawRow12696 : Integer.Sparse Key := [(key1754, -24), (key1282, 6), (key1705, 6), (key1754, 6), (key1705, 6)]

def rawRow12697 : Integer.Sparse Key := [(key1754, -24), (key1282, 6), (key1754, 6), (key1705, 6), (key1705, 6)]

def rawRow12698 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1282, 6), (key1705, 6), (key1754, 6)]

def rawRow12699 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1282, 6), (key1754, 6), (key1705, 6)]

def rawRow12700 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1705, 6), (key1282, 6), (key1754, 6)]

def rawRow12701 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1705, 6), (key1754, 6), (key1282, 6)]

def rawRow12702 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1754, 6), (key1282, 6), (key1705, 6)]

def rawRow12703 : Integer.Sparse Key := [(key1754, -24), (key1705, 6), (key1754, 6), (key1705, 6), (key1282, 6)]

def rawRow12704 : Integer.Sparse Key := [(key1754, -24), (key1754, 6), (key1282, 6), (key1705, 6), (key1705, 6)]

def rawRow12705 : Integer.Sparse Key := [(key1754, -24), (key1754, 6), (key1705, 6), (key1282, 6), (key1705, 6)]

def rawRow12706 : Integer.Sparse Key := [(key1754, -24), (key1754, 6), (key1705, 6), (key1705, 6), (key1282, 6)]

def rawRow12707 : Integer.Sparse Key := [(key1491, -2), (key1491, -2), (key1497, -2), (key1717, -2), (key1717, -2), (key1724, -2), (key1724, -2), (key1729, -2), (key1729, -2), (key1939, -2), (key1942, -2), (key1942, -2), (key1365, 2), (key1365, 2), (key1371, 2), (key1717, 2), (key1717, 2), (key1742, 2), (key1742, 2), (key1748, 2), (key1748, 2), (key1939, 2), (key1951, 2), (key1951, 2)]

def rawRow12708 : Integer.Sparse Key := [(key1491, -2), (key1497, -2), (key1491, -2), (key1724, -2), (key1729, -2), (key1717, -2), (key1729, -2), (key1717, -2), (key1724, -2), (key1942, -2), (key1939, -2), (key1942, -2), (key1365, 2), (key1371, 2), (key1365, 2), (key1742, 2), (key1748, 2), (key1717, 2), (key1748, 2), (key1717, 2), (key1742, 2), (key1951, 2), (key1939, 2), (key1951, 2)]

def rawRow12709 : Integer.Sparse Key := [(key1497, -2), (key1491, -2), (key1491, -2), (key1729, -2), (key1724, -2), (key1729, -2), (key1717, -2), (key1724, -2), (key1717, -2), (key1942, -2), (key1942, -2), (key1939, -2), (key1371, 2), (key1365, 2), (key1365, 2), (key1748, 2), (key1742, 2), (key1748, 2), (key1717, 2), (key1742, 2), (key1717, 2), (key1951, 2), (key1951, 2), (key1939, 2)]

def rawRow12710 : Integer.Sparse Key := [(key1717, -2), (key1717, -2), (key1939, -2), (key1491, -2), (key1491, -2), (key1724, -2), (key1724, -2), (key1942, -2), (key1942, -2), (key1497, -2), (key1729, -2), (key1729, -2), (key1717, 2), (key1717, 2), (key1939, 2), (key1365, 2), (key1365, 2), (key1742, 2), (key1742, 2), (key1951, 2), (key1951, 2), (key1371, 2), (key1748, 2), (key1748, 2)]

def rawRow12711 : Integer.Sparse Key := [(key1717, -2), (key1939, -2), (key1717, -2), (key1724, -2), (key1942, -2), (key1491, -2), (key1942, -2), (key1491, -2), (key1724, -2), (key1729, -2), (key1497, -2), (key1729, -2), (key1717, 2), (key1939, 2), (key1717, 2), (key1742, 2), (key1951, 2), (key1365, 2), (key1951, 2), (key1365, 2), (key1742, 2), (key1748, 2), (key1371, 2), (key1748, 2)]

def rawRow12712 : Integer.Sparse Key := [(key1939, -2), (key1717, -2), (key1717, -2), (key1942, -2), (key1724, -2), (key1942, -2), (key1491, -2), (key1724, -2), (key1491, -2), (key1729, -2), (key1729, -2), (key1497, -2), (key1939, 2), (key1717, 2), (key1717, 2), (key1951, 2), (key1742, 2), (key1951, 2), (key1365, 2), (key1742, 2), (key1365, 2), (key1748, 2), (key1748, 2), (key1371, 2)]

def rawRow12713 : Integer.Sparse Key := [(key1724, -2), (key1729, -2), (key1942, -2), (key1491, -2), (key1497, -2), (key1717, -2), (key1729, -2), (key1939, -2), (key1942, -2), (key1491, -2), (key1717, -2), (key1724, -2), (key1742, 2), (key1748, 2), (key1951, 2), (key1365, 2), (key1371, 2), (key1717, 2), (key1748, 2), (key1939, 2), (key1951, 2), (key1365, 2), (key1717, 2), (key1742, 2)]

def rawRow12714 : Integer.Sparse Key := [(key1729, -2), (key1724, -2), (key1942, -2), (key1497, -2), (key1491, -2), (key1729, -2), (key1717, -2), (key1942, -2), (key1939, -2), (key1491, -2), (key1724, -2), (key1717, -2), (key1748, 2), (key1742, 2), (key1951, 2), (key1371, 2), (key1365, 2), (key1748, 2), (key1717, 2), (key1951, 2), (key1939, 2), (key1365, 2), (key1742, 2), (key1717, 2)]

def rawRow12715 : Integer.Sparse Key := [(key1724, -2), (key1942, -2), (key1729, -2), (key1717, -2), (key1939, -2), (key1491, -2), (key1942, -2), (key1497, -2), (key1729, -2), (key1717, -2), (key1491, -2), (key1724, -2), (key1742, 2), (key1951, 2), (key1748, 2), (key1717, 2), (key1939, 2), (key1365, 2), (key1951, 2), (key1371, 2), (key1748, 2), (key1717, 2), (key1365, 2), (key1742, 2)]

def rawRow12716 : Integer.Sparse Key := [(key1942, -2), (key1724, -2), (key1729, -2), (key1939, -2), (key1717, -2), (key1942, -2), (key1491, -2), (key1729, -2), (key1497, -2), (key1717, -2), (key1724, -2), (key1491, -2), (key1951, 2), (key1742, 2), (key1748, 2), (key1939, 2), (key1717, 2), (key1951, 2), (key1365, 2), (key1748, 2), (key1371, 2), (key1717, 2), (key1742, 2), (key1365, 2)]

def rawRow12717 : Integer.Sparse Key := [(key1729, -2), (key1942, -2), (key1724, -2), (key1729, -2), (key1942, -2), (key1497, -2), (key1939, -2), (key1491, -2), (key1717, -2), (key1724, -2), (key1491, -2), (key1717, -2), (key1748, 2), (key1951, 2), (key1742, 2), (key1748, 2), (key1951, 2), (key1371, 2), (key1939, 2), (key1365, 2), (key1717, 2), (key1742, 2), (key1365, 2), (key1717, 2)]

def rawRow12718 : Integer.Sparse Key := [(key1942, -2), (key1729, -2), (key1724, -2), (key1942, -2), (key1729, -2), (key1939, -2), (key1497, -2), (key1717, -2), (key1491, -2), (key1724, -2), (key1717, -2), (key1491, -2), (key1951, 2), (key1748, 2), (key1742, 2), (key1951, 2), (key1748, 2), (key1939, 2), (key1371, 2), (key1717, 2), (key1365, 2), (key1742, 2), (key1717, 2), (key1365, 2)]

def rawRow12719 : Integer.Sparse Key := [(key1514, -2), (key1520, -2), (key1520, -2), (key1742, -2), (key1748, -2), (key1742, -2), (key1759, -2), (key1748, -2), (key1759, -2), (key1951, -2), (key1951, -2), (key1956, -2), (key1375, 2), (key1380, 2), (key1380, 2), (key1724, 2), (key1729, 2), (key1724, 2), (key1759, 2), (key1729, 2), (key1759, 2), (key1942, 2), (key1942, 2), (key1956, 2)]

def rawRow12720 : Integer.Sparse Key := [(key1520, -2), (key1514, -2), (key1520, -2), (key1748, -2), (key1742, -2), (key1759, -2), (key1742, -2), (key1759, -2), (key1748, -2), (key1951, -2), (key1956, -2), (key1951, -2), (key1380, 2), (key1375, 2), (key1380, 2), (key1729, 2), (key1724, 2), (key1759, 2), (key1724, 2), (key1759, 2), (key1729, 2), (key1942, 2), (key1956, 2), (key1942, 2)]

def rawRow12721 : Integer.Sparse Key := [(key1520, -2), (key1520, -2), (key1514, -2), (key1759, -2), (key1759, -2), (key1748, -2), (key1748, -2), (key1742, -2), (key1742, -2), (key1956, -2), (key1951, -2), (key1951, -2), (key1380, 2), (key1380, 2), (key1375, 2), (key1759, 2), (key1759, 2), (key1729, 2), (key1729, 2), (key1724, 2), (key1724, 2), (key1956, 2), (key1942, 2), (key1942, 2)]

def rawRow12722 : Integer.Sparse Key := [(key1742, -2), (key1748, -2), (key1951, -2), (key1514, -2), (key1520, -2), (key1742, -2), (key1759, -2), (key1951, -2), (key1956, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1724, 2), (key1729, 2), (key1942, 2), (key1375, 2), (key1380, 2), (key1724, 2), (key1759, 2), (key1942, 2), (key1956, 2), (key1380, 2), (key1729, 2), (key1759, 2)]

def rawRow12723 : Integer.Sparse Key := [(key1748, -2), (key1742, -2), (key1951, -2), (key1520, -2), (key1514, -2), (key1759, -2), (key1742, -2), (key1956, -2), (key1951, -2), (key1520, -2), (key1759, -2), (key1748, -2), (key1729, 2), (key1724, 2), (key1942, 2), (key1380, 2), (key1375, 2), (key1759, 2), (key1724, 2), (key1956, 2), (key1942, 2), (key1380, 2), (key1759, 2), (key1729, 2)]

def rawRow12724 : Integer.Sparse Key := [(key1742, -2), (key1951, -2), (key1748, -2), (key1742, -2), (key1951, -2), (key1514, -2), (key1956, -2), (key1520, -2), (key1759, -2), (key1748, -2), (key1520, -2), (key1759, -2), (key1724, 2), (key1942, 2), (key1729, 2), (key1724, 2), (key1942, 2), (key1375, 2), (key1956, 2), (key1380, 2), (key1759, 2), (key1729, 2), (key1380, 2), (key1759, 2)]

def rawRow12725 : Integer.Sparse Key := [(key1951, -2), (key1742, -2), (key1748, -2), (key1951, -2), (key1742, -2), (key1956, -2), (key1514, -2), (key1759, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1520, -2), (key1942, 2), (key1724, 2), (key1729, 2), (key1942, 2), (key1724, 2), (key1956, 2), (key1375, 2), (key1759, 2), (key1380, 2), (key1729, 2), (key1759, 2), (key1380, 2)]

def rawRow12726 : Integer.Sparse Key := [(key1748, -2), (key1951, -2), (key1742, -2), (key1759, -2), (key1956, -2), (key1520, -2), (key1951, -2), (key1514, -2), (key1742, -2), (key1759, -2), (key1520, -2), (key1748, -2), (key1729, 2), (key1942, 2), (key1724, 2), (key1759, 2), (key1956, 2), (key1380, 2), (key1942, 2), (key1375, 2), (key1724, 2), (key1759, 2), (key1380, 2), (key1729, 2)]

def rawRow12727 : Integer.Sparse Key := [(key1951, -2), (key1748, -2), (key1742, -2), (key1956, -2), (key1759, -2), (key1951, -2), (key1520, -2), (key1742, -2), (key1514, -2), (key1759, -2), (key1748, -2), (key1520, -2), (key1942, 2), (key1729, 2), (key1724, 2), (key1956, 2), (key1759, 2), (key1942, 2), (key1380, 2), (key1724, 2), (key1375, 2), (key1759, 2), (key1729, 2), (key1380, 2)]

def rawRow12728 : Integer.Sparse Key := [(key1759, -2), (key1759, -2), (key1956, -2), (key1520, -2), (key1520, -2), (key1748, -2), (key1748, -2), (key1951, -2), (key1951, -2), (key1514, -2), (key1742, -2), (key1742, -2), (key1759, 2), (key1759, 2), (key1956, 2), (key1380, 2), (key1380, 2), (key1729, 2), (key1729, 2), (key1942, 2), (key1942, 2), (key1375, 2), (key1724, 2), (key1724, 2)]

def rawRow12729 : Integer.Sparse Key := [(key1759, -2), (key1956, -2), (key1759, -2), (key1748, -2), (key1951, -2), (key1520, -2), (key1951, -2), (key1520, -2), (key1748, -2), (key1742, -2), (key1514, -2), (key1742, -2), (key1759, 2), (key1956, 2), (key1759, 2), (key1729, 2), (key1942, 2), (key1380, 2), (key1942, 2), (key1380, 2), (key1729, 2), (key1724, 2), (key1375, 2), (key1724, 2)]

def rawRow12730 : Integer.Sparse Key := [(key1956, -2), (key1759, -2), (key1759, -2), (key1951, -2), (key1748, -2), (key1951, -2), (key1520, -2), (key1748, -2), (key1520, -2), (key1742, -2), (key1742, -2), (key1514, -2), (key1956, 2), (key1759, 2), (key1759, 2), (key1942, 2), (key1729, 2), (key1942, 2), (key1380, 2), (key1729, 2), (key1380, 2), (key1724, 2), (key1724, 2), (key1375, 2)]

def rawRow12731 : Integer.Sparse Key := [(key284, -2), (key284, -2), (key287, -2), (key510, -2), (key510, -2), (key542, -2), (key542, -2), (key546, -2), (key546, -2), (key669, -2), (key679, -2), (key679, -2), (key284, 1), (key284, 1), (key293, 1), (key293, 1), (key299, 1), (key299, 1), (key353, 1), (key353, 1), (key370, 1), (key370, 1), (key373, 1), (key373, 1), (key521, 1), (key521, 1), (key542, 1), (key542, 1), (key563, 1), (key563, 1), (key673, 1), (key673, 1), (key679, 1), (key679, 1), (key684, 1), (key684, 1)]

def rawRow12732 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key284, -2), (key542, -2), (key546, -2), (key510, -2), (key546, -2), (key510, -2), (key542, -2), (key679, -2), (key669, -2), (key679, -2), (key293, 1), (key299, 1), (key284, 1), (key299, 1), (key284, 1), (key293, 1), (key370, 1), (key373, 1), (key353, 1), (key373, 1), (key353, 1), (key370, 1), (key542, 1), (key563, 1), (key521, 1), (key563, 1), (key521, 1), (key542, 1), (key679, 1), (key684, 1), (key673, 1), (key684, 1), (key673, 1), (key679, 1)]

def rawRow12733 : Integer.Sparse Key := [(key287, -2), (key284, -2), (key284, -2), (key546, -2), (key542, -2), (key546, -2), (key510, -2), (key542, -2), (key510, -2), (key679, -2), (key679, -2), (key669, -2), (key299, 1), (key293, 1), (key299, 1), (key284, 1), (key293, 1), (key284, 1), (key373, 1), (key370, 1), (key373, 1), (key353, 1), (key370, 1), (key353, 1), (key563, 1), (key542, 1), (key563, 1), (key521, 1), (key542, 1), (key521, 1), (key684, 1), (key679, 1), (key684, 1), (key673, 1), (key679, 1), (key673, 1)]

def rawRow12734 : Integer.Sparse Key := [(key510, -2), (key510, -2), (key669, -2), (key284, -2), (key284, -2), (key542, -2), (key542, -2), (key679, -2), (key679, -2), (key287, -2), (key546, -2), (key546, -2), (key353, 1), (key353, 1), (key521, 1), (key521, 1), (key673, 1), (key673, 1), (key284, 1), (key284, 1), (key542, 1), (key542, 1), (key679, 1), (key679, 1), (key293, 1), (key293, 1), (key370, 1), (key370, 1), (key684, 1), (key684, 1), (key299, 1), (key299, 1), (key373, 1), (key373, 1), (key563, 1), (key563, 1)]

def rawRow12735 : Integer.Sparse Key := [(key510, -2), (key669, -2), (key510, -2), (key542, -2), (key679, -2), (key284, -2), (key679, -2), (key284, -2), (key542, -2), (key546, -2), (key287, -2), (key546, -2), (key521, 1), (key673, 1), (key353, 1), (key673, 1), (key353, 1), (key521, 1), (key542, 1), (key679, 1), (key284, 1), (key679, 1), (key284, 1), (key542, 1), (key370, 1), (key684, 1), (key293, 1), (key684, 1), (key293, 1), (key370, 1), (key373, 1), (key563, 1), (key299, 1), (key563, 1), (key299, 1), (key373, 1)]

def rawRow12736 : Integer.Sparse Key := [(key669, -2), (key510, -2), (key510, -2), (key679, -2), (key542, -2), (key679, -2), (key284, -2), (key542, -2), (key284, -2), (key546, -2), (key546, -2), (key287, -2), (key673, 1), (key521, 1), (key673, 1), (key353, 1), (key521, 1), (key353, 1), (key679, 1), (key542, 1), (key679, 1), (key284, 1), (key542, 1), (key284, 1), (key684, 1), (key370, 1), (key684, 1), (key293, 1), (key370, 1), (key293, 1), (key563, 1), (key373, 1), (key563, 1), (key299, 1), (key373, 1), (key299, 1)]

def rawRow12737 : Integer.Sparse Key := [(key542, -2), (key546, -2), (key679, -2), (key284, -2), (key287, -2), (key510, -2), (key546, -2), (key669, -2), (key679, -2), (key284, -2), (key510, -2), (key542, -2), (key370, 1), (key373, 1), (key542, 1), (key563, 1), (key679, 1), (key684, 1), (key293, 1), (key299, 1), (key521, 1), (key563, 1), (key673, 1), (key684, 1), (key284, 1), (key299, 1), (key353, 1), (key373, 1), (key673, 1), (key679, 1), (key284, 1), (key293, 1), (key353, 1), (key370, 1), (key521, 1), (key542, 1)]

def rawRow12738 : Integer.Sparse Key := [(key546, -2), (key542, -2), (key679, -2), (key287, -2), (key284, -2), (key546, -2), (key510, -2), (key679, -2), (key669, -2), (key284, -2), (key542, -2), (key510, -2), (key373, 1), (key370, 1), (key563, 1), (key542, 1), (key684, 1), (key679, 1), (key299, 1), (key293, 1), (key563, 1), (key521, 1), (key684, 1), (key673, 1), (key299, 1), (key284, 1), (key373, 1), (key353, 1), (key679, 1), (key673, 1), (key293, 1), (key284, 1), (key370, 1), (key353, 1), (key542, 1), (key521, 1)]

def rawRow12739 : Integer.Sparse Key := [(key542, -2), (key679, -2), (key546, -2), (key510, -2), (key669, -2), (key284, -2), (key679, -2), (key287, -2), (key546, -2), (key510, -2), (key284, -2), (key542, -2), (key542, 1), (key679, 1), (key370, 1), (key684, 1), (key373, 1), (key563, 1), (key521, 1), (key673, 1), (key293, 1), (key684, 1), (key299, 1), (key563, 1), (key353, 1), (key673, 1), (key284, 1), (key679, 1), (key299, 1), (key373, 1), (key353, 1), (key521, 1), (key284, 1), (key542, 1), (key293, 1), (key370, 1)]

def rawRow12740 : Integer.Sparse Key := [(key679, -2), (key542, -2), (key546, -2), (key669, -2), (key510, -2), (key679, -2), (key284, -2), (key546, -2), (key287, -2), (key510, -2), (key542, -2), (key284, -2), (key679, 1), (key542, 1), (key684, 1), (key370, 1), (key563, 1), (key373, 1), (key673, 1), (key521, 1), (key684, 1), (key293, 1), (key563, 1), (key299, 1), (key673, 1), (key353, 1), (key679, 1), (key284, 1), (key373, 1), (key299, 1), (key521, 1), (key353, 1), (key542, 1), (key284, 1), (key370, 1), (key293, 1)]

def rawRow12741 : Integer.Sparse Key := [(key546, -2), (key679, -2), (key542, -2), (key546, -2), (key679, -2), (key287, -2), (key669, -2), (key284, -2), (key510, -2), (key542, -2), (key284, -2), (key510, -2), (key563, 1), (key684, 1), (key373, 1), (key679, 1), (key370, 1), (key542, 1), (key563, 1), (key684, 1), (key299, 1), (key673, 1), (key293, 1), (key521, 1), (key373, 1), (key679, 1), (key299, 1), (key673, 1), (key284, 1), (key353, 1), (key370, 1), (key542, 1), (key293, 1), (key521, 1), (key284, 1), (key353, 1)]

def rawRow12742 : Integer.Sparse Key := [(key679, -2), (key546, -2), (key542, -2), (key679, -2), (key546, -2), (key669, -2), (key287, -2), (key510, -2), (key284, -2), (key542, -2), (key510, -2), (key284, -2), (key684, 1), (key563, 1), (key679, 1), (key373, 1), (key542, 1), (key370, 1), (key684, 1), (key563, 1), (key673, 1), (key299, 1), (key521, 1), (key293, 1), (key679, 1), (key373, 1), (key673, 1), (key299, 1), (key353, 1), (key284, 1), (key542, 1), (key370, 1), (key521, 1), (key293, 1), (key353, 1), (key284, 1)]

def rawRow12743 : Integer.Sparse Key := [(key293, -2), (key299, -2), (key299, -2), (key521, -2), (key526, -2), (key521, -2), (key563, -2), (key526, -2), (key563, -2), (key673, -2), (key673, -2), (key684, -2), (key284, 1), (key287, 1), (key284, 1), (key299, 1), (key287, 1), (key299, 1), (key353, 1), (key356, 1), (key353, 1), (key373, 1), (key356, 1), (key373, 1), (key510, 1), (key526, 1), (key510, 1), (key546, 1), (key526, 1), (key546, 1), (key669, 1), (key673, 1), (key669, 1), (key679, 1), (key673, 1), (key679, 1)]

def rawRow12744 : Integer.Sparse Key := [(key299, -2), (key293, -2), (key299, -2), (key526, -2), (key521, -2), (key563, -2), (key521, -2), (key563, -2), (key526, -2), (key673, -2), (key684, -2), (key673, -2), (key287, 1), (key284, 1), (key299, 1), (key284, 1), (key299, 1), (key287, 1), (key356, 1), (key353, 1), (key373, 1), (key353, 1), (key373, 1), (key356, 1), (key526, 1), (key510, 1), (key546, 1), (key510, 1), (key546, 1), (key526, 1), (key673, 1), (key669, 1), (key679, 1), (key669, 1), (key679, 1), (key673, 1)]

def rawRow12745 : Integer.Sparse Key := [(key299, -2), (key299, -2), (key293, -2), (key563, -2), (key563, -2), (key526, -2), (key526, -2), (key521, -2), (key521, -2), (key684, -2), (key673, -2), (key673, -2), (key299, 1), (key299, 1), (key287, 1), (key287, 1), (key284, 1), (key284, 1), (key373, 1), (key373, 1), (key356, 1), (key356, 1), (key353, 1), (key353, 1), (key546, 1), (key546, 1), (key526, 1), (key526, 1), (key510, 1), (key510, 1), (key679, 1), (key679, 1), (key673, 1), (key673, 1), (key669, 1), (key669, 1)]

def rawRow12746 : Integer.Sparse Key := [(key521, -2), (key526, -2), (key673, -2), (key293, -2), (key299, -2), (key521, -2), (key563, -2), (key673, -2), (key684, -2), (key299, -2), (key526, -2), (key563, -2), (key353, 1), (key356, 1), (key510, 1), (key526, 1), (key669, 1), (key673, 1), (key284, 1), (key287, 1), (key510, 1), (key546, 1), (key669, 1), (key679, 1), (key284, 1), (key299, 1), (key353, 1), (key373, 1), (key673, 1), (key679, 1), (key287, 1), (key299, 1), (key356, 1), (key373, 1), (key526, 1), (key546, 1)]

def rawRow12747 : Integer.Sparse Key := [(key526, -2), (key521, -2), (key673, -2), (key299, -2), (key293, -2), (key563, -2), (key521, -2), (key684, -2), (key673, -2), (key299, -2), (key563, -2), (key526, -2), (key356, 1), (key353, 1), (key526, 1), (key510, 1), (key673, 1), (key669, 1), (key287, 1), (key284, 1), (key546, 1), (key510, 1), (key679, 1), (key669, 1), (key299, 1), (key284, 1), (key373, 1), (key353, 1), (key679, 1), (key673, 1), (key299, 1), (key287, 1), (key373, 1), (key356, 1), (key546, 1), (key526, 1)]

def rawRow12748 : Integer.Sparse Key := [(key521, -2), (key673, -2), (key526, -2), (key521, -2), (key673, -2), (key293, -2), (key684, -2), (key299, -2), (key563, -2), (key526, -2), (key299, -2), (key563, -2), (key510, 1), (key669, 1), (key353, 1), (key673, 1), (key356, 1), (key526, 1), (key510, 1), (key669, 1), (key284, 1), (key679, 1), (key287, 1), (key546, 1), (key353, 1), (key673, 1), (key284, 1), (key679, 1), (key299, 1), (key373, 1), (key356, 1), (key526, 1), (key287, 1), (key546, 1), (key299, 1), (key373, 1)]

def rawRow12749 : Integer.Sparse Key := [(key673, -2), (key521, -2), (key526, -2), (key673, -2), (key521, -2), (key684, -2), (key293, -2), (key563, -2), (key299, -2), (key526, -2), (key563, -2), (key299, -2), (key669, 1), (key510, 1), (key673, 1), (key353, 1), (key526, 1), (key356, 1), (key669, 1), (key510, 1), (key679, 1), (key284, 1), (key546, 1), (key287, 1), (key673, 1), (key353, 1), (key679, 1), (key284, 1), (key373, 1), (key299, 1), (key526, 1), (key356, 1), (key546, 1), (key287, 1), (key373, 1), (key299, 1)]

def rawRow12750 : Integer.Sparse Key := [(key526, -2), (key673, -2), (key521, -2), (key563, -2), (key684, -2), (key299, -2), (key673, -2), (key293, -2), (key521, -2), (key563, -2), (key299, -2), (key526, -2), (key526, 1), (key673, 1), (key356, 1), (key669, 1), (key353, 1), (key510, 1), (key546, 1), (key679, 1), (key287, 1), (key669, 1), (key284, 1), (key510, 1), (key373, 1), (key679, 1), (key299, 1), (key673, 1), (key284, 1), (key353, 1), (key373, 1), (key546, 1), (key299, 1), (key526, 1), (key287, 1), (key356, 1)]

def rawRow12751 : Integer.Sparse Key := [(key673, -2), (key526, -2), (key521, -2), (key684, -2), (key563, -2), (key673, -2), (key299, -2), (key521, -2), (key293, -2), (key563, -2), (key526, -2), (key299, -2), (key673, 1), (key526, 1), (key669, 1), (key356, 1), (key510, 1), (key353, 1), (key679, 1), (key546, 1), (key669, 1), (key287, 1), (key510, 1), (key284, 1), (key679, 1), (key373, 1), (key673, 1), (key299, 1), (key353, 1), (key284, 1), (key546, 1), (key373, 1), (key526, 1), (key299, 1), (key356, 1), (key287, 1)]

def rawRow12752 : Integer.Sparse Key := [(key563, -2), (key563, -2), (key684, -2), (key299, -2), (key299, -2), (key526, -2), (key526, -2), (key673, -2), (key673, -2), (key293, -2), (key521, -2), (key521, -2), (key373, 1), (key373, 1), (key546, 1), (key546, 1), (key679, 1), (key679, 1), (key299, 1), (key299, 1), (key526, 1), (key526, 1), (key673, 1), (key673, 1), (key287, 1), (key287, 1), (key356, 1), (key356, 1), (key669, 1), (key669, 1), (key284, 1), (key284, 1), (key353, 1), (key353, 1), (key510, 1), (key510, 1)]

def rawRow12753 : Integer.Sparse Key := [(key563, -2), (key684, -2), (key563, -2), (key526, -2), (key673, -2), (key299, -2), (key673, -2), (key299, -2), (key526, -2), (key521, -2), (key293, -2), (key521, -2), (key546, 1), (key679, 1), (key373, 1), (key679, 1), (key373, 1), (key546, 1), (key526, 1), (key673, 1), (key299, 1), (key673, 1), (key299, 1), (key526, 1), (key356, 1), (key669, 1), (key287, 1), (key669, 1), (key287, 1), (key356, 1), (key353, 1), (key510, 1), (key284, 1), (key510, 1), (key284, 1), (key353, 1)]

def rawRow12754 : Integer.Sparse Key := [(key684, -2), (key563, -2), (key563, -2), (key673, -2), (key526, -2), (key673, -2), (key299, -2), (key526, -2), (key299, -2), (key521, -2), (key521, -2), (key293, -2), (key679, 1), (key546, 1), (key679, 1), (key373, 1), (key546, 1), (key373, 1), (key673, 1), (key526, 1), (key673, 1), (key299, 1), (key526, 1), (key299, 1), (key669, 1), (key356, 1), (key669, 1), (key287, 1), (key356, 1), (key287, 1), (key510, 1), (key353, 1), (key510, 1), (key284, 1), (key353, 1), (key284, 1)]

def rawRow12755 : Integer.Sparse Key := [(key1365, 1), (key1365, 1), (key1375, 1), (key1375, 1), (key1380, 1), (key1380, 1), (key1491, 1), (key1491, 1), (key1514, 1), (key1514, 1), (key1520, 1), (key1520, 1), (key1724, 1), (key1724, 1), (key1742, 1), (key1742, 1), (key1759, 1), (key1759, 1), (key1942, 1), (key1942, 1), (key1951, 1), (key1951, 1), (key1956, 1), (key1956, 1), (key1371, -2), (key1380, -2), (key1380, -2), (key1497, -2), (key1520, -2), (key1520, -2), (key1729, -2), (key1729, -2), (key1748, -2), (key1748, -2), (key1759, -2), (key1759, -2)]

def rawRow12756 : Integer.Sparse Key := [(key1375, 1), (key1380, 1), (key1365, 1), (key1380, 1), (key1365, 1), (key1375, 1), (key1514, 1), (key1520, 1), (key1491, 1), (key1520, 1), (key1491, 1), (key1514, 1), (key1742, 1), (key1759, 1), (key1724, 1), (key1759, 1), (key1724, 1), (key1742, 1), (key1951, 1), (key1956, 1), (key1942, 1), (key1956, 1), (key1942, 1), (key1951, 1), (key1380, -2), (key1371, -2), (key1380, -2), (key1520, -2), (key1497, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1729, -2), (key1759, -2), (key1729, -2), (key1748, -2)]

def rawRow12757 : Integer.Sparse Key := [(key1380, 1), (key1375, 1), (key1380, 1), (key1365, 1), (key1375, 1), (key1365, 1), (key1520, 1), (key1514, 1), (key1520, 1), (key1491, 1), (key1514, 1), (key1491, 1), (key1759, 1), (key1742, 1), (key1759, 1), (key1724, 1), (key1742, 1), (key1724, 1), (key1956, 1), (key1951, 1), (key1956, 1), (key1942, 1), (key1951, 1), (key1942, 1), (key1380, -2), (key1380, -2), (key1371, -2), (key1520, -2), (key1520, -2), (key1497, -2), (key1759, -2), (key1748, -2), (key1759, -2), (key1729, -2), (key1748, -2), (key1729, -2)]

def rawRow12758 : Integer.Sparse Key := [(key1491, 1), (key1491, 1), (key1724, 1), (key1724, 1), (key1942, 1), (key1942, 1), (key1365, 1), (key1365, 1), (key1742, 1), (key1742, 1), (key1951, 1), (key1951, 1), (key1375, 1), (key1375, 1), (key1514, 1), (key1514, 1), (key1956, 1), (key1956, 1), (key1380, 1), (key1380, 1), (key1520, 1), (key1520, 1), (key1759, 1), (key1759, 1), (key1497, -2), (key1729, -2), (key1729, -2), (key1371, -2), (key1748, -2), (key1748, -2), (key1380, -2), (key1380, -2), (key1520, -2), (key1520, -2), (key1759, -2), (key1759, -2)]

def rawRow12759 : Integer.Sparse Key := [(key1724, 1), (key1942, 1), (key1491, 1), (key1942, 1), (key1491, 1), (key1724, 1), (key1742, 1), (key1951, 1), (key1365, 1), (key1951, 1), (key1365, 1), (key1742, 1), (key1514, 1), (key1956, 1), (key1375, 1), (key1956, 1), (key1375, 1), (key1514, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1729, -2), (key1497, -2), (key1729, -2), (key1748, -2), (key1371, -2), (key1748, -2), (key1520, -2), (key1759, -2), (key1380, -2), (key1759, -2), (key1380, -2), (key1520, -2)]

def rawRow12760 : Integer.Sparse Key := [(key1942, 1), (key1724, 1), (key1942, 1), (key1491, 1), (key1724, 1), (key1491, 1), (key1951, 1), (key1742, 1), (key1951, 1), (key1365, 1), (key1742, 1), (key1365, 1), (key1956, 1), (key1514, 1), (key1956, 1), (key1375, 1), (key1514, 1), (key1375, 1), (key1759, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1380, 1), (key1729, -2), (key1729, -2), (key1497, -2), (key1748, -2), (key1748, -2), (key1371, -2), (key1759, -2), (key1520, -2), (key1759, -2), (key1380, -2), (key1520, -2), (key1380, -2)]

def rawRow12761 : Integer.Sparse Key := [(key1514, 1), (key1520, 1), (key1742, 1), (key1759, 1), (key1951, 1), (key1956, 1), (key1375, 1), (key1380, 1), (key1724, 1), (key1759, 1), (key1942, 1), (key1956, 1), (key1365, 1), (key1380, 1), (key1491, 1), (key1520, 1), (key1942, 1), (key1951, 1), (key1365, 1), (key1375, 1), (key1491, 1), (key1514, 1), (key1724, 1), (key1742, 1), (key1520, -2), (key1748, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1371, -2), (key1380, -2), (key1497, -2), (key1520, -2), (key1729, -2), (key1748, -2)]

def rawRow12762 : Integer.Sparse Key := [(key1520, 1), (key1514, 1), (key1759, 1), (key1742, 1), (key1956, 1), (key1951, 1), (key1380, 1), (key1375, 1), (key1759, 1), (key1724, 1), (key1956, 1), (key1942, 1), (key1380, 1), (key1365, 1), (key1520, 1), (key1491, 1), (key1951, 1), (key1942, 1), (key1375, 1), (key1365, 1), (key1514, 1), (key1491, 1), (key1742, 1), (key1724, 1), (key1520, -2), (key1759, -2), (key1748, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1371, -2), (key1520, -2), (key1497, -2), (key1748, -2), (key1729, -2)]

def rawRow12763 : Integer.Sparse Key := [(key1742, 1), (key1951, 1), (key1514, 1), (key1956, 1), (key1520, 1), (key1759, 1), (key1724, 1), (key1942, 1), (key1375, 1), (key1956, 1), (key1380, 1), (key1759, 1), (key1491, 1), (key1942, 1), (key1365, 1), (key1951, 1), (key1380, 1), (key1520, 1), (key1491, 1), (key1724, 1), (key1365, 1), (key1742, 1), (key1375, 1), (key1514, 1), (key1748, -2), (key1520, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1759, -2), (key1497, -2), (key1729, -2), (key1371, -2), (key1748, -2), (key1380, -2), (key1520, -2)]

def rawRow12764 : Integer.Sparse Key := [(key1951, 1), (key1742, 1), (key1956, 1), (key1514, 1), (key1759, 1), (key1520, 1), (key1942, 1), (key1724, 1), (key1956, 1), (key1375, 1), (key1759, 1), (key1380, 1), (key1942, 1), (key1491, 1), (key1951, 1), (key1365, 1), (key1520, 1), (key1380, 1), (key1724, 1), (key1491, 1), (key1742, 1), (key1365, 1), (key1514, 1), (key1375, 1), (key1748, -2), (key1759, -2), (key1520, -2), (key1729, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1497, -2), (key1748, -2), (key1371, -2), (key1520, -2), (key1380, -2)]

def rawRow12765 : Integer.Sparse Key := [(key1759, 1), (key1956, 1), (key1520, 1), (key1951, 1), (key1514, 1), (key1742, 1), (key1759, 1), (key1956, 1), (key1380, 1), (key1942, 1), (key1375, 1), (key1724, 1), (key1520, 1), (key1951, 1), (key1380, 1), (key1942, 1), (key1365, 1), (key1491, 1), (key1514, 1), (key1742, 1), (key1375, 1), (key1724, 1), (key1365, 1), (key1491, 1), (key1759, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1520, -2), (key1748, -2), (key1380, -2), (key1729, -2), (key1371, -2), (key1497, -2)]

def rawRow12766 : Integer.Sparse Key := [(key1956, 1), (key1759, 1), (key1951, 1), (key1520, 1), (key1742, 1), (key1514, 1), (key1956, 1), (key1759, 1), (key1942, 1), (key1380, 1), (key1724, 1), (key1375, 1), (key1951, 1), (key1520, 1), (key1942, 1), (key1380, 1), (key1491, 1), (key1365, 1), (key1742, 1), (key1514, 1), (key1724, 1), (key1375, 1), (key1491, 1), (key1365, 1), (key1759, -2), (key1748, -2), (key1520, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1748, -2), (key1520, -2), (key1729, -2), (key1380, -2), (key1497, -2), (key1371, -2)]

def rawRow12767 : Integer.Sparse Key := [(key1365, 1), (key1371, 1), (key1365, 1), (key1380, 1), (key1371, 1), (key1380, 1), (key1491, 1), (key1497, 1), (key1491, 1), (key1520, 1), (key1497, 1), (key1520, 1), (key1717, 1), (key1729, 1), (key1717, 1), (key1748, 1), (key1729, 1), (key1748, 1), (key1939, 1), (key1942, 1), (key1939, 1), (key1951, 1), (key1942, 1), (key1951, 1), (key1365, -2), (key1365, -2), (key1375, -2), (key1491, -2), (key1491, -2), (key1514, -2), (key1717, -2), (key1724, -2), (key1717, -2), (key1742, -2), (key1724, -2), (key1742, -2)]

def rawRow12768 : Integer.Sparse Key := [(key1371, 1), (key1365, 1), (key1380, 1), (key1365, 1), (key1380, 1), (key1371, 1), (key1497, 1), (key1491, 1), (key1520, 1), (key1491, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1717, 1), (key1748, 1), (key1717, 1), (key1748, 1), (key1729, 1), (key1942, 1), (key1939, 1), (key1951, 1), (key1939, 1), (key1951, 1), (key1942, 1), (key1365, -2), (key1375, -2), (key1365, -2), (key1491, -2), (key1514, -2), (key1491, -2), (key1724, -2), (key1717, -2), (key1742, -2), (key1717, -2), (key1742, -2), (key1724, -2)]

def rawRow12769 : Integer.Sparse Key := [(key1380, 1), (key1380, 1), (key1371, 1), (key1371, 1), (key1365, 1), (key1365, 1), (key1520, 1), (key1520, 1), (key1497, 1), (key1497, 1), (key1491, 1), (key1491, 1), (key1748, 1), (key1748, 1), (key1729, 1), (key1729, 1), (key1717, 1), (key1717, 1), (key1951, 1), (key1951, 1), (key1942, 1), (key1942, 1), (key1939, 1), (key1939, 1), (key1375, -2), (key1365, -2), (key1365, -2), (key1514, -2), (key1491, -2), (key1491, -2), (key1742, -2), (key1742, -2), (key1724, -2), (key1724, -2), (key1717, -2), (key1717, -2)]

def rawRow12770 : Integer.Sparse Key := [(key1491, 1), (key1497, 1), (key1717, 1), (key1729, 1), (key1939, 1), (key1942, 1), (key1365, 1), (key1371, 1), (key1717, 1), (key1748, 1), (key1939, 1), (key1951, 1), (key1365, 1), (key1380, 1), (key1491, 1), (key1520, 1), (key1942, 1), (key1951, 1), (key1371, 1), (key1380, 1), (key1497, 1), (key1520, 1), (key1729, 1), (key1748, 1), (key1491, -2), (key1717, -2), (key1724, -2), (key1365, -2), (key1717, -2), (key1742, -2), (key1365, -2), (key1375, -2), (key1491, -2), (key1514, -2), (key1724, -2), (key1742, -2)]

def rawRow12771 : Integer.Sparse Key := [(key1497, 1), (key1491, 1), (key1729, 1), (key1717, 1), (key1942, 1), (key1939, 1), (key1371, 1), (key1365, 1), (key1748, 1), (key1717, 1), (key1951, 1), (key1939, 1), (key1380, 1), (key1365, 1), (key1520, 1), (key1491, 1), (key1951, 1), (key1942, 1), (key1380, 1), (key1371, 1), (key1520, 1), (key1497, 1), (key1748, 1), (key1729, 1), (key1491, -2), (key1724, -2), (key1717, -2), (key1365, -2), (key1742, -2), (key1717, -2), (key1375, -2), (key1365, -2), (key1514, -2), (key1491, -2), (key1742, -2), (key1724, -2)]

def rawRow12772 : Integer.Sparse Key := [(key1717, 1), (key1939, 1), (key1491, 1), (key1942, 1), (key1497, 1), (key1729, 1), (key1717, 1), (key1939, 1), (key1365, 1), (key1951, 1), (key1371, 1), (key1748, 1), (key1491, 1), (key1942, 1), (key1365, 1), (key1951, 1), (key1380, 1), (key1520, 1), (key1497, 1), (key1729, 1), (key1371, 1), (key1748, 1), (key1380, 1), (key1520, 1), (key1717, -2), (key1491, -2), (key1724, -2), (key1717, -2), (key1365, -2), (key1742, -2), (key1491, -2), (key1724, -2), (key1365, -2), (key1742, -2), (key1375, -2), (key1514, -2)]

def rawRow12773 : Integer.Sparse Key := [(key1939, 1), (key1717, 1), (key1942, 1), (key1491, 1), (key1729, 1), (key1497, 1), (key1939, 1), (key1717, 1), (key1951, 1), (key1365, 1), (key1748, 1), (key1371, 1), (key1942, 1), (key1491, 1), (key1951, 1), (key1365, 1), (key1520, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1748, 1), (key1371, 1), (key1520, 1), (key1380, 1), (key1717, -2), (key1724, -2), (key1491, -2), (key1717, -2), (key1742, -2), (key1365, -2), (key1724, -2), (key1491, -2), (key1742, -2), (key1365, -2), (key1514, -2), (key1375, -2)]

def rawRow12774 : Integer.Sparse Key := [(key1729, 1), (key1942, 1), (key1497, 1), (key1939, 1), (key1491, 1), (key1717, 1), (key1748, 1), (key1951, 1), (key1371, 1), (key1939, 1), (key1365, 1), (key1717, 1), (key1520, 1), (key1951, 1), (key1380, 1), (key1942, 1), (key1365, 1), (key1491, 1), (key1520, 1), (key1748, 1), (key1380, 1), (key1729, 1), (key1371, 1), (key1497, 1), (key1724, -2), (key1491, -2), (key1717, -2), (key1742, -2), (key1365, -2), (key1717, -2), (key1514, -2), (key1742, -2), (key1375, -2), (key1724, -2), (key1365, -2), (key1491, -2)]

def rawRow12775 : Integer.Sparse Key := [(key1942, 1), (key1729, 1), (key1939, 1), (key1497, 1), (key1717, 1), (key1491, 1), (key1951, 1), (key1748, 1), (key1939, 1), (key1371, 1), (key1717, 1), (key1365, 1), (key1951, 1), (key1520, 1), (key1942, 1), (key1380, 1), (key1491, 1), (key1365, 1), (key1748, 1), (key1520, 1), (key1729, 1), (key1380, 1), (key1497, 1), (key1371, 1), (key1724, -2), (key1717, -2), (key1491, -2), (key1742, -2), (key1717, -2), (key1365, -2), (key1742, -2), (key1514, -2), (key1724, -2), (key1375, -2), (key1491, -2), (key1365, -2)]

def rawRow12776 : Integer.Sparse Key := [(key1520, 1), (key1520, 1), (key1748, 1), (key1748, 1), (key1951, 1), (key1951, 1), (key1380, 1), (key1380, 1), (key1729, 1), (key1729, 1), (key1942, 1), (key1942, 1), (key1371, 1), (key1371, 1), (key1497, 1), (key1497, 1), (key1939, 1), (key1939, 1), (key1365, 1), (key1365, 1), (key1491, 1), (key1491, 1), (key1717, 1), (key1717, 1), (key1514, -2), (key1742, -2), (key1742, -2), (key1375, -2), (key1724, -2), (key1724, -2), (key1365, -2), (key1365, -2), (key1491, -2), (key1491, -2), (key1717, -2), (key1717, -2)]

def rawRow12777 : Integer.Sparse Key := [(key1748, 1), (key1951, 1), (key1520, 1), (key1951, 1), (key1520, 1), (key1748, 1), (key1729, 1), (key1942, 1), (key1380, 1), (key1942, 1), (key1380, 1), (key1729, 1), (key1497, 1), (key1939, 1), (key1371, 1), (key1939, 1), (key1371, 1), (key1497, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1717, 1), (key1365, 1), (key1491, 1), (key1742, -2), (key1514, -2), (key1742, -2), (key1724, -2), (key1375, -2), (key1724, -2), (key1491, -2), (key1717, -2), (key1365, -2), (key1717, -2), (key1365, -2), (key1491, -2)]

def rawRow12778 : Integer.Sparse Key := [(key1951, 1), (key1748, 1), (key1951, 1), (key1520, 1), (key1748, 1), (key1520, 1), (key1942, 1), (key1729, 1), (key1942, 1), (key1380, 1), (key1729, 1), (key1380, 1), (key1939, 1), (key1497, 1), (key1939, 1), (key1371, 1), (key1497, 1), (key1371, 1), (key1717, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1491, 1), (key1365, 1), (key1742, -2), (key1742, -2), (key1514, -2), (key1724, -2), (key1724, -2), (key1375, -2), (key1717, -2), (key1491, -2), (key1717, -2), (key1365, -2), (key1491, -2), (key1365, -2)]

def rawRow12779 : Integer.Sparse Key := [(key286, -6), (key512, -6), (key545, -6), (key545, -6), (key286, 2), (key297, 2), (key297, 2), (key355, 2), (key372, 2), (key372, 2), (key525, 2), (key525, 2), (key545, 2), (key545, 2), (key558, 2), (key558, 2)]

def rawRow12780 : Integer.Sparse Key := [(key286, -6), (key545, -6), (key512, -6), (key545, -6), (key297, 2), (key286, 2), (key297, 2), (key372, 2), (key355, 2), (key372, 2), (key545, 2), (key558, 2), (key525, 2), (key558, 2), (key525, 2), (key545, 2)]

def rawRow12781 : Integer.Sparse Key := [(key286, -6), (key545, -6), (key545, -6), (key512, -6), (key297, 2), (key297, 2), (key286, 2), (key372, 2), (key372, 2), (key355, 2), (key558, 2), (key545, 2), (key558, 2), (key525, 2), (key545, 2), (key525, 2)]

def rawRow12782 : Integer.Sparse Key := [(key512, -6), (key286, -6), (key545, -6), (key545, -6), (key355, 2), (key525, 2), (key525, 2), (key286, 2), (key545, 2), (key545, 2), (key297, 2), (key297, 2), (key372, 2), (key372, 2), (key558, 2), (key558, 2)]

def rawRow12783 : Integer.Sparse Key := [(key512, -6), (key545, -6), (key286, -6), (key545, -6), (key525, 2), (key355, 2), (key525, 2), (key545, 2), (key286, 2), (key545, 2), (key372, 2), (key558, 2), (key297, 2), (key558, 2), (key297, 2), (key372, 2)]

def rawRow12784 : Integer.Sparse Key := [(key512, -6), (key545, -6), (key545, -6), (key286, -6), (key525, 2), (key525, 2), (key355, 2), (key545, 2), (key545, 2), (key286, 2), (key558, 2), (key372, 2), (key558, 2), (key297, 2), (key372, 2), (key297, 2)]

def rawRow12785 : Integer.Sparse Key := [(key545, -6), (key286, -6), (key512, -6), (key545, -6), (key372, 2), (key545, 2), (key558, 2), (key297, 2), (key525, 2), (key558, 2), (key286, 2), (key297, 2), (key355, 2), (key372, 2), (key525, 2), (key545, 2)]

def rawRow12786 : Integer.Sparse Key := [(key545, -6), (key286, -6), (key545, -6), (key512, -6), (key372, 2), (key558, 2), (key545, 2), (key297, 2), (key558, 2), (key525, 2), (key297, 2), (key286, 2), (key372, 2), (key355, 2), (key545, 2), (key525, 2)]

def rawRow12787 : Integer.Sparse Key := [(key545, -6), (key512, -6), (key286, -6), (key545, -6), (key545, 2), (key372, 2), (key558, 2), (key525, 2), (key297, 2), (key558, 2), (key355, 2), (key525, 2), (key286, 2), (key545, 2), (key297, 2), (key372, 2)]

def rawRow12788 : Integer.Sparse Key := [(key545, -6), (key512, -6), (key545, -6), (key286, -6), (key545, 2), (key558, 2), (key372, 2), (key525, 2), (key558, 2), (key297, 2), (key525, 2), (key355, 2), (key545, 2), (key286, 2), (key372, 2), (key297, 2)]

def rawRow12789 : Integer.Sparse Key := [(key545, -6), (key545, -6), (key286, -6), (key512, -6), (key558, 2), (key372, 2), (key545, 2), (key558, 2), (key297, 2), (key525, 2), (key372, 2), (key545, 2), (key297, 2), (key525, 2), (key286, 2), (key355, 2)]

def rawRow12790 : Integer.Sparse Key := [(key545, -6), (key545, -6), (key512, -6), (key286, -6), (key558, 2), (key545, 2), (key372, 2), (key558, 2), (key525, 2), (key297, 2), (key545, 2), (key372, 2), (key525, 2), (key297, 2), (key355, 2), (key286, 2)]

def rawRow12791 : Integer.Sparse Key := [(key297, -6), (key525, -6), (key525, -6), (key558, -6), (key286, 2), (key286, 2), (key297, 2), (key355, 2), (key355, 2), (key372, 2), (key512, 2), (key525, 2), (key512, 2), (key545, 2), (key525, 2), (key545, 2)]

def rawRow12792 : Integer.Sparse Key := [(key297, -6), (key525, -6), (key558, -6), (key525, -6), (key286, 2), (key297, 2), (key286, 2), (key355, 2), (key372, 2), (key355, 2), (key525, 2), (key512, 2), (key545, 2), (key512, 2), (key545, 2), (key525, 2)]

def rawRow12793 : Integer.Sparse Key := [(key297, -6), (key558, -6), (key525, -6), (key525, -6), (key297, 2), (key286, 2), (key286, 2), (key372, 2), (key355, 2), (key355, 2), (key545, 2), (key545, 2), (key525, 2), (key525, 2), (key512, 2), (key512, 2)]

def rawRow12794 : Integer.Sparse Key := [(key525, -6), (key297, -6), (key525, -6), (key558, -6), (key355, 2), (key512, 2), (key525, 2), (key286, 2), (key512, 2), (key545, 2), (key286, 2), (key297, 2), (key355, 2), (key372, 2), (key525, 2), (key545, 2)]

def rawRow12795 : Integer.Sparse Key := [(key525, -6), (key297, -6), (key558, -6), (key525, -6), (key355, 2), (key525, 2), (key512, 2), (key286, 2), (key545, 2), (key512, 2), (key297, 2), (key286, 2), (key372, 2), (key355, 2), (key545, 2), (key525, 2)]

def rawRow12796 : Integer.Sparse Key := [(key525, -6), (key525, -6), (key297, -6), (key558, -6), (key512, 2), (key355, 2), (key525, 2), (key512, 2), (key286, 2), (key545, 2), (key355, 2), (key525, 2), (key286, 2), (key545, 2), (key297, 2), (key372, 2)]

def rawRow12797 : Integer.Sparse Key := [(key525, -6), (key525, -6), (key558, -6), (key297, -6), (key512, 2), (key525, 2), (key355, 2), (key512, 2), (key545, 2), (key286, 2), (key525, 2), (key355, 2), (key545, 2), (key286, 2), (key372, 2), (key297, 2)]

def rawRow12798 : Integer.Sparse Key := [(key525, -6), (key558, -6), (key297, -6), (key525, -6), (key525, 2), (key355, 2), (key512, 2), (key545, 2), (key286, 2), (key512, 2), (key372, 2), (key545, 2), (key297, 2), (key525, 2), (key286, 2), (key355, 2)]

def rawRow12799 : Integer.Sparse Key := [(key525, -6), (key558, -6), (key525, -6), (key297, -6), (key525, 2), (key512, 2), (key355, 2), (key545, 2), (key512, 2), (key286, 2), (key545, 2), (key372, 2), (key525, 2), (key297, 2), (key355, 2), (key286, 2)]

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

def rawRow12800 : Integer.Sparse Key := [(key558, -6), (key297, -6), (key525, -6), (key525, -6), (key372, 2), (key545, 2), (key545, 2), (key297, 2), (key525, 2), (key525, 2), (key286, 2), (key286, 2), (key355, 2), (key355, 2), (key512, 2), (key512, 2)]

def rawRow12801 : Integer.Sparse Key := [(key558, -6), (key525, -6), (key297, -6), (key525, -6), (key545, 2), (key372, 2), (key545, 2), (key525, 2), (key297, 2), (key525, 2), (key355, 2), (key512, 2), (key286, 2), (key512, 2), (key286, 2), (key355, 2)]

def rawRow12802 : Integer.Sparse Key := [(key558, -6), (key525, -6), (key525, -6), (key297, -6), (key545, 2), (key545, 2), (key372, 2), (key525, 2), (key525, 2), (key297, 2), (key512, 2), (key355, 2), (key512, 2), (key286, 2), (key355, 2), (key286, 2)]

def rawRow12803 : Integer.Sparse Key := [(key1704, 6), (key1704, 6), (key1708, 6), (key1857, 6), (key1285, -6), (key1708, -6), (key1758, -6), (key1758, -6)]

def rawRow12804 : Integer.Sparse Key := [(key1704, 6), (key1708, 6), (key1704, 6), (key1857, 6), (key1285, -6), (key1758, -6), (key1708, -6), (key1758, -6)]

def rawRow12805 : Integer.Sparse Key := [(key1708, 6), (key1704, 6), (key1704, 6), (key1857, 6), (key1285, -6), (key1758, -6), (key1758, -6), (key1708, -6)]

def rawRow12806 : Integer.Sparse Key := [(key1704, 6), (key1704, 6), (key1857, 6), (key1708, 6), (key1708, -6), (key1285, -6), (key1758, -6), (key1758, -6)]

def rawRow12807 : Integer.Sparse Key := [(key1704, 6), (key1857, 6), (key1704, 6), (key1708, 6), (key1708, -6), (key1758, -6), (key1285, -6), (key1758, -6)]

def rawRow12808 : Integer.Sparse Key := [(key1857, 6), (key1704, 6), (key1704, 6), (key1708, 6), (key1708, -6), (key1758, -6), (key1758, -6), (key1285, -6)]

def rawRow12809 : Integer.Sparse Key := [(key1704, 6), (key1708, 6), (key1857, 6), (key1704, 6), (key1758, -6), (key1285, -6), (key1708, -6), (key1758, -6)]

def rawRow12810 : Integer.Sparse Key := [(key1708, 6), (key1704, 6), (key1857, 6), (key1704, 6), (key1758, -6), (key1285, -6), (key1758, -6), (key1708, -6)]

def rawRow12811 : Integer.Sparse Key := [(key1704, 6), (key1857, 6), (key1708, 6), (key1704, 6), (key1758, -6), (key1708, -6), (key1285, -6), (key1758, -6)]

def rawRow12812 : Integer.Sparse Key := [(key1857, 6), (key1704, 6), (key1708, 6), (key1704, 6), (key1758, -6), (key1708, -6), (key1758, -6), (key1285, -6)]

def rawRow12813 : Integer.Sparse Key := [(key1708, 6), (key1857, 6), (key1704, 6), (key1704, 6), (key1758, -6), (key1758, -6), (key1285, -6), (key1708, -6)]

def rawRow12814 : Integer.Sparse Key := [(key1857, 6), (key1708, 6), (key1704, 6), (key1704, 6), (key1758, -6), (key1758, -6), (key1708, -6), (key1285, -6)]

def rawRow12815 : Integer.Sparse Key := [(key1753, 6), (key1758, 6), (key1758, 6), (key1888, 6), (key1281, -6), (key1704, -6), (key1704, -6), (key1753, -6)]

def rawRow12816 : Integer.Sparse Key := [(key1758, 6), (key1753, 6), (key1758, 6), (key1888, 6), (key1281, -6), (key1704, -6), (key1753, -6), (key1704, -6)]

def rawRow12817 : Integer.Sparse Key := [(key1758, 6), (key1758, 6), (key1753, 6), (key1888, 6), (key1281, -6), (key1753, -6), (key1704, -6), (key1704, -6)]

def rawRow12818 : Integer.Sparse Key := [(key1753, 6), (key1758, 6), (key1888, 6), (key1758, 6), (key1704, -6), (key1281, -6), (key1704, -6), (key1753, -6)]

def rawRow12819 : Integer.Sparse Key := [(key1758, 6), (key1753, 6), (key1888, 6), (key1758, 6), (key1704, -6), (key1281, -6), (key1753, -6), (key1704, -6)]

def rawRow12820 : Integer.Sparse Key := [(key1753, 6), (key1888, 6), (key1758, 6), (key1758, 6), (key1704, -6), (key1704, -6), (key1281, -6), (key1753, -6)]

def rawRow12821 : Integer.Sparse Key := [(key1888, 6), (key1753, 6), (key1758, 6), (key1758, 6), (key1704, -6), (key1704, -6), (key1753, -6), (key1281, -6)]

def rawRow12822 : Integer.Sparse Key := [(key1758, 6), (key1888, 6), (key1753, 6), (key1758, 6), (key1704, -6), (key1753, -6), (key1281, -6), (key1704, -6)]

def rawRow12823 : Integer.Sparse Key := [(key1888, 6), (key1758, 6), (key1753, 6), (key1758, 6), (key1704, -6), (key1753, -6), (key1704, -6), (key1281, -6)]

def rawRow12824 : Integer.Sparse Key := [(key1758, 6), (key1758, 6), (key1888, 6), (key1753, 6), (key1753, -6), (key1281, -6), (key1704, -6), (key1704, -6)]

def rawRow12825 : Integer.Sparse Key := [(key1758, 6), (key1888, 6), (key1758, 6), (key1753, 6), (key1753, -6), (key1704, -6), (key1281, -6), (key1704, -6)]

def rawRow12826 : Integer.Sparse Key := [(key1888, 6), (key1758, 6), (key1758, 6), (key1753, 6), (key1753, -6), (key1704, -6), (key1704, -6), (key1281, -6)]

def rawRow12827 : Integer.Sparse Key := [(key1702, 6), (key1702, 6), (key1708, 6), (key1935, 6), (key1285, -6), (key1708, -6), (key1758, -6), (key1758, -6)]

def rawRow12828 : Integer.Sparse Key := [(key1702, 6), (key1708, 6), (key1702, 6), (key1935, 6), (key1285, -6), (key1758, -6), (key1708, -6), (key1758, -6)]

def rawRow12829 : Integer.Sparse Key := [(key1708, 6), (key1702, 6), (key1702, 6), (key1935, 6), (key1285, -6), (key1758, -6), (key1758, -6), (key1708, -6)]

def rawRow12830 : Integer.Sparse Key := [(key1702, 6), (key1702, 6), (key1935, 6), (key1708, 6), (key1708, -6), (key1285, -6), (key1758, -6), (key1758, -6)]

def rawRow12831 : Integer.Sparse Key := [(key1702, 6), (key1935, 6), (key1702, 6), (key1708, 6), (key1708, -6), (key1758, -6), (key1285, -6), (key1758, -6)]

def rawRow12832 : Integer.Sparse Key := [(key1935, 6), (key1702, 6), (key1702, 6), (key1708, 6), (key1708, -6), (key1758, -6), (key1758, -6), (key1285, -6)]

def rawRow12833 : Integer.Sparse Key := [(key1702, 6), (key1708, 6), (key1935, 6), (key1702, 6), (key1758, -6), (key1285, -6), (key1708, -6), (key1758, -6)]

def rawRow12834 : Integer.Sparse Key := [(key1708, 6), (key1702, 6), (key1935, 6), (key1702, 6), (key1758, -6), (key1285, -6), (key1758, -6), (key1708, -6)]

def rawRow12835 : Integer.Sparse Key := [(key1702, 6), (key1935, 6), (key1708, 6), (key1702, 6), (key1758, -6), (key1708, -6), (key1285, -6), (key1758, -6)]

def rawRow12836 : Integer.Sparse Key := [(key1935, 6), (key1702, 6), (key1708, 6), (key1702, 6), (key1758, -6), (key1708, -6), (key1758, -6), (key1285, -6)]

def rawRow12837 : Integer.Sparse Key := [(key1708, 6), (key1935, 6), (key1702, 6), (key1702, 6), (key1758, -6), (key1758, -6), (key1285, -6), (key1708, -6)]

def rawRow12838 : Integer.Sparse Key := [(key1935, 6), (key1708, 6), (key1702, 6), (key1702, 6), (key1758, -6), (key1758, -6), (key1708, -6), (key1285, -6)]

def rawRow12839 : Integer.Sparse Key := [(key1752, 6), (key1758, 6), (key1758, 6), (key1955, 6), (key1279, -6), (key1702, -6), (key1702, -6), (key1752, -6)]

def rawRow12840 : Integer.Sparse Key := [(key1758, 6), (key1752, 6), (key1758, 6), (key1955, 6), (key1279, -6), (key1702, -6), (key1752, -6), (key1702, -6)]

def rawRow12841 : Integer.Sparse Key := [(key1758, 6), (key1758, 6), (key1752, 6), (key1955, 6), (key1279, -6), (key1752, -6), (key1702, -6), (key1702, -6)]

def rawRow12842 : Integer.Sparse Key := [(key1752, 6), (key1758, 6), (key1955, 6), (key1758, 6), (key1702, -6), (key1279, -6), (key1702, -6), (key1752, -6)]

def rawRow12843 : Integer.Sparse Key := [(key1758, 6), (key1752, 6), (key1955, 6), (key1758, 6), (key1702, -6), (key1279, -6), (key1752, -6), (key1702, -6)]

def rawRow12844 : Integer.Sparse Key := [(key1752, 6), (key1955, 6), (key1758, 6), (key1758, 6), (key1702, -6), (key1702, -6), (key1279, -6), (key1752, -6)]

def rawRow12845 : Integer.Sparse Key := [(key1955, 6), (key1752, 6), (key1758, 6), (key1758, 6), (key1702, -6), (key1702, -6), (key1752, -6), (key1279, -6)]

def rawRow12846 : Integer.Sparse Key := [(key1758, 6), (key1955, 6), (key1752, 6), (key1758, 6), (key1702, -6), (key1752, -6), (key1279, -6), (key1702, -6)]

def rawRow12847 : Integer.Sparse Key := [(key1955, 6), (key1758, 6), (key1752, 6), (key1758, 6), (key1702, -6), (key1752, -6), (key1702, -6), (key1279, -6)]

def rawRow12848 : Integer.Sparse Key := [(key1758, 6), (key1758, 6), (key1955, 6), (key1752, 6), (key1752, -6), (key1279, -6), (key1702, -6), (key1702, -6)]

def rawRow12849 : Integer.Sparse Key := [(key1758, 6), (key1955, 6), (key1758, 6), (key1752, 6), (key1752, -6), (key1702, -6), (key1279, -6), (key1702, -6)]

def rawRow12850 : Integer.Sparse Key := [(key1955, 6), (key1758, 6), (key1758, 6), (key1752, 6), (key1752, -6), (key1702, -6), (key1702, -6), (key1279, -6)]

def rawRow12851 : Integer.Sparse Key := [(key866, -6), (key866, -6), (key868, -6), (key882, -6), (key732, 2), (key732, 2), (key734, 2), (key866, 2), (key866, 2), (key900, 2), (key900, 2), (key901, 2), (key901, 2), (key882, 2), (key913, 2), (key913, 2)]

def rawRow12852 : Integer.Sparse Key := [(key866, -6), (key868, -6), (key866, -6), (key882, -6), (key732, 2), (key734, 2), (key732, 2), (key900, 2), (key901, 2), (key866, 2), (key901, 2), (key866, 2), (key900, 2), (key913, 2), (key882, 2), (key913, 2)]

def rawRow12853 : Integer.Sparse Key := [(key868, -6), (key866, -6), (key866, -6), (key882, -6), (key734, 2), (key732, 2), (key732, 2), (key901, 2), (key900, 2), (key901, 2), (key866, 2), (key900, 2), (key866, 2), (key913, 2), (key913, 2), (key882, 2)]

def rawRow12854 : Integer.Sparse Key := [(key866, -6), (key866, -6), (key882, -6), (key868, -6), (key866, 2), (key866, 2), (key882, 2), (key732, 2), (key732, 2), (key900, 2), (key900, 2), (key913, 2), (key913, 2), (key734, 2), (key901, 2), (key901, 2)]

def rawRow12855 : Integer.Sparse Key := [(key866, -6), (key882, -6), (key866, -6), (key868, -6), (key866, 2), (key882, 2), (key866, 2), (key900, 2), (key913, 2), (key732, 2), (key913, 2), (key732, 2), (key900, 2), (key901, 2), (key734, 2), (key901, 2)]

def rawRow12856 : Integer.Sparse Key := [(key882, -6), (key866, -6), (key866, -6), (key868, -6), (key882, 2), (key866, 2), (key866, 2), (key913, 2), (key900, 2), (key913, 2), (key732, 2), (key900, 2), (key732, 2), (key901, 2), (key901, 2), (key734, 2)]

def rawRow12857 : Integer.Sparse Key := [(key866, -6), (key868, -6), (key882, -6), (key866, -6), (key900, 2), (key901, 2), (key913, 2), (key732, 2), (key734, 2), (key866, 2), (key901, 2), (key882, 2), (key913, 2), (key732, 2), (key866, 2), (key900, 2)]

def rawRow12858 : Integer.Sparse Key := [(key868, -6), (key866, -6), (key882, -6), (key866, -6), (key901, 2), (key900, 2), (key913, 2), (key734, 2), (key732, 2), (key901, 2), (key866, 2), (key913, 2), (key882, 2), (key732, 2), (key900, 2), (key866, 2)]

def rawRow12859 : Integer.Sparse Key := [(key866, -6), (key882, -6), (key868, -6), (key866, -6), (key900, 2), (key913, 2), (key901, 2), (key866, 2), (key882, 2), (key732, 2), (key913, 2), (key734, 2), (key901, 2), (key866, 2), (key732, 2), (key900, 2)]

def rawRow12860 : Integer.Sparse Key := [(key882, -6), (key866, -6), (key868, -6), (key866, -6), (key913, 2), (key900, 2), (key901, 2), (key882, 2), (key866, 2), (key913, 2), (key732, 2), (key901, 2), (key734, 2), (key866, 2), (key900, 2), (key732, 2)]

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

def rawRow20097 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key627, 24), (key640, 24), (key629, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1214 : Integer.Sparse Key := [(key318, -6), (key437, 2), (key408, 2), (key441, 2), (key250, 6), (key437, -2), (key387, -2), (key449, -2), (key250, -2), (key238, -2), (key259, -2), (key318, 2), (key304, 2), (key327, 2)]

def rawRow1215 : Integer.Sparse Key := [(key318, -6), (key437, 2), (key441, 2), (key408, 2), (key250, 6), (key437, -2), (key449, -2), (key387, -2), (key250, -2), (key259, -2), (key238, -2), (key318, 2), (key327, 2), (key304, 2)]

def rawRow1216 : Integer.Sparse Key := [(key318, -6), (key441, 2), (key408, 2), (key437, 2), (key250, 6), (key449, -2), (key387, -2), (key437, -2), (key259, -2), (key238, -2), (key250, -2), (key327, 2), (key304, 2), (key318, 2)]

def rawRow1217 : Integer.Sparse Key := [(key318, -6), (key441, 2), (key437, 2), (key408, 2), (key250, 6), (key449, -2), (key437, -2), (key387, -2), (key259, -2), (key250, -2), (key238, -2), (key327, 2), (key318, 2), (key304, 2)]

def rawRow1218 : Integer.Sparse Key := [(key1291, -2), (key1299, -2), (key1299, -2), (key1311, 1), (key1319, 1), (key1311, 1), (key1327, 1), (key1319, 1), (key1327, 1), (key1386, 2), (key1394, 2), (key1394, 2), (key1419, -1), (key1427, -1), (key1419, -1), (key1445, -1), (key1427, -1), (key1445, -1), (key1541, -1), (key1549, -1), (key1541, -1), (key1557, -1), (key1549, -1), (key1557, -1), (key1568, 1), (key1576, 1), (key1568, 1), (key1594, 1), (key1576, 1), (key1594, 1)]

def rawRow1219 : Integer.Sparse Key := [(key1299, -2), (key1291, -2), (key1299, -2), (key1319, 1), (key1311, 1), (key1327, 1), (key1311, 1), (key1327, 1), (key1319, 1), (key1394, 2), (key1386, 2), (key1394, 2), (key1427, -1), (key1419, -1), (key1445, -1), (key1419, -1), (key1445, -1), (key1427, -1), (key1549, -1), (key1541, -1), (key1557, -1), (key1541, -1), (key1557, -1), (key1549, -1), (key1576, 1), (key1568, 1), (key1594, 1), (key1568, 1), (key1594, 1), (key1576, 1)]

def rawRow1220 : Integer.Sparse Key := [(key1299, -2), (key1299, -2), (key1291, -2), (key1327, 1), (key1327, 1), (key1319, 1), (key1319, 1), (key1311, 1), (key1311, 1), (key1394, 2), (key1394, 2), (key1386, 2), (key1445, -1), (key1445, -1), (key1427, -1), (key1427, -1), (key1419, -1), (key1419, -1), (key1557, -1), (key1557, -1), (key1549, -1), (key1549, -1), (key1541, -1), (key1541, -1), (key1594, 1), (key1594, 1), (key1576, 1), (key1576, 1), (key1568, 1), (key1568, 1)]

def rawRow1221 : Integer.Sparse Key := [(key1311, -2), (key1319, -2), (key1352, -2), (key1291, 1), (key1299, 1), (key1311, 1), (key1327, 1), (key1352, 1), (key1355, 1), (key1419, 2), (key1427, 2), (key1473, 2), (key1386, -1), (key1394, -1), (key1419, -1), (key1445, -1), (key1473, -1), (key1481, -1), (key1568, -1), (key1576, -1), (key1617, -1), (key1625, -1), (key1682, -1), (key1684, -1), (key1541, 1), (key1549, 1), (key1617, 1), (key1634, 1), (key1682, 1), (key1690, 1)]

def rawRow1222 : Integer.Sparse Key := [(key1319, -2), (key1311, -2), (key1352, -2), (key1299, 1), (key1291, 1), (key1327, 1), (key1311, 1), (key1355, 1), (key1352, 1), (key1427, 2), (key1419, 2), (key1473, 2), (key1394, -1), (key1386, -1), (key1445, -1), (key1419, -1), (key1481, -1), (key1473, -1), (key1576, -1), (key1568, -1), (key1625, -1), (key1617, -1), (key1684, -1), (key1682, -1), (key1549, 1), (key1541, 1), (key1634, 1), (key1617, 1), (key1690, 1), (key1682, 1)]

def rawRow1223 : Integer.Sparse Key := [(key1311, -2), (key1352, -2), (key1319, -2), (key1311, 1), (key1352, 1), (key1291, 1), (key1355, 1), (key1299, 1), (key1327, 1), (key1419, 2), (key1473, 2), (key1427, 2), (key1419, -1), (key1473, -1), (key1386, -1), (key1481, -1), (key1394, -1), (key1445, -1), (key1617, -1), (key1682, -1), (key1568, -1), (key1684, -1), (key1576, -1), (key1625, -1), (key1617, 1), (key1682, 1), (key1541, 1), (key1690, 1), (key1549, 1), (key1634, 1)]

def rawRow1224 : Integer.Sparse Key := [(key1352, -2), (key1311, -2), (key1319, -2), (key1352, 1), (key1311, 1), (key1355, 1), (key1291, 1), (key1327, 1), (key1299, 1), (key1473, 2), (key1419, 2), (key1427, 2), (key1473, -1), (key1419, -1), (key1481, -1), (key1386, -1), (key1445, -1), (key1394, -1), (key1682, -1), (key1617, -1), (key1684, -1), (key1568, -1), (key1625, -1), (key1576, -1), (key1682, 1), (key1617, 1), (key1690, 1), (key1541, 1), (key1634, 1), (key1549, 1)]

def rawRow1225 : Integer.Sparse Key := [(key1319, -2), (key1352, -2), (key1311, -2), (key1327, 1), (key1355, 1), (key1299, 1), (key1352, 1), (key1291, 1), (key1311, 1), (key1427, 2), (key1473, 2), (key1419, 2), (key1445, -1), (key1481, -1), (key1394, -1), (key1473, -1), (key1386, -1), (key1419, -1), (key1625, -1), (key1684, -1), (key1576, -1), (key1682, -1), (key1568, -1), (key1617, -1), (key1634, 1), (key1690, 1), (key1549, 1), (key1682, 1), (key1541, 1), (key1617, 1)]

def rawRow1226 : Integer.Sparse Key := [(key1352, -2), (key1319, -2), (key1311, -2), (key1355, 1), (key1327, 1), (key1352, 1), (key1299, 1), (key1311, 1), (key1291, 1), (key1473, 2), (key1427, 2), (key1419, 2), (key1481, -1), (key1445, -1), (key1473, -1), (key1394, -1), (key1419, -1), (key1386, -1), (key1684, -1), (key1625, -1), (key1682, -1), (key1576, -1), (key1617, -1), (key1568, -1), (key1690, 1), (key1634, 1), (key1682, 1), (key1549, 1), (key1617, 1), (key1541, 1)]

def rawRow1227 : Integer.Sparse Key := [(key1386, -2), (key1394, -2), (key1394, -2), (key1541, 1), (key1549, 1), (key1541, 1), (key1557, 1), (key1549, 1), (key1557, 1), (key1291, 2), (key1299, 2), (key1299, 2), (key1568, -1), (key1576, -1), (key1568, -1), (key1594, -1), (key1576, -1), (key1594, -1), (key1311, -1), (key1319, -1), (key1311, -1), (key1327, -1), (key1319, -1), (key1327, -1), (key1419, 1), (key1427, 1), (key1419, 1), (key1445, 1), (key1427, 1), (key1445, 1)]

def rawRow1228 : Integer.Sparse Key := [(key1394, -2), (key1386, -2), (key1394, -2), (key1549, 1), (key1541, 1), (key1557, 1), (key1541, 1), (key1557, 1), (key1549, 1), (key1299, 2), (key1291, 2), (key1299, 2), (key1576, -1), (key1568, -1), (key1594, -1), (key1568, -1), (key1594, -1), (key1576, -1), (key1319, -1), (key1311, -1), (key1327, -1), (key1311, -1), (key1327, -1), (key1319, -1), (key1427, 1), (key1419, 1), (key1445, 1), (key1419, 1), (key1445, 1), (key1427, 1)]

def rawRow1229 : Integer.Sparse Key := [(key1394, -2), (key1394, -2), (key1386, -2), (key1557, 1), (key1557, 1), (key1549, 1), (key1549, 1), (key1541, 1), (key1541, 1), (key1299, 2), (key1299, 2), (key1291, 2), (key1594, -1), (key1594, -1), (key1576, -1), (key1576, -1), (key1568, -1), (key1568, -1), (key1327, -1), (key1327, -1), (key1319, -1), (key1319, -1), (key1311, -1), (key1311, -1), (key1445, 1), (key1445, 1), (key1427, 1), (key1427, 1), (key1419, 1), (key1419, 1)]

def rawRow1230 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1473, -2), (key1568, 1), (key1576, 1), (key1617, 1), (key1625, 1), (key1682, 1), (key1684, 1), (key1311, 2), (key1319, 2), (key1352, 2), (key1541, -1), (key1549, -1), (key1617, -1), (key1634, -1), (key1682, -1), (key1690, -1), (key1291, -1), (key1299, -1), (key1311, -1), (key1327, -1), (key1352, -1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1)]

def rawRow1231 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1473, -2), (key1576, 1), (key1568, 1), (key1625, 1), (key1617, 1), (key1684, 1), (key1682, 1), (key1319, 2), (key1311, 2), (key1352, 2), (key1549, -1), (key1541, -1), (key1634, -1), (key1617, -1), (key1690, -1), (key1682, -1), (key1299, -1), (key1291, -1), (key1327, -1), (key1311, -1), (key1355, -1), (key1352, -1), (key1394, 1), (key1386, 1), (key1445, 1), (key1419, 1), (key1481, 1), (key1473, 1)]

def rawRow1232 : Integer.Sparse Key := [(key1419, -2), (key1473, -2), (key1427, -2), (key1617, 1), (key1682, 1), (key1568, 1), (key1684, 1), (key1576, 1), (key1625, 1), (key1311, 2), (key1352, 2), (key1319, 2), (key1617, -1), (key1682, -1), (key1541, -1), (key1690, -1), (key1549, -1), (key1634, -1), (key1311, -1), (key1352, -1), (key1291, -1), (key1355, -1), (key1299, -1), (key1327, -1), (key1419, 1), (key1473, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1445, 1)]

def rawRow1233 : Integer.Sparse Key := [(key1473, -2), (key1419, -2), (key1427, -2), (key1682, 1), (key1617, 1), (key1684, 1), (key1568, 1), (key1625, 1), (key1576, 1), (key1352, 2), (key1311, 2), (key1319, 2), (key1682, -1), (key1617, -1), (key1690, -1), (key1541, -1), (key1634, -1), (key1549, -1), (key1352, -1), (key1311, -1), (key1355, -1), (key1291, -1), (key1327, -1), (key1299, -1), (key1473, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1445, 1), (key1394, 1)]

def rawRow1234 : Integer.Sparse Key := [(key1427, -2), (key1473, -2), (key1419, -2), (key1625, 1), (key1684, 1), (key1576, 1), (key1682, 1), (key1568, 1), (key1617, 1), (key1319, 2), (key1352, 2), (key1311, 2), (key1634, -1), (key1690, -1), (key1549, -1), (key1682, -1), (key1541, -1), (key1617, -1), (key1327, -1), (key1355, -1), (key1299, -1), (key1352, -1), (key1291, -1), (key1311, -1), (key1445, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1386, 1), (key1419, 1)]

def rawRow1235 : Integer.Sparse Key := [(key1473, -2), (key1427, -2), (key1419, -2), (key1684, 1), (key1625, 1), (key1682, 1), (key1576, 1), (key1617, 1), (key1568, 1), (key1352, 2), (key1319, 2), (key1311, 2), (key1690, -1), (key1634, -1), (key1682, -1), (key1549, -1), (key1617, -1), (key1541, -1), (key1355, -1), (key1327, -1), (key1352, -1), (key1299, -1), (key1311, -1), (key1291, -1), (key1481, 1), (key1445, 1), (key1473, 1), (key1394, 1), (key1419, 1), (key1386, 1)]

def rawRow1236 : Integer.Sparse Key := [(key18, -2), (key23, -2), (key23, -2), (key35, 6), (key375, 2), (key381, 2), (key381, 2), (key486, -2), (key486, -2), (key490, -2), (key654, -6), (key659, 2), (key659, 2), (key663, 2)]

def rawRow1237 : Integer.Sparse Key := [(key23, -2), (key18, -2), (key23, -2), (key35, 6), (key381, 2), (key375, 2), (key381, 2), (key486, -2), (key490, -2), (key486, -2), (key654, -6), (key659, 2), (key663, 2), (key659, 2)]

def rawRow1238 : Integer.Sparse Key := [(key23, -2), (key23, -2), (key18, -2), (key35, 6), (key381, 2), (key381, 2), (key375, 2), (key490, -2), (key486, -2), (key486, -2), (key654, -6), (key663, 2), (key659, 2), (key659, 2)]

def rawRow1239 : Integer.Sparse Key := [(key18, -2), (key23, -2), (key35, -2), (key23, 6), (key426, 2), (key432, 2), (key486, 2), (key381, -2), (key432, -2), (key460, -2), (key659, -6), (key654, 2), (key659, 2), (key663, 2)]

def rawRow1240 : Integer.Sparse Key := [(key23, -2), (key18, -2), (key35, -2), (key23, 6), (key432, 2), (key426, 2), (key486, 2), (key381, -2), (key460, -2), (key432, -2), (key659, -6), (key654, 2), (key663, 2), (key659, 2)]

def rawRow1241 : Integer.Sparse Key := [(key18, -2), (key35, -2), (key23, -2), (key23, 6), (key426, 2), (key486, 2), (key432, 2), (key432, -2), (key381, -2), (key460, -2), (key659, -6), (key659, 2), (key654, 2), (key663, 2)]

def rawRow1242 : Integer.Sparse Key := [(key35, -2), (key18, -2), (key23, -2), (key23, 6), (key486, 2), (key426, 2), (key432, 2), (key432, -2), (key460, -2), (key381, -2), (key659, -6), (key659, 2), (key663, 2), (key654, 2)]

def rawRow1243 : Integer.Sparse Key := [(key23, -2), (key35, -2), (key18, -2), (key23, 6), (key432, 2), (key486, 2), (key426, 2), (key460, -2), (key381, -2), (key432, -2), (key659, -6), (key663, 2), (key654, 2), (key659, 2)]

def rawRow1244 : Integer.Sparse Key := [(key35, -2), (key23, -2), (key18, -2), (key23, 6), (key486, 2), (key432, 2), (key426, 2), (key460, -2), (key432, -2), (key381, -2), (key659, -6), (key663, 2), (key659, 2), (key654, 2)]

def rawRow1245 : Integer.Sparse Key := [(key43, -2), (key48, -2), (key48, -2), (key74, 6), (key206, 2), (key212, 2), (key212, 2), (key659, -2), (key659, -2), (key663, -2), (key218, -6), (key486, 2), (key486, 2), (key490, 2)]

def rawRow1246 : Integer.Sparse Key := [(key48, -2), (key43, -2), (key48, -2), (key74, 6), (key212, 2), (key206, 2), (key212, 2), (key659, -2), (key663, -2), (key659, -2), (key218, -6), (key486, 2), (key490, 2), (key486, 2)]

def rawRow1247 : Integer.Sparse Key := [(key48, -2), (key48, -2), (key43, -2), (key74, 6), (key212, 2), (key212, 2), (key206, 2), (key663, -2), (key659, -2), (key659, -2), (key218, -6), (key490, 2), (key486, 2), (key486, 2)]

def rawRow1248 : Integer.Sparse Key := [(key100, -2), (key105, -2), (key115, -2), (key137, 6), (key18, 2), (key23, 2), (key35, 2), (key654, -2), (key659, -2), (key663, -2), (key212, -6), (key381, 2), (key432, 2), (key460, 2)]

def rawRow1249 : Integer.Sparse Key := [(key105, -2), (key100, -2), (key115, -2), (key137, 6), (key23, 2), (key18, 2), (key35, 2), (key654, -2), (key663, -2), (key659, -2), (key212, -6), (key381, 2), (key460, 2), (key432, 2)]

def rawRow1250 : Integer.Sparse Key := [(key100, -2), (key115, -2), (key105, -2), (key137, 6), (key18, 2), (key35, 2), (key23, 2), (key659, -2), (key654, -2), (key663, -2), (key212, -6), (key432, 2), (key381, 2), (key460, 2)]

def rawRow1251 : Integer.Sparse Key := [(key115, -2), (key100, -2), (key105, -2), (key137, 6), (key35, 2), (key18, 2), (key23, 2), (key659, -2), (key663, -2), (key654, -2), (key212, -6), (key432, 2), (key460, 2), (key381, 2)]

def rawRow1252 : Integer.Sparse Key := [(key105, -2), (key115, -2), (key100, -2), (key137, 6), (key23, 2), (key35, 2), (key18, 2), (key663, -2), (key654, -2), (key659, -2), (key212, -6), (key460, 2), (key381, 2), (key432, 2)]

def rawRow1253 : Integer.Sparse Key := [(key115, -2), (key105, -2), (key100, -2), (key137, 6), (key35, 2), (key23, 2), (key18, 2), (key663, -2), (key659, -2), (key654, -2), (key212, -6), (key460, 2), (key432, 2), (key381, 2)]

def rawRow1254 : Integer.Sparse Key := [(key1293, -6), (key1313, 2), (key1313, 2), (key1323, 2), (key1388, 6), (key1421, -2), (key1421, -2), (key1441, -2), (key1543, -2), (key1543, -2), (key1553, -2), (key1570, 2), (key1570, 2), (key1590, 2)]

def rawRow1255 : Integer.Sparse Key := [(key1293, -6), (key1313, 2), (key1323, 2), (key1313, 2), (key1388, 6), (key1421, -2), (key1441, -2), (key1421, -2), (key1543, -2), (key1553, -2), (key1543, -2), (key1570, 2), (key1590, 2), (key1570, 2)]

def rawRow1256 : Integer.Sparse Key := [(key1293, -6), (key1323, 2), (key1313, 2), (key1313, 2), (key1388, 6), (key1441, -2), (key1421, -2), (key1421, -2), (key1553, -2), (key1543, -2), (key1543, -2), (key1590, 2), (key1570, 2), (key1570, 2)]

def rawRow1257 : Integer.Sparse Key := [(key1313, -6), (key1293, 2), (key1313, 2), (key1323, 2), (key1421, 6), (key1388, -2), (key1421, -2), (key1441, -2), (key1570, -2), (key1619, -2), (key1621, -2), (key1543, 2), (key1619, 2), (key1630, 2)]

def rawRow1258 : Integer.Sparse Key := [(key1313, -6), (key1293, 2), (key1323, 2), (key1313, 2), (key1421, 6), (key1388, -2), (key1441, -2), (key1421, -2), (key1570, -2), (key1621, -2), (key1619, -2), (key1543, 2), (key1630, 2), (key1619, 2)]

def rawRow1259 : Integer.Sparse Key := [(key1313, -6), (key1313, 2), (key1293, 2), (key1323, 2), (key1421, 6), (key1421, -2), (key1388, -2), (key1441, -2), (key1619, -2), (key1570, -2), (key1621, -2), (key1619, 2), (key1543, 2), (key1630, 2)]

def rawRow1260 : Integer.Sparse Key := [(key1313, -6), (key1313, 2), (key1323, 2), (key1293, 2), (key1421, 6), (key1421, -2), (key1441, -2), (key1388, -2), (key1619, -2), (key1621, -2), (key1570, -2), (key1619, 2), (key1630, 2), (key1543, 2)]

def rawRow1261 : Integer.Sparse Key := [(key1313, -6), (key1323, 2), (key1293, 2), (key1313, 2), (key1421, 6), (key1441, -2), (key1388, -2), (key1421, -2), (key1621, -2), (key1570, -2), (key1619, -2), (key1630, 2), (key1543, 2), (key1619, 2)]

def rawRow1262 : Integer.Sparse Key := [(key1313, -6), (key1323, 2), (key1313, 2), (key1293, 2), (key1421, 6), (key1441, -2), (key1421, -2), (key1388, -2), (key1621, -2), (key1619, -2), (key1570, -2), (key1630, 2), (key1619, 2), (key1543, 2)]

def rawRow1263 : Integer.Sparse Key := [(key1388, -6), (key1543, 2), (key1543, 2), (key1553, 2), (key1293, 6), (key1570, -2), (key1570, -2), (key1590, -2), (key1313, -2), (key1313, -2), (key1323, -2), (key1421, 2), (key1421, 2), (key1441, 2)]

def rawRow1264 : Integer.Sparse Key := [(key1388, -6), (key1543, 2), (key1553, 2), (key1543, 2), (key1293, 6), (key1570, -2), (key1590, -2), (key1570, -2), (key1313, -2), (key1323, -2), (key1313, -2), (key1421, 2), (key1441, 2), (key1421, 2)]

def rawRow1265 : Integer.Sparse Key := [(key1388, -6), (key1553, 2), (key1543, 2), (key1543, 2), (key1293, 6), (key1590, -2), (key1570, -2), (key1570, -2), (key1323, -2), (key1313, -2), (key1313, -2), (key1441, 2), (key1421, 2), (key1421, 2)]

def rawRow1266 : Integer.Sparse Key := [(key1421, -6), (key1570, 2), (key1619, 2), (key1621, 2), (key1313, 6), (key1543, -2), (key1619, -2), (key1630, -2), (key1293, -2), (key1313, -2), (key1323, -2), (key1388, 2), (key1421, 2), (key1441, 2)]

def rawRow1267 : Integer.Sparse Key := [(key1421, -6), (key1570, 2), (key1621, 2), (key1619, 2), (key1313, 6), (key1543, -2), (key1630, -2), (key1619, -2), (key1293, -2), (key1323, -2), (key1313, -2), (key1388, 2), (key1441, 2), (key1421, 2)]

def rawRow1268 : Integer.Sparse Key := [(key1421, -6), (key1619, 2), (key1570, 2), (key1621, 2), (key1313, 6), (key1619, -2), (key1543, -2), (key1630, -2), (key1313, -2), (key1293, -2), (key1323, -2), (key1421, 2), (key1388, 2), (key1441, 2)]

def rawRow1269 : Integer.Sparse Key := [(key1421, -6), (key1619, 2), (key1621, 2), (key1570, 2), (key1313, 6), (key1619, -2), (key1630, -2), (key1543, -2), (key1313, -2), (key1323, -2), (key1293, -2), (key1421, 2), (key1441, 2), (key1388, 2)]

def rawRow1270 : Integer.Sparse Key := [(key1421, -6), (key1621, 2), (key1570, 2), (key1619, 2), (key1313, 6), (key1630, -2), (key1543, -2), (key1619, -2), (key1323, -2), (key1293, -2), (key1313, -2), (key1441, 2), (key1388, 2), (key1421, 2)]

def rawRow1271 : Integer.Sparse Key := [(key1421, -6), (key1621, 2), (key1619, 2), (key1570, 2), (key1313, 6), (key1630, -2), (key1619, -2), (key1543, -2), (key1323, -2), (key1313, -2), (key1293, -2), (key1441, 2), (key1421, 2), (key1388, 2)]

def rawRow1272 : Integer.Sparse Key := [(key316, -1), (key321, -1), (key316, -1), (key331, -1), (key321, -1), (key331, -1), (key346, 2), (key346, 2), (key347, 2), (key406, 1), (key411, 1), (key406, 1), (key421, 1), (key411, 1), (key421, 1), (key487, -1), (key488, -1), (key487, -1), (key489, -1), (key488, -1), (key489, -1), (key657, -2), (key657, -2), (key658, -2), (key660, 1), (key661, 1), (key660, 1), (key662, 1), (key661, 1), (key662, 1)]

def rawRow1273 : Integer.Sparse Key := [(key321, -1), (key316, -1), (key331, -1), (key316, -1), (key331, -1), (key321, -1), (key346, 2), (key347, 2), (key346, 2), (key411, 1), (key406, 1), (key421, 1), (key406, 1), (key421, 1), (key411, 1), (key488, -1), (key487, -1), (key489, -1), (key487, -1), (key489, -1), (key488, -1), (key657, -2), (key658, -2), (key657, -2), (key661, 1), (key660, 1), (key662, 1), (key660, 1), (key662, 1), (key661, 1)]

def rawRow1274 : Integer.Sparse Key := [(key331, -1), (key331, -1), (key321, -1), (key321, -1), (key316, -1), (key316, -1), (key347, 2), (key346, 2), (key346, 2), (key421, 1), (key421, 1), (key411, 1), (key411, 1), (key406, 1), (key406, 1), (key489, -1), (key489, -1), (key488, -1), (key488, -1), (key487, -1), (key487, -1), (key658, -2), (key657, -2), (key657, -2), (key662, 1), (key662, 1), (key661, 1), (key661, 1), (key660, 1), (key660, 1)]

def rawRow1275 : Integer.Sparse Key := [(key302, -1), (key307, -1), (key316, -1), (key331, -1), (key346, -1), (key347, -1), (key307, 2), (key321, 2), (key331, 2), (key385, 1), (key390, 1), (key435, 1), (key453, 1), (key487, 1), (key489, 1), (key390, -1), (key400, -1), (key411, -1), (key421, -1), (key445, -1), (key453, -1), (key655, -2), (key660, -2), (key662, -2), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key661, 1), (key662, 1)]

def rawRow1276 : Integer.Sparse Key := [(key307, -1), (key302, -1), (key331, -1), (key316, -1), (key347, -1), (key346, -1), (key307, 2), (key331, 2), (key321, 2), (key390, 1), (key385, 1), (key453, 1), (key435, 1), (key489, 1), (key487, 1), (key400, -1), (key390, -1), (key421, -1), (key411, -1), (key453, -1), (key445, -1), (key655, -2), (key662, -2), (key660, -2), (key656, 1), (key655, 1), (key658, 1), (key657, 1), (key662, 1), (key661, 1)]

def rawRow1277 : Integer.Sparse Key := [(key316, -1), (key346, -1), (key302, -1), (key347, -1), (key307, -1), (key331, -1), (key321, 2), (key307, 2), (key331, 2), (key435, 1), (key487, 1), (key385, 1), (key489, 1), (key390, 1), (key453, 1), (key411, -1), (key445, -1), (key390, -1), (key453, -1), (key400, -1), (key421, -1), (key660, -2), (key655, -2), (key662, -2), (key657, 1), (key661, 1), (key655, 1), (key662, 1), (key656, 1), (key658, 1)]

def rawRow1278 : Integer.Sparse Key := [(key346, -1), (key316, -1), (key347, -1), (key302, -1), (key331, -1), (key307, -1), (key321, 2), (key331, 2), (key307, 2), (key487, 1), (key435, 1), (key489, 1), (key385, 1), (key453, 1), (key390, 1), (key445, -1), (key411, -1), (key453, -1), (key390, -1), (key421, -1), (key400, -1), (key660, -2), (key662, -2), (key655, -2), (key661, 1), (key657, 1), (key662, 1), (key655, 1), (key658, 1), (key656, 1)]

def rawRow1279 : Integer.Sparse Key := [(key331, -1), (key347, -1), (key307, -1), (key346, -1), (key302, -1), (key316, -1), (key331, 2), (key307, 2), (key321, 2), (key453, 1), (key489, 1), (key390, 1), (key487, 1), (key385, 1), (key435, 1), (key421, -1), (key453, -1), (key400, -1), (key445, -1), (key390, -1), (key411, -1), (key662, -2), (key655, -2), (key660, -2), (key658, 1), (key662, 1), (key656, 1), (key661, 1), (key655, 1), (key657, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1280 : Integer.Sparse Key := [(key347, -1), (key331, -1), (key346, -1), (key307, -1), (key316, -1), (key302, -1), (key331, 2), (key321, 2), (key307, 2), (key489, 1), (key453, 1), (key487, 1), (key390, 1), (key435, 1), (key385, 1), (key453, -1), (key421, -1), (key445, -1), (key400, -1), (key411, -1), (key390, -1), (key662, -2), (key660, -2), (key655, -2), (key662, 1), (key658, 1), (key661, 1), (key656, 1), (key657, 1), (key655, 1)]

def rawRow1281 : Integer.Sparse Key := [(key406, -1), (key411, -1), (key406, -1), (key421, -1), (key411, -1), (key421, -1), (key657, 2), (key657, 2), (key658, 2), (key316, 1), (key321, 1), (key316, 1), (key331, 1), (key321, 1), (key331, 1), (key660, -1), (key661, -1), (key660, -1), (key662, -1), (key661, -1), (key662, -1), (key346, -2), (key346, -2), (key347, -2), (key487, 1), (key488, 1), (key487, 1), (key489, 1), (key488, 1), (key489, 1)]

def rawRow1282 : Integer.Sparse Key := [(key411, -1), (key406, -1), (key421, -1), (key406, -1), (key421, -1), (key411, -1), (key657, 2), (key658, 2), (key657, 2), (key321, 1), (key316, 1), (key331, 1), (key316, 1), (key331, 1), (key321, 1), (key661, -1), (key660, -1), (key662, -1), (key660, -1), (key662, -1), (key661, -1), (key346, -2), (key347, -2), (key346, -2), (key488, 1), (key487, 1), (key489, 1), (key487, 1), (key489, 1), (key488, 1)]

def rawRow1283 : Integer.Sparse Key := [(key421, -1), (key421, -1), (key411, -1), (key411, -1), (key406, -1), (key406, -1), (key658, 2), (key657, 2), (key657, 2), (key331, 1), (key331, 1), (key321, 1), (key321, 1), (key316, 1), (key316, 1), (key662, -1), (key662, -1), (key661, -1), (key661, -1), (key660, -1), (key660, -1), (key347, -2), (key346, -2), (key346, -2), (key489, 1), (key489, 1), (key488, 1), (key488, 1), (key487, 1), (key487, 1)]

def rawRow1284 : Integer.Sparse Key := [(key316, -1), (key321, -1), (key435, -1), (key660, -1), (key445, -1), (key661, -1), (key331, 2), (key453, 2), (key662, 2), (key302, 1), (key307, 1), (key316, 1), (key331, 1), (key346, 1), (key347, 1), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key661, -1), (key662, -1), (key307, -2), (key321, -2), (key331, -2), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key445, 1), (key453, 1)]

def rawRow1285 : Integer.Sparse Key := [(key321, -1), (key316, -1), (key660, -1), (key435, -1), (key661, -1), (key445, -1), (key331, 2), (key662, 2), (key453, 2), (key307, 1), (key302, 1), (key331, 1), (key316, 1), (key347, 1), (key346, 1), (key656, -1), (key655, -1), (key658, -1), (key657, -1), (key662, -1), (key661, -1), (key307, -2), (key331, -2), (key321, -2), (key400, 1), (key390, 1), (key421, 1), (key411, 1), (key453, 1), (key445, 1)]

def rawRow1286 : Integer.Sparse Key := [(key435, -1), (key445, -1), (key316, -1), (key661, -1), (key321, -1), (key660, -1), (key453, 2), (key331, 2), (key662, 2), (key316, 1), (key346, 1), (key302, 1), (key347, 1), (key307, 1), (key331, 1), (key657, -1), (key661, -1), (key655, -1), (key662, -1), (key656, -1), (key658, -1), (key321, -2), (key307, -2), (key331, -2), (key411, 1), (key445, 1), (key390, 1), (key453, 1), (key400, 1), (key421, 1)]

end MUB6.Certificate.GramRows

end OAI
end


