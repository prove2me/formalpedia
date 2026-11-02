-- Prove2me | Definitions.Def_OAIQ106D162
-- name    : OAIQ106D162
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:10:53.824172+00:00
-- url     : https://prove2.me/theorems/0d996af4-c6bd-4c4c-9c71-6ab23faddef2
-- title:
--   Definitions bundle OAIQ106D162 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 621 declarations of OpenAI's Lean: 621 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow15882`, `OAI.MUB6.Certificate.GramRows.rawRow15883`, `OAI.MUB6.Certificate.GramRows.rawRow15884`, `OAI.MUB6.Certificate.GramRows.rawRow15885`, `OAI.MUB6.Certificate.GramRows.rawRow15886`, `OAI.MUB6.Certificate.GramRows.rawRow15887`, `OAI.MUB6.Certificate.GramRows.rawRow15888`, `OAI.MUB6.Certificate.GramRows.rawRow15889`, `OAI.MUB6.Certificate.GramRows.rawRow1589`, `OAI.MUB6.Certificate.GramRows.rawRow15890`, `OAI.MUB6.Certificate.GramRows.rawRow15891`, `OAI.MUB6.Certificate.GramRows.rawRow15892`, `OAI.MUB6.Certificate.GramRows.rawRow15893`, `OAI.MUB6.Certificate.GramRows.rawRow15894`, `OAI.MUB6.Certificate.GramRows.rawRow15895`, `OAI.MUB6.Certificate.GramRows.rawRow15896`, `OAI.MUB6.Certificate.GramRows.rawRow159`, `OAI.MUB6.Certificate.GramRows.rawRow1590`, `OAI.MUB6.Certificate.GramRows.rawRow1591`, `OAI.MUB6.Certificate.GramRows.rawRow15915`, `OAI.MUB6.Certificate.GramRows.rawRow15916`, `OAI.MUB6.Certificate.GramRows.rawRow15917`, `OAI.MUB6.Certificate.GramRows.rawRow15918`, `OAI.MUB6.Certificate.GramRows.rawRow15919`, `OAI.MUB6.Certificate.GramRows.rawRow1592`, `OAI.MUB6.Certificate.GramRows.rawRow15920`, `OAI.MUB6.Certificate.GramRows.rawRow15921`, `OAI.MUB6.Certificate.GramRows.rawRow15922`, `OAI.MUB6.Certificate.GramRows.rawRow15923`, `OAI.MUB6.Certificate.GramRows.rawRow15924`, `OAI.MUB6.Certificate.GramRows.rawRow15925`, `OAI.MUB6.Certificate.GramRows.rawRow15926`, `OAI.MUB6.Certificate.GramRows.rawRow15927`, `OAI.MUB6.Certificate.GramRows.rawRow15928`, `OAI.MUB6.Certificate.GramRows.rawRow15929`, `OAI.MUB6.Certificate.GramRows.rawRow1593`, `OAI.MUB6.Certificate.GramRows.rawRow15930`, `OAI.MUB6.Certificate.GramRows.rawRow15931`, `OAI.MUB6.Certificate.GramRows.rawRow15932`, `OAI.MUB6.Certificate.GramRows.rawRow15933` and 581 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block1.lean), [`MutuallyUnbiased_GramRows_Block148`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block148.lean), [`MutuallyUnbiased_GramRows_Block150`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block150.lean), [`MutuallyUnbiased_GramRows_Block151`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block151.lean), [`MutuallyUnbiased_GramRows_Block152`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block152.lean), [`MutuallyUnbiased_GramRows_Block153`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block153.lean), [`MutuallyUnbiased_GramRows_Block154`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block154.lean), [`MutuallyUnbiased_GramRows_Block155`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block155.lean), [`MutuallyUnbiased_GramRows_Block2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block2.lean), [`MutuallyUnbiased_GramRows_Block36`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block36.lean), [`MutuallyUnbiased_GramRows_Block37`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block37.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D073`, `OAIQ106D076`, `OAIQ106D083`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D092`, `OAIQ106D093` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval15_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8` and `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D073
import Definitions.Def_OAIQ106D076
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D093
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow159 : Integer.Sparse Key := [(key1896, -1), (key1899, -1), (key1896, 2), (key1918, 1), (key1920, 1), (key1903, -1), (key1918, -1), (key1926, -2), (key1911, 1), (key1926, 1), (key1351, 1), (key1354, 1), (key1351, -2), (key1681, -1), (key1683, -1), (key1472, 1), (key1681, 1), (key1689, 2), (key1480, -1), (key1689, -1), (key1318, -1), (key1326, -1), (key1298, 1), (key1318, 1), (key1548, 1), (key1556, 1), (key1393, -1), (key1548, -1), (key1593, -1), (key1633, -1), (key1444, 1), (key1633, 1), (key1312, 2), (key1292, -1), (key1312, -1), (key1542, -2), (key1387, 1), (key1542, 1), (key1569, 1), (key1618, 1), (key1420, -1), (key1618, -1)]

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

def rawRow15882 : Integer.Sparse Key := [(key2040, 4), (key2048, 4), (key2011, 4), (key2048, -4), (key2011, -4), (key2020, -4), (key2220, -4), (key2125, -4), (key2135, -4), (key2135, 12)]

def rawRow15883 : Integer.Sparse Key := [(key2048, 4), (key2011, 4), (key2040, 4), (key2020, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2220, -4), (key2125, -4), (key2135, 12)]

def rawRow15884 : Integer.Sparse Key := [(key2048, 4), (key2040, 4), (key2011, 4), (key2048, -4), (key2020, -4), (key2011, -4), (key2220, -4), (key2135, -4), (key2125, -4), (key2135, 12)]

def rawRow15885 : Integer.Sparse Key := [(key2020, 4), (key2048, 4), (key2048, 4), (key2011, -4), (key2011, -4), (key2040, -4), (key2135, -4), (key2135, -4), (key2220, -4), (key2125, 12)]

def rawRow15886 : Integer.Sparse Key := [(key2048, 4), (key2020, 4), (key2048, 4), (key2011, -4), (key2040, -4), (key2011, -4), (key2135, -4), (key2220, -4), (key2135, -4), (key2125, 12)]

def rawRow15887 : Integer.Sparse Key := [(key2048, 4), (key2048, 4), (key2020, 4), (key2040, -4), (key2011, -4), (key2011, -4), (key2220, -4), (key2135, -4), (key2135, -4), (key2125, 12)]

def rawRow15888 : Integer.Sparse Key := [(key2011, 4), (key2040, 4), (key2048, 4), (key2125, -4), (key2135, -4), (key2220, -4), (key2011, -4), (key2020, -4), (key2048, -4), (key2135, 12)]

def rawRow15889 : Integer.Sparse Key := [(key2011, 4), (key2048, 4), (key2040, 4), (key2135, -4), (key2125, -4), (key2220, -4), (key2020, -4), (key2011, -4), (key2048, -4), (key2135, 12)]

def rawRow15890 : Integer.Sparse Key := [(key2040, 4), (key2011, 4), (key2048, 4), (key2125, -4), (key2220, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2020, -4), (key2135, 12)]

def rawRow15891 : Integer.Sparse Key := [(key2040, 4), (key2048, 4), (key2011, 4), (key2220, -4), (key2125, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2020, -4), (key2135, 12)]

def rawRow15892 : Integer.Sparse Key := [(key2048, 4), (key2011, 4), (key2040, 4), (key2135, -4), (key2220, -4), (key2125, -4), (key2020, -4), (key2048, -4), (key2011, -4), (key2135, 12)]

def rawRow15893 : Integer.Sparse Key := [(key2048, 4), (key2040, 4), (key2011, 4), (key2220, -4), (key2135, -4), (key2125, -4), (key2048, -4), (key2020, -4), (key2011, -4), (key2135, 12)]

def rawRow15894 : Integer.Sparse Key := [(key2020, 4), (key2048, 4), (key2048, 4), (key2135, -4), (key2135, -4), (key2220, -4), (key2011, -4), (key2011, -4), (key2040, -4), (key2125, 12)]

def rawRow15895 : Integer.Sparse Key := [(key2048, 4), (key2020, 4), (key2048, 4), (key2135, -4), (key2220, -4), (key2135, -4), (key2011, -4), (key2040, -4), (key2011, -4), (key2125, 12)]

def rawRow15896 : Integer.Sparse Key := [(key2048, 4), (key2048, 4), (key2020, 4), (key2220, -4), (key2135, -4), (key2135, -4), (key2040, -4), (key2011, -4), (key2011, -4), (key2125, 12)]

def rawRow15915 : Integer.Sparse Key := [(key1359, -2), (key1364, -2), (key1374, -2), (key1364, 6), (key1711, -2), (key1716, -2), (key1723, -2), (key1485, 2), (key1490, 2), (key1711, 2), (key1861, 2), (key1723, 2), (key1867, 2), (key1490, -2), (key1716, -2), (key1861, -2), (key1741, 6), (key1513, -2), (key1741, -2), (key1877, -2)]

def rawRow15916 : Integer.Sparse Key := [(key1364, -2), (key1359, -2), (key1374, -2), (key1364, 6), (key1716, -2), (key1711, -2), (key1723, -2), (key1490, 2), (key1485, 2), (key1861, 2), (key1711, 2), (key1867, 2), (key1723, 2), (key1490, -2), (key1861, -2), (key1716, -2), (key1741, 6), (key1513, -2), (key1877, -2), (key1741, -2)]

def rawRow15917 : Integer.Sparse Key := [(key1359, -2), (key1374, -2), (key1364, -2), (key1364, 6), (key1711, -2), (key1723, -2), (key1716, -2), (key1711, 2), (key1723, 2), (key1485, 2), (key1867, 2), (key1490, 2), (key1861, 2), (key1716, -2), (key1490, -2), (key1861, -2), (key1741, 6), (key1741, -2), (key1513, -2), (key1877, -2)]

def rawRow15918 : Integer.Sparse Key := [(key1374, -2), (key1359, -2), (key1364, -2), (key1364, 6), (key1723, -2), (key1711, -2), (key1716, -2), (key1723, 2), (key1711, 2), (key1867, 2), (key1485, 2), (key1861, 2), (key1490, 2), (key1716, -2), (key1861, -2), (key1490, -2), (key1741, 6), (key1741, -2), (key1877, -2), (key1513, -2)]

def rawRow15919 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1359, -2), (key1364, 6), (key1716, -2), (key1723, -2), (key1711, -2), (key1861, 2), (key1867, 2), (key1490, 2), (key1723, 2), (key1485, 2), (key1711, 2), (key1861, -2), (key1490, -2), (key1716, -2), (key1741, 6), (key1877, -2), (key1513, -2), (key1741, -2)]

def rawRow15920 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1359, -2), (key1364, 6), (key1723, -2), (key1716, -2), (key1711, -2), (key1867, 2), (key1861, 2), (key1723, 2), (key1490, 2), (key1711, 2), (key1485, 2), (key1861, -2), (key1716, -2), (key1490, -2), (key1741, 6), (key1877, -2), (key1741, -2), (key1513, -2)]

def rawRow15921 : Integer.Sparse Key := [(key1364, -2), (key1364, -2), (key1374, -2), (key1359, 6), (key1861, -2), (key1861, -2), (key1867, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1485, -2), (key1711, -2), (key1711, -2), (key1877, 6), (key1513, -2), (key1741, -2), (key1741, -2)]

def rawRow15922 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1364, -2), (key1359, 6), (key1861, -2), (key1867, -2), (key1861, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1711, -2), (key1485, -2), (key1711, -2), (key1877, 6), (key1741, -2), (key1513, -2), (key1741, -2)]

def rawRow15923 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1364, -2), (key1359, 6), (key1867, -2), (key1861, -2), (key1861, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1711, -2), (key1711, -2), (key1485, -2), (key1877, 6), (key1741, -2), (key1741, -2), (key1513, -2)]

def rawRow15924 : Integer.Sparse Key := [(key1485, -2), (key1490, -2), (key1513, -2), (key1490, 6), (key1711, -2), (key1716, -2), (key1741, -2), (key1359, 2), (key1364, 2), (key1711, 2), (key1861, 2), (key1741, 2), (key1877, 2), (key1364, -2), (key1716, -2), (key1861, -2), (key1723, 6), (key1374, -2), (key1723, -2), (key1867, -2)]

def rawRow15925 : Integer.Sparse Key := [(key1490, -2), (key1485, -2), (key1513, -2), (key1490, 6), (key1716, -2), (key1711, -2), (key1741, -2), (key1364, 2), (key1359, 2), (key1861, 2), (key1711, 2), (key1877, 2), (key1741, 2), (key1364, -2), (key1861, -2), (key1716, -2), (key1723, 6), (key1374, -2), (key1867, -2), (key1723, -2)]

def rawRow15926 : Integer.Sparse Key := [(key1485, -2), (key1513, -2), (key1490, -2), (key1490, 6), (key1711, -2), (key1741, -2), (key1716, -2), (key1711, 2), (key1741, 2), (key1359, 2), (key1877, 2), (key1364, 2), (key1861, 2), (key1716, -2), (key1364, -2), (key1861, -2), (key1723, 6), (key1723, -2), (key1374, -2), (key1867, -2)]

def rawRow15927 : Integer.Sparse Key := [(key1513, -2), (key1485, -2), (key1490, -2), (key1490, 6), (key1741, -2), (key1711, -2), (key1716, -2), (key1741, 2), (key1711, 2), (key1877, 2), (key1359, 2), (key1861, 2), (key1364, 2), (key1716, -2), (key1861, -2), (key1364, -2), (key1723, 6), (key1723, -2), (key1867, -2), (key1374, -2)]

def rawRow15928 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1485, -2), (key1490, 6), (key1716, -2), (key1741, -2), (key1711, -2), (key1861, 2), (key1877, 2), (key1364, 2), (key1741, 2), (key1359, 2), (key1711, 2), (key1861, -2), (key1364, -2), (key1716, -2), (key1723, 6), (key1867, -2), (key1374, -2), (key1723, -2)]

def rawRow15929 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1485, -2), (key1490, 6), (key1741, -2), (key1716, -2), (key1711, -2), (key1877, 2), (key1861, 2), (key1741, 2), (key1364, 2), (key1711, 2), (key1359, 2), (key1861, -2), (key1716, -2), (key1364, -2), (key1723, 6), (key1867, -2), (key1723, -2), (key1374, -2)]

def rawRow15930 : Integer.Sparse Key := [(key1490, -2), (key1490, -2), (key1513, -2), (key1485, 6), (key1861, -2), (key1861, -2), (key1877, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1359, -2), (key1711, -2), (key1711, -2), (key1867, 6), (key1374, -2), (key1723, -2), (key1723, -2)]

def rawRow15931 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1490, -2), (key1485, 6), (key1861, -2), (key1877, -2), (key1861, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1711, -2), (key1359, -2), (key1711, -2), (key1867, 6), (key1723, -2), (key1374, -2), (key1723, -2)]

def rawRow15932 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1490, -2), (key1485, 6), (key1877, -2), (key1861, -2), (key1861, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1711, -2), (key1711, -2), (key1359, -2), (key1867, 6), (key1723, -2), (key1723, -2), (key1374, -2)]

def rawRow15933 : Integer.Sparse Key := [(key1711, -2), (key1716, -2), (key1723, -2), (key1741, 6), (key1359, -2), (key1364, -2), (key1374, -2), (key1485, 2), (key1490, 2), (key1711, 2), (key1861, 2), (key1723, 2), (key1867, 2), (key1513, -2), (key1741, -2), (key1877, -2), (key1364, 6), (key1490, -2), (key1716, -2), (key1861, -2)]

def rawRow15934 : Integer.Sparse Key := [(key1716, -2), (key1711, -2), (key1723, -2), (key1741, 6), (key1364, -2), (key1359, -2), (key1374, -2), (key1490, 2), (key1485, 2), (key1861, 2), (key1711, 2), (key1867, 2), (key1723, 2), (key1513, -2), (key1877, -2), (key1741, -2), (key1364, 6), (key1490, -2), (key1861, -2), (key1716, -2)]

def rawRow15935 : Integer.Sparse Key := [(key1711, -2), (key1723, -2), (key1716, -2), (key1741, 6), (key1359, -2), (key1374, -2), (key1364, -2), (key1711, 2), (key1723, 2), (key1485, 2), (key1867, 2), (key1490, 2), (key1861, 2), (key1741, -2), (key1513, -2), (key1877, -2), (key1364, 6), (key1716, -2), (key1490, -2), (key1861, -2)]

def rawRow15936 : Integer.Sparse Key := [(key1723, -2), (key1711, -2), (key1716, -2), (key1741, 6), (key1374, -2), (key1359, -2), (key1364, -2), (key1723, 2), (key1711, 2), (key1867, 2), (key1485, 2), (key1861, 2), (key1490, 2), (key1741, -2), (key1877, -2), (key1513, -2), (key1364, 6), (key1716, -2), (key1861, -2), (key1490, -2)]

def rawRow15937 : Integer.Sparse Key := [(key1716, -2), (key1723, -2), (key1711, -2), (key1741, 6), (key1364, -2), (key1374, -2), (key1359, -2), (key1861, 2), (key1867, 2), (key1490, 2), (key1723, 2), (key1485, 2), (key1711, 2), (key1877, -2), (key1513, -2), (key1741, -2), (key1364, 6), (key1861, -2), (key1490, -2), (key1716, -2)]

def rawRow15938 : Integer.Sparse Key := [(key1723, -2), (key1716, -2), (key1711, -2), (key1741, 6), (key1374, -2), (key1364, -2), (key1359, -2), (key1867, 2), (key1861, 2), (key1723, 2), (key1490, 2), (key1711, 2), (key1485, 2), (key1877, -2), (key1741, -2), (key1513, -2), (key1364, 6), (key1861, -2), (key1716, -2), (key1490, -2)]

def rawRow15939 : Integer.Sparse Key := [(key1711, -2), (key1716, -2), (key1741, -2), (key1723, 6), (key1485, -2), (key1490, -2), (key1513, -2), (key1359, 2), (key1364, 2), (key1711, 2), (key1861, 2), (key1741, 2), (key1877, 2), (key1374, -2), (key1723, -2), (key1867, -2), (key1490, 6), (key1364, -2), (key1716, -2), (key1861, -2)]

def rawRow15940 : Integer.Sparse Key := [(key1716, -2), (key1711, -2), (key1741, -2), (key1723, 6), (key1490, -2), (key1485, -2), (key1513, -2), (key1364, 2), (key1359, 2), (key1861, 2), (key1711, 2), (key1877, 2), (key1741, 2), (key1374, -2), (key1867, -2), (key1723, -2), (key1490, 6), (key1364, -2), (key1861, -2), (key1716, -2)]

def rawRow15941 : Integer.Sparse Key := [(key1711, -2), (key1741, -2), (key1716, -2), (key1723, 6), (key1485, -2), (key1513, -2), (key1490, -2), (key1711, 2), (key1741, 2), (key1359, 2), (key1877, 2), (key1364, 2), (key1861, 2), (key1723, -2), (key1374, -2), (key1867, -2), (key1490, 6), (key1716, -2), (key1364, -2), (key1861, -2)]

def rawRow15942 : Integer.Sparse Key := [(key1741, -2), (key1711, -2), (key1716, -2), (key1723, 6), (key1513, -2), (key1485, -2), (key1490, -2), (key1741, 2), (key1711, 2), (key1877, 2), (key1359, 2), (key1861, 2), (key1364, 2), (key1723, -2), (key1867, -2), (key1374, -2), (key1490, 6), (key1716, -2), (key1861, -2), (key1364, -2)]

def rawRow15943 : Integer.Sparse Key := [(key1716, -2), (key1741, -2), (key1711, -2), (key1723, 6), (key1490, -2), (key1513, -2), (key1485, -2), (key1861, 2), (key1877, 2), (key1364, 2), (key1741, 2), (key1359, 2), (key1711, 2), (key1867, -2), (key1374, -2), (key1723, -2), (key1490, 6), (key1861, -2), (key1364, -2), (key1716, -2)]

def rawRow15944 : Integer.Sparse Key := [(key1741, -2), (key1716, -2), (key1711, -2), (key1723, 6), (key1513, -2), (key1490, -2), (key1485, -2), (key1877, 2), (key1861, 2), (key1741, 2), (key1364, 2), (key1711, 2), (key1359, 2), (key1867, -2), (key1723, -2), (key1374, -2), (key1490, 6), (key1861, -2), (key1716, -2), (key1364, -2)]

def rawRow15945 : Integer.Sparse Key := [(key1861, -2), (key1861, -2), (key1867, -2), (key1877, 6), (key1364, -2), (key1364, -2), (key1374, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1513, -2), (key1741, -2), (key1741, -2), (key1359, 6), (key1485, -2), (key1711, -2), (key1711, -2)]

def rawRow15946 : Integer.Sparse Key := [(key1861, -2), (key1867, -2), (key1861, -2), (key1877, 6), (key1364, -2), (key1374, -2), (key1364, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, -2), (key1513, -2), (key1741, -2), (key1359, 6), (key1711, -2), (key1485, -2), (key1711, -2)]

def rawRow15947 : Integer.Sparse Key := [(key1867, -2), (key1861, -2), (key1861, -2), (key1877, 6), (key1374, -2), (key1364, -2), (key1364, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1741, -2), (key1741, -2), (key1513, -2), (key1359, 6), (key1711, -2), (key1711, -2), (key1485, -2)]

def rawRow15948 : Integer.Sparse Key := [(key1861, -2), (key1861, -2), (key1877, -2), (key1867, 6), (key1490, -2), (key1490, -2), (key1513, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1374, -2), (key1723, -2), (key1723, -2), (key1485, 6), (key1359, -2), (key1711, -2), (key1711, -2)]

def rawRow15949 : Integer.Sparse Key := [(key1861, -2), (key1877, -2), (key1861, -2), (key1867, 6), (key1490, -2), (key1513, -2), (key1490, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1723, -2), (key1374, -2), (key1723, -2), (key1485, 6), (key1711, -2), (key1359, -2), (key1711, -2)]

def rawRow15950 : Integer.Sparse Key := [(key1877, -2), (key1861, -2), (key1861, -2), (key1867, 6), (key1513, -2), (key1490, -2), (key1490, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1723, -2), (key1723, -2), (key1374, -2), (key1485, 6), (key1711, -2), (key1711, -2), (key1359, -2)]

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

def rawRow16131 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1076, -2), (key1041, 6), (key1111, -2), (key1111, -2), (key1155, -2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1212, 2), (key1212, 2), (key1006, -2), (key1193, -2), (key1193, -2), (key1127, 6), (key1019, -2), (key1199, -2), (key1199, -2)]

def rawRow16132 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1033, -2), (key1041, 6), (key1111, -2), (key1155, -2), (key1111, -2), (key1190, 2), (key1212, 2), (key998, 2), (key1212, 2), (key998, 2), (key1190, 2), (key1193, -2), (key1006, -2), (key1193, -2), (key1127, 6), (key1199, -2), (key1019, -2), (key1199, -2)]

def rawRow16133 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1033, -2), (key1041, 6), (key1155, -2), (key1111, -2), (key1111, -2), (key1212, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1190, 2), (key998, 2), (key1193, -2), (key1193, -2), (key1006, -2), (key1127, 6), (key1199, -2), (key1199, -2), (key1019, -2)]

def rawRow16134 : Integer.Sparse Key := [(key1033, -2), (key1041, -2), (key1076, -2), (key1033, 6), (key1190, -2), (key1193, -2), (key1212, -2), (key998, 2), (key1006, 2), (key1111, 2), (key1193, 2), (key1155, 2), (key1212, 2), (key998, -2), (key1111, -2), (key1190, -2), (key1199, 6), (key1019, -2), (key1127, -2), (key1199, -2)]

def rawRow16135 : Integer.Sparse Key := [(key1041, -2), (key1033, -2), (key1076, -2), (key1033, 6), (key1193, -2), (key1190, -2), (key1212, -2), (key1006, 2), (key998, 2), (key1193, 2), (key1111, 2), (key1212, 2), (key1155, 2), (key998, -2), (key1190, -2), (key1111, -2), (key1199, 6), (key1019, -2), (key1199, -2), (key1127, -2)]

def rawRow16136 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1041, -2), (key1033, 6), (key1190, -2), (key1212, -2), (key1193, -2), (key1111, 2), (key1155, 2), (key998, 2), (key1212, 2), (key1006, 2), (key1193, 2), (key1111, -2), (key998, -2), (key1190, -2), (key1199, 6), (key1127, -2), (key1019, -2), (key1199, -2)]

def rawRow16137 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1041, -2), (key1033, 6), (key1212, -2), (key1190, -2), (key1193, -2), (key1155, 2), (key1111, 2), (key1212, 2), (key998, 2), (key1193, 2), (key1006, 2), (key1111, -2), (key1190, -2), (key998, -2), (key1199, 6), (key1127, -2), (key1199, -2), (key1019, -2)]

def rawRow16138 : Integer.Sparse Key := [(key1041, -2), (key1076, -2), (key1033, -2), (key1033, 6), (key1193, -2), (key1212, -2), (key1190, -2), (key1193, 2), (key1212, 2), (key1006, 2), (key1155, 2), (key998, 2), (key1111, 2), (key1190, -2), (key998, -2), (key1111, -2), (key1199, 6), (key1199, -2), (key1019, -2), (key1127, -2)]

def rawRow16139 : Integer.Sparse Key := [(key1076, -2), (key1041, -2), (key1033, -2), (key1033, 6), (key1212, -2), (key1193, -2), (key1190, -2), (key1212, 2), (key1193, 2), (key1155, 2), (key1006, 2), (key1111, 2), (key998, 2), (key1190, -2), (key1111, -2), (key998, -2), (key1199, 6), (key1199, -2), (key1127, -2), (key1019, -2)]

def rawRow16140 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1155, -2), (key1127, 6), (key1033, -2), (key1033, -2), (key1076, -2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1212, 2), (key1212, 2), (key1019, -2), (key1199, -2), (key1199, -2), (key1041, 6), (key1006, -2), (key1193, -2), (key1193, -2)]

def rawRow16141 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1111, -2), (key1127, 6), (key1033, -2), (key1076, -2), (key1033, -2), (key1190, 2), (key1212, 2), (key998, 2), (key1212, 2), (key998, 2), (key1190, 2), (key1199, -2), (key1019, -2), (key1199, -2), (key1041, 6), (key1193, -2), (key1006, -2), (key1193, -2)]

def rawRow16142 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1111, -2), (key1127, 6), (key1076, -2), (key1033, -2), (key1033, -2), (key1212, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1190, 2), (key998, 2), (key1199, -2), (key1199, -2), (key1019, -2), (key1041, 6), (key1193, -2), (key1193, -2), (key1006, -2)]

def rawRow16143 : Integer.Sparse Key := [(key1111, -2), (key1127, -2), (key1155, -2), (key1111, 6), (key1190, -2), (key1199, -2), (key1212, -2), (key998, 2), (key1019, 2), (key1033, 2), (key1199, 2), (key1076, 2), (key1212, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1193, 6), (key1006, -2), (key1041, -2), (key1193, -2)]

def rawRow16144 : Integer.Sparse Key := [(key1127, -2), (key1111, -2), (key1155, -2), (key1111, 6), (key1199, -2), (key1190, -2), (key1212, -2), (key1019, 2), (key998, 2), (key1199, 2), (key1033, 2), (key1212, 2), (key1076, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1193, 6), (key1006, -2), (key1193, -2), (key1041, -2)]

def rawRow16145 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1127, -2), (key1111, 6), (key1190, -2), (key1212, -2), (key1199, -2), (key1033, 2), (key1076, 2), (key998, 2), (key1212, 2), (key1019, 2), (key1199, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1193, 6), (key1041, -2), (key1006, -2), (key1193, -2)]

def rawRow16146 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1127, -2), (key1111, 6), (key1212, -2), (key1190, -2), (key1199, -2), (key1076, 2), (key1033, 2), (key1212, 2), (key998, 2), (key1199, 2), (key1019, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1193, 6), (key1041, -2), (key1193, -2), (key1006, -2)]

def rawRow16147 : Integer.Sparse Key := [(key1127, -2), (key1155, -2), (key1111, -2), (key1111, 6), (key1199, -2), (key1212, -2), (key1190, -2), (key1199, 2), (key1212, 2), (key1019, 2), (key1076, 2), (key998, 2), (key1033, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1193, 6), (key1193, -2), (key1006, -2), (key1041, -2)]

def rawRow16148 : Integer.Sparse Key := [(key1155, -2), (key1127, -2), (key1111, -2), (key1111, 6), (key1212, -2), (key1199, -2), (key1190, -2), (key1212, 2), (key1199, 2), (key1076, 2), (key1019, 2), (key1033, 2), (key998, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1193, 6), (key1193, -2), (key1041, -2), (key1006, -2)]

def rawRow16149 : Integer.Sparse Key := [(key1190, -2), (key1193, -2), (key1212, -2), (key1199, 6), (key1033, -2), (key1041, -2), (key1076, -2), (key998, 2), (key1006, 2), (key1111, 2), (key1193, 2), (key1155, 2), (key1212, 2), (key1019, -2), (key1127, -2), (key1199, -2), (key1033, 6), (key998, -2), (key1111, -2), (key1190, -2)]

def rawRow16150 : Integer.Sparse Key := [(key1193, -2), (key1190, -2), (key1212, -2), (key1199, 6), (key1041, -2), (key1033, -2), (key1076, -2), (key1006, 2), (key998, 2), (key1193, 2), (key1111, 2), (key1212, 2), (key1155, 2), (key1019, -2), (key1199, -2), (key1127, -2), (key1033, 6), (key998, -2), (key1190, -2), (key1111, -2)]

def rawRow16151 : Integer.Sparse Key := [(key1190, -2), (key1212, -2), (key1193, -2), (key1199, 6), (key1033, -2), (key1076, -2), (key1041, -2), (key1111, 2), (key1155, 2), (key998, 2), (key1212, 2), (key1006, 2), (key1193, 2), (key1127, -2), (key1019, -2), (key1199, -2), (key1033, 6), (key1111, -2), (key998, -2), (key1190, -2)]

def rawRow16152 : Integer.Sparse Key := [(key1212, -2), (key1190, -2), (key1193, -2), (key1199, 6), (key1076, -2), (key1033, -2), (key1041, -2), (key1155, 2), (key1111, 2), (key1212, 2), (key998, 2), (key1193, 2), (key1006, 2), (key1127, -2), (key1199, -2), (key1019, -2), (key1033, 6), (key1111, -2), (key1190, -2), (key998, -2)]

def rawRow16153 : Integer.Sparse Key := [(key1193, -2), (key1212, -2), (key1190, -2), (key1199, 6), (key1041, -2), (key1076, -2), (key1033, -2), (key1193, 2), (key1212, 2), (key1006, 2), (key1155, 2), (key998, 2), (key1111, 2), (key1199, -2), (key1019, -2), (key1127, -2), (key1033, 6), (key1190, -2), (key998, -2), (key1111, -2)]

def rawRow16154 : Integer.Sparse Key := [(key1212, -2), (key1193, -2), (key1190, -2), (key1199, 6), (key1076, -2), (key1041, -2), (key1033, -2), (key1212, 2), (key1193, 2), (key1155, 2), (key1006, 2), (key1111, 2), (key998, 2), (key1199, -2), (key1127, -2), (key1019, -2), (key1033, 6), (key1190, -2), (key1111, -2), (key998, -2)]

def rawRow16155 : Integer.Sparse Key := [(key1190, -2), (key1199, -2), (key1212, -2), (key1193, 6), (key1111, -2), (key1127, -2), (key1155, -2), (key998, 2), (key1019, 2), (key1033, 2), (key1199, 2), (key1076, 2), (key1212, 2), (key1006, -2), (key1041, -2), (key1193, -2), (key1111, 6), (key998, -2), (key1033, -2), (key1190, -2)]

def rawRow16156 : Integer.Sparse Key := [(key1199, -2), (key1190, -2), (key1212, -2), (key1193, 6), (key1127, -2), (key1111, -2), (key1155, -2), (key1019, 2), (key998, 2), (key1199, 2), (key1033, 2), (key1212, 2), (key1076, 2), (key1006, -2), (key1193, -2), (key1041, -2), (key1111, 6), (key998, -2), (key1190, -2), (key1033, -2)]

def rawRow16157 : Integer.Sparse Key := [(key1190, -2), (key1212, -2), (key1199, -2), (key1193, 6), (key1111, -2), (key1155, -2), (key1127, -2), (key1033, 2), (key1076, 2), (key998, 2), (key1212, 2), (key1019, 2), (key1199, 2), (key1041, -2), (key1006, -2), (key1193, -2), (key1111, 6), (key1033, -2), (key998, -2), (key1190, -2)]

def rawRow16158 : Integer.Sparse Key := [(key1212, -2), (key1190, -2), (key1199, -2), (key1193, 6), (key1155, -2), (key1111, -2), (key1127, -2), (key1076, 2), (key1033, 2), (key1212, 2), (key998, 2), (key1199, 2), (key1019, 2), (key1041, -2), (key1193, -2), (key1006, -2), (key1111, 6), (key1033, -2), (key1190, -2), (key998, -2)]

def rawRow16159 : Integer.Sparse Key := [(key1199, -2), (key1212, -2), (key1190, -2), (key1193, 6), (key1127, -2), (key1155, -2), (key1111, -2), (key1199, 2), (key1212, 2), (key1019, 2), (key1076, 2), (key998, 2), (key1033, 2), (key1193, -2), (key1006, -2), (key1041, -2), (key1111, 6), (key1190, -2), (key998, -2), (key1033, -2)]

def rawRow16160 : Integer.Sparse Key := [(key1212, -2), (key1199, -2), (key1190, -2), (key1193, 6), (key1155, -2), (key1127, -2), (key1111, -2), (key1212, 2), (key1199, 2), (key1076, 2), (key1019, 2), (key1033, 2), (key998, 2), (key1193, -2), (key1041, -2), (key1006, -2), (key1111, 6), (key1190, -2), (key1033, -2), (key998, -2)]

def rawRow16161 : Integer.Sparse Key := [(key1193, -2), (key1199, -2), (key1212, -2), (key1190, 6), (key1193, -2), (key1199, -2), (key1212, -2), (key1006, 2), (key1019, 2), (key1041, 2), (key1127, 2), (key1076, 2), (key1155, 2), (key998, -2), (key1033, -2), (key1111, -2), (key1190, 6), (key998, -2), (key1033, -2), (key1111, -2)]

def rawRow16162 : Integer.Sparse Key := [(key1199, -2), (key1193, -2), (key1212, -2), (key1190, 6), (key1199, -2), (key1193, -2), (key1212, -2), (key1019, 2), (key1006, 2), (key1127, 2), (key1041, 2), (key1155, 2), (key1076, 2), (key998, -2), (key1111, -2), (key1033, -2), (key1190, 6), (key998, -2), (key1111, -2), (key1033, -2)]

def rawRow16163 : Integer.Sparse Key := [(key1193, -2), (key1212, -2), (key1199, -2), (key1190, 6), (key1193, -2), (key1212, -2), (key1199, -2), (key1041, 2), (key1076, 2), (key1006, 2), (key1155, 2), (key1019, 2), (key1127, 2), (key1033, -2), (key998, -2), (key1111, -2), (key1190, 6), (key1033, -2), (key998, -2), (key1111, -2)]

def rawRow16164 : Integer.Sparse Key := [(key1212, -2), (key1193, -2), (key1199, -2), (key1190, 6), (key1212, -2), (key1193, -2), (key1199, -2), (key1076, 2), (key1041, 2), (key1155, 2), (key1006, 2), (key1127, 2), (key1019, 2), (key1033, -2), (key1111, -2), (key998, -2), (key1190, 6), (key1033, -2), (key1111, -2), (key998, -2)]

def rawRow16165 : Integer.Sparse Key := [(key1199, -2), (key1212, -2), (key1193, -2), (key1190, 6), (key1199, -2), (key1212, -2), (key1193, -2), (key1127, 2), (key1155, 2), (key1019, 2), (key1076, 2), (key1006, 2), (key1041, 2), (key1111, -2), (key998, -2), (key1033, -2), (key1190, 6), (key1111, -2), (key998, -2), (key1033, -2)]

def rawRow16166 : Integer.Sparse Key := [(key1212, -2), (key1199, -2), (key1193, -2), (key1190, 6), (key1212, -2), (key1199, -2), (key1193, -2), (key1155, 2), (key1127, 2), (key1076, 2), (key1019, 2), (key1041, 2), (key1006, 2), (key1111, -2), (key1033, -2), (key998, -2), (key1190, 6), (key1111, -2), (key1033, -2), (key998, -2)]

def rawRow16203 : Integer.Sparse Key := [(key2785, 6), (key2670, -2), (key2793, -2), (key2793, -2), (key2808, 6), (key2615, -2), (key2828, -2), (key2828, -2), (key2705, -2), (key2859, -2), (key2859, -2), (key2631, -2), (key2869, -2), (key2869, -2), (key2639, 2), (key2639, 2), (key2725, 2), (key2725, 2), (key2879, 2), (key2879, 2)]

def rawRow16204 : Integer.Sparse Key := [(key2785, 6), (key2793, -2), (key2670, -2), (key2793, -2), (key2808, 6), (key2828, -2), (key2615, -2), (key2828, -2), (key2859, -2), (key2705, -2), (key2859, -2), (key2869, -2), (key2631, -2), (key2869, -2), (key2725, 2), (key2879, 2), (key2639, 2), (key2879, 2), (key2639, 2), (key2725, 2)]

def rawRow16205 : Integer.Sparse Key := [(key2785, 6), (key2793, -2), (key2793, -2), (key2670, -2), (key2808, 6), (key2828, -2), (key2828, -2), (key2615, -2), (key2859, -2), (key2859, -2), (key2705, -2), (key2869, -2), (key2869, -2), (key2631, -2), (key2879, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2725, 2), (key2639, 2)]

def rawRow16206 : Integer.Sparse Key := [(key2793, 6), (key2670, -2), (key2785, -2), (key2793, -2), (key2828, 6), (key2615, -2), (key2808, -2), (key2828, -2), (key2725, -2), (key2869, -2), (key2879, -2), (key2639, -2), (key2859, -2), (key2879, -2), (key2631, 2), (key2639, 2), (key2705, 2), (key2725, 2), (key2859, 2), (key2869, 2)]

def rawRow16207 : Integer.Sparse Key := [(key2793, 6), (key2670, -2), (key2793, -2), (key2785, -2), (key2828, 6), (key2615, -2), (key2828, -2), (key2808, -2), (key2725, -2), (key2879, -2), (key2869, -2), (key2639, -2), (key2879, -2), (key2859, -2), (key2639, 2), (key2631, 2), (key2725, 2), (key2705, 2), (key2869, 2), (key2859, 2)]

def rawRow16208 : Integer.Sparse Key := [(key2793, 6), (key2785, -2), (key2670, -2), (key2793, -2), (key2828, 6), (key2808, -2), (key2615, -2), (key2828, -2), (key2869, -2), (key2725, -2), (key2879, -2), (key2859, -2), (key2639, -2), (key2879, -2), (key2705, 2), (key2859, 2), (key2631, 2), (key2869, 2), (key2639, 2), (key2725, 2)]

def rawRow16209 : Integer.Sparse Key := [(key2793, 6), (key2785, -2), (key2793, -2), (key2670, -2), (key2828, 6), (key2808, -2), (key2828, -2), (key2615, -2), (key2869, -2), (key2879, -2), (key2725, -2), (key2859, -2), (key2879, -2), (key2639, -2), (key2859, 2), (key2705, 2), (key2869, 2), (key2631, 2), (key2725, 2), (key2639, 2)]

def rawRow16210 : Integer.Sparse Key := [(key2793, 6), (key2793, -2), (key2670, -2), (key2785, -2), (key2828, 6), (key2828, -2), (key2615, -2), (key2808, -2), (key2879, -2), (key2725, -2), (key2869, -2), (key2879, -2), (key2639, -2), (key2859, -2), (key2725, 2), (key2869, 2), (key2639, 2), (key2859, 2), (key2631, 2), (key2705, 2)]

def rawRow16211 : Integer.Sparse Key := [(key2793, 6), (key2793, -2), (key2785, -2), (key2670, -2), (key2828, 6), (key2828, -2), (key2808, -2), (key2615, -2), (key2879, -2), (key2869, -2), (key2725, -2), (key2879, -2), (key2859, -2), (key2639, -2), (key2869, 2), (key2725, 2), (key2859, 2), (key2639, 2), (key2705, 2), (key2631, 2)]

def rawRow16212 : Integer.Sparse Key := [(key2808, 6), (key2705, -2), (key2859, -2), (key2859, -2), (key2785, 6), (key2631, -2), (key2869, -2), (key2869, -2), (key2670, -2), (key2793, -2), (key2793, -2), (key2615, -2), (key2828, -2), (key2828, -2), (key2639, 2), (key2639, 2), (key2725, 2), (key2725, 2), (key2879, 2), (key2879, 2)]

def rawRow16213 : Integer.Sparse Key := [(key2808, 6), (key2859, -2), (key2705, -2), (key2859, -2), (key2785, 6), (key2869, -2), (key2631, -2), (key2869, -2), (key2793, -2), (key2670, -2), (key2793, -2), (key2828, -2), (key2615, -2), (key2828, -2), (key2725, 2), (key2879, 2), (key2639, 2), (key2879, 2), (key2639, 2), (key2725, 2)]

def rawRow16214 : Integer.Sparse Key := [(key2808, 6), (key2859, -2), (key2859, -2), (key2705, -2), (key2785, 6), (key2869, -2), (key2869, -2), (key2631, -2), (key2793, -2), (key2793, -2), (key2670, -2), (key2828, -2), (key2828, -2), (key2615, -2), (key2879, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2725, 2), (key2639, 2)]

def rawRow16215 : Integer.Sparse Key := [(key2859, 6), (key2705, -2), (key2808, -2), (key2859, -2), (key2869, 6), (key2631, -2), (key2785, -2), (key2869, -2), (key2725, -2), (key2828, -2), (key2879, -2), (key2639, -2), (key2793, -2), (key2879, -2), (key2615, 2), (key2639, 2), (key2670, 2), (key2725, 2), (key2793, 2), (key2828, 2)]

def rawRow16216 : Integer.Sparse Key := [(key2859, 6), (key2705, -2), (key2859, -2), (key2808, -2), (key2869, 6), (key2631, -2), (key2869, -2), (key2785, -2), (key2725, -2), (key2879, -2), (key2828, -2), (key2639, -2), (key2879, -2), (key2793, -2), (key2639, 2), (key2615, 2), (key2725, 2), (key2670, 2), (key2828, 2), (key2793, 2)]

def rawRow16217 : Integer.Sparse Key := [(key2859, 6), (key2808, -2), (key2705, -2), (key2859, -2), (key2869, 6), (key2785, -2), (key2631, -2), (key2869, -2), (key2828, -2), (key2725, -2), (key2879, -2), (key2793, -2), (key2639, -2), (key2879, -2), (key2670, 2), (key2793, 2), (key2615, 2), (key2828, 2), (key2639, 2), (key2725, 2)]

def rawRow16218 : Integer.Sparse Key := [(key2859, 6), (key2808, -2), (key2859, -2), (key2705, -2), (key2869, 6), (key2785, -2), (key2869, -2), (key2631, -2), (key2828, -2), (key2879, -2), (key2725, -2), (key2793, -2), (key2879, -2), (key2639, -2), (key2793, 2), (key2670, 2), (key2828, 2), (key2615, 2), (key2725, 2), (key2639, 2)]

def rawRow16219 : Integer.Sparse Key := [(key2859, 6), (key2859, -2), (key2705, -2), (key2808, -2), (key2869, 6), (key2869, -2), (key2631, -2), (key2785, -2), (key2879, -2), (key2725, -2), (key2828, -2), (key2879, -2), (key2639, -2), (key2793, -2), (key2725, 2), (key2828, 2), (key2639, 2), (key2793, 2), (key2615, 2), (key2670, 2)]

def rawRow16220 : Integer.Sparse Key := [(key2859, 6), (key2859, -2), (key2808, -2), (key2705, -2), (key2869, 6), (key2869, -2), (key2785, -2), (key2631, -2), (key2879, -2), (key2828, -2), (key2725, -2), (key2879, -2), (key2793, -2), (key2639, -2), (key2828, 2), (key2725, 2), (key2793, 2), (key2639, 2), (key2670, 2), (key2615, 2)]

def rawRow16221 : Integer.Sparse Key := [(key2828, 6), (key2725, -2), (key2869, -2), (key2879, -2), (key2793, 6), (key2639, -2), (key2859, -2), (key2879, -2), (key2670, -2), (key2785, -2), (key2793, -2), (key2615, -2), (key2808, -2), (key2828, -2), (key2631, 2), (key2639, 2), (key2705, 2), (key2725, 2), (key2859, 2), (key2869, 2)]

def rawRow16222 : Integer.Sparse Key := [(key2828, 6), (key2725, -2), (key2879, -2), (key2869, -2), (key2793, 6), (key2639, -2), (key2879, -2), (key2859, -2), (key2670, -2), (key2793, -2), (key2785, -2), (key2615, -2), (key2828, -2), (key2808, -2), (key2639, 2), (key2631, 2), (key2725, 2), (key2705, 2), (key2869, 2), (key2859, 2)]

def rawRow16223 : Integer.Sparse Key := [(key2828, 6), (key2869, -2), (key2725, -2), (key2879, -2), (key2793, 6), (key2859, -2), (key2639, -2), (key2879, -2), (key2785, -2), (key2670, -2), (key2793, -2), (key2808, -2), (key2615, -2), (key2828, -2), (key2705, 2), (key2859, 2), (key2631, 2), (key2869, 2), (key2639, 2), (key2725, 2)]

def rawRow16224 : Integer.Sparse Key := [(key2828, 6), (key2869, -2), (key2879, -2), (key2725, -2), (key2793, 6), (key2859, -2), (key2879, -2), (key2639, -2), (key2785, -2), (key2793, -2), (key2670, -2), (key2808, -2), (key2828, -2), (key2615, -2), (key2859, 2), (key2705, 2), (key2869, 2), (key2631, 2), (key2725, 2), (key2639, 2)]

def rawRow16225 : Integer.Sparse Key := [(key2828, 6), (key2879, -2), (key2725, -2), (key2869, -2), (key2793, 6), (key2879, -2), (key2639, -2), (key2859, -2), (key2793, -2), (key2670, -2), (key2785, -2), (key2828, -2), (key2615, -2), (key2808, -2), (key2725, 2), (key2869, 2), (key2639, 2), (key2859, 2), (key2631, 2), (key2705, 2)]

def rawRow16226 : Integer.Sparse Key := [(key2828, 6), (key2879, -2), (key2869, -2), (key2725, -2), (key2793, 6), (key2879, -2), (key2859, -2), (key2639, -2), (key2793, -2), (key2785, -2), (key2670, -2), (key2828, -2), (key2808, -2), (key2615, -2), (key2869, 2), (key2725, 2), (key2859, 2), (key2639, 2), (key2705, 2), (key2631, 2)]

def rawRow16227 : Integer.Sparse Key := [(key2869, 6), (key2725, -2), (key2828, -2), (key2879, -2), (key2859, 6), (key2639, -2), (key2793, -2), (key2879, -2), (key2705, -2), (key2808, -2), (key2859, -2), (key2631, -2), (key2785, -2), (key2869, -2), (key2615, 2), (key2639, 2), (key2670, 2), (key2725, 2), (key2793, 2), (key2828, 2)]

def rawRow16228 : Integer.Sparse Key := [(key2869, 6), (key2725, -2), (key2879, -2), (key2828, -2), (key2859, 6), (key2639, -2), (key2879, -2), (key2793, -2), (key2705, -2), (key2859, -2), (key2808, -2), (key2631, -2), (key2869, -2), (key2785, -2), (key2639, 2), (key2615, 2), (key2725, 2), (key2670, 2), (key2828, 2), (key2793, 2)]

def rawRow16229 : Integer.Sparse Key := [(key2869, 6), (key2828, -2), (key2725, -2), (key2879, -2), (key2859, 6), (key2793, -2), (key2639, -2), (key2879, -2), (key2808, -2), (key2705, -2), (key2859, -2), (key2785, -2), (key2631, -2), (key2869, -2), (key2670, 2), (key2793, 2), (key2615, 2), (key2828, 2), (key2639, 2), (key2725, 2)]

def rawRow16230 : Integer.Sparse Key := [(key2869, 6), (key2828, -2), (key2879, -2), (key2725, -2), (key2859, 6), (key2793, -2), (key2879, -2), (key2639, -2), (key2808, -2), (key2859, -2), (key2705, -2), (key2785, -2), (key2869, -2), (key2631, -2), (key2793, 2), (key2670, 2), (key2828, 2), (key2615, 2), (key2725, 2), (key2639, 2)]

def rawRow16231 : Integer.Sparse Key := [(key2869, 6), (key2879, -2), (key2725, -2), (key2828, -2), (key2859, 6), (key2879, -2), (key2639, -2), (key2793, -2), (key2859, -2), (key2705, -2), (key2808, -2), (key2869, -2), (key2631, -2), (key2785, -2), (key2725, 2), (key2828, 2), (key2639, 2), (key2793, 2), (key2615, 2), (key2670, 2)]

def rawRow16232 : Integer.Sparse Key := [(key2869, 6), (key2879, -2), (key2828, -2), (key2725, -2), (key2859, 6), (key2879, -2), (key2793, -2), (key2639, -2), (key2859, -2), (key2808, -2), (key2705, -2), (key2869, -2), (key2785, -2), (key2631, -2), (key2828, 2), (key2725, 2), (key2793, 2), (key2639, 2), (key2670, 2), (key2615, 2)]

def rawRow16233 : Integer.Sparse Key := [(key2879, 6), (key2725, -2), (key2828, -2), (key2869, -2), (key2879, 6), (key2639, -2), (key2793, -2), (key2859, -2), (key2725, -2), (key2828, -2), (key2869, -2), (key2639, -2), (key2793, -2), (key2859, -2), (key2615, 2), (key2631, 2), (key2670, 2), (key2705, 2), (key2785, 2), (key2808, 2)]

def rawRow16234 : Integer.Sparse Key := [(key2879, 6), (key2725, -2), (key2869, -2), (key2828, -2), (key2879, 6), (key2639, -2), (key2859, -2), (key2793, -2), (key2725, -2), (key2869, -2), (key2828, -2), (key2639, -2), (key2859, -2), (key2793, -2), (key2631, 2), (key2615, 2), (key2705, 2), (key2670, 2), (key2808, 2), (key2785, 2)]

def rawRow16235 : Integer.Sparse Key := [(key2879, 6), (key2828, -2), (key2725, -2), (key2869, -2), (key2879, 6), (key2793, -2), (key2639, -2), (key2859, -2), (key2828, -2), (key2725, -2), (key2869, -2), (key2793, -2), (key2639, -2), (key2859, -2), (key2670, 2), (key2785, 2), (key2615, 2), (key2808, 2), (key2631, 2), (key2705, 2)]

def rawRow16236 : Integer.Sparse Key := [(key2879, 6), (key2828, -2), (key2869, -2), (key2725, -2), (key2879, 6), (key2793, -2), (key2859, -2), (key2639, -2), (key2828, -2), (key2869, -2), (key2725, -2), (key2793, -2), (key2859, -2), (key2639, -2), (key2785, 2), (key2670, 2), (key2808, 2), (key2615, 2), (key2705, 2), (key2631, 2)]

def rawRow16237 : Integer.Sparse Key := [(key2879, 6), (key2869, -2), (key2725, -2), (key2828, -2), (key2879, 6), (key2859, -2), (key2639, -2), (key2793, -2), (key2869, -2), (key2725, -2), (key2828, -2), (key2859, -2), (key2639, -2), (key2793, -2), (key2705, 2), (key2808, 2), (key2631, 2), (key2785, 2), (key2615, 2), (key2670, 2)]

def rawRow16238 : Integer.Sparse Key := [(key2879, 6), (key2869, -2), (key2828, -2), (key2725, -2), (key2879, 6), (key2859, -2), (key2793, -2), (key2639, -2), (key2869, -2), (key2828, -2), (key2725, -2), (key2859, -2), (key2793, -2), (key2639, -2), (key2808, 2), (key2705, 2), (key2785, 2), (key2631, 2), (key2670, 2), (key2615, 2)]

def rawRow16239 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1075, -2), (key1040, 6), (key1111, -2), (key1111, -2), (key1154, -2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1211, 2), (key1211, 2), (key1005, -2), (key1192, -2), (key1192, -2), (key1126, 6), (key1018, -2), (key1198, -2), (key1198, -2)]

def rawRow16240 : Integer.Sparse Key := [(key1033, -2), (key1075, -2), (key1033, -2), (key1040, 6), (key1111, -2), (key1154, -2), (key1111, -2), (key1190, 2), (key1211, 2), (key998, 2), (key1211, 2), (key998, 2), (key1190, 2), (key1192, -2), (key1005, -2), (key1192, -2), (key1126, 6), (key1198, -2), (key1018, -2), (key1198, -2)]

def rawRow16241 : Integer.Sparse Key := [(key1075, -2), (key1033, -2), (key1033, -2), (key1040, 6), (key1154, -2), (key1111, -2), (key1111, -2), (key1211, 2), (key1190, 2), (key1211, 2), (key998, 2), (key1190, 2), (key998, 2), (key1192, -2), (key1192, -2), (key1005, -2), (key1126, 6), (key1198, -2), (key1198, -2), (key1018, -2)]

def rawRow16242 : Integer.Sparse Key := [(key1033, -2), (key1040, -2), (key1075, -2), (key1033, 6), (key1190, -2), (key1192, -2), (key1211, -2), (key998, 2), (key1005, 2), (key1111, 2), (key1192, 2), (key1154, 2), (key1211, 2), (key998, -2), (key1111, -2), (key1190, -2), (key1198, 6), (key1018, -2), (key1126, -2), (key1198, -2)]

def rawRow16243 : Integer.Sparse Key := [(key1040, -2), (key1033, -2), (key1075, -2), (key1033, 6), (key1192, -2), (key1190, -2), (key1211, -2), (key1005, 2), (key998, 2), (key1192, 2), (key1111, 2), (key1211, 2), (key1154, 2), (key998, -2), (key1190, -2), (key1111, -2), (key1198, 6), (key1018, -2), (key1198, -2), (key1126, -2)]

def rawRow16244 : Integer.Sparse Key := [(key1033, -2), (key1075, -2), (key1040, -2), (key1033, 6), (key1190, -2), (key1211, -2), (key1192, -2), (key1111, 2), (key1154, 2), (key998, 2), (key1211, 2), (key1005, 2), (key1192, 2), (key1111, -2), (key998, -2), (key1190, -2), (key1198, 6), (key1126, -2), (key1018, -2), (key1198, -2)]

def rawRow16245 : Integer.Sparse Key := [(key1075, -2), (key1033, -2), (key1040, -2), (key1033, 6), (key1211, -2), (key1190, -2), (key1192, -2), (key1154, 2), (key1111, 2), (key1211, 2), (key998, 2), (key1192, 2), (key1005, 2), (key1111, -2), (key1190, -2), (key998, -2), (key1198, 6), (key1126, -2), (key1198, -2), (key1018, -2)]

def rawRow16246 : Integer.Sparse Key := [(key1040, -2), (key1075, -2), (key1033, -2), (key1033, 6), (key1192, -2), (key1211, -2), (key1190, -2), (key1192, 2), (key1211, 2), (key1005, 2), (key1154, 2), (key998, 2), (key1111, 2), (key1190, -2), (key998, -2), (key1111, -2), (key1198, 6), (key1198, -2), (key1018, -2), (key1126, -2)]

def rawRow16247 : Integer.Sparse Key := [(key1075, -2), (key1040, -2), (key1033, -2), (key1033, 6), (key1211, -2), (key1192, -2), (key1190, -2), (key1211, 2), (key1192, 2), (key1154, 2), (key1005, 2), (key1111, 2), (key998, 2), (key1190, -2), (key1111, -2), (key998, -2), (key1198, 6), (key1198, -2), (key1126, -2), (key1018, -2)]

def rawRow16248 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1154, -2), (key1126, 6), (key1033, -2), (key1033, -2), (key1075, -2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1211, 2), (key1211, 2), (key1018, -2), (key1198, -2), (key1198, -2), (key1040, 6), (key1005, -2), (key1192, -2), (key1192, -2)]

def rawRow16249 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1111, -2), (key1126, 6), (key1033, -2), (key1075, -2), (key1033, -2), (key1190, 2), (key1211, 2), (key998, 2), (key1211, 2), (key998, 2), (key1190, 2), (key1198, -2), (key1018, -2), (key1198, -2), (key1040, 6), (key1192, -2), (key1005, -2), (key1192, -2)]

def rawRow16250 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1111, -2), (key1126, 6), (key1075, -2), (key1033, -2), (key1033, -2), (key1211, 2), (key1190, 2), (key1211, 2), (key998, 2), (key1190, 2), (key998, 2), (key1198, -2), (key1198, -2), (key1018, -2), (key1040, 6), (key1192, -2), (key1192, -2), (key1005, -2)]

def rawRow16251 : Integer.Sparse Key := [(key1111, -2), (key1126, -2), (key1154, -2), (key1111, 6), (key1190, -2), (key1198, -2), (key1211, -2), (key998, 2), (key1018, 2), (key1033, 2), (key1198, 2), (key1075, 2), (key1211, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1192, 6), (key1005, -2), (key1040, -2), (key1192, -2)]

def rawRow16252 : Integer.Sparse Key := [(key1126, -2), (key1111, -2), (key1154, -2), (key1111, 6), (key1198, -2), (key1190, -2), (key1211, -2), (key1018, 2), (key998, 2), (key1198, 2), (key1033, 2), (key1211, 2), (key1075, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1192, 6), (key1005, -2), (key1192, -2), (key1040, -2)]

def rawRow16253 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1126, -2), (key1111, 6), (key1190, -2), (key1211, -2), (key1198, -2), (key1033, 2), (key1075, 2), (key998, 2), (key1211, 2), (key1018, 2), (key1198, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1192, 6), (key1040, -2), (key1005, -2), (key1192, -2)]

def rawRow16254 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1126, -2), (key1111, 6), (key1211, -2), (key1190, -2), (key1198, -2), (key1075, 2), (key1033, 2), (key1211, 2), (key998, 2), (key1198, 2), (key1018, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1192, 6), (key1040, -2), (key1192, -2), (key1005, -2)]

def rawRow16255 : Integer.Sparse Key := [(key1126, -2), (key1154, -2), (key1111, -2), (key1111, 6), (key1198, -2), (key1211, -2), (key1190, -2), (key1198, 2), (key1211, 2), (key1018, 2), (key1075, 2), (key998, 2), (key1033, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1192, 6), (key1192, -2), (key1005, -2), (key1040, -2)]

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

def rawRow16256 : Integer.Sparse Key := [(key1154, -2), (key1126, -2), (key1111, -2), (key1111, 6), (key1211, -2), (key1198, -2), (key1190, -2), (key1211, 2), (key1198, 2), (key1075, 2), (key1018, 2), (key1033, 2), (key998, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1192, 6), (key1192, -2), (key1040, -2), (key1005, -2)]

def rawRow16257 : Integer.Sparse Key := [(key1190, -2), (key1192, -2), (key1211, -2), (key1198, 6), (key1033, -2), (key1040, -2), (key1075, -2), (key998, 2), (key1005, 2), (key1111, 2), (key1192, 2), (key1154, 2), (key1211, 2), (key1018, -2), (key1126, -2), (key1198, -2), (key1033, 6), (key998, -2), (key1111, -2), (key1190, -2)]

def rawRow16258 : Integer.Sparse Key := [(key1192, -2), (key1190, -2), (key1211, -2), (key1198, 6), (key1040, -2), (key1033, -2), (key1075, -2), (key1005, 2), (key998, 2), (key1192, 2), (key1111, 2), (key1211, 2), (key1154, 2), (key1018, -2), (key1198, -2), (key1126, -2), (key1033, 6), (key998, -2), (key1190, -2), (key1111, -2)]

def rawRow16259 : Integer.Sparse Key := [(key1190, -2), (key1211, -2), (key1192, -2), (key1198, 6), (key1033, -2), (key1075, -2), (key1040, -2), (key1111, 2), (key1154, 2), (key998, 2), (key1211, 2), (key1005, 2), (key1192, 2), (key1126, -2), (key1018, -2), (key1198, -2), (key1033, 6), (key1111, -2), (key998, -2), (key1190, -2)]

def rawRow16260 : Integer.Sparse Key := [(key1211, -2), (key1190, -2), (key1192, -2), (key1198, 6), (key1075, -2), (key1033, -2), (key1040, -2), (key1154, 2), (key1111, 2), (key1211, 2), (key998, 2), (key1192, 2), (key1005, 2), (key1126, -2), (key1198, -2), (key1018, -2), (key1033, 6), (key1111, -2), (key1190, -2), (key998, -2)]

def rawRow16261 : Integer.Sparse Key := [(key1192, -2), (key1211, -2), (key1190, -2), (key1198, 6), (key1040, -2), (key1075, -2), (key1033, -2), (key1192, 2), (key1211, 2), (key1005, 2), (key1154, 2), (key998, 2), (key1111, 2), (key1198, -2), (key1018, -2), (key1126, -2), (key1033, 6), (key1190, -2), (key998, -2), (key1111, -2)]

def rawRow16262 : Integer.Sparse Key := [(key1211, -2), (key1192, -2), (key1190, -2), (key1198, 6), (key1075, -2), (key1040, -2), (key1033, -2), (key1211, 2), (key1192, 2), (key1154, 2), (key1005, 2), (key1111, 2), (key998, 2), (key1198, -2), (key1126, -2), (key1018, -2), (key1033, 6), (key1190, -2), (key1111, -2), (key998, -2)]

def rawRow16263 : Integer.Sparse Key := [(key1190, -2), (key1198, -2), (key1211, -2), (key1192, 6), (key1111, -2), (key1126, -2), (key1154, -2), (key998, 2), (key1018, 2), (key1033, 2), (key1198, 2), (key1075, 2), (key1211, 2), (key1005, -2), (key1040, -2), (key1192, -2), (key1111, 6), (key998, -2), (key1033, -2), (key1190, -2)]

def rawRow16264 : Integer.Sparse Key := [(key1198, -2), (key1190, -2), (key1211, -2), (key1192, 6), (key1126, -2), (key1111, -2), (key1154, -2), (key1018, 2), (key998, 2), (key1198, 2), (key1033, 2), (key1211, 2), (key1075, 2), (key1005, -2), (key1192, -2), (key1040, -2), (key1111, 6), (key998, -2), (key1190, -2), (key1033, -2)]

def rawRow16265 : Integer.Sparse Key := [(key1190, -2), (key1211, -2), (key1198, -2), (key1192, 6), (key1111, -2), (key1154, -2), (key1126, -2), (key1033, 2), (key1075, 2), (key998, 2), (key1211, 2), (key1018, 2), (key1198, 2), (key1040, -2), (key1005, -2), (key1192, -2), (key1111, 6), (key1033, -2), (key998, -2), (key1190, -2)]

def rawRow16266 : Integer.Sparse Key := [(key1211, -2), (key1190, -2), (key1198, -2), (key1192, 6), (key1154, -2), (key1111, -2), (key1126, -2), (key1075, 2), (key1033, 2), (key1211, 2), (key998, 2), (key1198, 2), (key1018, 2), (key1040, -2), (key1192, -2), (key1005, -2), (key1111, 6), (key1033, -2), (key1190, -2), (key998, -2)]

def rawRow16267 : Integer.Sparse Key := [(key1198, -2), (key1211, -2), (key1190, -2), (key1192, 6), (key1126, -2), (key1154, -2), (key1111, -2), (key1198, 2), (key1211, 2), (key1018, 2), (key1075, 2), (key998, 2), (key1033, 2), (key1192, -2), (key1005, -2), (key1040, -2), (key1111, 6), (key1190, -2), (key998, -2), (key1033, -2)]

def rawRow16268 : Integer.Sparse Key := [(key1211, -2), (key1198, -2), (key1190, -2), (key1192, 6), (key1154, -2), (key1126, -2), (key1111, -2), (key1211, 2), (key1198, 2), (key1075, 2), (key1018, 2), (key1033, 2), (key998, 2), (key1192, -2), (key1040, -2), (key1005, -2), (key1111, 6), (key1190, -2), (key1033, -2), (key998, -2)]

def rawRow16269 : Integer.Sparse Key := [(key1192, -2), (key1198, -2), (key1211, -2), (key1190, 6), (key1192, -2), (key1198, -2), (key1211, -2), (key1005, 2), (key1018, 2), (key1040, 2), (key1126, 2), (key1075, 2), (key1154, 2), (key998, -2), (key1033, -2), (key1111, -2), (key1190, 6), (key998, -2), (key1033, -2), (key1111, -2)]

def rawRow16270 : Integer.Sparse Key := [(key1198, -2), (key1192, -2), (key1211, -2), (key1190, 6), (key1198, -2), (key1192, -2), (key1211, -2), (key1018, 2), (key1005, 2), (key1126, 2), (key1040, 2), (key1154, 2), (key1075, 2), (key998, -2), (key1111, -2), (key1033, -2), (key1190, 6), (key998, -2), (key1111, -2), (key1033, -2)]

def rawRow16271 : Integer.Sparse Key := [(key1192, -2), (key1211, -2), (key1198, -2), (key1190, 6), (key1192, -2), (key1211, -2), (key1198, -2), (key1040, 2), (key1075, 2), (key1005, 2), (key1154, 2), (key1018, 2), (key1126, 2), (key1033, -2), (key998, -2), (key1111, -2), (key1190, 6), (key1033, -2), (key998, -2), (key1111, -2)]

def rawRow16272 : Integer.Sparse Key := [(key1211, -2), (key1192, -2), (key1198, -2), (key1190, 6), (key1211, -2), (key1192, -2), (key1198, -2), (key1075, 2), (key1040, 2), (key1154, 2), (key1005, 2), (key1126, 2), (key1018, 2), (key1033, -2), (key1111, -2), (key998, -2), (key1190, 6), (key1033, -2), (key1111, -2), (key998, -2)]

def rawRow16273 : Integer.Sparse Key := [(key1198, -2), (key1211, -2), (key1192, -2), (key1190, 6), (key1198, -2), (key1211, -2), (key1192, -2), (key1126, 2), (key1154, 2), (key1018, 2), (key1075, 2), (key1005, 2), (key1040, 2), (key1111, -2), (key998, -2), (key1033, -2), (key1190, 6), (key1111, -2), (key998, -2), (key1033, -2)]

def rawRow16274 : Integer.Sparse Key := [(key1211, -2), (key1198, -2), (key1192, -2), (key1190, 6), (key1211, -2), (key1198, -2), (key1192, -2), (key1154, 2), (key1126, 2), (key1075, 2), (key1018, 2), (key1040, 2), (key1005, 2), (key1111, -2), (key1033, -2), (key998, -2), (key1190, 6), (key1111, -2), (key1033, -2), (key998, -2)]

def rawRow16275 : Integer.Sparse Key := [(key1004, 4), (key1214, 4), (key1214, 4), (key1008, -2), (key1008, -2), (key1195, -2), (key1195, -2), (key1216, -2), (key1216, -2), (key1021, -2), (key1021, -2), (key1201, -2), (key1201, -2), (key1225, -2), (key1225, -2), (key1023, 4), (key1202, 4), (key1202, 4)]

def rawRow16276 : Integer.Sparse Key := [(key1214, 4), (key1004, 4), (key1214, 4), (key1195, -2), (key1216, -2), (key1008, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1225, -2), (key1021, -2), (key1201, -2), (key1202, 4), (key1023, 4), (key1202, 4)]

def rawRow16277 : Integer.Sparse Key := [(key1214, 4), (key1214, 4), (key1004, 4), (key1216, -2), (key1195, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1008, -2), (key1225, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1201, -2), (key1021, -2), (key1202, 4), (key1202, 4), (key1023, 4)]

def rawRow16278 : Integer.Sparse Key := [(key1008, 4), (key1157, 4), (key1216, 4), (key1004, -2), (key1008, -2), (key1117, -2), (key1195, -2), (key1157, -2), (key1214, -2), (key1021, -2), (key1023, -2), (key1129, -2), (key1202, -2), (key1176, -2), (key1225, -2), (key1021, 4), (key1129, 4), (key1201, 4)]

def rawRow16279 : Integer.Sparse Key := [(key1008, 4), (key1216, 4), (key1157, 4), (key1008, -2), (key1004, -2), (key1195, -2), (key1117, -2), (key1214, -2), (key1157, -2), (key1023, -2), (key1021, -2), (key1202, -2), (key1129, -2), (key1225, -2), (key1176, -2), (key1021, 4), (key1201, 4), (key1129, 4)]

def rawRow16280 : Integer.Sparse Key := [(key1157, 4), (key1008, 4), (key1216, 4), (key1117, -2), (key1157, -2), (key1004, -2), (key1214, -2), (key1008, -2), (key1195, -2), (key1129, -2), (key1176, -2), (key1021, -2), (key1225, -2), (key1023, -2), (key1202, -2), (key1129, 4), (key1021, 4), (key1201, 4)]

def rawRow16281 : Integer.Sparse Key := [(key1157, 4), (key1216, 4), (key1008, 4), (key1157, -2), (key1117, -2), (key1214, -2), (key1004, -2), (key1195, -2), (key1008, -2), (key1176, -2), (key1129, -2), (key1225, -2), (key1021, -2), (key1202, -2), (key1023, -2), (key1129, 4), (key1201, 4), (key1021, 4)]

def rawRow16282 : Integer.Sparse Key := [(key1216, 4), (key1008, 4), (key1157, 4), (key1195, -2), (key1214, -2), (key1008, -2), (key1157, -2), (key1004, -2), (key1117, -2), (key1202, -2), (key1225, -2), (key1023, -2), (key1176, -2), (key1021, -2), (key1129, -2), (key1201, 4), (key1021, 4), (key1129, 4)]

def rawRow16283 : Integer.Sparse Key := [(key1216, 4), (key1157, 4), (key1008, 4), (key1214, -2), (key1195, -2), (key1157, -2), (key1008, -2), (key1117, -2), (key1004, -2), (key1225, -2), (key1202, -2), (key1176, -2), (key1023, -2), (key1129, -2), (key1021, -2), (key1201, 4), (key1129, 4), (key1021, 4)]

def rawRow16284 : Integer.Sparse Key := [(key1004, 4), (key1214, 4), (key1214, 4), (key1021, -2), (key1021, -2), (key1201, -2), (key1201, -2), (key1225, -2), (key1225, -2), (key1008, -2), (key1008, -2), (key1195, -2), (key1195, -2), (key1216, -2), (key1216, -2), (key1023, 4), (key1202, 4), (key1202, 4)]

def rawRow16285 : Integer.Sparse Key := [(key1214, 4), (key1004, 4), (key1214, 4), (key1201, -2), (key1225, -2), (key1021, -2), (key1225, -2), (key1021, -2), (key1201, -2), (key1195, -2), (key1216, -2), (key1008, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1202, 4), (key1023, 4), (key1202, 4)]

def rawRow16286 : Integer.Sparse Key := [(key1214, 4), (key1214, 4), (key1004, 4), (key1225, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1201, -2), (key1021, -2), (key1216, -2), (key1195, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1008, -2), (key1202, 4), (key1202, 4), (key1023, 4)]

def rawRow16287 : Integer.Sparse Key := [(key1021, 4), (key1078, 4), (key1225, 4), (key1004, -2), (key1021, -2), (key1039, -2), (key1201, -2), (key1078, -2), (key1214, -2), (key1008, -2), (key1023, -2), (key1043, -2), (key1202, -2), (key1081, -2), (key1216, -2), (key1008, 4), (key1043, 4), (key1195, 4)]

def rawRow16288 : Integer.Sparse Key := [(key1021, 4), (key1225, 4), (key1078, 4), (key1021, -2), (key1004, -2), (key1201, -2), (key1039, -2), (key1214, -2), (key1078, -2), (key1023, -2), (key1008, -2), (key1202, -2), (key1043, -2), (key1216, -2), (key1081, -2), (key1008, 4), (key1195, 4), (key1043, 4)]

def rawRow16289 : Integer.Sparse Key := [(key1078, 4), (key1021, 4), (key1225, 4), (key1039, -2), (key1078, -2), (key1004, -2), (key1214, -2), (key1021, -2), (key1201, -2), (key1043, -2), (key1081, -2), (key1008, -2), (key1216, -2), (key1023, -2), (key1202, -2), (key1043, 4), (key1008, 4), (key1195, 4)]

def rawRow16290 : Integer.Sparse Key := [(key1078, 4), (key1225, 4), (key1021, 4), (key1078, -2), (key1039, -2), (key1214, -2), (key1004, -2), (key1201, -2), (key1021, -2), (key1081, -2), (key1043, -2), (key1216, -2), (key1008, -2), (key1202, -2), (key1023, -2), (key1043, 4), (key1195, 4), (key1008, 4)]

def rawRow16291 : Integer.Sparse Key := [(key1225, 4), (key1021, 4), (key1078, 4), (key1201, -2), (key1214, -2), (key1021, -2), (key1078, -2), (key1004, -2), (key1039, -2), (key1202, -2), (key1216, -2), (key1023, -2), (key1081, -2), (key1008, -2), (key1043, -2), (key1195, 4), (key1008, 4), (key1043, 4)]

def rawRow16292 : Integer.Sparse Key := [(key1225, 4), (key1078, 4), (key1021, 4), (key1214, -2), (key1201, -2), (key1078, -2), (key1021, -2), (key1039, -2), (key1004, -2), (key1216, -2), (key1202, -2), (key1081, -2), (key1023, -2), (key1043, -2), (key1008, -2), (key1195, 4), (key1043, 4), (key1008, 4)]

def rawRow16293 : Integer.Sparse Key := [(key1008, 4), (key1157, 4), (key1216, 4), (key1021, -2), (key1023, -2), (key1129, -2), (key1202, -2), (key1176, -2), (key1225, -2), (key1004, -2), (key1008, -2), (key1117, -2), (key1195, -2), (key1157, -2), (key1214, -2), (key1021, 4), (key1129, 4), (key1201, 4)]

def rawRow16294 : Integer.Sparse Key := [(key1008, 4), (key1216, 4), (key1157, 4), (key1023, -2), (key1021, -2), (key1202, -2), (key1129, -2), (key1225, -2), (key1176, -2), (key1008, -2), (key1004, -2), (key1195, -2), (key1117, -2), (key1214, -2), (key1157, -2), (key1021, 4), (key1201, 4), (key1129, 4)]

def rawRow16295 : Integer.Sparse Key := [(key1157, 4), (key1008, 4), (key1216, 4), (key1129, -2), (key1176, -2), (key1021, -2), (key1225, -2), (key1023, -2), (key1202, -2), (key1117, -2), (key1157, -2), (key1004, -2), (key1214, -2), (key1008, -2), (key1195, -2), (key1129, 4), (key1021, 4), (key1201, 4)]

def rawRow16296 : Integer.Sparse Key := [(key1157, 4), (key1216, 4), (key1008, 4), (key1176, -2), (key1129, -2), (key1225, -2), (key1021, -2), (key1202, -2), (key1023, -2), (key1157, -2), (key1117, -2), (key1214, -2), (key1004, -2), (key1195, -2), (key1008, -2), (key1129, 4), (key1201, 4), (key1021, 4)]

def rawRow16297 : Integer.Sparse Key := [(key1216, 4), (key1008, 4), (key1157, 4), (key1202, -2), (key1225, -2), (key1023, -2), (key1176, -2), (key1021, -2), (key1129, -2), (key1195, -2), (key1214, -2), (key1008, -2), (key1157, -2), (key1004, -2), (key1117, -2), (key1201, 4), (key1021, 4), (key1129, 4)]

def rawRow16298 : Integer.Sparse Key := [(key1216, 4), (key1157, 4), (key1008, 4), (key1225, -2), (key1202, -2), (key1176, -2), (key1023, -2), (key1129, -2), (key1021, -2), (key1214, -2), (key1195, -2), (key1157, -2), (key1008, -2), (key1117, -2), (key1004, -2), (key1201, 4), (key1129, 4), (key1021, 4)]

def rawRow16299 : Integer.Sparse Key := [(key1021, 4), (key1078, 4), (key1225, 4), (key1008, -2), (key1023, -2), (key1043, -2), (key1202, -2), (key1081, -2), (key1216, -2), (key1004, -2), (key1021, -2), (key1039, -2), (key1201, -2), (key1078, -2), (key1214, -2), (key1008, 4), (key1043, 4), (key1195, 4)]

def rawRow16300 : Integer.Sparse Key := [(key1021, 4), (key1225, 4), (key1078, 4), (key1023, -2), (key1008, -2), (key1202, -2), (key1043, -2), (key1216, -2), (key1081, -2), (key1021, -2), (key1004, -2), (key1201, -2), (key1039, -2), (key1214, -2), (key1078, -2), (key1008, 4), (key1195, 4), (key1043, 4)]

def rawRow16301 : Integer.Sparse Key := [(key1078, 4), (key1021, 4), (key1225, 4), (key1043, -2), (key1081, -2), (key1008, -2), (key1216, -2), (key1023, -2), (key1202, -2), (key1039, -2), (key1078, -2), (key1004, -2), (key1214, -2), (key1021, -2), (key1201, -2), (key1043, 4), (key1008, 4), (key1195, 4)]

def rawRow16302 : Integer.Sparse Key := [(key1078, 4), (key1225, 4), (key1021, 4), (key1081, -2), (key1043, -2), (key1216, -2), (key1008, -2), (key1202, -2), (key1023, -2), (key1078, -2), (key1039, -2), (key1214, -2), (key1004, -2), (key1201, -2), (key1021, -2), (key1043, 4), (key1195, 4), (key1008, 4)]

def rawRow16303 : Integer.Sparse Key := [(key1225, 4), (key1021, 4), (key1078, 4), (key1202, -2), (key1216, -2), (key1023, -2), (key1081, -2), (key1008, -2), (key1043, -2), (key1201, -2), (key1214, -2), (key1021, -2), (key1078, -2), (key1004, -2), (key1039, -2), (key1195, 4), (key1008, 4), (key1043, 4)]

def rawRow16304 : Integer.Sparse Key := [(key1225, 4), (key1078, 4), (key1021, 4), (key1216, -2), (key1202, -2), (key1081, -2), (key1023, -2), (key1043, -2), (key1008, -2), (key1214, -2), (key1201, -2), (key1078, -2), (key1021, -2), (key1039, -2), (key1004, -2), (key1195, 4), (key1043, 4), (key1008, 4)]

def rawRow16305 : Integer.Sparse Key := [(key1023, 4), (key1081, 4), (key1176, 4), (key1008, -2), (key1021, -2), (key1043, -2), (key1129, -2), (key1078, -2), (key1157, -2), (key1008, -2), (key1021, -2), (key1043, -2), (key1129, -2), (key1078, -2), (key1157, -2), (key1004, 4), (key1039, 4), (key1117, 4)]

def rawRow16306 : Integer.Sparse Key := [(key1023, 4), (key1176, 4), (key1081, 4), (key1021, -2), (key1008, -2), (key1129, -2), (key1043, -2), (key1157, -2), (key1078, -2), (key1021, -2), (key1008, -2), (key1129, -2), (key1043, -2), (key1157, -2), (key1078, -2), (key1004, 4), (key1117, 4), (key1039, 4)]

def rawRow16307 : Integer.Sparse Key := [(key1081, 4), (key1023, 4), (key1176, 4), (key1043, -2), (key1078, -2), (key1008, -2), (key1157, -2), (key1021, -2), (key1129, -2), (key1043, -2), (key1078, -2), (key1008, -2), (key1157, -2), (key1021, -2), (key1129, -2), (key1039, 4), (key1004, 4), (key1117, 4)]

def rawRow16308 : Integer.Sparse Key := [(key1081, 4), (key1176, 4), (key1023, 4), (key1078, -2), (key1043, -2), (key1157, -2), (key1008, -2), (key1129, -2), (key1021, -2), (key1078, -2), (key1043, -2), (key1157, -2), (key1008, -2), (key1129, -2), (key1021, -2), (key1039, 4), (key1117, 4), (key1004, 4)]

def rawRow16309 : Integer.Sparse Key := [(key1176, 4), (key1023, 4), (key1081, 4), (key1129, -2), (key1157, -2), (key1021, -2), (key1078, -2), (key1008, -2), (key1043, -2), (key1129, -2), (key1157, -2), (key1021, -2), (key1078, -2), (key1008, -2), (key1043, -2), (key1117, 4), (key1004, 4), (key1039, 4)]

def rawRow16310 : Integer.Sparse Key := [(key1176, 4), (key1081, 4), (key1023, 4), (key1157, -2), (key1129, -2), (key1078, -2), (key1021, -2), (key1043, -2), (key1008, -2), (key1157, -2), (key1129, -2), (key1078, -2), (key1021, -2), (key1043, -2), (key1008, -2), (key1117, 4), (key1039, 4), (key1004, 4)]

def rawRow16347 : Integer.Sparse Key := [(key2685, 4), (key2821, 4), (key2821, 4), (key2692, -4), (key2692, -4), (key2830, -4), (key2718, -4), (key2718, -4), (key2871, -4), (key2727, 12)]

def rawRow16348 : Integer.Sparse Key := [(key2821, 4), (key2685, 4), (key2821, 4), (key2692, -4), (key2830, -4), (key2692, -4), (key2718, -4), (key2871, -4), (key2718, -4), (key2727, 12)]

def rawRow16349 : Integer.Sparse Key := [(key2821, 4), (key2821, 4), (key2685, 4), (key2830, -4), (key2692, -4), (key2692, -4), (key2871, -4), (key2718, -4), (key2718, -4), (key2727, 12)]

def rawRow16350 : Integer.Sparse Key := [(key2692, 4), (key2821, 4), (key2830, 4), (key2685, -4), (key2692, -4), (key2821, -4), (key2718, -4), (key2727, -4), (key2871, -4), (key2718, 12)]

def rawRow16351 : Integer.Sparse Key := [(key2692, 4), (key2830, 4), (key2821, 4), (key2692, -4), (key2685, -4), (key2821, -4), (key2727, -4), (key2718, -4), (key2871, -4), (key2718, 12)]

def rawRow16352 : Integer.Sparse Key := [(key2821, 4), (key2692, 4), (key2830, 4), (key2685, -4), (key2821, -4), (key2692, -4), (key2718, -4), (key2871, -4), (key2727, -4), (key2718, 12)]

def rawRow16353 : Integer.Sparse Key := [(key2821, 4), (key2830, 4), (key2692, 4), (key2821, -4), (key2685, -4), (key2692, -4), (key2871, -4), (key2718, -4), (key2727, -4), (key2718, 12)]

def rawRow16354 : Integer.Sparse Key := [(key2830, 4), (key2692, 4), (key2821, 4), (key2692, -4), (key2821, -4), (key2685, -4), (key2727, -4), (key2871, -4), (key2718, -4), (key2718, 12)]

def rawRow16355 : Integer.Sparse Key := [(key2830, 4), (key2821, 4), (key2692, 4), (key2821, -4), (key2692, -4), (key2685, -4), (key2871, -4), (key2727, -4), (key2718, -4), (key2718, 12)]

def rawRow16356 : Integer.Sparse Key := [(key2685, 4), (key2821, 4), (key2821, 4), (key2718, -4), (key2718, -4), (key2871, -4), (key2692, -4), (key2692, -4), (key2830, -4), (key2727, 12)]

def rawRow16357 : Integer.Sparse Key := [(key2821, 4), (key2685, 4), (key2821, 4), (key2718, -4), (key2871, -4), (key2718, -4), (key2692, -4), (key2830, -4), (key2692, -4), (key2727, 12)]

def rawRow16358 : Integer.Sparse Key := [(key2821, 4), (key2821, 4), (key2685, 4), (key2871, -4), (key2718, -4), (key2718, -4), (key2830, -4), (key2692, -4), (key2692, -4), (key2727, 12)]

def rawRow16359 : Integer.Sparse Key := [(key2718, 4), (key2821, 4), (key2871, 4), (key2685, -4), (key2718, -4), (key2821, -4), (key2692, -4), (key2727, -4), (key2830, -4), (key2692, 12)]

def rawRow16360 : Integer.Sparse Key := [(key2718, 4), (key2871, 4), (key2821, 4), (key2718, -4), (key2685, -4), (key2821, -4), (key2727, -4), (key2692, -4), (key2830, -4), (key2692, 12)]

def rawRow16361 : Integer.Sparse Key := [(key2821, 4), (key2718, 4), (key2871, 4), (key2685, -4), (key2821, -4), (key2718, -4), (key2692, -4), (key2830, -4), (key2727, -4), (key2692, 12)]

def rawRow16362 : Integer.Sparse Key := [(key2821, 4), (key2871, 4), (key2718, 4), (key2821, -4), (key2685, -4), (key2718, -4), (key2830, -4), (key2692, -4), (key2727, -4), (key2692, 12)]

def rawRow16363 : Integer.Sparse Key := [(key2871, 4), (key2718, 4), (key2821, 4), (key2718, -4), (key2821, -4), (key2685, -4), (key2727, -4), (key2830, -4), (key2692, -4), (key2692, 12)]

def rawRow16364 : Integer.Sparse Key := [(key2871, 4), (key2821, 4), (key2718, 4), (key2821, -4), (key2718, -4), (key2685, -4), (key2830, -4), (key2727, -4), (key2692, -4), (key2692, 12)]

def rawRow16365 : Integer.Sparse Key := [(key2692, 4), (key2821, 4), (key2830, 4), (key2718, -4), (key2727, -4), (key2871, -4), (key2685, -4), (key2692, -4), (key2821, -4), (key2718, 12)]

def rawRow16366 : Integer.Sparse Key := [(key2692, 4), (key2830, 4), (key2821, 4), (key2727, -4), (key2718, -4), (key2871, -4), (key2692, -4), (key2685, -4), (key2821, -4), (key2718, 12)]

def rawRow16367 : Integer.Sparse Key := [(key2821, 4), (key2692, 4), (key2830, 4), (key2718, -4), (key2871, -4), (key2727, -4), (key2685, -4), (key2821, -4), (key2692, -4), (key2718, 12)]

def rawRow16368 : Integer.Sparse Key := [(key2821, 4), (key2830, 4), (key2692, 4), (key2871, -4), (key2718, -4), (key2727, -4), (key2821, -4), (key2685, -4), (key2692, -4), (key2718, 12)]

def rawRow16369 : Integer.Sparse Key := [(key2830, 4), (key2692, 4), (key2821, 4), (key2727, -4), (key2871, -4), (key2718, -4), (key2692, -4), (key2821, -4), (key2685, -4), (key2718, 12)]

def rawRow16370 : Integer.Sparse Key := [(key2830, 4), (key2821, 4), (key2692, 4), (key2871, -4), (key2727, -4), (key2718, -4), (key2821, -4), (key2692, -4), (key2685, -4), (key2718, 12)]

def rawRow16371 : Integer.Sparse Key := [(key2718, 4), (key2821, 4), (key2871, 4), (key2692, -4), (key2727, -4), (key2830, -4), (key2685, -4), (key2718, -4), (key2821, -4), (key2692, 12)]

def rawRow16372 : Integer.Sparse Key := [(key2718, 4), (key2871, 4), (key2821, 4), (key2727, -4), (key2692, -4), (key2830, -4), (key2718, -4), (key2685, -4), (key2821, -4), (key2692, 12)]

def rawRow16373 : Integer.Sparse Key := [(key2821, 4), (key2718, 4), (key2871, 4), (key2692, -4), (key2830, -4), (key2727, -4), (key2685, -4), (key2821, -4), (key2718, -4), (key2692, 12)]

def rawRow16374 : Integer.Sparse Key := [(key2821, 4), (key2871, 4), (key2718, 4), (key2830, -4), (key2692, -4), (key2727, -4), (key2821, -4), (key2685, -4), (key2718, -4), (key2692, 12)]

def rawRow16375 : Integer.Sparse Key := [(key2871, 4), (key2718, 4), (key2821, 4), (key2727, -4), (key2830, -4), (key2692, -4), (key2718, -4), (key2821, -4), (key2685, -4), (key2692, 12)]

def rawRow16376 : Integer.Sparse Key := [(key2871, 4), (key2821, 4), (key2718, 4), (key2830, -4), (key2727, -4), (key2692, -4), (key2821, -4), (key2718, -4), (key2685, -4), (key2692, 12)]

def rawRow16377 : Integer.Sparse Key := [(key2727, 4), (key2830, 4), (key2871, 4), (key2692, -4), (key2718, -4), (key2821, -4), (key2692, -4), (key2718, -4), (key2821, -4), (key2685, 12)]

def rawRow16378 : Integer.Sparse Key := [(key2727, 4), (key2871, 4), (key2830, 4), (key2718, -4), (key2692, -4), (key2821, -4), (key2718, -4), (key2692, -4), (key2821, -4), (key2685, 12)]

def rawRow16379 : Integer.Sparse Key := [(key2830, 4), (key2727, 4), (key2871, 4), (key2692, -4), (key2821, -4), (key2718, -4), (key2692, -4), (key2821, -4), (key2718, -4), (key2685, 12)]

def rawRow16380 : Integer.Sparse Key := [(key2830, 4), (key2871, 4), (key2727, 4), (key2821, -4), (key2692, -4), (key2718, -4), (key2821, -4), (key2692, -4), (key2718, -4), (key2685, 12)]

def rawRow16381 : Integer.Sparse Key := [(key2871, 4), (key2727, 4), (key2830, 4), (key2718, -4), (key2821, -4), (key2692, -4), (key2718, -4), (key2821, -4), (key2692, -4), (key2685, 12)]

def rawRow16382 : Integer.Sparse Key := [(key2871, 4), (key2830, 4), (key2727, 4), (key2821, -4), (key2718, -4), (key2692, -4), (key2821, -4), (key2718, -4), (key2692, -4), (key2685, 12)]

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

def rawRow16419 : Integer.Sparse Key := [(key2016, 4), (key2136, 4), (key2136, 4), (key2021, -4), (key2021, -4), (key2171, -4), (key2049, -4), (key2049, -4), (key2263, -4), (key2074, 12)]

def rawRow16420 : Integer.Sparse Key := [(key2136, 4), (key2016, 4), (key2136, 4), (key2021, -4), (key2171, -4), (key2021, -4), (key2049, -4), (key2263, -4), (key2049, -4), (key2074, 12)]

def rawRow16421 : Integer.Sparse Key := [(key2136, 4), (key2136, 4), (key2016, 4), (key2171, -4), (key2021, -4), (key2021, -4), (key2263, -4), (key2049, -4), (key2049, -4), (key2074, 12)]

def rawRow16422 : Integer.Sparse Key := [(key2021, 4), (key2136, 4), (key2171, 4), (key2016, -4), (key2021, -4), (key2136, -4), (key2049, -4), (key2074, -4), (key2263, -4), (key2049, 12)]

def rawRow16423 : Integer.Sparse Key := [(key2021, 4), (key2171, 4), (key2136, 4), (key2021, -4), (key2016, -4), (key2136, -4), (key2074, -4), (key2049, -4), (key2263, -4), (key2049, 12)]

def rawRow16424 : Integer.Sparse Key := [(key2136, 4), (key2021, 4), (key2171, 4), (key2016, -4), (key2136, -4), (key2021, -4), (key2049, -4), (key2263, -4), (key2074, -4), (key2049, 12)]

def rawRow16425 : Integer.Sparse Key := [(key2136, 4), (key2171, 4), (key2021, 4), (key2136, -4), (key2016, -4), (key2021, -4), (key2263, -4), (key2049, -4), (key2074, -4), (key2049, 12)]

def rawRow16426 : Integer.Sparse Key := [(key2171, 4), (key2021, 4), (key2136, 4), (key2021, -4), (key2136, -4), (key2016, -4), (key2074, -4), (key2263, -4), (key2049, -4), (key2049, 12)]

def rawRow16427 : Integer.Sparse Key := [(key2171, 4), (key2136, 4), (key2021, 4), (key2136, -4), (key2021, -4), (key2016, -4), (key2263, -4), (key2074, -4), (key2049, -4), (key2049, 12)]

def rawRow16428 : Integer.Sparse Key := [(key2016, 4), (key2136, 4), (key2136, 4), (key2049, -4), (key2049, -4), (key2263, -4), (key2021, -4), (key2021, -4), (key2171, -4), (key2074, 12)]

def rawRow16429 : Integer.Sparse Key := [(key2136, 4), (key2016, 4), (key2136, 4), (key2049, -4), (key2263, -4), (key2049, -4), (key2021, -4), (key2171, -4), (key2021, -4), (key2074, 12)]

def rawRow16430 : Integer.Sparse Key := [(key2136, 4), (key2136, 4), (key2016, 4), (key2263, -4), (key2049, -4), (key2049, -4), (key2171, -4), (key2021, -4), (key2021, -4), (key2074, 12)]

def rawRow16431 : Integer.Sparse Key := [(key2049, 4), (key2136, 4), (key2263, 4), (key2016, -4), (key2049, -4), (key2136, -4), (key2021, -4), (key2074, -4), (key2171, -4), (key2021, 12)]

def rawRow16432 : Integer.Sparse Key := [(key2049, 4), (key2263, 4), (key2136, 4), (key2049, -4), (key2016, -4), (key2136, -4), (key2074, -4), (key2021, -4), (key2171, -4), (key2021, 12)]

def rawRow16433 : Integer.Sparse Key := [(key2136, 4), (key2049, 4), (key2263, 4), (key2016, -4), (key2136, -4), (key2049, -4), (key2021, -4), (key2171, -4), (key2074, -4), (key2021, 12)]

def rawRow16434 : Integer.Sparse Key := [(key2136, 4), (key2263, 4), (key2049, 4), (key2136, -4), (key2016, -4), (key2049, -4), (key2171, -4), (key2021, -4), (key2074, -4), (key2021, 12)]

def rawRow16435 : Integer.Sparse Key := [(key2263, 4), (key2049, 4), (key2136, 4), (key2049, -4), (key2136, -4), (key2016, -4), (key2074, -4), (key2171, -4), (key2021, -4), (key2021, 12)]

def rawRow16436 : Integer.Sparse Key := [(key2263, 4), (key2136, 4), (key2049, 4), (key2136, -4), (key2049, -4), (key2016, -4), (key2171, -4), (key2074, -4), (key2021, -4), (key2021, 12)]

def rawRow16437 : Integer.Sparse Key := [(key2021, 4), (key2136, 4), (key2171, 4), (key2049, -4), (key2074, -4), (key2263, -4), (key2016, -4), (key2021, -4), (key2136, -4), (key2049, 12)]

def rawRow16438 : Integer.Sparse Key := [(key2021, 4), (key2171, 4), (key2136, 4), (key2074, -4), (key2049, -4), (key2263, -4), (key2021, -4), (key2016, -4), (key2136, -4), (key2049, 12)]

def rawRow16439 : Integer.Sparse Key := [(key2136, 4), (key2021, 4), (key2171, 4), (key2049, -4), (key2263, -4), (key2074, -4), (key2016, -4), (key2136, -4), (key2021, -4), (key2049, 12)]

def rawRow16440 : Integer.Sparse Key := [(key2136, 4), (key2171, 4), (key2021, 4), (key2263, -4), (key2049, -4), (key2074, -4), (key2136, -4), (key2016, -4), (key2021, -4), (key2049, 12)]

def rawRow16441 : Integer.Sparse Key := [(key2171, 4), (key2021, 4), (key2136, 4), (key2074, -4), (key2263, -4), (key2049, -4), (key2021, -4), (key2136, -4), (key2016, -4), (key2049, 12)]

def rawRow16442 : Integer.Sparse Key := [(key2171, 4), (key2136, 4), (key2021, 4), (key2263, -4), (key2074, -4), (key2049, -4), (key2136, -4), (key2021, -4), (key2016, -4), (key2049, 12)]

def rawRow16443 : Integer.Sparse Key := [(key2049, 4), (key2136, 4), (key2263, 4), (key2021, -4), (key2074, -4), (key2171, -4), (key2016, -4), (key2049, -4), (key2136, -4), (key2021, 12)]

def rawRow16444 : Integer.Sparse Key := [(key2049, 4), (key2263, 4), (key2136, 4), (key2074, -4), (key2021, -4), (key2171, -4), (key2049, -4), (key2016, -4), (key2136, -4), (key2021, 12)]

def rawRow16445 : Integer.Sparse Key := [(key2136, 4), (key2049, 4), (key2263, 4), (key2021, -4), (key2171, -4), (key2074, -4), (key2016, -4), (key2136, -4), (key2049, -4), (key2021, 12)]

def rawRow16446 : Integer.Sparse Key := [(key2136, 4), (key2263, 4), (key2049, 4), (key2171, -4), (key2021, -4), (key2074, -4), (key2136, -4), (key2016, -4), (key2049, -4), (key2021, 12)]

def rawRow16447 : Integer.Sparse Key := [(key2263, 4), (key2049, 4), (key2136, 4), (key2074, -4), (key2171, -4), (key2021, -4), (key2049, -4), (key2136, -4), (key2016, -4), (key2021, 12)]

def rawRow16448 : Integer.Sparse Key := [(key2263, 4), (key2136, 4), (key2049, 4), (key2171, -4), (key2074, -4), (key2021, -4), (key2136, -4), (key2049, -4), (key2016, -4), (key2021, 12)]

def rawRow16449 : Integer.Sparse Key := [(key2074, 4), (key2171, 4), (key2263, 4), (key2021, -4), (key2049, -4), (key2136, -4), (key2021, -4), (key2049, -4), (key2136, -4), (key2016, 12)]

def rawRow16450 : Integer.Sparse Key := [(key2074, 4), (key2263, 4), (key2171, 4), (key2049, -4), (key2021, -4), (key2136, -4), (key2049, -4), (key2021, -4), (key2136, -4), (key2016, 12)]

def rawRow16451 : Integer.Sparse Key := [(key2171, 4), (key2074, 4), (key2263, 4), (key2021, -4), (key2136, -4), (key2049, -4), (key2021, -4), (key2136, -4), (key2049, -4), (key2016, 12)]

def rawRow16452 : Integer.Sparse Key := [(key2171, 4), (key2263, 4), (key2074, 4), (key2136, -4), (key2021, -4), (key2049, -4), (key2136, -4), (key2021, -4), (key2049, -4), (key2016, 12)]

def rawRow16453 : Integer.Sparse Key := [(key2263, 4), (key2074, 4), (key2171, 4), (key2049, -4), (key2136, -4), (key2021, -4), (key2049, -4), (key2136, -4), (key2021, -4), (key2016, 12)]

def rawRow16454 : Integer.Sparse Key := [(key2263, 4), (key2171, 4), (key2074, 4), (key2136, -4), (key2049, -4), (key2021, -4), (key2136, -4), (key2049, -4), (key2021, -4), (key2016, 12)]

def rawRow16491 : Integer.Sparse Key := [(key1489, -2), (key1489, -2), (key1518, -2), (key1495, 6), (key1715, -2), (key1715, -2), (key1746, -2), (key1363, 2), (key1363, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1879, 2), (key1369, -2), (key1864, -2), (key1864, -2), (key1727, 6), (key1378, -2), (key1869, -2), (key1869, -2)]

def rawRow16492 : Integer.Sparse Key := [(key1489, -2), (key1518, -2), (key1489, -2), (key1495, 6), (key1715, -2), (key1746, -2), (key1715, -2), (key1860, 2), (key1879, 2), (key1363, 2), (key1879, 2), (key1363, 2), (key1860, 2), (key1864, -2), (key1369, -2), (key1864, -2), (key1727, 6), (key1869, -2), (key1378, -2), (key1869, -2)]

def rawRow16493 : Integer.Sparse Key := [(key1518, -2), (key1489, -2), (key1489, -2), (key1495, 6), (key1746, -2), (key1715, -2), (key1715, -2), (key1879, 2), (key1860, 2), (key1879, 2), (key1363, 2), (key1860, 2), (key1363, 2), (key1864, -2), (key1864, -2), (key1369, -2), (key1727, 6), (key1869, -2), (key1869, -2), (key1378, -2)]

def rawRow16494 : Integer.Sparse Key := [(key1489, -2), (key1495, -2), (key1518, -2), (key1489, 6), (key1860, -2), (key1864, -2), (key1879, -2), (key1363, 2), (key1369, 2), (key1715, 2), (key1864, 2), (key1746, 2), (key1879, 2), (key1363, -2), (key1715, -2), (key1860, -2), (key1869, 6), (key1378, -2), (key1727, -2), (key1869, -2)]

def rawRow16495 : Integer.Sparse Key := [(key1495, -2), (key1489, -2), (key1518, -2), (key1489, 6), (key1864, -2), (key1860, -2), (key1879, -2), (key1369, 2), (key1363, 2), (key1864, 2), (key1715, 2), (key1879, 2), (key1746, 2), (key1363, -2), (key1860, -2), (key1715, -2), (key1869, 6), (key1378, -2), (key1869, -2), (key1727, -2)]

def rawRow16496 : Integer.Sparse Key := [(key1489, -2), (key1518, -2), (key1495, -2), (key1489, 6), (key1860, -2), (key1879, -2), (key1864, -2), (key1715, 2), (key1746, 2), (key1363, 2), (key1879, 2), (key1369, 2), (key1864, 2), (key1715, -2), (key1363, -2), (key1860, -2), (key1869, 6), (key1727, -2), (key1378, -2), (key1869, -2)]

def rawRow16497 : Integer.Sparse Key := [(key1518, -2), (key1489, -2), (key1495, -2), (key1489, 6), (key1879, -2), (key1860, -2), (key1864, -2), (key1746, 2), (key1715, 2), (key1879, 2), (key1363, 2), (key1864, 2), (key1369, 2), (key1715, -2), (key1860, -2), (key1363, -2), (key1869, 6), (key1727, -2), (key1869, -2), (key1378, -2)]

def rawRow16498 : Integer.Sparse Key := [(key1495, -2), (key1518, -2), (key1489, -2), (key1489, 6), (key1864, -2), (key1879, -2), (key1860, -2), (key1864, 2), (key1879, 2), (key1369, 2), (key1746, 2), (key1363, 2), (key1715, 2), (key1860, -2), (key1363, -2), (key1715, -2), (key1869, 6), (key1869, -2), (key1378, -2), (key1727, -2)]

def rawRow16499 : Integer.Sparse Key := [(key1518, -2), (key1495, -2), (key1489, -2), (key1489, 6), (key1879, -2), (key1864, -2), (key1860, -2), (key1879, 2), (key1864, 2), (key1746, 2), (key1369, 2), (key1715, 2), (key1363, 2), (key1860, -2), (key1715, -2), (key1363, -2), (key1869, 6), (key1869, -2), (key1727, -2), (key1378, -2)]

def rawRow16500 : Integer.Sparse Key := [(key1715, -2), (key1715, -2), (key1746, -2), (key1727, 6), (key1489, -2), (key1489, -2), (key1518, -2), (key1363, 2), (key1363, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1879, 2), (key1378, -2), (key1869, -2), (key1869, -2), (key1495, 6), (key1369, -2), (key1864, -2), (key1864, -2)]

def rawRow16501 : Integer.Sparse Key := [(key1715, -2), (key1746, -2), (key1715, -2), (key1727, 6), (key1489, -2), (key1518, -2), (key1489, -2), (key1860, 2), (key1879, 2), (key1363, 2), (key1879, 2), (key1363, 2), (key1860, 2), (key1869, -2), (key1378, -2), (key1869, -2), (key1495, 6), (key1864, -2), (key1369, -2), (key1864, -2)]

def rawRow16502 : Integer.Sparse Key := [(key1746, -2), (key1715, -2), (key1715, -2), (key1727, 6), (key1518, -2), (key1489, -2), (key1489, -2), (key1879, 2), (key1860, 2), (key1879, 2), (key1363, 2), (key1860, 2), (key1363, 2), (key1869, -2), (key1869, -2), (key1378, -2), (key1495, 6), (key1864, -2), (key1864, -2), (key1369, -2)]

def rawRow16503 : Integer.Sparse Key := [(key1715, -2), (key1727, -2), (key1746, -2), (key1715, 6), (key1860, -2), (key1869, -2), (key1879, -2), (key1363, 2), (key1378, 2), (key1489, 2), (key1869, 2), (key1518, 2), (key1879, 2), (key1363, -2), (key1489, -2), (key1860, -2), (key1864, 6), (key1369, -2), (key1495, -2), (key1864, -2)]

def rawRow16504 : Integer.Sparse Key := [(key1727, -2), (key1715, -2), (key1746, -2), (key1715, 6), (key1869, -2), (key1860, -2), (key1879, -2), (key1378, 2), (key1363, 2), (key1869, 2), (key1489, 2), (key1879, 2), (key1518, 2), (key1363, -2), (key1860, -2), (key1489, -2), (key1864, 6), (key1369, -2), (key1864, -2), (key1495, -2)]

def rawRow16505 : Integer.Sparse Key := [(key1715, -2), (key1746, -2), (key1727, -2), (key1715, 6), (key1860, -2), (key1879, -2), (key1869, -2), (key1489, 2), (key1518, 2), (key1363, 2), (key1879, 2), (key1378, 2), (key1869, 2), (key1489, -2), (key1363, -2), (key1860, -2), (key1864, 6), (key1495, -2), (key1369, -2), (key1864, -2)]

def rawRow16506 : Integer.Sparse Key := [(key1746, -2), (key1715, -2), (key1727, -2), (key1715, 6), (key1879, -2), (key1860, -2), (key1869, -2), (key1518, 2), (key1489, 2), (key1879, 2), (key1363, 2), (key1869, 2), (key1378, 2), (key1489, -2), (key1860, -2), (key1363, -2), (key1864, 6), (key1495, -2), (key1864, -2), (key1369, -2)]

def rawRow16507 : Integer.Sparse Key := [(key1727, -2), (key1746, -2), (key1715, -2), (key1715, 6), (key1869, -2), (key1879, -2), (key1860, -2), (key1869, 2), (key1879, 2), (key1378, 2), (key1518, 2), (key1363, 2), (key1489, 2), (key1860, -2), (key1363, -2), (key1489, -2), (key1864, 6), (key1864, -2), (key1369, -2), (key1495, -2)]

def rawRow16508 : Integer.Sparse Key := [(key1746, -2), (key1727, -2), (key1715, -2), (key1715, 6), (key1879, -2), (key1869, -2), (key1860, -2), (key1879, 2), (key1869, 2), (key1518, 2), (key1378, 2), (key1489, 2), (key1363, 2), (key1860, -2), (key1489, -2), (key1363, -2), (key1864, 6), (key1864, -2), (key1495, -2), (key1369, -2)]

def rawRow16509 : Integer.Sparse Key := [(key1860, -2), (key1864, -2), (key1879, -2), (key1869, 6), (key1489, -2), (key1495, -2), (key1518, -2), (key1363, 2), (key1369, 2), (key1715, 2), (key1864, 2), (key1746, 2), (key1879, 2), (key1378, -2), (key1727, -2), (key1869, -2), (key1489, 6), (key1363, -2), (key1715, -2), (key1860, -2)]

def rawRow16510 : Integer.Sparse Key := [(key1864, -2), (key1860, -2), (key1879, -2), (key1869, 6), (key1495, -2), (key1489, -2), (key1518, -2), (key1369, 2), (key1363, 2), (key1864, 2), (key1715, 2), (key1879, 2), (key1746, 2), (key1378, -2), (key1869, -2), (key1727, -2), (key1489, 6), (key1363, -2), (key1860, -2), (key1715, -2)]

def rawRow16511 : Integer.Sparse Key := [(key1860, -2), (key1879, -2), (key1864, -2), (key1869, 6), (key1489, -2), (key1518, -2), (key1495, -2), (key1715, 2), (key1746, 2), (key1363, 2), (key1879, 2), (key1369, 2), (key1864, 2), (key1727, -2), (key1378, -2), (key1869, -2), (key1489, 6), (key1715, -2), (key1363, -2), (key1860, -2)]

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

def rawRow16512 : Integer.Sparse Key := [(key1879, -2), (key1860, -2), (key1864, -2), (key1869, 6), (key1518, -2), (key1489, -2), (key1495, -2), (key1746, 2), (key1715, 2), (key1879, 2), (key1363, 2), (key1864, 2), (key1369, 2), (key1727, -2), (key1869, -2), (key1378, -2), (key1489, 6), (key1715, -2), (key1860, -2), (key1363, -2)]

def rawRow16513 : Integer.Sparse Key := [(key1864, -2), (key1879, -2), (key1860, -2), (key1869, 6), (key1495, -2), (key1518, -2), (key1489, -2), (key1864, 2), (key1879, 2), (key1369, 2), (key1746, 2), (key1363, 2), (key1715, 2), (key1869, -2), (key1378, -2), (key1727, -2), (key1489, 6), (key1860, -2), (key1363, -2), (key1715, -2)]

def rawRow16514 : Integer.Sparse Key := [(key1879, -2), (key1864, -2), (key1860, -2), (key1869, 6), (key1518, -2), (key1495, -2), (key1489, -2), (key1879, 2), (key1864, 2), (key1746, 2), (key1369, 2), (key1715, 2), (key1363, 2), (key1869, -2), (key1727, -2), (key1378, -2), (key1489, 6), (key1860, -2), (key1715, -2), (key1363, -2)]

def rawRow16515 : Integer.Sparse Key := [(key1860, -2), (key1869, -2), (key1879, -2), (key1864, 6), (key1715, -2), (key1727, -2), (key1746, -2), (key1363, 2), (key1378, 2), (key1489, 2), (key1869, 2), (key1518, 2), (key1879, 2), (key1369, -2), (key1495, -2), (key1864, -2), (key1715, 6), (key1363, -2), (key1489, -2), (key1860, -2)]

def rawRow16516 : Integer.Sparse Key := [(key1869, -2), (key1860, -2), (key1879, -2), (key1864, 6), (key1727, -2), (key1715, -2), (key1746, -2), (key1378, 2), (key1363, 2), (key1869, 2), (key1489, 2), (key1879, 2), (key1518, 2), (key1369, -2), (key1864, -2), (key1495, -2), (key1715, 6), (key1363, -2), (key1860, -2), (key1489, -2)]

def rawRow16517 : Integer.Sparse Key := [(key1860, -2), (key1879, -2), (key1869, -2), (key1864, 6), (key1715, -2), (key1746, -2), (key1727, -2), (key1489, 2), (key1518, 2), (key1363, 2), (key1879, 2), (key1378, 2), (key1869, 2), (key1495, -2), (key1369, -2), (key1864, -2), (key1715, 6), (key1489, -2), (key1363, -2), (key1860, -2)]

def rawRow16518 : Integer.Sparse Key := [(key1879, -2), (key1860, -2), (key1869, -2), (key1864, 6), (key1746, -2), (key1715, -2), (key1727, -2), (key1518, 2), (key1489, 2), (key1879, 2), (key1363, 2), (key1869, 2), (key1378, 2), (key1495, -2), (key1864, -2), (key1369, -2), (key1715, 6), (key1489, -2), (key1860, -2), (key1363, -2)]

def rawRow16519 : Integer.Sparse Key := [(key1869, -2), (key1879, -2), (key1860, -2), (key1864, 6), (key1727, -2), (key1746, -2), (key1715, -2), (key1869, 2), (key1879, 2), (key1378, 2), (key1518, 2), (key1363, 2), (key1489, 2), (key1864, -2), (key1369, -2), (key1495, -2), (key1715, 6), (key1860, -2), (key1363, -2), (key1489, -2)]

def rawRow16520 : Integer.Sparse Key := [(key1879, -2), (key1869, -2), (key1860, -2), (key1864, 6), (key1746, -2), (key1727, -2), (key1715, -2), (key1879, 2), (key1869, 2), (key1518, 2), (key1378, 2), (key1489, 2), (key1363, 2), (key1864, -2), (key1495, -2), (key1369, -2), (key1715, 6), (key1860, -2), (key1489, -2), (key1363, -2)]

def rawRow16521 : Integer.Sparse Key := [(key1864, -2), (key1869, -2), (key1879, -2), (key1860, 6), (key1864, -2), (key1869, -2), (key1879, -2), (key1369, 2), (key1378, 2), (key1495, 2), (key1727, 2), (key1518, 2), (key1746, 2), (key1363, -2), (key1489, -2), (key1715, -2), (key1860, 6), (key1363, -2), (key1489, -2), (key1715, -2)]

def rawRow16522 : Integer.Sparse Key := [(key1869, -2), (key1864, -2), (key1879, -2), (key1860, 6), (key1869, -2), (key1864, -2), (key1879, -2), (key1378, 2), (key1369, 2), (key1727, 2), (key1495, 2), (key1746, 2), (key1518, 2), (key1363, -2), (key1715, -2), (key1489, -2), (key1860, 6), (key1363, -2), (key1715, -2), (key1489, -2)]

def rawRow16523 : Integer.Sparse Key := [(key1864, -2), (key1879, -2), (key1869, -2), (key1860, 6), (key1864, -2), (key1879, -2), (key1869, -2), (key1495, 2), (key1518, 2), (key1369, 2), (key1746, 2), (key1378, 2), (key1727, 2), (key1489, -2), (key1363, -2), (key1715, -2), (key1860, 6), (key1489, -2), (key1363, -2), (key1715, -2)]

def rawRow16524 : Integer.Sparse Key := [(key1879, -2), (key1864, -2), (key1869, -2), (key1860, 6), (key1879, -2), (key1864, -2), (key1869, -2), (key1518, 2), (key1495, 2), (key1746, 2), (key1369, 2), (key1727, 2), (key1378, 2), (key1489, -2), (key1715, -2), (key1363, -2), (key1860, 6), (key1489, -2), (key1715, -2), (key1363, -2)]

def rawRow16525 : Integer.Sparse Key := [(key1869, -2), (key1879, -2), (key1864, -2), (key1860, 6), (key1869, -2), (key1879, -2), (key1864, -2), (key1727, 2), (key1746, 2), (key1378, 2), (key1518, 2), (key1369, 2), (key1495, 2), (key1715, -2), (key1363, -2), (key1489, -2), (key1860, 6), (key1715, -2), (key1363, -2), (key1489, -2)]

def rawRow16526 : Integer.Sparse Key := [(key1879, -2), (key1869, -2), (key1864, -2), (key1860, 6), (key1879, -2), (key1869, -2), (key1864, -2), (key1746, 2), (key1727, 2), (key1518, 2), (key1378, 2), (key1495, 2), (key1369, 2), (key1715, -2), (key1489, -2), (key1363, -2), (key1860, 6), (key1715, -2), (key1489, -2), (key1363, -2)]

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

def rawRow16671 : Integer.Sparse Key := [(key2617, 2), (key2962, 2), (key2962, 2), (key2620, -1), (key2620, -1), (key2833, -1), (key2833, -1), (key2964, -1), (key2964, -1), (key2633, 2), (key2985, 2), (key2985, 2), (key2643, -1), (key2643, -1), (key2730, -1), (key2730, -1), (key2994, -1), (key2994, -1), (key2650, -1), (key2650, -1), (key2906, -1), (key2906, -1), (key3001, -1), (key3001, -1), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, -1), (key3004, -1), (key2656, 2), (key2656, 2), (key2751, 2), (key2751, 2), (key2915, 2), (key2915, 2)]

def rawRow16672 : Integer.Sparse Key := [(key2962, 2), (key2617, 2), (key2962, 2), (key2833, -1), (key2964, -1), (key2620, -1), (key2964, -1), (key2620, -1), (key2833, -1), (key2985, 2), (key2633, 2), (key2985, 2), (key2730, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2906, -1), (key3001, -1), (key2650, -1), (key3001, -1), (key2650, -1), (key2906, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2751, 2), (key2915, 2), (key2656, 2), (key2915, 2), (key2656, 2), (key2751, 2)]

def rawRow16673 : Integer.Sparse Key := [(key2962, 2), (key2962, 2), (key2617, 2), (key2964, -1), (key2833, -1), (key2964, -1), (key2620, -1), (key2833, -1), (key2620, -1), (key2985, 2), (key2985, 2), (key2633, 2), (key2994, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2643, -1), (key3001, -1), (key2906, -1), (key3001, -1), (key2650, -1), (key2906, -1), (key2650, -1), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2655, -1), (key2915, 2), (key2751, 2), (key2915, 2), (key2656, 2), (key2751, 2), (key2656, 2)]

def rawRow16674 : Integer.Sparse Key := [(key2620, 2), (key2833, 2), (key2964, 2), (key2617, -1), (key2620, -1), (key2810, -1), (key2833, -1), (key2952, -1), (key2962, -1), (key2643, 2), (key2978, 2), (key2994, 2), (key2633, -1), (key2643, -1), (key2707, -1), (key2730, -1), (key2978, -1), (key2985, -1), (key2655, -1), (key2656, -1), (key2899, -1), (key2915, -1), (key2999, -1), (key3004, -1), (key2650, -1), (key2656, -1), (key2739, -1), (key2751, -1), (key2999, -1), (key3001, -1), (key2650, 2), (key2655, 2), (key2739, 2), (key2749, 2), (key2899, 2), (key2906, 2)]

def rawRow16675 : Integer.Sparse Key := [(key2620, 2), (key2964, 2), (key2833, 2), (key2620, -1), (key2617, -1), (key2833, -1), (key2810, -1), (key2962, -1), (key2952, -1), (key2643, 2), (key2994, 2), (key2978, 2), (key2643, -1), (key2633, -1), (key2730, -1), (key2707, -1), (key2985, -1), (key2978, -1), (key2656, -1), (key2655, -1), (key2915, -1), (key2899, -1), (key3004, -1), (key2999, -1), (key2656, -1), (key2650, -1), (key2751, -1), (key2739, -1), (key3001, -1), (key2999, -1), (key2655, 2), (key2650, 2), (key2749, 2), (key2739, 2), (key2906, 2), (key2899, 2)]

def rawRow16676 : Integer.Sparse Key := [(key2833, 2), (key2620, 2), (key2964, 2), (key2810, -1), (key2833, -1), (key2617, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2978, 2), (key2643, 2), (key2994, 2), (key2707, -1), (key2978, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2899, -1), (key2999, -1), (key2655, -1), (key3004, -1), (key2656, -1), (key2915, -1), (key2739, -1), (key2999, -1), (key2650, -1), (key3001, -1), (key2656, -1), (key2751, -1), (key2739, 2), (key2899, 2), (key2650, 2), (key2906, 2), (key2655, 2), (key2749, 2)]

def rawRow16677 : Integer.Sparse Key := [(key2833, 2), (key2964, 2), (key2620, 2), (key2833, -1), (key2810, -1), (key2962, -1), (key2617, -1), (key2833, -1), (key2620, -1), (key2978, 2), (key2994, 2), (key2643, 2), (key2978, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2730, -1), (key2643, -1), (key2999, -1), (key2899, -1), (key3004, -1), (key2655, -1), (key2915, -1), (key2656, -1), (key2999, -1), (key2739, -1), (key3001, -1), (key2650, -1), (key2751, -1), (key2656, -1), (key2899, 2), (key2739, 2), (key2906, 2), (key2650, 2), (key2749, 2), (key2655, 2)]

def rawRow16678 : Integer.Sparse Key := [(key2964, 2), (key2620, 2), (key2833, 2), (key2952, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2617, -1), (key2810, -1), (key2994, 2), (key2643, 2), (key2978, 2), (key2730, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2633, -1), (key2707, -1), (key2915, -1), (key3004, -1), (key2656, -1), (key2999, -1), (key2655, -1), (key2899, -1), (key2751, -1), (key3001, -1), (key2656, -1), (key2999, -1), (key2650, -1), (key2739, -1), (key2749, 2), (key2906, 2), (key2655, 2), (key2899, 2), (key2650, 2), (key2739, 2)]

def rawRow16679 : Integer.Sparse Key := [(key2964, 2), (key2833, 2), (key2620, 2), (key2962, -1), (key2952, -1), (key2833, -1), (key2620, -1), (key2810, -1), (key2617, -1), (key2994, 2), (key2978, 2), (key2643, 2), (key2985, -1), (key2730, -1), (key2978, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key3004, -1), (key2915, -1), (key2999, -1), (key2656, -1), (key2899, -1), (key2655, -1), (key3001, -1), (key2751, -1), (key2999, -1), (key2656, -1), (key2739, -1), (key2650, -1), (key2906, 2), (key2749, 2), (key2899, 2), (key2655, 2), (key2739, 2), (key2650, 2)]

def rawRow16680 : Integer.Sparse Key := [(key2633, 2), (key2985, 2), (key2985, 2), (key2643, -1), (key2643, -1), (key2978, -1), (key2978, -1), (key2994, -1), (key2994, -1), (key2617, 2), (key2962, 2), (key2962, 2), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, -1), (key3004, -1), (key2620, -1), (key2620, -1), (key2833, -1), (key2833, -1), (key2964, -1), (key2964, -1), (key2643, -1), (key2643, -1), (key2730, -1), (key2730, -1), (key2994, -1), (key2994, -1), (key2656, 2), (key2656, 2), (key2751, 2), (key2751, 2), (key2915, 2), (key2915, 2)]

def rawRow16681 : Integer.Sparse Key := [(key2985, 2), (key2633, 2), (key2985, 2), (key2978, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, -1), (key2978, -1), (key2962, 2), (key2617, 2), (key2962, 2), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2833, -1), (key2964, -1), (key2620, -1), (key2964, -1), (key2620, -1), (key2833, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2751, 2), (key2915, 2), (key2656, 2), (key2915, 2), (key2656, 2), (key2751, 2)]

def rawRow16682 : Integer.Sparse Key := [(key2985, 2), (key2985, 2), (key2633, 2), (key2994, -1), (key2978, -1), (key2994, -1), (key2643, -1), (key2978, -1), (key2643, -1), (key2962, 2), (key2962, 2), (key2617, 2), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2655, -1), (key2964, -1), (key2833, -1), (key2964, -1), (key2620, -1), (key2833, -1), (key2620, -1), (key2994, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2643, -1), (key2915, 2), (key2751, 2), (key2915, 2), (key2656, 2), (key2751, 2), (key2656, 2)]

def rawRow16683 : Integer.Sparse Key := [(key2643, 2), (key2730, 2), (key2994, 2), (key2633, -1), (key2643, -1), (key2707, -1), (key2978, -1), (key2730, -1), (key2985, -1), (key2655, 2), (key2749, 2), (key3004, 2), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2643, -1), (key2656, -1), (key2797, -1), (key2915, -1), (key2946, -1), (key2994, -1), (key2620, -1), (key2656, -1), (key2675, -1), (key2751, -1), (key2946, -1), (key2964, -1), (key2620, 2), (key2643, 2), (key2675, 2), (key2730, 2), (key2797, 2), (key2833, 2)]

def rawRow16684 : Integer.Sparse Key := [(key2643, 2), (key2994, 2), (key2730, 2), (key2643, -1), (key2633, -1), (key2978, -1), (key2707, -1), (key2985, -1), (key2730, -1), (key2655, 2), (key3004, 2), (key2749, 2), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2945, -1), (key2656, -1), (key2643, -1), (key2915, -1), (key2797, -1), (key2994, -1), (key2946, -1), (key2656, -1), (key2620, -1), (key2751, -1), (key2675, -1), (key2964, -1), (key2946, -1), (key2643, 2), (key2620, 2), (key2730, 2), (key2675, 2), (key2833, 2), (key2797, 2)]

def rawRow16685 : Integer.Sparse Key := [(key2730, 2), (key2643, 2), (key2994, 2), (key2707, -1), (key2730, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2749, 2), (key2655, 2), (key3004, 2), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2797, -1), (key2946, -1), (key2643, -1), (key2994, -1), (key2656, -1), (key2915, -1), (key2675, -1), (key2946, -1), (key2620, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2675, 2), (key2797, 2), (key2620, 2), (key2833, 2), (key2643, 2), (key2730, 2)]

def rawRow16686 : Integer.Sparse Key := [(key2730, 2), (key2994, 2), (key2643, 2), (key2730, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2978, -1), (key2643, -1), (key2749, 2), (key3004, 2), (key2655, 2), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, -1), (key2655, -1), (key2946, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2915, -1), (key2656, -1), (key2946, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2751, -1), (key2656, -1), (key2797, 2), (key2675, 2), (key2833, 2), (key2620, 2), (key2730, 2), (key2643, 2)]

def rawRow16687 : Integer.Sparse Key := [(key2994, 2), (key2643, 2), (key2730, 2), (key2978, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2633, -1), (key2707, -1), (key3004, 2), (key2655, 2), (key2749, 2), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, -1), (key2672, -1), (key2915, -1), (key2994, -1), (key2656, -1), (key2946, -1), (key2643, -1), (key2797, -1), (key2751, -1), (key2964, -1), (key2656, -1), (key2946, -1), (key2620, -1), (key2675, -1), (key2730, 2), (key2833, 2), (key2643, 2), (key2797, 2), (key2620, 2), (key2675, 2)]

def rawRow16688 : Integer.Sparse Key := [(key2994, 2), (key2730, 2), (key2643, 2), (key2985, -1), (key2978, -1), (key2730, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key3004, 2), (key2749, 2), (key2655, 2), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, -1), (key2617, -1), (key2994, -1), (key2915, -1), (key2946, -1), (key2656, -1), (key2797, -1), (key2643, -1), (key2964, -1), (key2751, -1), (key2946, -1), (key2656, -1), (key2675, -1), (key2620, -1), (key2833, 2), (key2730, 2), (key2797, 2), (key2643, 2), (key2675, 2), (key2620, 2)]

def rawRow16689 : Integer.Sparse Key := [(key2650, 2), (key2906, 2), (key3001, 2), (key2655, -1), (key2656, -1), (key2899, -1), (key2999, -1), (key2915, -1), (key3004, -1), (key2620, 2), (key2833, 2), (key2964, 2), (key2643, -1), (key2656, -1), (key2797, -1), (key2946, -1), (key2915, -1), (key2994, -1), (key2617, -1), (key2620, -1), (key2810, -1), (key2833, -1), (key2952, -1), (key2962, -1), (key2633, -1), (key2643, -1), (key2707, -1), (key2730, -1), (key2978, -1), (key2985, -1), (key2650, 2), (key2655, 2), (key2739, 2), (key2749, 2), (key2899, 2), (key2906, 2)]

def rawRow16690 : Integer.Sparse Key := [(key2650, 2), (key3001, 2), (key2906, 2), (key2656, -1), (key2655, -1), (key2999, -1), (key2899, -1), (key3004, -1), (key2915, -1), (key2620, 2), (key2964, 2), (key2833, 2), (key2656, -1), (key2643, -1), (key2946, -1), (key2797, -1), (key2994, -1), (key2915, -1), (key2620, -1), (key2617, -1), (key2833, -1), (key2810, -1), (key2962, -1), (key2952, -1), (key2643, -1), (key2633, -1), (key2730, -1), (key2707, -1), (key2985, -1), (key2978, -1), (key2655, 2), (key2650, 2), (key2749, 2), (key2739, 2), (key2906, 2), (key2899, 2)]

def rawRow16691 : Integer.Sparse Key := [(key2906, 2), (key2650, 2), (key3001, 2), (key2899, -1), (key2915, -1), (key2655, -1), (key3004, -1), (key2656, -1), (key2999, -1), (key2833, 2), (key2620, 2), (key2964, 2), (key2797, -1), (key2915, -1), (key2643, -1), (key2994, -1), (key2656, -1), (key2946, -1), (key2810, -1), (key2833, -1), (key2617, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2707, -1), (key2978, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2739, 2), (key2899, 2), (key2650, 2), (key2906, 2), (key2655, 2), (key2749, 2)]

def rawRow16692 : Integer.Sparse Key := [(key2906, 2), (key3001, 2), (key2650, 2), (key2915, -1), (key2899, -1), (key3004, -1), (key2655, -1), (key2999, -1), (key2656, -1), (key2833, 2), (key2964, 2), (key2620, 2), (key2915, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2946, -1), (key2656, -1), (key2833, -1), (key2810, -1), (key2962, -1), (key2617, -1), (key2833, -1), (key2620, -1), (key2978, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2730, -1), (key2643, -1), (key2899, 2), (key2739, 2), (key2906, 2), (key2650, 2), (key2749, 2), (key2655, 2)]

def rawRow16693 : Integer.Sparse Key := [(key3001, 2), (key2650, 2), (key2906, 2), (key2999, -1), (key3004, -1), (key2656, -1), (key2915, -1), (key2655, -1), (key2899, -1), (key2964, 2), (key2620, 2), (key2833, 2), (key2946, -1), (key2994, -1), (key2656, -1), (key2915, -1), (key2643, -1), (key2797, -1), (key2952, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2617, -1), (key2810, -1), (key2730, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2633, -1), (key2707, -1), (key2749, 2), (key2906, 2), (key2655, 2), (key2899, 2), (key2650, 2), (key2739, 2)]

def rawRow16694 : Integer.Sparse Key := [(key3001, 2), (key2906, 2), (key2650, 2), (key3004, -1), (key2999, -1), (key2915, -1), (key2656, -1), (key2899, -1), (key2655, -1), (key2964, 2), (key2833, 2), (key2620, 2), (key2994, -1), (key2946, -1), (key2915, -1), (key2656, -1), (key2797, -1), (key2643, -1), (key2962, -1), (key2952, -1), (key2833, -1), (key2620, -1), (key2810, -1), (key2617, -1), (key2985, -1), (key2730, -1), (key2978, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key2906, 2), (key2749, 2), (key2899, 2), (key2655, 2), (key2739, 2), (key2650, 2)]

def rawRow16695 : Integer.Sparse Key := [(key2655, 2), (key2749, 2), (key3004, 2), (key2650, -1), (key2656, -1), (key2739, -1), (key2999, -1), (key2751, -1), (key3001, -1), (key2643, 2), (key2730, 2), (key2994, 2), (key2620, -1), (key2656, -1), (key2675, -1), (key2946, -1), (key2751, -1), (key2964, -1), (key2633, -1), (key2643, -1), (key2707, -1), (key2978, -1), (key2730, -1), (key2985, -1), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2620, 2), (key2643, 2), (key2675, 2), (key2730, 2), (key2797, 2), (key2833, 2)]

def rawRow16696 : Integer.Sparse Key := [(key2655, 2), (key3004, 2), (key2749, 2), (key2656, -1), (key2650, -1), (key2999, -1), (key2739, -1), (key3001, -1), (key2751, -1), (key2643, 2), (key2994, 2), (key2730, 2), (key2656, -1), (key2620, -1), (key2946, -1), (key2675, -1), (key2964, -1), (key2751, -1), (key2643, -1), (key2633, -1), (key2978, -1), (key2707, -1), (key2985, -1), (key2730, -1), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2945, -1), (key2643, 2), (key2620, 2), (key2730, 2), (key2675, 2), (key2833, 2), (key2797, 2)]

def rawRow16697 : Integer.Sparse Key := [(key2749, 2), (key2655, 2), (key3004, 2), (key2739, -1), (key2751, -1), (key2650, -1), (key3001, -1), (key2656, -1), (key2999, -1), (key2730, 2), (key2643, 2), (key2994, 2), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, -1), (key2946, -1), (key2707, -1), (key2730, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2675, 2), (key2797, 2), (key2620, 2), (key2833, 2), (key2643, 2), (key2730, 2)]

def rawRow16698 : Integer.Sparse Key := [(key2749, 2), (key3004, 2), (key2655, 2), (key2751, -1), (key2739, -1), (key3001, -1), (key2650, -1), (key2999, -1), (key2656, -1), (key2730, 2), (key2994, 2), (key2643, 2), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, -1), (key2656, -1), (key2730, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2978, -1), (key2643, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, -1), (key2655, -1), (key2797, 2), (key2675, 2), (key2833, 2), (key2620, 2), (key2730, 2), (key2643, 2)]

def rawRow16699 : Integer.Sparse Key := [(key3004, 2), (key2655, 2), (key2749, 2), (key2999, -1), (key3001, -1), (key2656, -1), (key2751, -1), (key2650, -1), (key2739, -1), (key2994, 2), (key2643, 2), (key2730, 2), (key2946, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2620, -1), (key2675, -1), (key2978, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2633, -1), (key2707, -1), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, -1), (key2672, -1), (key2730, 2), (key2833, 2), (key2643, 2), (key2797, 2), (key2620, 2), (key2675, 2)]

def rawRow16700 : Integer.Sparse Key := [(key3004, 2), (key2749, 2), (key2655, 2), (key3001, -1), (key2999, -1), (key2751, -1), (key2656, -1), (key2739, -1), (key2650, -1), (key2994, 2), (key2730, 2), (key2643, 2), (key2964, -1), (key2946, -1), (key2751, -1), (key2656, -1), (key2675, -1), (key2620, -1), (key2985, -1), (key2978, -1), (key2730, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, -1), (key2617, -1), (key2833, 2), (key2730, 2), (key2797, 2), (key2643, 2), (key2675, 2), (key2620, 2)]

def rawRow16701 : Integer.Sparse Key := [(key2656, 2), (key2751, 2), (key2915, 2), (key2650, -1), (key2655, -1), (key2739, -1), (key2899, -1), (key2749, -1), (key2906, -1), (key2656, 2), (key2751, 2), (key2915, 2), (key2620, -1), (key2643, -1), (key2675, -1), (key2797, -1), (key2730, -1), (key2833, -1), (key2650, -1), (key2655, -1), (key2739, -1), (key2899, -1), (key2749, -1), (key2906, -1), (key2620, -1), (key2643, -1), (key2675, -1), (key2797, -1), (key2730, -1), (key2833, -1), (key2617, 2), (key2633, 2), (key2672, 2), (key2707, 2), (key2787, 2), (key2810, 2)]

def rawRow16702 : Integer.Sparse Key := [(key2656, 2), (key2915, 2), (key2751, 2), (key2655, -1), (key2650, -1), (key2899, -1), (key2739, -1), (key2906, -1), (key2749, -1), (key2656, 2), (key2915, 2), (key2751, 2), (key2643, -1), (key2620, -1), (key2797, -1), (key2675, -1), (key2833, -1), (key2730, -1), (key2655, -1), (key2650, -1), (key2899, -1), (key2739, -1), (key2906, -1), (key2749, -1), (key2643, -1), (key2620, -1), (key2797, -1), (key2675, -1), (key2833, -1), (key2730, -1), (key2633, 2), (key2617, 2), (key2707, 2), (key2672, 2), (key2810, 2), (key2787, 2)]

def rawRow16703 : Integer.Sparse Key := [(key2751, 2), (key2656, 2), (key2915, 2), (key2739, -1), (key2749, -1), (key2650, -1), (key2906, -1), (key2655, -1), (key2899, -1), (key2751, 2), (key2656, 2), (key2915, 2), (key2675, -1), (key2730, -1), (key2620, -1), (key2833, -1), (key2643, -1), (key2797, -1), (key2739, -1), (key2749, -1), (key2650, -1), (key2906, -1), (key2655, -1), (key2899, -1), (key2675, -1), (key2730, -1), (key2620, -1), (key2833, -1), (key2643, -1), (key2797, -1), (key2672, 2), (key2707, 2), (key2617, 2), (key2810, 2), (key2633, 2), (key2707, 2)]

def rawRow16704 : Integer.Sparse Key := [(key2751, 2), (key2915, 2), (key2656, 2), (key2749, -1), (key2739, -1), (key2906, -1), (key2650, -1), (key2899, -1), (key2655, -1), (key2751, 2), (key2915, 2), (key2656, 2), (key2730, -1), (key2675, -1), (key2833, -1), (key2620, -1), (key2797, -1), (key2643, -1), (key2749, -1), (key2739, -1), (key2906, -1), (key2650, -1), (key2899, -1), (key2655, -1), (key2730, -1), (key2675, -1), (key2833, -1), (key2620, -1), (key2797, -1), (key2643, -1), (key2707, 2), (key2672, 2), (key2810, 2), (key2617, 2), (key2707, 2), (key2633, 2)]

def rawRow16705 : Integer.Sparse Key := [(key2915, 2), (key2656, 2), (key2751, 2), (key2899, -1), (key2906, -1), (key2655, -1), (key2749, -1), (key2650, -1), (key2739, -1), (key2915, 2), (key2656, 2), (key2751, 2), (key2797, -1), (key2833, -1), (key2643, -1), (key2730, -1), (key2620, -1), (key2675, -1), (key2899, -1), (key2906, -1), (key2655, -1), (key2749, -1), (key2650, -1), (key2739, -1), (key2797, -1), (key2833, -1), (key2643, -1), (key2730, -1), (key2620, -1), (key2675, -1), (key2787, 2), (key2810, 2), (key2633, 2), (key2707, 2), (key2617, 2), (key2672, 2)]

def rawRow16706 : Integer.Sparse Key := [(key2915, 2), (key2751, 2), (key2656, 2), (key2906, -1), (key2899, -1), (key2749, -1), (key2655, -1), (key2739, -1), (key2650, -1), (key2915, 2), (key2751, 2), (key2656, 2), (key2833, -1), (key2797, -1), (key2730, -1), (key2643, -1), (key2675, -1), (key2620, -1), (key2906, -1), (key2899, -1), (key2749, -1), (key2655, -1), (key2739, -1), (key2650, -1), (key2833, -1), (key2797, -1), (key2730, -1), (key2643, -1), (key2675, -1), (key2620, -1), (key2810, 2), (key2787, 2), (key2707, 2), (key2633, 2), (key2672, 2), (key2617, 2)]

def rawRow16707 : Integer.Sparse Key := [(key2234, 4), (key2234, 4), (key2259, 4), (key2268, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2294, -2), (key2268, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2294, -2), (key2324, 4), (key2324, 4), (key2336, 4)]

def rawRow16708 : Integer.Sparse Key := [(key2234, 4), (key2259, 4), (key2234, 4), (key2272, -2), (key2268, -2), (key2294, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2324, 4), (key2336, 4), (key2324, 4)]

def rawRow16709 : Integer.Sparse Key := [(key2259, 4), (key2234, 4), (key2234, 4), (key2294, -2), (key2294, -2), (key2272, -2), (key2272, -2), (key2268, -2), (key2268, -2), (key2294, -2), (key2294, -2), (key2272, -2), (key2272, -2), (key2268, -2), (key2268, -2), (key2336, 4), (key2324, 4), (key2324, 4)]

def rawRow16710 : Integer.Sparse Key := [(key1989, 4), (key2268, 4), (key2294, 4), (key1989, -2), (key1994, -2), (key2234, -2), (key2259, -2), (key2272, -2), (key2294, -2), (key1999, -2), (key2003, -2), (key2268, -2), (key2294, -2), (key2324, -2), (key2336, -2), (key2003, 4), (key2272, 4), (key2294, 4)]

def rawRow16711 : Integer.Sparse Key := [(key1989, 4), (key2294, 4), (key2268, 4), (key1994, -2), (key1989, -2), (key2259, -2), (key2234, -2), (key2294, -2), (key2272, -2), (key2003, -2), (key1999, -2), (key2294, -2), (key2268, -2), (key2336, -2), (key2324, -2), (key2003, 4), (key2294, 4), (key2272, 4)]

def rawRow16712 : Integer.Sparse Key := [(key2268, 4), (key1989, 4), (key2294, 4), (key2234, -2), (key2272, -2), (key1989, -2), (key2294, -2), (key1994, -2), (key2259, -2), (key2268, -2), (key2324, -2), (key1999, -2), (key2336, -2), (key2003, -2), (key2294, -2), (key2272, 4), (key2003, 4), (key2294, 4)]

def rawRow16713 : Integer.Sparse Key := [(key2268, 4), (key2294, 4), (key1989, 4), (key2272, -2), (key2234, -2), (key2294, -2), (key1989, -2), (key2259, -2), (key1994, -2), (key2324, -2), (key2268, -2), (key2336, -2), (key1999, -2), (key2294, -2), (key2003, -2), (key2272, 4), (key2294, 4), (key2003, 4)]

def rawRow16714 : Integer.Sparse Key := [(key2294, 4), (key1989, 4), (key2268, 4), (key2259, -2), (key2294, -2), (key1994, -2), (key2272, -2), (key1989, -2), (key2234, -2), (key2294, -2), (key2336, -2), (key2003, -2), (key2324, -2), (key1999, -2), (key2268, -2), (key2294, 4), (key2003, 4), (key2272, 4)]

def rawRow16715 : Integer.Sparse Key := [(key2294, 4), (key2268, 4), (key1989, 4), (key2294, -2), (key2259, -2), (key2272, -2), (key1994, -2), (key2234, -2), (key1989, -2), (key2336, -2), (key2294, -2), (key2324, -2), (key2003, -2), (key2268, -2), (key1999, -2), (key2294, 4), (key2272, 4), (key2003, 4)]

def rawRow16716 : Integer.Sparse Key := [(key1989, 4), (key2268, 4), (key2294, 4), (key1999, -2), (key2003, -2), (key2268, -2), (key2294, -2), (key2324, -2), (key2336, -2), (key1989, -2), (key1994, -2), (key2234, -2), (key2259, -2), (key2272, -2), (key2294, -2), (key2003, 4), (key2272, 4), (key2294, 4)]

def rawRow16717 : Integer.Sparse Key := [(key1989, 4), (key2294, 4), (key2268, 4), (key2003, -2), (key1999, -2), (key2294, -2), (key2268, -2), (key2336, -2), (key2324, -2), (key1994, -2), (key1989, -2), (key2259, -2), (key2234, -2), (key2294, -2), (key2272, -2), (key2003, 4), (key2294, 4), (key2272, 4)]

def rawRow16718 : Integer.Sparse Key := [(key2268, 4), (key1989, 4), (key2294, 4), (key2268, -2), (key2324, -2), (key1999, -2), (key2336, -2), (key2003, -2), (key2294, -2), (key2234, -2), (key2272, -2), (key1989, -2), (key2294, -2), (key1994, -2), (key2259, -2), (key2272, 4), (key2003, 4), (key2294, 4)]

def rawRow16719 : Integer.Sparse Key := [(key2268, 4), (key2294, 4), (key1989, 4), (key2324, -2), (key2268, -2), (key2336, -2), (key1999, -2), (key2294, -2), (key2003, -2), (key2272, -2), (key2234, -2), (key2294, -2), (key1989, -2), (key2259, -2), (key1994, -2), (key2272, 4), (key2294, 4), (key2003, 4)]

def rawRow16720 : Integer.Sparse Key := [(key2294, 4), (key1989, 4), (key2268, 4), (key2294, -2), (key2336, -2), (key2003, -2), (key2324, -2), (key1999, -2), (key2268, -2), (key2259, -2), (key2294, -2), (key1994, -2), (key2272, -2), (key1989, -2), (key2234, -2), (key2294, 4), (key2003, 4), (key2272, 4)]

def rawRow16721 : Integer.Sparse Key := [(key2294, 4), (key2268, 4), (key1989, 4), (key2336, -2), (key2294, -2), (key2324, -2), (key2003, -2), (key2268, -2), (key1999, -2), (key2294, -2), (key2259, -2), (key2272, -2), (key1994, -2), (key2234, -2), (key1989, -2), (key2294, 4), (key2272, 4), (key2003, 4)]

def rawRow16722 : Integer.Sparse Key := [(key1999, 4), (key1999, 4), (key2336, 4), (key1989, -2), (key2003, -2), (key1989, -2), (key2294, -2), (key2003, -2), (key2294, -2), (key1989, -2), (key2003, -2), (key1989, -2), (key2294, -2), (key2003, -2), (key2294, -2), (key1994, 4), (key1994, 4), (key2259, 4)]

def rawRow16723 : Integer.Sparse Key := [(key1999, 4), (key2336, 4), (key1999, 4), (key2003, -2), (key1989, -2), (key2294, -2), (key1989, -2), (key2294, -2), (key2003, -2), (key2003, -2), (key1989, -2), (key2294, -2), (key1989, -2), (key2294, -2), (key2003, -2), (key1994, 4), (key2259, 4), (key1994, 4)]

def rawRow16724 : Integer.Sparse Key := [(key2336, 4), (key1999, 4), (key1999, 4), (key2294, -2), (key2294, -2), (key2003, -2), (key2003, -2), (key1989, -2), (key1989, -2), (key2294, -2), (key2294, -2), (key2003, -2), (key2003, -2), (key1989, -2), (key1989, -2), (key2259, 4), (key1994, 4), (key1994, 4)]

def rawRow16725 : Integer.Sparse Key := [(key702, -2), (key706, -2), (key706, -2), (key722, 6), (key702, -2), (key706, -2), (key706, -2), (key856, 2), (key860, 2), (key856, 2), (key883, 2), (key860, 2), (key883, 2), (key922, -2), (key922, -2), (key939, -2), (key722, 6), (key922, -2), (key922, -2), (key939, -2)]

def rawRow16726 : Integer.Sparse Key := [(key706, -2), (key702, -2), (key706, -2), (key722, 6), (key706, -2), (key702, -2), (key706, -2), (key860, 2), (key856, 2), (key883, 2), (key856, 2), (key883, 2), (key860, 2), (key922, -2), (key939, -2), (key922, -2), (key722, 6), (key922, -2), (key939, -2), (key922, -2)]

def rawRow16727 : Integer.Sparse Key := [(key706, -2), (key706, -2), (key702, -2), (key722, 6), (key706, -2), (key706, -2), (key702, -2), (key883, 2), (key883, 2), (key860, 2), (key860, 2), (key856, 2), (key856, 2), (key939, -2), (key922, -2), (key922, -2), (key722, 6), (key939, -2), (key922, -2), (key922, -2)]

def rawRow16728 : Integer.Sparse Key := [(key702, -2), (key706, -2), (key722, -2), (key706, 6), (key856, -2), (key860, -2), (key922, -2), (key702, 2), (key706, 2), (key856, 2), (key883, 2), (key922, 2), (key939, 2), (key706, -2), (key860, -2), (key883, -2), (key922, 6), (key722, -2), (key922, -2), (key939, -2)]

def rawRow16729 : Integer.Sparse Key := [(key706, -2), (key702, -2), (key722, -2), (key706, 6), (key860, -2), (key856, -2), (key922, -2), (key706, 2), (key702, 2), (key883, 2), (key856, 2), (key939, 2), (key922, 2), (key706, -2), (key883, -2), (key860, -2), (key922, 6), (key722, -2), (key939, -2), (key922, -2)]

def rawRow16730 : Integer.Sparse Key := [(key702, -2), (key722, -2), (key706, -2), (key706, 6), (key856, -2), (key922, -2), (key860, -2), (key856, 2), (key922, 2), (key702, 2), (key939, 2), (key706, 2), (key883, 2), (key860, -2), (key706, -2), (key883, -2), (key922, 6), (key922, -2), (key722, -2), (key939, -2)]

def rawRow16731 : Integer.Sparse Key := [(key722, -2), (key702, -2), (key706, -2), (key706, 6), (key922, -2), (key856, -2), (key860, -2), (key922, 2), (key856, 2), (key939, 2), (key702, 2), (key883, 2), (key706, 2), (key860, -2), (key883, -2), (key706, -2), (key922, 6), (key922, -2), (key939, -2), (key722, -2)]

def rawRow16732 : Integer.Sparse Key := [(key706, -2), (key722, -2), (key702, -2), (key706, 6), (key860, -2), (key922, -2), (key856, -2), (key883, 2), (key939, 2), (key706, 2), (key922, 2), (key702, 2), (key856, 2), (key883, -2), (key706, -2), (key860, -2), (key922, 6), (key939, -2), (key722, -2), (key922, -2)]

def rawRow16733 : Integer.Sparse Key := [(key722, -2), (key706, -2), (key702, -2), (key706, 6), (key922, -2), (key860, -2), (key856, -2), (key939, 2), (key883, 2), (key922, 2), (key706, 2), (key856, 2), (key702, 2), (key883, -2), (key860, -2), (key706, -2), (key922, 6), (key939, -2), (key922, -2), (key722, -2)]

def rawRow16734 : Integer.Sparse Key := [(key856, -2), (key860, -2), (key922, -2), (key922, 6), (key702, -2), (key706, -2), (key722, -2), (key702, 2), (key706, 2), (key856, 2), (key883, 2), (key922, 2), (key939, 2), (key722, -2), (key922, -2), (key939, -2), (key706, 6), (key706, -2), (key860, -2), (key883, -2)]

def rawRow16735 : Integer.Sparse Key := [(key860, -2), (key856, -2), (key922, -2), (key922, 6), (key706, -2), (key702, -2), (key722, -2), (key706, 2), (key702, 2), (key883, 2), (key856, 2), (key939, 2), (key922, 2), (key722, -2), (key939, -2), (key922, -2), (key706, 6), (key706, -2), (key883, -2), (key860, -2)]

def rawRow16736 : Integer.Sparse Key := [(key856, -2), (key922, -2), (key860, -2), (key922, 6), (key702, -2), (key722, -2), (key706, -2), (key856, 2), (key922, 2), (key702, 2), (key939, 2), (key706, 2), (key883, 2), (key922, -2), (key722, -2), (key939, -2), (key706, 6), (key860, -2), (key706, -2), (key883, -2)]

def rawRow16737 : Integer.Sparse Key := [(key922, -2), (key856, -2), (key860, -2), (key922, 6), (key722, -2), (key702, -2), (key706, -2), (key922, 2), (key856, 2), (key939, 2), (key702, 2), (key883, 2), (key706, 2), (key922, -2), (key939, -2), (key722, -2), (key706, 6), (key860, -2), (key883, -2), (key706, -2)]

def rawRow16738 : Integer.Sparse Key := [(key860, -2), (key922, -2), (key856, -2), (key922, 6), (key706, -2), (key722, -2), (key702, -2), (key883, 2), (key939, 2), (key706, 2), (key922, 2), (key702, 2), (key856, 2), (key939, -2), (key722, -2), (key922, -2), (key706, 6), (key883, -2), (key706, -2), (key860, -2)]

def rawRow16739 : Integer.Sparse Key := [(key922, -2), (key860, -2), (key856, -2), (key922, 6), (key722, -2), (key706, -2), (key702, -2), (key939, 2), (key883, 2), (key922, 2), (key706, 2), (key856, 2), (key702, 2), (key939, -2), (key922, -2), (key722, -2), (key706, 6), (key883, -2), (key860, -2), (key706, -2)]

def rawRow16740 : Integer.Sparse Key := [(key856, -2), (key922, -2), (key922, -2), (key860, 6), (key856, -2), (key922, -2), (key922, -2), (key702, 2), (key722, 2), (key702, 2), (key939, 2), (key722, 2), (key939, 2), (key706, -2), (key706, -2), (key883, -2), (key860, 6), (key706, -2), (key706, -2), (key883, -2)]

def rawRow16741 : Integer.Sparse Key := [(key922, -2), (key856, -2), (key922, -2), (key860, 6), (key922, -2), (key856, -2), (key922, -2), (key722, 2), (key702, 2), (key939, 2), (key702, 2), (key939, 2), (key722, 2), (key706, -2), (key883, -2), (key706, -2), (key860, 6), (key706, -2), (key883, -2), (key706, -2)]

def rawRow16742 : Integer.Sparse Key := [(key922, -2), (key922, -2), (key856, -2), (key860, 6), (key922, -2), (key922, -2), (key856, -2), (key939, 2), (key939, 2), (key722, 2), (key722, 2), (key702, 2), (key702, 2), (key883, -2), (key706, -2), (key706, -2), (key860, 6), (key883, -2), (key706, -2), (key706, -2)]

def rawRow16743 : Integer.Sparse Key := [(key1986, -2), (key1990, -2), (key1990, -2), (key2007, 6), (key1986, -2), (key1990, -2), (key1990, -2), (key2231, 2), (key2235, 2), (key2231, 2), (key2256, 2), (key2235, 2), (key2256, 2), (key2300, -2), (key2300, -2), (key2313, -2), (key2007, 6), (key2300, -2), (key2300, -2), (key2313, -2)]

def rawRow16744 : Integer.Sparse Key := [(key1990, -2), (key1986, -2), (key1990, -2), (key2007, 6), (key1990, -2), (key1986, -2), (key1990, -2), (key2235, 2), (key2231, 2), (key2256, 2), (key2231, 2), (key2256, 2), (key2235, 2), (key2300, -2), (key2313, -2), (key2300, -2), (key2007, 6), (key2300, -2), (key2313, -2), (key2300, -2)]

def rawRow16745 : Integer.Sparse Key := [(key1990, -2), (key1990, -2), (key1986, -2), (key2007, 6), (key1990, -2), (key1990, -2), (key1986, -2), (key2256, 2), (key2256, 2), (key2235, 2), (key2235, 2), (key2231, 2), (key2231, 2), (key2313, -2), (key2300, -2), (key2300, -2), (key2007, 6), (key2313, -2), (key2300, -2), (key2300, -2)]

def rawRow16746 : Integer.Sparse Key := [(key1986, -2), (key1990, -2), (key2007, -2), (key1990, 6), (key2231, -2), (key2235, -2), (key2300, -2), (key1986, 2), (key1990, 2), (key2231, 2), (key2256, 2), (key2300, 2), (key2313, 2), (key1990, -2), (key2235, -2), (key2256, -2), (key2300, 6), (key2007, -2), (key2300, -2), (key2313, -2)]

def rawRow16747 : Integer.Sparse Key := [(key1990, -2), (key1986, -2), (key2007, -2), (key1990, 6), (key2235, -2), (key2231, -2), (key2300, -2), (key1990, 2), (key1986, 2), (key2256, 2), (key2231, 2), (key2313, 2), (key2300, 2), (key1990, -2), (key2256, -2), (key2235, -2), (key2300, 6), (key2007, -2), (key2313, -2), (key2300, -2)]

def rawRow16748 : Integer.Sparse Key := [(key1986, -2), (key2007, -2), (key1990, -2), (key1990, 6), (key2231, -2), (key2300, -2), (key2235, -2), (key2231, 2), (key2300, 2), (key1986, 2), (key2313, 2), (key1990, 2), (key2256, 2), (key2235, -2), (key1990, -2), (key2256, -2), (key2300, 6), (key2300, -2), (key2007, -2), (key2313, -2)]

def rawRow16749 : Integer.Sparse Key := [(key2007, -2), (key1986, -2), (key1990, -2), (key1990, 6), (key2300, -2), (key2231, -2), (key2235, -2), (key2300, 2), (key2231, 2), (key2313, 2), (key1986, 2), (key2256, 2), (key1990, 2), (key2235, -2), (key2256, -2), (key1990, -2), (key2300, 6), (key2300, -2), (key2313, -2), (key2007, -2)]

def rawRow16750 : Integer.Sparse Key := [(key1990, -2), (key2007, -2), (key1986, -2), (key1990, 6), (key2235, -2), (key2300, -2), (key2231, -2), (key2256, 2), (key2313, 2), (key1990, 2), (key2300, 2), (key1986, 2), (key2231, 2), (key2256, -2), (key1990, -2), (key2235, -2), (key2300, 6), (key2313, -2), (key2007, -2), (key2300, -2)]

def rawRow16751 : Integer.Sparse Key := [(key2007, -2), (key1990, -2), (key1986, -2), (key1990, 6), (key2300, -2), (key2235, -2), (key2231, -2), (key2313, 2), (key2256, 2), (key2300, 2), (key1990, 2), (key2231, 2), (key1986, 2), (key2256, -2), (key2235, -2), (key1990, -2), (key2300, 6), (key2313, -2), (key2300, -2), (key2007, -2)]

def rawRow16752 : Integer.Sparse Key := [(key2231, -2), (key2235, -2), (key2300, -2), (key2300, 6), (key1986, -2), (key1990, -2), (key2007, -2), (key1986, 2), (key1990, 2), (key2231, 2), (key2256, 2), (key2300, 2), (key2313, 2), (key2007, -2), (key2300, -2), (key2313, -2), (key1990, 6), (key1990, -2), (key2235, -2), (key2256, -2)]

def rawRow16753 : Integer.Sparse Key := [(key2235, -2), (key2231, -2), (key2300, -2), (key2300, 6), (key1990, -2), (key1986, -2), (key2007, -2), (key1990, 2), (key1986, 2), (key2256, 2), (key2231, 2), (key2313, 2), (key2300, 2), (key2007, -2), (key2313, -2), (key2300, -2), (key1990, 6), (key1990, -2), (key2256, -2), (key2235, -2)]

def rawRow16754 : Integer.Sparse Key := [(key2231, -2), (key2300, -2), (key2235, -2), (key2300, 6), (key1986, -2), (key2007, -2), (key1990, -2), (key2231, 2), (key2300, 2), (key1986, 2), (key2313, 2), (key1990, 2), (key2256, 2), (key2300, -2), (key2007, -2), (key2313, -2), (key1990, 6), (key2235, -2), (key1990, -2), (key2256, -2)]

def rawRow16755 : Integer.Sparse Key := [(key2300, -2), (key2231, -2), (key2235, -2), (key2300, 6), (key2007, -2), (key1986, -2), (key1990, -2), (key2300, 2), (key2231, 2), (key2313, 2), (key1986, 2), (key2256, 2), (key1990, 2), (key2300, -2), (key2313, -2), (key2007, -2), (key1990, 6), (key2235, -2), (key2256, -2), (key1990, -2)]

def rawRow16756 : Integer.Sparse Key := [(key2235, -2), (key2300, -2), (key2231, -2), (key2300, 6), (key1990, -2), (key2007, -2), (key1986, -2), (key2256, 2), (key2313, 2), (key1990, 2), (key2300, 2), (key1986, 2), (key2231, 2), (key2313, -2), (key2007, -2), (key2300, -2), (key1990, 6), (key2256, -2), (key1990, -2), (key2235, -2)]

def rawRow16757 : Integer.Sparse Key := [(key2300, -2), (key2235, -2), (key2231, -2), (key2300, 6), (key2007, -2), (key1990, -2), (key1986, -2), (key2313, 2), (key2256, 2), (key2300, 2), (key1990, 2), (key2231, 2), (key1986, 2), (key2313, -2), (key2300, -2), (key2007, -2), (key1990, 6), (key2256, -2), (key2235, -2), (key1990, -2)]

def rawRow16758 : Integer.Sparse Key := [(key2231, -2), (key2300, -2), (key2300, -2), (key2235, 6), (key2231, -2), (key2300, -2), (key2300, -2), (key1986, 2), (key2007, 2), (key1986, 2), (key2313, 2), (key2007, 2), (key2313, 2), (key1990, -2), (key1990, -2), (key2256, -2), (key2235, 6), (key1990, -2), (key1990, -2), (key2256, -2)]

def rawRow16759 : Integer.Sparse Key := [(key2300, -2), (key2231, -2), (key2300, -2), (key2235, 6), (key2300, -2), (key2231, -2), (key2300, -2), (key2007, 2), (key1986, 2), (key2313, 2), (key1986, 2), (key2313, 2), (key2007, 2), (key1990, -2), (key2256, -2), (key1990, -2), (key2235, 6), (key1990, -2), (key2256, -2), (key1990, -2)]

def rawRow16760 : Integer.Sparse Key := [(key2300, -2), (key2300, -2), (key2231, -2), (key2235, 6), (key2300, -2), (key2300, -2), (key2231, -2), (key2313, 2), (key2313, 2), (key2007, 2), (key2007, 2), (key1986, 2), (key1986, 2), (key2256, -2), (key1990, -2), (key1990, -2), (key2235, 6), (key2256, -2), (key1990, -2), (key1990, -2)]

def rawRow16761 : Integer.Sparse Key := [(key2029, 6), (key2059, -2), (key2059, -2), (key2067, -2), (key2029, 6), (key2148, -2), (key2148, -2), (key2164, -2), (key2059, -2), (key2059, -2), (key2067, -2), (key2148, -2), (key2148, -2), (key2164, -2), (key2241, 2), (key2244, 2), (key2241, 2), (key2251, 2), (key2244, 2), (key2251, 2)]

def rawRow16762 : Integer.Sparse Key := [(key2029, 6), (key2059, -2), (key2067, -2), (key2059, -2), (key2029, 6), (key2148, -2), (key2164, -2), (key2148, -2), (key2059, -2), (key2067, -2), (key2059, -2), (key2148, -2), (key2164, -2), (key2148, -2), (key2244, 2), (key2241, 2), (key2251, 2), (key2241, 2), (key2251, 2), (key2244, 2)]

def rawRow16763 : Integer.Sparse Key := [(key2029, 6), (key2067, -2), (key2059, -2), (key2059, -2), (key2029, 6), (key2164, -2), (key2148, -2), (key2148, -2), (key2067, -2), (key2059, -2), (key2059, -2), (key2164, -2), (key2148, -2), (key2148, -2), (key2251, 2), (key2251, 2), (key2244, 2), (key2244, 2), (key2241, 2), (key2241, 2)]

def rawRow16764 : Integer.Sparse Key := [(key2059, 6), (key2029, -2), (key2059, -2), (key2067, -2), (key2148, 6), (key2029, -2), (key2148, -2), (key2164, -2), (key2148, -2), (key2241, -2), (key2244, -2), (key2059, -2), (key2241, -2), (key2251, -2), (key2059, 2), (key2067, 2), (key2148, 2), (key2164, 2), (key2244, 2), (key2251, 2)]

def rawRow16765 : Integer.Sparse Key := [(key2059, 6), (key2029, -2), (key2067, -2), (key2059, -2), (key2148, 6), (key2029, -2), (key2164, -2), (key2148, -2), (key2148, -2), (key2244, -2), (key2241, -2), (key2059, -2), (key2251, -2), (key2241, -2), (key2067, 2), (key2059, 2), (key2164, 2), (key2148, 2), (key2251, 2), (key2244, 2)]

def rawRow16766 : Integer.Sparse Key := [(key2059, 6), (key2059, -2), (key2029, -2), (key2067, -2), (key2148, 6), (key2148, -2), (key2029, -2), (key2164, -2), (key2241, -2), (key2148, -2), (key2244, -2), (key2241, -2), (key2059, -2), (key2251, -2), (key2148, 2), (key2244, 2), (key2059, 2), (key2251, 2), (key2067, 2), (key2164, 2)]

def rawRow16767 : Integer.Sparse Key := [(key2059, 6), (key2059, -2), (key2067, -2), (key2029, -2), (key2148, 6), (key2148, -2), (key2164, -2), (key2029, -2), (key2241, -2), (key2244, -2), (key2148, -2), (key2241, -2), (key2251, -2), (key2059, -2), (key2244, 2), (key2148, 2), (key2251, 2), (key2059, 2), (key2164, 2), (key2067, 2)]

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

def rawRow16768 : Integer.Sparse Key := [(key2059, 6), (key2067, -2), (key2029, -2), (key2059, -2), (key2148, 6), (key2164, -2), (key2029, -2), (key2148, -2), (key2244, -2), (key2148, -2), (key2241, -2), (key2251, -2), (key2059, -2), (key2241, -2), (key2164, 2), (key2251, 2), (key2067, 2), (key2244, 2), (key2059, 2), (key2148, 2)]

def rawRow16769 : Integer.Sparse Key := [(key2059, 6), (key2067, -2), (key2059, -2), (key2029, -2), (key2148, 6), (key2164, -2), (key2148, -2), (key2029, -2), (key2244, -2), (key2241, -2), (key2148, -2), (key2251, -2), (key2241, -2), (key2059, -2), (key2251, 2), (key2164, 2), (key2244, 2), (key2067, 2), (key2148, 2), (key2059, 2)]

def rawRow16770 : Integer.Sparse Key := [(key2148, 6), (key2148, -2), (key2241, -2), (key2244, -2), (key2059, 6), (key2059, -2), (key2241, -2), (key2251, -2), (key2029, -2), (key2059, -2), (key2067, -2), (key2029, -2), (key2148, -2), (key2164, -2), (key2059, 2), (key2067, 2), (key2148, 2), (key2164, 2), (key2244, 2), (key2251, 2)]

def rawRow16771 : Integer.Sparse Key := [(key2148, 6), (key2148, -2), (key2244, -2), (key2241, -2), (key2059, 6), (key2059, -2), (key2251, -2), (key2241, -2), (key2029, -2), (key2067, -2), (key2059, -2), (key2029, -2), (key2164, -2), (key2148, -2), (key2067, 2), (key2059, 2), (key2164, 2), (key2148, 2), (key2251, 2), (key2244, 2)]

def rawRow16772 : Integer.Sparse Key := [(key2148, 6), (key2241, -2), (key2148, -2), (key2244, -2), (key2059, 6), (key2241, -2), (key2059, -2), (key2251, -2), (key2059, -2), (key2029, -2), (key2067, -2), (key2148, -2), (key2029, -2), (key2164, -2), (key2148, 2), (key2244, 2), (key2059, 2), (key2251, 2), (key2067, 2), (key2164, 2)]

def rawRow16773 : Integer.Sparse Key := [(key2148, 6), (key2241, -2), (key2244, -2), (key2148, -2), (key2059, 6), (key2241, -2), (key2251, -2), (key2059, -2), (key2059, -2), (key2067, -2), (key2029, -2), (key2148, -2), (key2164, -2), (key2029, -2), (key2244, 2), (key2148, 2), (key2251, 2), (key2059, 2), (key2164, 2), (key2067, 2)]

def rawRow16774 : Integer.Sparse Key := [(key2148, 6), (key2244, -2), (key2148, -2), (key2241, -2), (key2059, 6), (key2251, -2), (key2059, -2), (key2241, -2), (key2067, -2), (key2029, -2), (key2059, -2), (key2164, -2), (key2029, -2), (key2148, -2), (key2164, 2), (key2251, 2), (key2067, 2), (key2244, 2), (key2059, 2), (key2148, 2)]

def rawRow16775 : Integer.Sparse Key := [(key2148, 6), (key2244, -2), (key2241, -2), (key2148, -2), (key2059, 6), (key2251, -2), (key2241, -2), (key2059, -2), (key2067, -2), (key2059, -2), (key2029, -2), (key2164, -2), (key2148, -2), (key2029, -2), (key2251, 2), (key2164, 2), (key2244, 2), (key2067, 2), (key2148, 2), (key2059, 2)]

def rawRow16776 : Integer.Sparse Key := [(key2241, 6), (key2148, -2), (key2148, -2), (key2244, -2), (key2241, 6), (key2059, -2), (key2059, -2), (key2251, -2), (key2148, -2), (key2148, -2), (key2244, -2), (key2059, -2), (key2059, -2), (key2251, -2), (key2029, 2), (key2067, 2), (key2029, 2), (key2164, 2), (key2067, 2), (key2164, 2)]

def rawRow16777 : Integer.Sparse Key := [(key2241, 6), (key2148, -2), (key2244, -2), (key2148, -2), (key2241, 6), (key2059, -2), (key2251, -2), (key2059, -2), (key2148, -2), (key2244, -2), (key2148, -2), (key2059, -2), (key2251, -2), (key2059, -2), (key2067, 2), (key2029, 2), (key2164, 2), (key2029, 2), (key2164, 2), (key2067, 2)]

def rawRow16778 : Integer.Sparse Key := [(key2241, 6), (key2244, -2), (key2148, -2), (key2148, -2), (key2241, 6), (key2251, -2), (key2059, -2), (key2059, -2), (key2244, -2), (key2148, -2), (key2148, -2), (key2251, -2), (key2059, -2), (key2059, -2), (key2164, 2), (key2164, 2), (key2067, 2), (key2067, 2), (key2029, 2), (key2029, 2)]

def rawRow16779 : Integer.Sparse Key := [(key703, -2), (key706, -2), (key706, -2), (key715, 6), (key703, -2), (key706, -2), (key706, -2), (key857, 2), (key860, 2), (key857, 2), (key883, 2), (key860, 2), (key883, 2), (key892, -2), (key892, -2), (key914, -2), (key715, 6), (key892, -2), (key892, -2), (key914, -2)]

def rawRow16780 : Integer.Sparse Key := [(key706, -2), (key703, -2), (key706, -2), (key715, 6), (key706, -2), (key703, -2), (key706, -2), (key860, 2), (key857, 2), (key883, 2), (key857, 2), (key883, 2), (key860, 2), (key892, -2), (key914, -2), (key892, -2), (key715, 6), (key892, -2), (key914, -2), (key892, -2)]

def rawRow16781 : Integer.Sparse Key := [(key706, -2), (key706, -2), (key703, -2), (key715, 6), (key706, -2), (key706, -2), (key703, -2), (key883, 2), (key883, 2), (key860, 2), (key860, 2), (key857, 2), (key857, 2), (key914, -2), (key892, -2), (key892, -2), (key715, 6), (key914, -2), (key892, -2), (key892, -2)]

def rawRow16782 : Integer.Sparse Key := [(key703, -2), (key706, -2), (key715, -2), (key706, 6), (key857, -2), (key860, -2), (key892, -2), (key703, 2), (key706, 2), (key857, 2), (key883, 2), (key892, 2), (key914, 2), (key706, -2), (key860, -2), (key883, -2), (key892, 6), (key715, -2), (key892, -2), (key914, -2)]

def rawRow16783 : Integer.Sparse Key := [(key706, -2), (key703, -2), (key715, -2), (key706, 6), (key860, -2), (key857, -2), (key892, -2), (key706, 2), (key703, 2), (key883, 2), (key857, 2), (key914, 2), (key892, 2), (key706, -2), (key883, -2), (key860, -2), (key892, 6), (key715, -2), (key914, -2), (key892, -2)]

def rawRow16784 : Integer.Sparse Key := [(key703, -2), (key715, -2), (key706, -2), (key706, 6), (key857, -2), (key892, -2), (key860, -2), (key857, 2), (key892, 2), (key703, 2), (key914, 2), (key706, 2), (key883, 2), (key860, -2), (key706, -2), (key883, -2), (key892, 6), (key892, -2), (key715, -2), (key914, -2)]

def rawRow16785 : Integer.Sparse Key := [(key715, -2), (key703, -2), (key706, -2), (key706, 6), (key892, -2), (key857, -2), (key860, -2), (key892, 2), (key857, 2), (key914, 2), (key703, 2), (key883, 2), (key706, 2), (key860, -2), (key883, -2), (key706, -2), (key892, 6), (key892, -2), (key914, -2), (key715, -2)]

def rawRow16786 : Integer.Sparse Key := [(key706, -2), (key715, -2), (key703, -2), (key706, 6), (key860, -2), (key892, -2), (key857, -2), (key883, 2), (key914, 2), (key706, 2), (key892, 2), (key703, 2), (key857, 2), (key883, -2), (key706, -2), (key860, -2), (key892, 6), (key914, -2), (key715, -2), (key892, -2)]

def rawRow16787 : Integer.Sparse Key := [(key715, -2), (key706, -2), (key703, -2), (key706, 6), (key892, -2), (key860, -2), (key857, -2), (key914, 2), (key883, 2), (key892, 2), (key706, 2), (key857, 2), (key703, 2), (key883, -2), (key860, -2), (key706, -2), (key892, 6), (key914, -2), (key892, -2), (key715, -2)]

def rawRow16788 : Integer.Sparse Key := [(key857, -2), (key860, -2), (key892, -2), (key892, 6), (key703, -2), (key706, -2), (key715, -2), (key703, 2), (key706, 2), (key857, 2), (key883, 2), (key892, 2), (key914, 2), (key715, -2), (key892, -2), (key914, -2), (key706, 6), (key706, -2), (key860, -2), (key883, -2)]

def rawRow16789 : Integer.Sparse Key := [(key860, -2), (key857, -2), (key892, -2), (key892, 6), (key706, -2), (key703, -2), (key715, -2), (key706, 2), (key703, 2), (key883, 2), (key857, 2), (key914, 2), (key892, 2), (key715, -2), (key914, -2), (key892, -2), (key706, 6), (key706, -2), (key883, -2), (key860, -2)]

def rawRow16790 : Integer.Sparse Key := [(key857, -2), (key892, -2), (key860, -2), (key892, 6), (key703, -2), (key715, -2), (key706, -2), (key857, 2), (key892, 2), (key703, 2), (key914, 2), (key706, 2), (key883, 2), (key892, -2), (key715, -2), (key914, -2), (key706, 6), (key860, -2), (key706, -2), (key883, -2)]

def rawRow16791 : Integer.Sparse Key := [(key892, -2), (key857, -2), (key860, -2), (key892, 6), (key715, -2), (key703, -2), (key706, -2), (key892, 2), (key857, 2), (key914, 2), (key703, 2), (key883, 2), (key706, 2), (key892, -2), (key914, -2), (key715, -2), (key706, 6), (key860, -2), (key883, -2), (key706, -2)]

def rawRow16792 : Integer.Sparse Key := [(key860, -2), (key892, -2), (key857, -2), (key892, 6), (key706, -2), (key715, -2), (key703, -2), (key883, 2), (key914, 2), (key706, 2), (key892, 2), (key703, 2), (key857, 2), (key914, -2), (key715, -2), (key892, -2), (key706, 6), (key883, -2), (key706, -2), (key860, -2)]

def rawRow16793 : Integer.Sparse Key := [(key892, -2), (key860, -2), (key857, -2), (key892, 6), (key715, -2), (key706, -2), (key703, -2), (key914, 2), (key883, 2), (key892, 2), (key706, 2), (key857, 2), (key703, 2), (key914, -2), (key892, -2), (key715, -2), (key706, 6), (key883, -2), (key860, -2), (key706, -2)]

def rawRow16794 : Integer.Sparse Key := [(key857, -2), (key892, -2), (key892, -2), (key860, 6), (key857, -2), (key892, -2), (key892, -2), (key703, 2), (key715, 2), (key703, 2), (key914, 2), (key715, 2), (key914, 2), (key706, -2), (key706, -2), (key883, -2), (key860, 6), (key706, -2), (key706, -2), (key883, -2)]

def rawRow16795 : Integer.Sparse Key := [(key892, -2), (key857, -2), (key892, -2), (key860, 6), (key892, -2), (key857, -2), (key892, -2), (key715, 2), (key703, 2), (key914, 2), (key703, 2), (key914, 2), (key715, 2), (key706, -2), (key883, -2), (key706, -2), (key860, 6), (key706, -2), (key883, -2), (key706, -2)]

def rawRow16796 : Integer.Sparse Key := [(key892, -2), (key892, -2), (key857, -2), (key860, 6), (key892, -2), (key892, -2), (key857, -2), (key914, 2), (key914, 2), (key715, 2), (key715, 2), (key703, 2), (key703, 2), (key883, -2), (key706, -2), (key706, -2), (key860, 6), (key883, -2), (key706, -2), (key706, -2)]

def rawRow16797 : Integer.Sparse Key := [(key859, 4), (key859, 4), (key886, 4), (key891, -2), (key895, -2), (key891, -2), (key916, -2), (key895, -2), (key916, -2), (key891, -2), (key895, -2), (key891, -2), (key916, -2), (key895, -2), (key916, -2), (key948, 4), (key948, 4), (key955, 4)]

def rawRow16798 : Integer.Sparse Key := [(key859, 4), (key886, 4), (key859, 4), (key895, -2), (key891, -2), (key916, -2), (key891, -2), (key916, -2), (key895, -2), (key895, -2), (key891, -2), (key916, -2), (key891, -2), (key916, -2), (key895, -2), (key948, 4), (key955, 4), (key948, 4)]

def rawRow16799 : Integer.Sparse Key := [(key886, 4), (key859, 4), (key859, 4), (key916, -2), (key916, -2), (key895, -2), (key895, -2), (key891, -2), (key891, -2), (key916, -2), (key916, -2), (key895, -2), (key895, -2), (key891, -2), (key891, -2), (key955, 4), (key948, 4), (key948, 4)]

def rawRow16800 : Integer.Sparse Key := [(key705, 4), (key891, 4), (key916, 4), (key705, -2), (key710, -2), (key859, -2), (key886, -2), (key895, -2), (key916, -2), (key714, -2), (key718, -2), (key891, -2), (key916, -2), (key948, -2), (key955, -2), (key718, 4), (key895, 4), (key916, 4)]

def rawRow16801 : Integer.Sparse Key := [(key705, 4), (key916, 4), (key891, 4), (key710, -2), (key705, -2), (key886, -2), (key859, -2), (key916, -2), (key895, -2), (key718, -2), (key714, -2), (key916, -2), (key891, -2), (key955, -2), (key948, -2), (key718, 4), (key916, 4), (key895, 4)]

def rawRow16802 : Integer.Sparse Key := [(key891, 4), (key705, 4), (key916, 4), (key859, -2), (key895, -2), (key705, -2), (key916, -2), (key710, -2), (key886, -2), (key891, -2), (key948, -2), (key714, -2), (key955, -2), (key718, -2), (key916, -2), (key895, 4), (key718, 4), (key916, 4)]

def rawRow16803 : Integer.Sparse Key := [(key891, 4), (key916, 4), (key705, 4), (key895, -2), (key859, -2), (key916, -2), (key705, -2), (key886, -2), (key710, -2), (key948, -2), (key891, -2), (key955, -2), (key714, -2), (key916, -2), (key718, -2), (key895, 4), (key916, 4), (key718, 4)]

def rawRow16804 : Integer.Sparse Key := [(key916, 4), (key705, 4), (key891, 4), (key886, -2), (key916, -2), (key710, -2), (key895, -2), (key705, -2), (key859, -2), (key916, -2), (key955, -2), (key718, -2), (key948, -2), (key714, -2), (key891, -2), (key916, 4), (key718, 4), (key895, 4)]

def rawRow16805 : Integer.Sparse Key := [(key916, 4), (key891, 4), (key705, 4), (key916, -2), (key886, -2), (key895, -2), (key710, -2), (key859, -2), (key705, -2), (key955, -2), (key916, -2), (key948, -2), (key718, -2), (key891, -2), (key714, -2), (key916, 4), (key895, 4), (key718, 4)]

def rawRow16806 : Integer.Sparse Key := [(key705, 4), (key891, 4), (key916, 4), (key714, -2), (key718, -2), (key891, -2), (key916, -2), (key948, -2), (key955, -2), (key705, -2), (key710, -2), (key859, -2), (key886, -2), (key895, -2), (key916, -2), (key718, 4), (key895, 4), (key916, 4)]

def rawRow16807 : Integer.Sparse Key := [(key705, 4), (key916, 4), (key891, 4), (key718, -2), (key714, -2), (key916, -2), (key891, -2), (key955, -2), (key948, -2), (key710, -2), (key705, -2), (key886, -2), (key859, -2), (key916, -2), (key895, -2), (key718, 4), (key916, 4), (key895, 4)]

def rawRow16808 : Integer.Sparse Key := [(key891, 4), (key705, 4), (key916, 4), (key891, -2), (key948, -2), (key714, -2), (key955, -2), (key718, -2), (key916, -2), (key859, -2), (key895, -2), (key705, -2), (key916, -2), (key710, -2), (key886, -2), (key895, 4), (key718, 4), (key916, 4)]

def rawRow16809 : Integer.Sparse Key := [(key891, 4), (key916, 4), (key705, 4), (key948, -2), (key891, -2), (key955, -2), (key714, -2), (key916, -2), (key718, -2), (key895, -2), (key859, -2), (key916, -2), (key705, -2), (key886, -2), (key710, -2), (key895, 4), (key916, 4), (key718, 4)]

def rawRow16810 : Integer.Sparse Key := [(key916, 4), (key705, 4), (key891, 4), (key916, -2), (key955, -2), (key718, -2), (key948, -2), (key714, -2), (key891, -2), (key886, -2), (key916, -2), (key710, -2), (key895, -2), (key705, -2), (key859, -2), (key916, 4), (key718, 4), (key895, 4)]

def rawRow16811 : Integer.Sparse Key := [(key916, 4), (key891, 4), (key705, 4), (key955, -2), (key916, -2), (key948, -2), (key718, -2), (key891, -2), (key714, -2), (key916, -2), (key886, -2), (key895, -2), (key710, -2), (key859, -2), (key705, -2), (key916, 4), (key895, 4), (key718, 4)]

def rawRow16812 : Integer.Sparse Key := [(key714, 4), (key714, 4), (key955, 4), (key705, -2), (key718, -2), (key705, -2), (key916, -2), (key718, -2), (key916, -2), (key705, -2), (key718, -2), (key705, -2), (key916, -2), (key718, -2), (key916, -2), (key710, 4), (key710, 4), (key886, 4)]

def rawRow16813 : Integer.Sparse Key := [(key714, 4), (key955, 4), (key714, 4), (key718, -2), (key705, -2), (key916, -2), (key705, -2), (key916, -2), (key718, -2), (key718, -2), (key705, -2), (key916, -2), (key705, -2), (key916, -2), (key718, -2), (key710, 4), (key886, 4), (key710, 4)]

def rawRow16814 : Integer.Sparse Key := [(key955, 4), (key714, 4), (key714, 4), (key916, -2), (key916, -2), (key718, -2), (key718, -2), (key705, -2), (key705, -2), (key916, -2), (key916, -2), (key718, -2), (key718, -2), (key705, -2), (key705, -2), (key886, 4), (key710, 4), (key710, 4)]

def rawRow16815 : Integer.Sparse Key := [(key2146, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2194, 2), (key2194, 2), (key2200, 2), (key2146, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2239, 2), (key2246, 2), (key2239, 2), (key2253, 2), (key2246, 2), (key2253, 2), (key2303, -1), (key2305, -1), (key2303, -1), (key2310, -1), (key2305, -1), (key2310, -1), (key2194, 2), (key2194, 2), (key2200, 2), (key2303, -1), (key2305, -1), (key2303, -1), (key2310, -1), (key2305, -1), (key2310, -1)]

def rawRow16816 : Integer.Sparse Key := [(key2152, -1), (key2146, -1), (key2166, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2194, 2), (key2200, 2), (key2194, 2), (key2152, -1), (key2146, -1), (key2166, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2246, 2), (key2239, 2), (key2253, 2), (key2239, 2), (key2253, 2), (key2246, 2), (key2305, -1), (key2303, -1), (key2310, -1), (key2303, -1), (key2310, -1), (key2305, -1), (key2194, 2), (key2200, 2), (key2194, 2), (key2305, -1), (key2303, -1), (key2310, -1), (key2303, -1), (key2310, -1), (key2305, -1)]

def rawRow16817 : Integer.Sparse Key := [(key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2146, -1), (key2146, -1), (key2200, 2), (key2194, 2), (key2194, 2), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2146, -1), (key2146, -1), (key2253, 2), (key2253, 2), (key2246, 2), (key2246, 2), (key2239, 2), (key2239, 2), (key2310, -1), (key2310, -1), (key2305, -1), (key2305, -1), (key2303, -1), (key2303, -1), (key2200, 2), (key2194, 2), (key2194, 2), (key2310, -1), (key2310, -1), (key2305, -1), (key2305, -1), (key2303, -1), (key2303, -1)]

def rawRow16818 : Integer.Sparse Key := [(key2027, -1), (key2033, -1), (key2146, -1), (key2166, -1), (key2194, -1), (key2200, -1), (key2033, 2), (key2152, 2), (key2166, 2), (key2057, -1), (key2063, -1), (key2239, -1), (key2253, -1), (key2303, -1), (key2310, -1), (key2057, 2), (key2069, 2), (key2146, 2), (key2166, 2), (key2305, 2), (key2310, 2), (key2063, -1), (key2069, -1), (key2152, -1), (key2166, -1), (key2246, -1), (key2253, -1), (key2092, 2), (key2303, 2), (key2310, 2), (key2092, -1), (key2095, -1), (key2194, -1), (key2200, -1), (key2305, -1), (key2310, -1)]

def rawRow16819 : Integer.Sparse Key := [(key2033, -1), (key2027, -1), (key2166, -1), (key2146, -1), (key2200, -1), (key2194, -1), (key2033, 2), (key2166, 2), (key2152, 2), (key2063, -1), (key2057, -1), (key2253, -1), (key2239, -1), (key2310, -1), (key2303, -1), (key2069, 2), (key2057, 2), (key2166, 2), (key2146, 2), (key2310, 2), (key2305, 2), (key2069, -1), (key2063, -1), (key2166, -1), (key2152, -1), (key2253, -1), (key2246, -1), (key2092, 2), (key2310, 2), (key2303, 2), (key2095, -1), (key2092, -1), (key2200, -1), (key2194, -1), (key2310, -1), (key2305, -1)]

def rawRow16820 : Integer.Sparse Key := [(key2146, -1), (key2194, -1), (key2027, -1), (key2200, -1), (key2033, -1), (key2166, -1), (key2152, 2), (key2033, 2), (key2166, 2), (key2239, -1), (key2303, -1), (key2057, -1), (key2310, -1), (key2063, -1), (key2253, -1), (key2146, 2), (key2305, 2), (key2057, 2), (key2310, 2), (key2069, 2), (key2166, 2), (key2152, -1), (key2246, -1), (key2063, -1), (key2253, -1), (key2069, -1), (key2166, -1), (key2303, 2), (key2092, 2), (key2310, 2), (key2194, -1), (key2305, -1), (key2092, -1), (key2310, -1), (key2095, -1), (key2200, -1)]

def rawRow16821 : Integer.Sparse Key := [(key2194, -1), (key2146, -1), (key2200, -1), (key2027, -1), (key2166, -1), (key2033, -1), (key2152, 2), (key2166, 2), (key2033, 2), (key2303, -1), (key2239, -1), (key2310, -1), (key2057, -1), (key2253, -1), (key2063, -1), (key2305, 2), (key2146, 2), (key2310, 2), (key2057, 2), (key2166, 2), (key2069, 2), (key2246, -1), (key2152, -1), (key2253, -1), (key2063, -1), (key2166, -1), (key2069, -1), (key2303, 2), (key2310, 2), (key2092, 2), (key2305, -1), (key2194, -1), (key2310, -1), (key2092, -1), (key2200, -1), (key2095, -1)]

def rawRow16822 : Integer.Sparse Key := [(key2166, -1), (key2200, -1), (key2033, -1), (key2194, -1), (key2027, -1), (key2146, -1), (key2166, 2), (key2033, 2), (key2152, 2), (key2253, -1), (key2310, -1), (key2063, -1), (key2303, -1), (key2057, -1), (key2239, -1), (key2166, 2), (key2310, 2), (key2069, 2), (key2305, 2), (key2057, 2), (key2146, 2), (key2166, -1), (key2253, -1), (key2069, -1), (key2246, -1), (key2063, -1), (key2152, -1), (key2310, 2), (key2092, 2), (key2303, 2), (key2200, -1), (key2310, -1), (key2095, -1), (key2305, -1), (key2092, -1), (key2194, -1)]

def rawRow16823 : Integer.Sparse Key := [(key2200, -1), (key2166, -1), (key2194, -1), (key2033, -1), (key2146, -1), (key2027, -1), (key2166, 2), (key2152, 2), (key2033, 2), (key2310, -1), (key2253, -1), (key2303, -1), (key2063, -1), (key2239, -1), (key2057, -1), (key2310, 2), (key2166, 2), (key2305, 2), (key2069, 2), (key2146, 2), (key2057, 2), (key2253, -1), (key2166, -1), (key2246, -1), (key2069, -1), (key2152, -1), (key2063, -1), (key2310, 2), (key2303, 2), (key2092, 2), (key2310, -1), (key2200, -1), (key2305, -1), (key2095, -1), (key2194, -1), (key2092, -1)]

def rawRow16824 : Integer.Sparse Key := [(key2057, -1), (key2063, -1), (key2239, -1), (key2253, -1), (key2303, -1), (key2310, -1), (key2092, 2), (key2303, 2), (key2310, 2), (key2027, -1), (key2033, -1), (key2146, -1), (key2166, -1), (key2194, -1), (key2200, -1), (key2057, 2), (key2069, 2), (key2146, 2), (key2166, 2), (key2305, 2), (key2310, 2), (key2092, -1), (key2095, -1), (key2194, -1), (key2200, -1), (key2305, -1), (key2310, -1), (key2033, 2), (key2152, 2), (key2166, 2), (key2063, -1), (key2069, -1), (key2152, -1), (key2166, -1), (key2246, -1), (key2253, -1)]

def rawRow16825 : Integer.Sparse Key := [(key2063, -1), (key2057, -1), (key2253, -1), (key2239, -1), (key2310, -1), (key2303, -1), (key2092, 2), (key2310, 2), (key2303, 2), (key2033, -1), (key2027, -1), (key2166, -1), (key2146, -1), (key2200, -1), (key2194, -1), (key2069, 2), (key2057, 2), (key2166, 2), (key2146, 2), (key2310, 2), (key2305, 2), (key2095, -1), (key2092, -1), (key2200, -1), (key2194, -1), (key2310, -1), (key2305, -1), (key2033, 2), (key2166, 2), (key2152, 2), (key2069, -1), (key2063, -1), (key2166, -1), (key2152, -1), (key2253, -1), (key2246, -1)]

def rawRow16826 : Integer.Sparse Key := [(key2239, -1), (key2303, -1), (key2057, -1), (key2310, -1), (key2063, -1), (key2253, -1), (key2303, 2), (key2092, 2), (key2310, 2), (key2146, -1), (key2194, -1), (key2027, -1), (key2200, -1), (key2033, -1), (key2166, -1), (key2146, 2), (key2305, 2), (key2057, 2), (key2310, 2), (key2069, 2), (key2166, 2), (key2194, -1), (key2305, -1), (key2092, -1), (key2310, -1), (key2095, -1), (key2200, -1), (key2152, 2), (key2033, 2), (key2166, 2), (key2152, -1), (key2246, -1), (key2063, -1), (key2253, -1), (key2069, -1), (key2166, -1)]

def rawRow16827 : Integer.Sparse Key := [(key2303, -1), (key2239, -1), (key2310, -1), (key2057, -1), (key2253, -1), (key2063, -1), (key2303, 2), (key2310, 2), (key2092, 2), (key2194, -1), (key2146, -1), (key2200, -1), (key2027, -1), (key2166, -1), (key2033, -1), (key2305, 2), (key2146, 2), (key2310, 2), (key2057, 2), (key2166, 2), (key2069, 2), (key2305, -1), (key2194, -1), (key2310, -1), (key2092, -1), (key2200, -1), (key2095, -1), (key2152, 2), (key2166, 2), (key2033, 2), (key2246, -1), (key2152, -1), (key2253, -1), (key2063, -1), (key2166, -1), (key2069, -1)]

def rawRow16828 : Integer.Sparse Key := [(key2253, -1), (key2310, -1), (key2063, -1), (key2303, -1), (key2057, -1), (key2239, -1), (key2310, 2), (key2092, 2), (key2303, 2), (key2166, -1), (key2200, -1), (key2033, -1), (key2194, -1), (key2027, -1), (key2146, -1), (key2166, 2), (key2310, 2), (key2069, 2), (key2305, 2), (key2057, 2), (key2146, 2), (key2200, -1), (key2310, -1), (key2095, -1), (key2305, -1), (key2092, -1), (key2194, -1), (key2166, 2), (key2033, 2), (key2152, 2), (key2166, -1), (key2253, -1), (key2069, -1), (key2246, -1), (key2063, -1), (key2152, -1)]

def rawRow16829 : Integer.Sparse Key := [(key2310, -1), (key2253, -1), (key2303, -1), (key2063, -1), (key2239, -1), (key2057, -1), (key2310, 2), (key2303, 2), (key2092, 2), (key2200, -1), (key2166, -1), (key2194, -1), (key2033, -1), (key2146, -1), (key2027, -1), (key2310, 2), (key2166, 2), (key2305, 2), (key2069, 2), (key2146, 2), (key2057, 2), (key2310, -1), (key2200, -1), (key2305, -1), (key2095, -1), (key2194, -1), (key2092, -1), (key2166, 2), (key2152, 2), (key2033, 2), (key2253, -1), (key2166, -1), (key2246, -1), (key2069, -1), (key2152, -1), (key2063, -1)]

def rawRow16830 : Integer.Sparse Key := [(key2057, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2310, -1), (key2063, 2), (key2063, 2), (key2253, 2), (key2057, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2310, -1), (key2027, 2), (key2095, 2), (key2027, 2), (key2200, 2), (key2095, 2), (key2200, 2), (key2033, -1), (key2069, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2166, -1), (key2063, 2), (key2063, 2), (key2253, 2), (key2033, -1), (key2069, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2166, -1)]

def rawRow16831 : Integer.Sparse Key := [(key2092, -1), (key2057, -1), (key2310, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2063, 2), (key2253, 2), (key2063, 2), (key2092, -1), (key2057, -1), (key2310, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2095, 2), (key2027, 2), (key2200, 2), (key2027, 2), (key2200, 2), (key2095, 2), (key2069, -1), (key2033, -1), (key2166, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2063, 2), (key2253, 2), (key2063, 2), (key2069, -1), (key2033, -1), (key2166, -1), (key2033, -1), (key2166, -1), (key2069, -1)]

def rawRow16832 : Integer.Sparse Key := [(key2310, -1), (key2310, -1), (key2092, -1), (key2092, -1), (key2057, -1), (key2057, -1), (key2253, 2), (key2063, 2), (key2063, 2), (key2310, -1), (key2310, -1), (key2092, -1), (key2092, -1), (key2057, -1), (key2057, -1), (key2200, 2), (key2200, 2), (key2095, 2), (key2095, 2), (key2027, 2), (key2027, 2), (key2166, -1), (key2166, -1), (key2069, -1), (key2069, -1), (key2033, -1), (key2033, -1), (key2253, 2), (key2063, 2), (key2063, 2), (key2166, -1), (key2166, -1), (key2069, -1), (key2069, -1), (key2033, -1), (key2033, -1)]

def rawRow16833 : Integer.Sparse Key := [(key2115, 4), (key2115, 4), (key2120, 4), (key2157, -4), (key2160, -4), (key2160, -4), (key2157, -4), (key2160, -4), (key2160, -4), (key2249, 12)]

def rawRow16834 : Integer.Sparse Key := [(key2115, 4), (key2120, 4), (key2115, 4), (key2160, -4), (key2157, -4), (key2160, -4), (key2160, -4), (key2157, -4), (key2160, -4), (key2249, 12)]

def rawRow16835 : Integer.Sparse Key := [(key2120, 4), (key2115, 4), (key2115, 4), (key2160, -4), (key2160, -4), (key2157, -4), (key2160, -4), (key2160, -4), (key2157, -4), (key2249, 12)]

def rawRow16836 : Integer.Sparse Key := [(key2115, 4), (key2157, 4), (key2160, 4), (key2115, -4), (key2120, -4), (key2160, -4), (key2157, -4), (key2160, -4), (key2249, -4), (key2160, 12)]

def rawRow16837 : Integer.Sparse Key := [(key2115, 4), (key2160, 4), (key2157, 4), (key2120, -4), (key2115, -4), (key2160, -4), (key2160, -4), (key2157, -4), (key2249, -4), (key2160, 12)]

def rawRow16838 : Integer.Sparse Key := [(key2157, 4), (key2115, 4), (key2160, 4), (key2115, -4), (key2160, -4), (key2120, -4), (key2157, -4), (key2249, -4), (key2160, -4), (key2160, 12)]

def rawRow16839 : Integer.Sparse Key := [(key2157, 4), (key2160, 4), (key2115, 4), (key2160, -4), (key2115, -4), (key2120, -4), (key2249, -4), (key2157, -4), (key2160, -4), (key2160, 12)]

def rawRow16840 : Integer.Sparse Key := [(key2160, 4), (key2115, 4), (key2157, 4), (key2120, -4), (key2160, -4), (key2115, -4), (key2160, -4), (key2249, -4), (key2157, -4), (key2160, 12)]

def rawRow16841 : Integer.Sparse Key := [(key2160, 4), (key2157, 4), (key2115, 4), (key2160, -4), (key2120, -4), (key2115, -4), (key2249, -4), (key2160, -4), (key2157, -4), (key2160, 12)]

def rawRow16842 : Integer.Sparse Key := [(key2115, 4), (key2157, 4), (key2160, 4), (key2157, -4), (key2160, -4), (key2249, -4), (key2115, -4), (key2120, -4), (key2160, -4), (key2160, 12)]

def rawRow16843 : Integer.Sparse Key := [(key2115, 4), (key2160, 4), (key2157, 4), (key2160, -4), (key2157, -4), (key2249, -4), (key2120, -4), (key2115, -4), (key2160, -4), (key2160, 12)]

def rawRow16844 : Integer.Sparse Key := [(key2157, 4), (key2115, 4), (key2160, 4), (key2157, -4), (key2249, -4), (key2160, -4), (key2115, -4), (key2160, -4), (key2120, -4), (key2160, 12)]

def rawRow16845 : Integer.Sparse Key := [(key2157, 4), (key2160, 4), (key2115, 4), (key2249, -4), (key2157, -4), (key2160, -4), (key2160, -4), (key2115, -4), (key2120, -4), (key2160, 12)]

def rawRow16846 : Integer.Sparse Key := [(key2160, 4), (key2115, 4), (key2157, 4), (key2160, -4), (key2249, -4), (key2157, -4), (key2120, -4), (key2160, -4), (key2115, -4), (key2160, 12)]

def rawRow16847 : Integer.Sparse Key := [(key2160, 4), (key2157, 4), (key2115, 4), (key2249, -4), (key2160, -4), (key2157, -4), (key2160, -4), (key2120, -4), (key2115, -4), (key2160, 12)]

def rawRow16848 : Integer.Sparse Key := [(key2157, 4), (key2157, 4), (key2249, 4), (key2115, -4), (key2160, -4), (key2160, -4), (key2115, -4), (key2160, -4), (key2160, -4), (key2120, 12)]

def rawRow16849 : Integer.Sparse Key := [(key2157, 4), (key2249, 4), (key2157, 4), (key2160, -4), (key2115, -4), (key2160, -4), (key2160, -4), (key2115, -4), (key2160, -4), (key2120, 12)]

def rawRow16850 : Integer.Sparse Key := [(key2249, 4), (key2157, 4), (key2157, 4), (key2160, -4), (key2160, -4), (key2115, -4), (key2160, -4), (key2160, -4), (key2115, -4), (key2120, 12)]

def rawRow16851 : Integer.Sparse Key := [(key1987, -2), (key1990, -2), (key1990, -2), (key2000, 6), (key1987, -2), (key1990, -2), (key1990, -2), (key2232, 2), (key2235, 2), (key2232, 2), (key2256, 2), (key2235, 2), (key2256, 2), (key2269, -2), (key2269, -2), (key2292, -2), (key2000, 6), (key2269, -2), (key2269, -2), (key2292, -2)]

def rawRow16852 : Integer.Sparse Key := [(key1990, -2), (key1987, -2), (key1990, -2), (key2000, 6), (key1990, -2), (key1987, -2), (key1990, -2), (key2235, 2), (key2232, 2), (key2256, 2), (key2232, 2), (key2256, 2), (key2235, 2), (key2269, -2), (key2292, -2), (key2269, -2), (key2000, 6), (key2269, -2), (key2292, -2), (key2269, -2)]

def rawRow16853 : Integer.Sparse Key := [(key1990, -2), (key1990, -2), (key1987, -2), (key2000, 6), (key1990, -2), (key1990, -2), (key1987, -2), (key2256, 2), (key2256, 2), (key2235, 2), (key2235, 2), (key2232, 2), (key2232, 2), (key2292, -2), (key2269, -2), (key2269, -2), (key2000, 6), (key2292, -2), (key2269, -2), (key2269, -2)]

def rawRow16854 : Integer.Sparse Key := [(key1987, -2), (key1990, -2), (key2000, -2), (key1990, 6), (key2232, -2), (key2235, -2), (key2269, -2), (key1987, 2), (key1990, 2), (key2232, 2), (key2256, 2), (key2269, 2), (key2292, 2), (key1990, -2), (key2235, -2), (key2256, -2), (key2269, 6), (key2000, -2), (key2269, -2), (key2292, -2)]

def rawRow16855 : Integer.Sparse Key := [(key1990, -2), (key1987, -2), (key2000, -2), (key1990, 6), (key2235, -2), (key2232, -2), (key2269, -2), (key1990, 2), (key1987, 2), (key2256, 2), (key2232, 2), (key2292, 2), (key2269, 2), (key1990, -2), (key2256, -2), (key2235, -2), (key2269, 6), (key2000, -2), (key2292, -2), (key2269, -2)]

def rawRow16856 : Integer.Sparse Key := [(key1987, -2), (key2000, -2), (key1990, -2), (key1990, 6), (key2232, -2), (key2269, -2), (key2235, -2), (key2232, 2), (key2269, 2), (key1987, 2), (key2292, 2), (key1990, 2), (key2256, 2), (key2235, -2), (key1990, -2), (key2256, -2), (key2269, 6), (key2269, -2), (key2000, -2), (key2292, -2)]

def rawRow16857 : Integer.Sparse Key := [(key2000, -2), (key1987, -2), (key1990, -2), (key1990, 6), (key2269, -2), (key2232, -2), (key2235, -2), (key2269, 2), (key2232, 2), (key2292, 2), (key1987, 2), (key2256, 2), (key1990, 2), (key2235, -2), (key2256, -2), (key1990, -2), (key2269, 6), (key2269, -2), (key2292, -2), (key2000, -2)]

def rawRow16858 : Integer.Sparse Key := [(key1990, -2), (key2000, -2), (key1987, -2), (key1990, 6), (key2235, -2), (key2269, -2), (key2232, -2), (key2256, 2), (key2292, 2), (key1990, 2), (key2269, 2), (key1987, 2), (key2232, 2), (key2256, -2), (key1990, -2), (key2235, -2), (key2269, 6), (key2292, -2), (key2000, -2), (key2269, -2)]

def rawRow16859 : Integer.Sparse Key := [(key2000, -2), (key1990, -2), (key1987, -2), (key1990, 6), (key2269, -2), (key2235, -2), (key2232, -2), (key2292, 2), (key2256, 2), (key2269, 2), (key1990, 2), (key2232, 2), (key1987, 2), (key2256, -2), (key2235, -2), (key1990, -2), (key2269, 6), (key2292, -2), (key2269, -2), (key2000, -2)]

def rawRow16860 : Integer.Sparse Key := [(key2232, -2), (key2235, -2), (key2269, -2), (key2269, 6), (key1987, -2), (key1990, -2), (key2000, -2), (key1987, 2), (key1990, 2), (key2232, 2), (key2256, 2), (key2269, 2), (key2292, 2), (key2000, -2), (key2269, -2), (key2292, -2), (key1990, 6), (key1990, -2), (key2235, -2), (key2256, -2)]

def rawRow16861 : Integer.Sparse Key := [(key2235, -2), (key2232, -2), (key2269, -2), (key2269, 6), (key1990, -2), (key1987, -2), (key2000, -2), (key1990, 2), (key1987, 2), (key2256, 2), (key2232, 2), (key2292, 2), (key2269, 2), (key2000, -2), (key2292, -2), (key2269, -2), (key1990, 6), (key1990, -2), (key2256, -2), (key2235, -2)]

def rawRow16862 : Integer.Sparse Key := [(key2232, -2), (key2269, -2), (key2235, -2), (key2269, 6), (key1987, -2), (key2000, -2), (key1990, -2), (key2232, 2), (key2269, 2), (key1987, 2), (key2292, 2), (key1990, 2), (key2256, 2), (key2269, -2), (key2000, -2), (key2292, -2), (key1990, 6), (key2235, -2), (key1990, -2), (key2256, -2)]

def rawRow16863 : Integer.Sparse Key := [(key2269, -2), (key2232, -2), (key2235, -2), (key2269, 6), (key2000, -2), (key1987, -2), (key1990, -2), (key2269, 2), (key2232, 2), (key2292, 2), (key1987, 2), (key2256, 2), (key1990, 2), (key2269, -2), (key2292, -2), (key2000, -2), (key1990, 6), (key2235, -2), (key2256, -2), (key1990, -2)]

def rawRow16864 : Integer.Sparse Key := [(key2235, -2), (key2269, -2), (key2232, -2), (key2269, 6), (key1990, -2), (key2000, -2), (key1987, -2), (key2256, 2), (key2292, 2), (key1990, 2), (key2269, 2), (key1987, 2), (key2232, 2), (key2292, -2), (key2000, -2), (key2269, -2), (key1990, 6), (key2256, -2), (key1990, -2), (key2235, -2)]

def rawRow16865 : Integer.Sparse Key := [(key2269, -2), (key2235, -2), (key2232, -2), (key2269, 6), (key2000, -2), (key1990, -2), (key1987, -2), (key2292, 2), (key2256, 2), (key2269, 2), (key1990, 2), (key2232, 2), (key1987, 2), (key2292, -2), (key2269, -2), (key2000, -2), (key1990, 6), (key2256, -2), (key2235, -2), (key1990, -2)]

def rawRow16866 : Integer.Sparse Key := [(key2232, -2), (key2269, -2), (key2269, -2), (key2235, 6), (key2232, -2), (key2269, -2), (key2269, -2), (key1987, 2), (key2000, 2), (key1987, 2), (key2292, 2), (key2000, 2), (key2292, 2), (key1990, -2), (key1990, -2), (key2256, -2), (key2235, 6), (key1990, -2), (key1990, -2), (key2256, -2)]

def rawRow16867 : Integer.Sparse Key := [(key2269, -2), (key2232, -2), (key2269, -2), (key2235, 6), (key2269, -2), (key2232, -2), (key2269, -2), (key2000, 2), (key1987, 2), (key2292, 2), (key1987, 2), (key2292, 2), (key2000, 2), (key1990, -2), (key2256, -2), (key1990, -2), (key2235, 6), (key1990, -2), (key2256, -2), (key1990, -2)]

def rawRow16868 : Integer.Sparse Key := [(key2269, -2), (key2269, -2), (key2232, -2), (key2235, 6), (key2269, -2), (key2269, -2), (key2232, -2), (key2292, 2), (key2292, 2), (key2000, 2), (key2000, 2), (key1987, 2), (key1987, 2), (key2256, -2), (key1990, -2), (key1990, -2), (key2235, 6), (key2256, -2), (key1990, -2), (key1990, -2)]

def rawRow16869 : Integer.Sparse Key := [(key771, 4), (key771, 4), (key779, 4), (key798, -4), (key804, -4), (key804, -4), (key798, -4), (key804, -4), (key804, -4), (key873, 12)]

def rawRow16870 : Integer.Sparse Key := [(key771, 4), (key779, 4), (key771, 4), (key804, -4), (key798, -4), (key804, -4), (key804, -4), (key798, -4), (key804, -4), (key873, 12)]

def rawRow16871 : Integer.Sparse Key := [(key779, 4), (key771, 4), (key771, 4), (key804, -4), (key804, -4), (key798, -4), (key804, -4), (key804, -4), (key798, -4), (key873, 12)]

def rawRow16872 : Integer.Sparse Key := [(key771, 4), (key798, 4), (key804, 4), (key771, -4), (key779, -4), (key804, -4), (key798, -4), (key804, -4), (key873, -4), (key804, 12)]

def rawRow16873 : Integer.Sparse Key := [(key771, 4), (key804, 4), (key798, 4), (key779, -4), (key771, -4), (key804, -4), (key804, -4), (key798, -4), (key873, -4), (key804, 12)]

def rawRow16874 : Integer.Sparse Key := [(key798, 4), (key771, 4), (key804, 4), (key771, -4), (key804, -4), (key779, -4), (key798, -4), (key873, -4), (key804, -4), (key804, 12)]

def rawRow16875 : Integer.Sparse Key := [(key798, 4), (key804, 4), (key771, 4), (key804, -4), (key771, -4), (key779, -4), (key873, -4), (key798, -4), (key804, -4), (key804, 12)]

def rawRow16876 : Integer.Sparse Key := [(key804, 4), (key771, 4), (key798, 4), (key779, -4), (key804, -4), (key771, -4), (key804, -4), (key873, -4), (key798, -4), (key804, 12)]

def rawRow16877 : Integer.Sparse Key := [(key804, 4), (key798, 4), (key771, 4), (key804, -4), (key779, -4), (key771, -4), (key873, -4), (key804, -4), (key798, -4), (key804, 12)]

def rawRow16878 : Integer.Sparse Key := [(key771, 4), (key798, 4), (key804, 4), (key798, -4), (key804, -4), (key873, -4), (key771, -4), (key779, -4), (key804, -4), (key804, 12)]

def rawRow16879 : Integer.Sparse Key := [(key771, 4), (key804, 4), (key798, 4), (key804, -4), (key798, -4), (key873, -4), (key779, -4), (key771, -4), (key804, -4), (key804, 12)]

def rawRow16880 : Integer.Sparse Key := [(key798, 4), (key771, 4), (key804, 4), (key798, -4), (key873, -4), (key804, -4), (key771, -4), (key804, -4), (key779, -4), (key804, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow160 : Integer.Sparse Key := [(key1899, -1), (key1896, -1), (key1896, 2), (key1920, 1), (key1918, 1), (key1918, -1), (key1903, -1), (key1926, -2), (key1926, 1), (key1911, 1), (key1354, 1), (key1351, 1), (key1351, -2), (key1683, -1), (key1681, -1), (key1681, 1), (key1472, 1), (key1689, 2), (key1689, -1), (key1480, -1), (key1326, -1), (key1318, -1), (key1318, 1), (key1298, 1), (key1556, 1), (key1548, 1), (key1548, -1), (key1393, -1), (key1633, -1), (key1593, -1), (key1633, 1), (key1444, 1), (key1312, 2), (key1312, -1), (key1292, -1), (key1542, -2), (key1542, 1), (key1387, 1), (key1618, 1), (key1569, 1), (key1618, -1), (key1420, -1)]

def rawRow162 : Integer.Sparse Key := [(key1903, -1), (key1911, -1), (key1903, 2), (key1918, 1), (key1926, 1), (key1896, -1), (key1918, -1), (key1920, -2), (key1899, 1), (key1920, 1), (key1472, 1), (key1480, 1), (key1472, -2), (key1681, -1), (key1689, -1), (key1351, 1), (key1681, 1), (key1683, 2), (key1354, -1), (key1683, -1), (key1426, -1), (key1444, -1), (key1393, 1), (key1426, 1), (key1575, 1), (key1593, 1), (key1298, -1), (key1575, -1), (key1556, -1), (key1624, -1), (key1326, 1), (key1624, 1), (key1420, 2), (key1387, -1), (key1420, -1), (key1569, -2), (key1292, 1), (key1569, 1), (key1542, 1), (key1618, 1), (key1312, -1), (key1618, -1)]

def rawRow163 : Integer.Sparse Key := [(key1911, -1), (key1903, -1), (key1903, 2), (key1926, 1), (key1918, 1), (key1918, -1), (key1896, -1), (key1920, -2), (key1920, 1), (key1899, 1), (key1480, 1), (key1472, 1), (key1472, -2), (key1689, -1), (key1681, -1), (key1681, 1), (key1351, 1), (key1683, 2), (key1683, -1), (key1354, -1), (key1444, -1), (key1426, -1), (key1426, 1), (key1393, 1), (key1593, 1), (key1575, 1), (key1575, -1), (key1298, -1), (key1624, -1), (key1556, -1), (key1624, 1), (key1326, 1), (key1420, 2), (key1420, -1), (key1387, -1), (key1569, -2), (key1569, 1), (key1292, 1), (key1618, 1), (key1542, 1), (key1618, -1), (key1312, -1)]

def rawRow164 : Integer.Sparse Key := [(key1918, -1), (key1920, -1), (key1926, 2), (key1896, 1), (key1899, 1), (key1911, -1), (key1926, -1), (key1896, -2), (key1903, 1), (key1918, 1), (key1681, 1), (key1683, 1), (key1689, -2), (key1351, -1), (key1354, -1), (key1480, 1), (key1689, 1), (key1351, 2), (key1472, -1), (key1681, -1), (key1548, -1), (key1556, -1), (key1593, 1), (key1633, 1), (key1318, 1), (key1326, 1), (key1444, -1), (key1633, -1), (key1298, -1), (key1318, -1), (key1393, 1), (key1548, 1), (key1542, 2), (key1569, -1), (key1618, -1), (key1312, -2), (key1420, 1), (key1618, 1), (key1292, 1), (key1312, 1), (key1387, -1), (key1542, -1)]

def rawRow165 : Integer.Sparse Key := [(key1920, -1), (key1918, -1), (key1926, 2), (key1899, 1), (key1896, 1), (key1926, -1), (key1911, -1), (key1896, -2), (key1918, 1), (key1903, 1), (key1683, 1), (key1681, 1), (key1689, -2), (key1354, -1), (key1351, -1), (key1689, 1), (key1480, 1), (key1351, 2), (key1681, -1), (key1472, -1), (key1556, -1), (key1548, -1), (key1633, 1), (key1593, 1), (key1326, 1), (key1318, 1), (key1633, -1), (key1444, -1), (key1318, -1), (key1298, -1), (key1548, 1), (key1393, 1), (key1542, 2), (key1618, -1), (key1569, -1), (key1312, -2), (key1618, 1), (key1420, 1), (key1312, 1), (key1292, 1), (key1542, -1), (key1387, -1)]

def rawRow166 : Integer.Sparse Key := [(key1918, -1), (key1926, -1), (key1920, 2), (key1903, 1), (key1911, 1), (key1899, -1), (key1920, -1), (key1903, -2), (key1896, 1), (key1918, 1), (key1681, 1), (key1689, 1), (key1683, -2), (key1472, -1), (key1480, -1), (key1354, 1), (key1683, 1), (key1472, 2), (key1351, -1), (key1681, -1), (key1575, -1), (key1593, -1), (key1556, 1), (key1624, 1), (key1426, 1), (key1444, 1), (key1326, -1), (key1624, -1), (key1393, -1), (key1426, -1), (key1298, 1), (key1575, 1), (key1569, 2), (key1542, -1), (key1618, -1), (key1420, -2), (key1312, 1), (key1618, 1), (key1387, 1), (key1420, 1), (key1292, -1), (key1569, -1)]

def rawRow167 : Integer.Sparse Key := [(key1926, -1), (key1918, -1), (key1920, 2), (key1911, 1), (key1903, 1), (key1920, -1), (key1899, -1), (key1903, -2), (key1918, 1), (key1896, 1), (key1689, 1), (key1681, 1), (key1683, -2), (key1480, -1), (key1472, -1), (key1683, 1), (key1354, 1), (key1472, 2), (key1681, -1), (key1351, -1), (key1593, -1), (key1575, -1), (key1624, 1), (key1556, 1), (key1444, 1), (key1426, 1), (key1624, -1), (key1326, -1), (key1426, -1), (key1393, -1), (key1575, 1), (key1298, 1), (key1569, 2), (key1618, -1), (key1542, -1), (key1420, -2), (key1618, 1), (key1312, 1), (key1420, 1), (key1387, 1), (key1569, -1), (key1292, -1)]

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

def rawRow1589 : Integer.Sparse Key := [(key2639, -6), (key2631, 2), (key2615, 2), (key2639, 2), (key2725, 6), (key2705, -2), (key2670, -2), (key2725, -2), (key2869, -2), (key2828, -2), (key2879, -2), (key2859, 2), (key2793, 2), (key2879, 2)]

def rawRow1590 : Integer.Sparse Key := [(key2639, -6), (key2631, 2), (key2639, 2), (key2615, 2), (key2725, 6), (key2705, -2), (key2725, -2), (key2670, -2), (key2869, -2), (key2879, -2), (key2828, -2), (key2859, 2), (key2879, 2), (key2793, 2)]

def rawRow1591 : Integer.Sparse Key := [(key2639, -6), (key2639, 2), (key2615, 2), (key2631, 2), (key2725, 6), (key2725, -2), (key2670, -2), (key2705, -2), (key2879, -2), (key2828, -2), (key2869, -2), (key2879, 2), (key2793, 2), (key2859, 2)]

def rawRow1592 : Integer.Sparse Key := [(key2639, -6), (key2639, 2), (key2631, 2), (key2615, 2), (key2725, 6), (key2725, -2), (key2705, -2), (key2670, -2), (key2879, -2), (key2869, -2), (key2828, -2), (key2879, 2), (key2859, 2), (key2793, 2)]

def rawRow1593 : Integer.Sparse Key := [(key2705, -6), (key2808, 2), (key2859, 2), (key2859, 2), (key2631, 6), (key2785, -2), (key2869, -2), (key2869, -2), (key2615, -2), (key2639, -2), (key2639, -2), (key2670, 2), (key2725, 2), (key2725, 2)]

def rawRow1594 : Integer.Sparse Key := [(key2705, -6), (key2859, 2), (key2808, 2), (key2859, 2), (key2631, 6), (key2869, -2), (key2785, -2), (key2869, -2), (key2639, -2), (key2615, -2), (key2639, -2), (key2725, 2), (key2670, 2), (key2725, 2)]

def rawRow1595 : Integer.Sparse Key := [(key2705, -6), (key2859, 2), (key2859, 2), (key2808, 2), (key2631, 6), (key2869, -2), (key2869, -2), (key2785, -2), (key2639, -2), (key2639, -2), (key2615, -2), (key2725, 2), (key2725, 2), (key2670, 2)]

def rawRow1596 : Integer.Sparse Key := [(key2859, -6), (key2705, 2), (key2808, 2), (key2859, 2), (key2869, 6), (key2631, -2), (key2785, -2), (key2869, -2), (key2725, -2), (key2828, -2), (key2879, -2), (key2639, 2), (key2793, 2), (key2879, 2)]

def rawRow1597 : Integer.Sparse Key := [(key2859, -6), (key2705, 2), (key2859, 2), (key2808, 2), (key2869, 6), (key2631, -2), (key2869, -2), (key2785, -2), (key2725, -2), (key2879, -2), (key2828, -2), (key2639, 2), (key2879, 2), (key2793, 2)]

def rawRow1598 : Integer.Sparse Key := [(key2859, -6), (key2808, 2), (key2705, 2), (key2859, 2), (key2869, 6), (key2785, -2), (key2631, -2), (key2869, -2), (key2828, -2), (key2725, -2), (key2879, -2), (key2793, 2), (key2639, 2), (key2879, 2)]

def rawRow1599 : Integer.Sparse Key := [(key2859, -6), (key2808, 2), (key2859, 2), (key2705, 2), (key2869, 6), (key2785, -2), (key2869, -2), (key2631, -2), (key2828, -2), (key2879, -2), (key2725, -2), (key2793, 2), (key2879, 2), (key2639, 2)]

def rawRow1600 : Integer.Sparse Key := [(key2859, -6), (key2859, 2), (key2705, 2), (key2808, 2), (key2869, 6), (key2869, -2), (key2631, -2), (key2785, -2), (key2879, -2), (key2725, -2), (key2828, -2), (key2879, 2), (key2639, 2), (key2793, 2)]

def rawRow1601 : Integer.Sparse Key := [(key2859, -6), (key2859, 2), (key2808, 2), (key2705, 2), (key2869, 6), (key2869, -2), (key2785, -2), (key2631, -2), (key2879, -2), (key2828, -2), (key2725, -2), (key2879, 2), (key2793, 2), (key2639, 2)]

def rawRow1602 : Integer.Sparse Key := [(key2725, -6), (key2828, 2), (key2869, 2), (key2879, 2), (key2639, 6), (key2793, -2), (key2859, -2), (key2879, -2), (key2615, -2), (key2631, -2), (key2639, -2), (key2670, 2), (key2705, 2), (key2725, 2)]

def rawRow1603 : Integer.Sparse Key := [(key2725, -6), (key2828, 2), (key2879, 2), (key2869, 2), (key2639, 6), (key2793, -2), (key2879, -2), (key2859, -2), (key2615, -2), (key2639, -2), (key2631, -2), (key2670, 2), (key2725, 2), (key2705, 2)]

def rawRow1604 : Integer.Sparse Key := [(key2725, -6), (key2869, 2), (key2828, 2), (key2879, 2), (key2639, 6), (key2859, -2), (key2793, -2), (key2879, -2), (key2631, -2), (key2615, -2), (key2639, -2), (key2705, 2), (key2670, 2), (key2725, 2)]

def rawRow1605 : Integer.Sparse Key := [(key2725, -6), (key2869, 2), (key2879, 2), (key2828, 2), (key2639, 6), (key2859, -2), (key2879, -2), (key2793, -2), (key2631, -2), (key2639, -2), (key2615, -2), (key2705, 2), (key2725, 2), (key2670, 2)]

def rawRow1606 : Integer.Sparse Key := [(key2725, -6), (key2879, 2), (key2828, 2), (key2869, 2), (key2639, 6), (key2879, -2), (key2793, -2), (key2859, -2), (key2639, -2), (key2615, -2), (key2631, -2), (key2725, 2), (key2670, 2), (key2705, 2)]

def rawRow1607 : Integer.Sparse Key := [(key2725, -6), (key2879, 2), (key2869, 2), (key2828, 2), (key2639, 6), (key2879, -2), (key2859, -2), (key2793, -2), (key2639, -2), (key2631, -2), (key2615, -2), (key2725, 2), (key2705, 2), (key2670, 2)]

def rawRow1608 : Integer.Sparse Key := [(key2869, -6), (key2725, 2), (key2828, 2), (key2879, 2), (key2859, 6), (key2639, -2), (key2793, -2), (key2879, -2), (key2705, -2), (key2808, -2), (key2859, -2), (key2631, 2), (key2785, 2), (key2869, 2)]

def rawRow1609 : Integer.Sparse Key := [(key2869, -6), (key2725, 2), (key2879, 2), (key2828, 2), (key2859, 6), (key2639, -2), (key2879, -2), (key2793, -2), (key2705, -2), (key2859, -2), (key2808, -2), (key2631, 2), (key2869, 2), (key2785, 2)]

def rawRow1610 : Integer.Sparse Key := [(key2869, -6), (key2828, 2), (key2725, 2), (key2879, 2), (key2859, 6), (key2793, -2), (key2639, -2), (key2879, -2), (key2808, -2), (key2705, -2), (key2859, -2), (key2785, 2), (key2631, 2), (key2869, 2)]

def rawRow1611 : Integer.Sparse Key := [(key2869, -6), (key2828, 2), (key2879, 2), (key2725, 2), (key2859, 6), (key2793, -2), (key2879, -2), (key2639, -2), (key2808, -2), (key2859, -2), (key2705, -2), (key2785, 2), (key2869, 2), (key2631, 2)]

def rawRow1612 : Integer.Sparse Key := [(key2869, -6), (key2879, 2), (key2725, 2), (key2828, 2), (key2859, 6), (key2879, -2), (key2639, -2), (key2793, -2), (key2859, -2), (key2705, -2), (key2808, -2), (key2869, 2), (key2631, 2), (key2785, 2)]

def rawRow1613 : Integer.Sparse Key := [(key2869, -6), (key2879, 2), (key2828, 2), (key2725, 2), (key2859, 6), (key2879, -2), (key2793, -2), (key2639, -2), (key2859, -2), (key2808, -2), (key2705, -2), (key2869, 2), (key2785, 2), (key2631, 2)]

def rawRow1614 : Integer.Sparse Key := [(key1391, -1), (key1391, -1), (key1772, -1), (key1772, -1), (key1781, -1), (key1781, -1), (key1398, 2), (key1775, 2), (key1775, 2), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1), (key1818, 1), (key1818, 1), (key1458, -1), (key1458, -1), (key1791, -1), (key1791, -1), (key1840, -1), (key1840, -1), (key1448, -2), (key1826, -2), (key1826, -2), (key1467, 1), (key1467, 1), (key1799, 1), (key1799, 1), (key1845, 1), (key1845, 1)]

def rawRow1615 : Integer.Sparse Key := [(key1772, -1), (key1781, -1), (key1391, -1), (key1781, -1), (key1391, -1), (key1772, -1), (key1775, 2), (key1398, 2), (key1775, 2), (key1813, 1), (key1818, 1), (key1424, 1), (key1818, 1), (key1424, 1), (key1813, 1), (key1791, -1), (key1840, -1), (key1458, -1), (key1840, -1), (key1458, -1), (key1791, -1), (key1826, -2), (key1448, -2), (key1826, -2), (key1799, 1), (key1845, 1), (key1467, 1), (key1845, 1), (key1467, 1), (key1799, 1)]

def rawRow1616 : Integer.Sparse Key := [(key1781, -1), (key1772, -1), (key1781, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1775, 2), (key1775, 2), (key1398, 2), (key1818, 1), (key1813, 1), (key1818, 1), (key1424, 1), (key1813, 1), (key1424, 1), (key1840, -1), (key1791, -1), (key1840, -1), (key1458, -1), (key1791, -1), (key1458, -1), (key1826, -2), (key1826, -2), (key1448, -2), (key1845, 1), (key1799, 1), (key1845, 1), (key1467, 1), (key1799, 1), (key1467, 1)]

def rawRow1617 : Integer.Sparse Key := [(key1391, -1), (key1398, -1), (key1546, -1), (key1775, -1), (key1560, -1), (key1781, -1), (key1391, 2), (key1546, 2), (key1772, 2), (key1455, 1), (key1458, 1), (key1655, 1), (key1840, 1), (key1660, 1), (key1842, 1), (key1424, -1), (key1455, -1), (key1573, -1), (key1788, -1), (key1655, -1), (key1813, -1), (key1467, -2), (key1668, -2), (key1845, -2), (key1448, 1), (key1467, 1), (key1597, 1), (key1799, 1), (key1668, 1), (key1826, 1)]

def rawRow1618 : Integer.Sparse Key := [(key1398, -1), (key1391, -1), (key1775, -1), (key1546, -1), (key1781, -1), (key1560, -1), (key1391, 2), (key1772, 2), (key1546, 2), (key1458, 1), (key1455, 1), (key1840, 1), (key1655, 1), (key1842, 1), (key1660, 1), (key1455, -1), (key1424, -1), (key1788, -1), (key1573, -1), (key1813, -1), (key1655, -1), (key1467, -2), (key1845, -2), (key1668, -2), (key1467, 1), (key1448, 1), (key1799, 1), (key1597, 1), (key1826, 1), (key1668, 1)]

def rawRow1619 : Integer.Sparse Key := [(key1546, -1), (key1560, -1), (key1391, -1), (key1781, -1), (key1398, -1), (key1775, -1), (key1546, 2), (key1391, 2), (key1772, 2), (key1655, 1), (key1660, 1), (key1455, 1), (key1842, 1), (key1458, 1), (key1840, 1), (key1573, -1), (key1655, -1), (key1424, -1), (key1813, -1), (key1455, -1), (key1788, -1), (key1668, -2), (key1467, -2), (key1845, -2), (key1597, 1), (key1668, 1), (key1448, 1), (key1826, 1), (key1467, 1), (key1799, 1)]

def rawRow1620 : Integer.Sparse Key := [(key1560, -1), (key1546, -1), (key1781, -1), (key1391, -1), (key1775, -1), (key1398, -1), (key1546, 2), (key1772, 2), (key1391, 2), (key1660, 1), (key1655, 1), (key1842, 1), (key1455, 1), (key1840, 1), (key1458, 1), (key1655, -1), (key1573, -1), (key1813, -1), (key1424, -1), (key1788, -1), (key1455, -1), (key1668, -2), (key1845, -2), (key1467, -2), (key1668, 1), (key1597, 1), (key1826, 1), (key1448, 1), (key1799, 1), (key1467, 1)]

def rawRow1621 : Integer.Sparse Key := [(key1775, -1), (key1781, -1), (key1398, -1), (key1560, -1), (key1391, -1), (key1546, -1), (key1772, 2), (key1391, 2), (key1546, 2), (key1840, 1), (key1842, 1), (key1458, 1), (key1660, 1), (key1455, 1), (key1655, 1), (key1788, -1), (key1813, -1), (key1455, -1), (key1655, -1), (key1424, -1), (key1573, -1), (key1845, -2), (key1467, -2), (key1668, -2), (key1799, 1), (key1826, 1), (key1467, 1), (key1668, 1), (key1448, 1), (key1597, 1)]

def rawRow1622 : Integer.Sparse Key := [(key1781, -1), (key1775, -1), (key1560, -1), (key1398, -1), (key1546, -1), (key1391, -1), (key1772, 2), (key1546, 2), (key1391, 2), (key1842, 1), (key1840, 1), (key1660, 1), (key1458, 1), (key1655, 1), (key1455, 1), (key1813, -1), (key1788, -1), (key1655, -1), (key1455, -1), (key1573, -1), (key1424, -1), (key1845, -2), (key1668, -2), (key1467, -2), (key1826, 1), (key1799, 1), (key1668, 1), (key1467, 1), (key1597, 1), (key1448, 1)]

def rawRow1623 : Integer.Sparse Key := [(key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1818, -1), (key1818, -1), (key1448, 2), (key1826, 2), (key1826, 2), (key1391, 1), (key1391, 1), (key1772, 1), (key1772, 1), (key1781, 1), (key1781, 1), (key1467, -1), (key1467, -1), (key1799, -1), (key1799, -1), (key1845, -1), (key1845, -1), (key1398, -2), (key1775, -2), (key1775, -2), (key1458, 1), (key1458, 1), (key1791, 1), (key1791, 1), (key1840, 1), (key1840, 1)]

def rawRow1624 : Integer.Sparse Key := [(key1813, -1), (key1818, -1), (key1424, -1), (key1818, -1), (key1424, -1), (key1813, -1), (key1826, 2), (key1448, 2), (key1826, 2), (key1772, 1), (key1781, 1), (key1391, 1), (key1781, 1), (key1391, 1), (key1772, 1), (key1799, -1), (key1845, -1), (key1467, -1), (key1845, -1), (key1467, -1), (key1799, -1), (key1775, -2), (key1398, -2), (key1775, -2), (key1791, 1), (key1840, 1), (key1458, 1), (key1840, 1), (key1458, 1), (key1791, 1)]

def rawRow1625 : Integer.Sparse Key := [(key1818, -1), (key1813, -1), (key1818, -1), (key1424, -1), (key1813, -1), (key1424, -1), (key1826, 2), (key1826, 2), (key1448, 2), (key1781, 1), (key1772, 1), (key1781, 1), (key1391, 1), (key1772, 1), (key1391, 1), (key1845, -1), (key1799, -1), (key1845, -1), (key1467, -1), (key1799, -1), (key1467, -1), (key1775, -2), (key1775, -2), (key1398, -2), (key1840, 1), (key1791, 1), (key1840, 1), (key1458, 1), (key1791, 1), (key1458, 1)]

def rawRow1626 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1424, -1), (key1818, -1), (key1448, -1), (key1826, -1), (key1316, 2), (key1424, 2), (key1813, 2), (key1337, 1), (key1346, 1), (key1455, 1), (key1842, 1), (key1467, 1), (key1845, 1), (key1296, -1), (key1337, -1), (key1391, -1), (key1772, -1), (key1455, -1), (key1788, -1), (key1340, -2), (key1458, -2), (key1840, -2), (key1303, 1), (key1340, 1), (key1398, 1), (key1775, 1), (key1458, 1), (key1791, 1)]

def rawRow1627 : Integer.Sparse Key := [(key1330, -1), (key1316, -1), (key1818, -1), (key1424, -1), (key1826, -1), (key1448, -1), (key1316, 2), (key1813, 2), (key1424, 2), (key1346, 1), (key1337, 1), (key1842, 1), (key1455, 1), (key1845, 1), (key1467, 1), (key1337, -1), (key1296, -1), (key1772, -1), (key1391, -1), (key1788, -1), (key1455, -1), (key1340, -2), (key1840, -2), (key1458, -2), (key1340, 1), (key1303, 1), (key1775, 1), (key1398, 1), (key1791, 1), (key1458, 1)]

def rawRow1628 : Integer.Sparse Key := [(key1424, -1), (key1448, -1), (key1316, -1), (key1826, -1), (key1330, -1), (key1818, -1), (key1424, 2), (key1316, 2), (key1813, 2), (key1455, 1), (key1467, 1), (key1337, 1), (key1845, 1), (key1346, 1), (key1842, 1), (key1391, -1), (key1455, -1), (key1296, -1), (key1788, -1), (key1337, -1), (key1772, -1), (key1458, -2), (key1340, -2), (key1840, -2), (key1398, 1), (key1458, 1), (key1303, 1), (key1791, 1), (key1340, 1), (key1775, 1)]

def rawRow1629 : Integer.Sparse Key := [(key1448, -1), (key1424, -1), (key1826, -1), (key1316, -1), (key1818, -1), (key1330, -1), (key1424, 2), (key1813, 2), (key1316, 2), (key1467, 1), (key1455, 1), (key1845, 1), (key1337, 1), (key1842, 1), (key1346, 1), (key1455, -1), (key1391, -1), (key1788, -1), (key1296, -1), (key1772, -1), (key1337, -1), (key1458, -2), (key1840, -2), (key1340, -2), (key1458, 1), (key1398, 1), (key1791, 1), (key1303, 1), (key1775, 1), (key1340, 1)]

def rawRow1630 : Integer.Sparse Key := [(key1818, -1), (key1826, -1), (key1330, -1), (key1448, -1), (key1316, -1), (key1424, -1), (key1813, 2), (key1316, 2), (key1424, 2), (key1842, 1), (key1845, 1), (key1346, 1), (key1467, 1), (key1337, 1), (key1455, 1), (key1772, -1), (key1788, -1), (key1337, -1), (key1455, -1), (key1296, -1), (key1391, -1), (key1840, -2), (key1340, -2), (key1458, -2), (key1775, 1), (key1791, 1), (key1340, 1), (key1458, 1), (key1303, 1), (key1398, 1)]

def rawRow1631 : Integer.Sparse Key := [(key1826, -1), (key1818, -1), (key1448, -1), (key1330, -1), (key1424, -1), (key1316, -1), (key1813, 2), (key1424, 2), (key1316, 2), (key1845, 1), (key1842, 1), (key1467, 1), (key1346, 1), (key1455, 1), (key1337, 1), (key1788, -1), (key1772, -1), (key1455, -1), (key1337, -1), (key1391, -1), (key1296, -1), (key1840, -2), (key1458, -2), (key1340, -2), (key1791, 1), (key1775, 1), (key1458, 1), (key1340, 1), (key1398, 1), (key1303, 1)]

def rawRow1632 : Integer.Sparse Key := [(key1455, -1), (key1458, -1), (key1655, -1), (key1840, -1), (key1660, -1), (key1842, -1), (key1467, 2), (key1668, 2), (key1845, 2), (key1391, 1), (key1398, 1), (key1546, 1), (key1775, 1), (key1560, 1), (key1781, 1), (key1448, -1), (key1467, -1), (key1597, -1), (key1799, -1), (key1668, -1), (key1826, -1), (key1391, -2), (key1546, -2), (key1772, -2), (key1424, 1), (key1455, 1), (key1573, 1), (key1788, 1), (key1655, 1), (key1813, 1)]

def rawRow1633 : Integer.Sparse Key := [(key1458, -1), (key1455, -1), (key1840, -1), (key1655, -1), (key1842, -1), (key1660, -1), (key1467, 2), (key1845, 2), (key1668, 2), (key1398, 1), (key1391, 1), (key1775, 1), (key1546, 1), (key1781, 1), (key1560, 1), (key1467, -1), (key1448, -1), (key1799, -1), (key1597, -1), (key1826, -1), (key1668, -1), (key1391, -2), (key1772, -2), (key1546, -2), (key1455, 1), (key1424, 1), (key1788, 1), (key1573, 1), (key1813, 1), (key1655, 1)]

def rawRow1634 : Integer.Sparse Key := [(key1655, -1), (key1660, -1), (key1455, -1), (key1842, -1), (key1458, -1), (key1840, -1), (key1668, 2), (key1467, 2), (key1845, 2), (key1546, 1), (key1560, 1), (key1391, 1), (key1781, 1), (key1398, 1), (key1775, 1), (key1597, -1), (key1668, -1), (key1448, -1), (key1826, -1), (key1467, -1), (key1799, -1), (key1546, -2), (key1391, -2), (key1772, -2), (key1573, 1), (key1655, 1), (key1424, 1), (key1813, 1), (key1455, 1), (key1788, 1)]

def rawRow1635 : Integer.Sparse Key := [(key1660, -1), (key1655, -1), (key1842, -1), (key1455, -1), (key1840, -1), (key1458, -1), (key1668, 2), (key1845, 2), (key1467, 2), (key1560, 1), (key1546, 1), (key1781, 1), (key1391, 1), (key1775, 1), (key1398, 1), (key1668, -1), (key1597, -1), (key1826, -1), (key1448, -1), (key1799, -1), (key1467, -1), (key1546, -2), (key1772, -2), (key1391, -2), (key1655, 1), (key1573, 1), (key1813, 1), (key1424, 1), (key1788, 1), (key1455, 1)]

def rawRow1636 : Integer.Sparse Key := [(key1840, -1), (key1842, -1), (key1458, -1), (key1660, -1), (key1455, -1), (key1655, -1), (key1845, 2), (key1467, 2), (key1668, 2), (key1775, 1), (key1781, 1), (key1398, 1), (key1560, 1), (key1391, 1), (key1546, 1), (key1799, -1), (key1826, -1), (key1467, -1), (key1668, -1), (key1448, -1), (key1597, -1), (key1772, -2), (key1391, -2), (key1546, -2), (key1788, 1), (key1813, 1), (key1455, 1), (key1655, 1), (key1424, 1), (key1573, 1)]

def rawRow1637 : Integer.Sparse Key := [(key1842, -1), (key1840, -1), (key1660, -1), (key1458, -1), (key1655, -1), (key1455, -1), (key1845, 2), (key1668, 2), (key1467, 2), (key1781, 1), (key1775, 1), (key1560, 1), (key1398, 1), (key1546, 1), (key1391, 1), (key1826, -1), (key1799, -1), (key1668, -1), (key1467, -1), (key1597, -1), (key1448, -1), (key1772, -2), (key1546, -2), (key1391, -2), (key1813, 1), (key1788, 1), (key1655, 1), (key1455, 1), (key1573, 1), (key1424, 1)]

def rawRow1638 : Integer.Sparse Key := [(key1337, -1), (key1346, -1), (key1455, -1), (key1842, -1), (key1467, -1), (key1845, -1), (key1340, 2), (key1458, 2), (key1840, 2), (key1316, 1), (key1330, 1), (key1424, 1), (key1818, 1), (key1448, 1), (key1826, 1), (key1303, -1), (key1340, -1), (key1398, -1), (key1775, -1), (key1458, -1), (key1791, -1), (key1316, -2), (key1424, -2), (key1813, -2), (key1296, 1), (key1337, 1), (key1391, 1), (key1772, 1), (key1455, 1), (key1788, 1)]

def rawRow1639 : Integer.Sparse Key := [(key1346, -1), (key1337, -1), (key1842, -1), (key1455, -1), (key1845, -1), (key1467, -1), (key1340, 2), (key1840, 2), (key1458, 2), (key1330, 1), (key1316, 1), (key1818, 1), (key1424, 1), (key1826, 1), (key1448, 1), (key1340, -1), (key1303, -1), (key1775, -1), (key1398, -1), (key1791, -1), (key1458, -1), (key1316, -2), (key1813, -2), (key1424, -2), (key1337, 1), (key1296, 1), (key1772, 1), (key1391, 1), (key1788, 1), (key1455, 1)]

def rawRow1640 : Integer.Sparse Key := [(key1455, -1), (key1467, -1), (key1337, -1), (key1845, -1), (key1346, -1), (key1842, -1), (key1458, 2), (key1340, 2), (key1840, 2), (key1424, 1), (key1448, 1), (key1316, 1), (key1826, 1), (key1330, 1), (key1818, 1), (key1398, -1), (key1458, -1), (key1303, -1), (key1791, -1), (key1340, -1), (key1775, -1), (key1424, -2), (key1316, -2), (key1813, -2), (key1391, 1), (key1455, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1772, 1)]

def rawRow1641 : Integer.Sparse Key := [(key1467, -1), (key1455, -1), (key1845, -1), (key1337, -1), (key1842, -1), (key1346, -1), (key1458, 2), (key1840, 2), (key1340, 2), (key1448, 1), (key1424, 1), (key1826, 1), (key1316, 1), (key1818, 1), (key1330, 1), (key1458, -1), (key1398, -1), (key1791, -1), (key1303, -1), (key1775, -1), (key1340, -1), (key1424, -2), (key1813, -2), (key1316, -2), (key1455, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1772, 1), (key1337, 1)]

def rawRow1642 : Integer.Sparse Key := [(key1842, -1), (key1845, -1), (key1346, -1), (key1467, -1), (key1337, -1), (key1455, -1), (key1840, 2), (key1340, 2), (key1458, 2), (key1818, 1), (key1826, 1), (key1330, 1), (key1448, 1), (key1316, 1), (key1424, 1), (key1775, -1), (key1791, -1), (key1340, -1), (key1458, -1), (key1303, -1), (key1398, -1), (key1813, -2), (key1316, -2), (key1424, -2), (key1772, 1), (key1788, 1), (key1337, 1), (key1455, 1), (key1296, 1), (key1391, 1)]

def rawRow1643 : Integer.Sparse Key := [(key1845, -1), (key1842, -1), (key1467, -1), (key1346, -1), (key1455, -1), (key1337, -1), (key1840, 2), (key1458, 2), (key1340, 2), (key1826, 1), (key1818, 1), (key1448, 1), (key1330, 1), (key1424, 1), (key1316, 1), (key1791, -1), (key1775, -1), (key1458, -1), (key1340, -1), (key1398, -1), (key1303, -1), (key1813, -2), (key1424, -2), (key1316, -2), (key1788, 1), (key1772, 1), (key1455, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

def rawRow1644 : Integer.Sparse Key := [(key2693, -2), (key2693, -2), (key2759, -2), (key2695, 2), (key2695, 2), (key2733, 2), (key2822, 2), (key2822, 2), (key2924, 2), (key2836, -6), (key3015, -2), (key3015, -2), (key3027, -2), (key3018, 6)]

def rawRow1645 : Integer.Sparse Key := [(key2693, -2), (key2759, -2), (key2693, -2), (key2695, 2), (key2733, 2), (key2695, 2), (key2822, 2), (key2924, 2), (key2822, 2), (key2836, -6), (key3015, -2), (key3027, -2), (key3015, -2), (key3018, 6)]

def rawRow1646 : Integer.Sparse Key := [(key2759, -2), (key2693, -2), (key2693, -2), (key2733, 2), (key2695, 2), (key2695, 2), (key2924, 2), (key2822, 2), (key2822, 2), (key2836, -6), (key3027, -2), (key3015, -2), (key3015, -2), (key3018, 6)]

def rawRow1647 : Integer.Sparse Key := [(key2686, -2), (key2695, -2), (key2756, -2), (key2686, 2), (key2693, 2), (key2719, 2), (key2822, 2), (key2836, 2), (key2924, 2), (key2822, -6), (key3015, -2), (key3018, -2), (key3027, -2), (key3015, 6)]

def rawRow1648 : Integer.Sparse Key := [(key2695, -2), (key2686, -2), (key2756, -2), (key2693, 2), (key2686, 2), (key2719, 2), (key2836, 2), (key2822, 2), (key2924, 2), (key2822, -6), (key3018, -2), (key3015, -2), (key3027, -2), (key3015, 6)]

def rawRow1649 : Integer.Sparse Key := [(key2686, -2), (key2756, -2), (key2695, -2), (key2686, 2), (key2719, 2), (key2693, 2), (key2822, 2), (key2924, 2), (key2836, 2), (key2822, -6), (key3015, -2), (key3027, -2), (key3018, -2), (key3015, 6)]

def rawRow1650 : Integer.Sparse Key := [(key2756, -2), (key2686, -2), (key2695, -2), (key2719, 2), (key2686, 2), (key2693, 2), (key2924, 2), (key2822, 2), (key2836, 2), (key2822, -6), (key3027, -2), (key3015, -2), (key3018, -2), (key3015, 6)]

def rawRow1651 : Integer.Sparse Key := [(key2695, -2), (key2756, -2), (key2686, -2), (key2693, 2), (key2719, 2), (key2686, 2), (key2836, 2), (key2924, 2), (key2822, 2), (key2822, -6), (key3018, -2), (key3027, -2), (key3015, -2), (key3015, 6)]

def rawRow1652 : Integer.Sparse Key := [(key2756, -2), (key2695, -2), (key2686, -2), (key2719, 2), (key2693, 2), (key2686, 2), (key2924, 2), (key2836, 2), (key2822, 2), (key2822, -6), (key3027, -2), (key3018, -2), (key3015, -2), (key3015, 6)]

def rawRow1653 : Integer.Sparse Key := [(key3107, -2), (key3107, -2), (key3146, -2), (key3112, 2), (key3112, 2), (key3147, 2), (key2693, 2), (key2693, 2), (key2759, 2), (key3018, -6), (key2695, -2), (key2695, -2), (key2733, -2), (key2836, 6)]

def rawRow1654 : Integer.Sparse Key := [(key3107, -2), (key3146, -2), (key3107, -2), (key3112, 2), (key3147, 2), (key3112, 2), (key2693, 2), (key2759, 2), (key2693, 2), (key3018, -6), (key2695, -2), (key2733, -2), (key2695, -2), (key2836, 6)]

def rawRow1655 : Integer.Sparse Key := [(key3146, -2), (key3107, -2), (key3107, -2), (key3147, 2), (key3112, 2), (key3112, 2), (key2759, 2), (key2693, 2), (key2693, 2), (key3018, -6), (key2733, -2), (key2695, -2), (key2695, -2), (key2836, 6)]

def rawRow1656 : Integer.Sparse Key := [(key3051, -2), (key3074, -2), (key3112, -2), (key3051, 2), (key3070, 2), (key3107, 2), (key3055, 2), (key3078, 2), (key3117, 2), (key2693, -6), (key2695, -2), (key2733, -2), (key2836, -2), (key2695, 6)]

def rawRow1657 : Integer.Sparse Key := [(key3074, -2), (key3051, -2), (key3112, -2), (key3070, 2), (key3051, 2), (key3107, 2), (key3078, 2), (key3055, 2), (key3117, 2), (key2693, -6), (key2733, -2), (key2695, -2), (key2836, -2), (key2695, 6)]

def rawRow1658 : Integer.Sparse Key := [(key3051, -2), (key3112, -2), (key3074, -2), (key3051, 2), (key3107, 2), (key3070, 2), (key3055, 2), (key3117, 2), (key3078, 2), (key2693, -6), (key2695, -2), (key2836, -2), (key2733, -2), (key2695, 6)]

def rawRow1659 : Integer.Sparse Key := [(key3112, -2), (key3051, -2), (key3074, -2), (key3107, 2), (key3051, 2), (key3070, 2), (key3117, 2), (key3055, 2), (key3078, 2), (key2693, -6), (key2836, -2), (key2695, -2), (key2733, -2), (key2695, 6)]

def rawRow1660 : Integer.Sparse Key := [(key3074, -2), (key3112, -2), (key3051, -2), (key3070, 2), (key3107, 2), (key3051, 2), (key3078, 2), (key3117, 2), (key3055, 2), (key2693, -6), (key2733, -2), (key2836, -2), (key2695, -2), (key2695, 6)]

def rawRow1661 : Integer.Sparse Key := [(key3112, -2), (key3074, -2), (key3051, -2), (key3107, 2), (key3070, 2), (key3051, 2), (key3117, 2), (key3078, 2), (key3055, 2), (key2693, -6), (key2836, -2), (key2733, -2), (key2695, -2), (key2695, 6)]

def rawRow1662 : Integer.Sparse Key := [(key3107, -2), (key3116, -2), (key3146, -2), (key3112, 2), (key3117, 2), (key3147, 2), (key3051, 2), (key3057, 2), (key3074, 2), (key3112, -6), (key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6)]

def rawRow1663 : Integer.Sparse Key := [(key3116, -2), (key3107, -2), (key3146, -2), (key3117, 2), (key3112, 2), (key3147, 2), (key3057, 2), (key3051, 2), (key3074, 2), (key3112, -6), (key2693, -2), (key2686, -2), (key2719, -2), (key2822, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1664 : Integer.Sparse Key := [(key3107, -2), (key3146, -2), (key3116, -2), (key3112, 2), (key3147, 2), (key3117, 2), (key3051, 2), (key3074, 2), (key3057, 2), (key3112, -6), (key2686, -2), (key2719, -2), (key2693, -2), (key2822, 6)]

def rawRow1665 : Integer.Sparse Key := [(key3146, -2), (key3107, -2), (key3116, -2), (key3147, 2), (key3112, 2), (key3117, 2), (key3074, 2), (key3051, 2), (key3057, 2), (key3112, -6), (key2719, -2), (key2686, -2), (key2693, -2), (key2822, 6)]

def rawRow1666 : Integer.Sparse Key := [(key3116, -2), (key3146, -2), (key3107, -2), (key3117, 2), (key3147, 2), (key3112, 2), (key3057, 2), (key3074, 2), (key3051, 2), (key3112, -6), (key2693, -2), (key2719, -2), (key2686, -2), (key2822, 6)]

def rawRow1667 : Integer.Sparse Key := [(key3146, -2), (key3116, -2), (key3107, -2), (key3147, 2), (key3117, 2), (key3112, 2), (key3074, 2), (key3057, 2), (key3051, 2), (key3112, -6), (key2719, -2), (key2693, -2), (key2686, -2), (key2822, 6)]

def rawRow1668 : Integer.Sparse Key := [(key3055, -2), (key3078, -2), (key3117, -2), (key3057, 2), (key3077, 2), (key3116, 2), (key3051, 2), (key3074, 2), (key3112, 2), (key3057, -6), (key2686, -2), (key2719, -2), (key2822, -2), (key2693, 6)]

def rawRow1669 : Integer.Sparse Key := [(key3078, -2), (key3055, -2), (key3117, -2), (key3077, 2), (key3057, 2), (key3116, 2), (key3074, 2), (key3051, 2), (key3112, 2), (key3057, -6), (key2719, -2), (key2686, -2), (key2822, -2), (key2693, 6)]

def rawRow1670 : Integer.Sparse Key := [(key3055, -2), (key3117, -2), (key3078, -2), (key3057, 2), (key3116, 2), (key3077, 2), (key3051, 2), (key3112, 2), (key3074, 2), (key3057, -6), (key2686, -2), (key2822, -2), (key2719, -2), (key2693, 6)]

def rawRow1671 : Integer.Sparse Key := [(key3117, -2), (key3055, -2), (key3078, -2), (key3116, 2), (key3057, 2), (key3077, 2), (key3112, 2), (key3051, 2), (key3074, 2), (key3057, -6), (key2822, -2), (key2686, -2), (key2719, -2), (key2693, 6)]

def rawRow1672 : Integer.Sparse Key := [(key3078, -2), (key3117, -2), (key3055, -2), (key3077, 2), (key3116, 2), (key3057, 2), (key3074, 2), (key3112, 2), (key3051, 2), (key3057, -6), (key2719, -2), (key2822, -2), (key2686, -2), (key2693, 6)]

def rawRow1673 : Integer.Sparse Key := [(key3117, -2), (key3078, -2), (key3055, -2), (key3116, 2), (key3077, 2), (key3057, 2), (key3112, 2), (key3074, 2), (key3051, 2), (key3057, -6), (key2822, -2), (key2719, -2), (key2686, -2), (key2693, 6)]

def rawRow1674 : Integer.Sparse Key := [(key1316, -2), (key1316, -2), (key1330, -2), (key1296, 1), (key1296, 1), (key1337, 1), (key1337, 1), (key1346, 1), (key1346, 1), (key1546, 2), (key1546, 2), (key1560, 2), (key1391, -1), (key1391, -1), (key1772, -1), (key1772, -1), (key1781, -1), (key1781, -1), (key1573, -1), (key1573, -1), (key1655, -1), (key1655, -1), (key1660, -1), (key1660, -1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1), (key1818, 1), (key1818, 1)]

def rawRow1675 : Integer.Sparse Key := [(key1316, -2), (key1330, -2), (key1316, -2), (key1337, 1), (key1346, 1), (key1296, 1), (key1346, 1), (key1296, 1), (key1337, 1), (key1546, 2), (key1560, 2), (key1546, 2), (key1772, -1), (key1781, -1), (key1391, -1), (key1781, -1), (key1391, -1), (key1772, -1), (key1655, -1), (key1660, -1), (key1573, -1), (key1660, -1), (key1573, -1), (key1655, -1), (key1813, 1), (key1818, 1), (key1424, 1), (key1818, 1), (key1424, 1), (key1813, 1)]

def rawRow1676 : Integer.Sparse Key := [(key1330, -2), (key1316, -2), (key1316, -2), (key1346, 1), (key1337, 1), (key1346, 1), (key1296, 1), (key1337, 1), (key1296, 1), (key1560, 2), (key1546, 2), (key1546, 2), (key1781, -1), (key1772, -1), (key1781, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1660, -1), (key1655, -1), (key1660, -1), (key1573, -1), (key1655, -1), (key1573, -1), (key1818, 1), (key1813, 1), (key1818, 1), (key1424, 1), (key1813, 1), (key1424, 1)]

def rawRow1677 : Integer.Sparse Key := [(key1337, -2), (key1340, -2), (key1346, -2), (key1296, 1), (key1303, 1), (key1316, 1), (key1340, 1), (key1330, 1), (key1346, 1), (key1772, 2), (key1775, 2), (key1781, 2), (key1391, -1), (key1398, -1), (key1546, -1), (key1775, -1), (key1560, -1), (key1781, -1), (key1788, -1), (key1791, -1), (key1813, -1), (key1840, -1), (key1818, -1), (key1842, -1), (key1455, 1), (key1458, 1), (key1655, 1), (key1840, 1), (key1660, 1), (key1842, 1)]

def rawRow1678 : Integer.Sparse Key := [(key1340, -2), (key1337, -2), (key1346, -2), (key1303, 1), (key1296, 1), (key1340, 1), (key1316, 1), (key1346, 1), (key1330, 1), (key1775, 2), (key1772, 2), (key1781, 2), (key1398, -1), (key1391, -1), (key1775, -1), (key1546, -1), (key1781, -1), (key1560, -1), (key1791, -1), (key1788, -1), (key1840, -1), (key1813, -1), (key1842, -1), (key1818, -1), (key1458, 1), (key1455, 1), (key1840, 1), (key1655, 1), (key1842, 1), (key1660, 1)]

def rawRow1679 : Integer.Sparse Key := [(key1337, -2), (key1346, -2), (key1340, -2), (key1316, 1), (key1330, 1), (key1296, 1), (key1346, 1), (key1303, 1), (key1340, 1), (key1772, 2), (key1781, 2), (key1775, 2), (key1546, -1), (key1560, -1), (key1391, -1), (key1781, -1), (key1398, -1), (key1775, -1), (key1813, -1), (key1818, -1), (key1788, -1), (key1842, -1), (key1791, -1), (key1840, -1), (key1655, 1), (key1660, 1), (key1455, 1), (key1842, 1), (key1458, 1), (key1840, 1)]

def rawRow1680 : Integer.Sparse Key := [(key1346, -2), (key1337, -2), (key1340, -2), (key1330, 1), (key1316, 1), (key1346, 1), (key1296, 1), (key1340, 1), (key1303, 1), (key1781, 2), (key1772, 2), (key1775, 2), (key1560, -1), (key1546, -1), (key1781, -1), (key1391, -1), (key1775, -1), (key1398, -1), (key1818, -1), (key1813, -1), (key1842, -1), (key1788, -1), (key1840, -1), (key1791, -1), (key1660, 1), (key1655, 1), (key1842, 1), (key1455, 1), (key1840, 1), (key1458, 1)]

def rawRow1681 : Integer.Sparse Key := [(key1340, -2), (key1346, -2), (key1337, -2), (key1340, 1), (key1346, 1), (key1303, 1), (key1330, 1), (key1296, 1), (key1316, 1), (key1775, 2), (key1781, 2), (key1772, 2), (key1775, -1), (key1781, -1), (key1398, -1), (key1560, -1), (key1391, -1), (key1546, -1), (key1840, -1), (key1842, -1), (key1791, -1), (key1818, -1), (key1788, -1), (key1813, -1), (key1840, 1), (key1842, 1), (key1458, 1), (key1660, 1), (key1455, 1), (key1655, 1)]

def rawRow1682 : Integer.Sparse Key := [(key1346, -2), (key1340, -2), (key1337, -2), (key1346, 1), (key1340, 1), (key1330, 1), (key1303, 1), (key1316, 1), (key1296, 1), (key1781, 2), (key1775, 2), (key1772, 2), (key1781, -1), (key1775, -1), (key1560, -1), (key1398, -1), (key1546, -1), (key1391, -1), (key1842, -1), (key1840, -1), (key1818, -1), (key1791, -1), (key1813, -1), (key1788, -1), (key1842, 1), (key1840, 1), (key1660, 1), (key1458, 1), (key1655, 1), (key1455, 1)]

def rawRow1683 : Integer.Sparse Key := [(key1546, -2), (key1546, -2), (key1560, -2), (key1573, 1), (key1573, 1), (key1655, 1), (key1655, 1), (key1660, 1), (key1660, 1), (key1316, 2), (key1316, 2), (key1330, 2), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1818, -1), (key1818, -1), (key1296, -1), (key1296, -1), (key1337, -1), (key1337, -1), (key1346, -1), (key1346, -1), (key1391, 1), (key1391, 1), (key1772, 1), (key1772, 1), (key1781, 1), (key1781, 1)]

def rawRow1684 : Integer.Sparse Key := [(key1546, -2), (key1560, -2), (key1546, -2), (key1655, 1), (key1660, 1), (key1573, 1), (key1660, 1), (key1573, 1), (key1655, 1), (key1316, 2), (key1330, 2), (key1316, 2), (key1813, -1), (key1818, -1), (key1424, -1), (key1818, -1), (key1424, -1), (key1813, -1), (key1337, -1), (key1346, -1), (key1296, -1), (key1346, -1), (key1296, -1), (key1337, -1), (key1772, 1), (key1781, 1), (key1391, 1), (key1781, 1), (key1391, 1), (key1772, 1)]

def rawRow1685 : Integer.Sparse Key := [(key1560, -2), (key1546, -2), (key1546, -2), (key1660, 1), (key1655, 1), (key1660, 1), (key1573, 1), (key1655, 1), (key1573, 1), (key1330, 2), (key1316, 2), (key1316, 2), (key1818, -1), (key1813, -1), (key1818, -1), (key1424, -1), (key1813, -1), (key1424, -1), (key1346, -1), (key1337, -1), (key1346, -1), (key1296, -1), (key1337, -1), (key1296, -1), (key1781, 1), (key1772, 1), (key1781, 1), (key1391, 1), (key1772, 1), (key1391, 1)]

def rawRow1686 : Integer.Sparse Key := [(key1655, -2), (key1660, -2), (key1668, -2), (key1546, 1), (key1560, 1), (key1573, 1), (key1660, 1), (key1597, 1), (key1668, 1), (key1813, 2), (key1818, 2), (key1826, 2), (key1316, -1), (key1330, -1), (key1424, -1), (key1818, -1), (key1448, -1), (key1826, -1), (key1772, -1), (key1781, -1), (key1788, -1), (key1842, -1), (key1799, -1), (key1845, -1), (key1337, 1), (key1346, 1), (key1455, 1), (key1842, 1), (key1467, 1), (key1845, 1)]

def rawRow1687 : Integer.Sparse Key := [(key1660, -2), (key1655, -2), (key1668, -2), (key1560, 1), (key1546, 1), (key1660, 1), (key1573, 1), (key1668, 1), (key1597, 1), (key1818, 2), (key1813, 2), (key1826, 2), (key1330, -1), (key1316, -1), (key1818, -1), (key1424, -1), (key1826, -1), (key1448, -1), (key1781, -1), (key1772, -1), (key1842, -1), (key1788, -1), (key1845, -1), (key1799, -1), (key1346, 1), (key1337, 1), (key1842, 1), (key1455, 1), (key1845, 1), (key1467, 1)]

def rawRow1688 : Integer.Sparse Key := [(key1655, -2), (key1668, -2), (key1660, -2), (key1573, 1), (key1597, 1), (key1546, 1), (key1668, 1), (key1560, 1), (key1660, 1), (key1813, 2), (key1826, 2), (key1818, 2), (key1424, -1), (key1448, -1), (key1316, -1), (key1826, -1), (key1330, -1), (key1818, -1), (key1788, -1), (key1799, -1), (key1772, -1), (key1845, -1), (key1781, -1), (key1842, -1), (key1455, 1), (key1467, 1), (key1337, 1), (key1845, 1), (key1346, 1), (key1842, 1)]

end MUB6.Certificate.GramRows

end OAI
end


