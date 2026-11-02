-- Prove2me | Definitions.Def_OAIQ106D171
-- name    : OAIQ106D171
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:35:05.718362+00:00
-- url     : https://prove2.me/theorems/a2a76316-54c8-4a3c-9a4f-9df97974d726
-- title:
--   Definitions bundle OAIQ106D171 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 523 declarations of OpenAI's Lean: 523 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow386`, `OAI.MUB6.Certificate.GramRows.rawRow3864`, `OAI.MUB6.Certificate.GramRows.rawRow3865`, `OAI.MUB6.Certificate.GramRows.rawRow3866`, `OAI.MUB6.Certificate.GramRows.rawRow3867`, `OAI.MUB6.Certificate.GramRows.rawRow3868`, `OAI.MUB6.Certificate.GramRows.rawRow3869`, `OAI.MUB6.Certificate.GramRows.rawRow387`, `OAI.MUB6.Certificate.GramRows.rawRow3870`, `OAI.MUB6.Certificate.GramRows.rawRow3871`, `OAI.MUB6.Certificate.GramRows.rawRow3872`, `OAI.MUB6.Certificate.GramRows.rawRow3873`, `OAI.MUB6.Certificate.GramRows.rawRow3874`, `OAI.MUB6.Certificate.GramRows.rawRow3878`, `OAI.MUB6.Certificate.GramRows.rawRow3879`, `OAI.MUB6.Certificate.GramRows.rawRow3880`, `OAI.MUB6.Certificate.GramRows.rawRow3881`, `OAI.MUB6.Certificate.GramRows.rawRow3882`, `OAI.MUB6.Certificate.GramRows.rawRow3883`, `OAI.MUB6.Certificate.GramRows.rawRow3884`, `OAI.MUB6.Certificate.GramRows.rawRow3885`, `OAI.MUB6.Certificate.GramRows.rawRow3886`, `OAI.MUB6.Certificate.GramRows.rawRow3887`, `OAI.MUB6.Certificate.GramRows.rawRow3888`, `OAI.MUB6.Certificate.GramRows.rawRow3889`, `OAI.MUB6.Certificate.GramRows.rawRow389`, `OAI.MUB6.Certificate.GramRows.rawRow3890`, `OAI.MUB6.Certificate.GramRows.rawRow3891`, `OAI.MUB6.Certificate.GramRows.rawRow3892`, `OAI.MUB6.Certificate.GramRows.rawRow3893`, `OAI.MUB6.Certificate.GramRows.rawRow3894`, `OAI.MUB6.Certificate.GramRows.rawRow3895`, `OAI.MUB6.Certificate.GramRows.rawRow3896`, `OAI.MUB6.Certificate.GramRows.rawRow3897`, `OAI.MUB6.Certificate.GramRows.rawRow3898`, `OAI.MUB6.Certificate.GramRows.rawRow3899`, `OAI.MUB6.Certificate.GramRows.rawRow39`, `OAI.MUB6.Certificate.GramRows.rawRow390`, `OAI.MUB6.Certificate.GramRows.rawRow3900`, `OAI.MUB6.Certificate.GramRows.rawRow3901` and 483 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block10.lean), [`MutuallyUnbiased_GramRows_Block11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block11.lean), [`MutuallyUnbiased_GramRows_Block54`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block54.lean), [`MutuallyUnbiased_GramRows_Block55`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block55.lean), [`MutuallyUnbiased_GramRows_Block56`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block56.lean), [`MutuallyUnbiased_GramRows_Block57`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block57.lean), [`MutuallyUnbiased_GramRows_Block58`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block58.lean), [`MutuallyUnbiased_GramRows_Block59`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block59.lean), [`MutuallyUnbiased_GramRows_Block9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block9.lean), [`MutuallyUnbiased_GramRows_Block93`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block93.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D086`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval3_3`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_13`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_14`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_13`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow18`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow19`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D086
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D092
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

def rawRow4 : Integer.Sparse Key := [(key251, -1), (key248, -1), (key260, 2), (key239, 1), (key236, 1), (key271, -1), (key267, -1), (key239, -2), (key260, 1), (key251, 1), (key319, 1), (key316, 1), (key335, -2), (key305, -1), (key302, -1), (key340, 1), (key335, 1), (key305, 2), (key328, -1), (key319, -1), (key409, -1), (key406, -1), (key469, 1), (key467, 1), (key388, 1), (key385, 1), (key475, -1), (key467, -1), (key397, -1), (key388, -1), (key418, 1), (key409, 1), (key578, 2), (key595, -1), (key593, -1), (key568, -2), (key601, 1), (key593, 1), (key572, 1), (key568, 1), (key583, -1), (key578, -1)]

def rawRow39 : Integer.Sparse Key := [(key595, -1), (key593, -1), (key601, 2), (key572, 1), (key568, 1), (key601, -1), (key583, -1), (key568, -2), (key593, 1), (key578, 1), (key469, 1), (key467, 1), (key475, -2), (key271, -1), (key267, -1), (key475, 1), (key340, 1), (key267, 2), (key467, -1), (key335, -1), (key397, -1), (key388, -1), (key450, 1), (key418, 1), (key260, 1), (key251, 1), (key450, -1), (key328, -1), (key251, -1), (key239, -1), (key388, 1), (key305, 1), (key385, 2), (key435, -1), (key406, -1), (key248, -2), (key435, 1), (key316, 1), (key248, 1), (key236, 1), (key316, -1), (key302, -1)]

def rawRow43 : Integer.Sparse Key := [(key1296, -1), (key1302, -1), (key1296, 2), (key1337, 1), (key1339, 1), (key1316, -1), (key1337, -1), (key1345, -2), (key1329, 1), (key1345, 1), (key1391, 1), (key1397, 1), (key1391, -2), (key1772, -1), (key1774, -1), (key1546, 1), (key1772, 1), (key1780, 2), (key1559, -1), (key1780, -1), (key1455, -1), (key1457, -1), (key1424, 1), (key1455, 1), (key1788, 1), (key1790, 1), (key1573, -1), (key1788, -1), (key1817, -1), (key1841, -1), (key1659, 1), (key1841, 1), (key1466, 2), (key1447, -1), (key1466, -1), (key1798, -2), (key1596, 1), (key1798, 1), (key1825, 1), (key1844, 1), (key1667, -1), (key1844, -1)]

def rawRow44 : Integer.Sparse Key := [(key1302, -1), (key1296, -1), (key1296, 2), (key1339, 1), (key1337, 1), (key1337, -1), (key1316, -1), (key1345, -2), (key1345, 1), (key1329, 1), (key1397, 1), (key1391, 1), (key1391, -2), (key1774, -1), (key1772, -1), (key1772, 1), (key1546, 1), (key1780, 2), (key1780, -1), (key1559, -1), (key1457, -1), (key1455, -1), (key1455, 1), (key1424, 1), (key1790, 1), (key1788, 1), (key1788, -1), (key1573, -1), (key1841, -1), (key1817, -1), (key1841, 1), (key1659, 1), (key1466, 2), (key1466, -1), (key1447, -1), (key1798, -2), (key1798, 1), (key1596, 1), (key1844, 1), (key1825, 1), (key1844, -1), (key1667, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow416 : Integer.Sparse Key := [(key599, -2), (key605, 1), (key611, 1), (key576, 2), (key587, -1), (key616, -1), (key571, -1), (key577, -1), (key581, 1), (key613, 1), (key473, 2), (key479, -1), (key485, -1), (key275, -2), (key344, 1), (key616, 1), (key270, 1), (key276, 1), (key338, -1), (key613, -1), (key403, -2), (key424, 1), (key485, 1), (key266, 2), (key334, -1), (key611, -1), (key245, -1), (key276, -1), (key311, 1), (key577, 1), (key392, 1), (key403, 1), (key413, -1), (key473, -1), (key255, -1), (key266, -1), (key323, 1), (key599, 1), (key243, 1), (key275, 1), (key309, -1), (key344, -1)]

def rawRow417 : Integer.Sparse Key := [(key599, -2), (key611, 1), (key605, 1), (key576, 2), (key616, -1), (key587, -1), (key577, -1), (key571, -1), (key613, 1), (key581, 1), (key473, 2), (key485, -1), (key479, -1), (key275, -2), (key616, 1), (key344, 1), (key276, 1), (key270, 1), (key613, -1), (key338, -1), (key403, -2), (key485, 1), (key424, 1), (key266, 2), (key611, -1), (key334, -1), (key276, -1), (key245, -1), (key577, 1), (key311, 1), (key403, 1), (key392, 1), (key473, -1), (key413, -1), (key266, -1), (key255, -1), (key599, 1), (key323, 1), (key275, 1), (key243, 1), (key344, -1), (key309, -1)]

def rawRow418 : Integer.Sparse Key := [(key605, -2), (key599, 1), (key611, 1), (key587, 2), (key576, -1), (key616, -1), (key581, -1), (key588, -1), (key571, 1), (key614, 1), (key479, 2), (key473, -1), (key485, -1), (key344, -2), (key275, 1), (key616, 1), (key338, 1), (key345, 1), (key270, -1), (key614, -1), (key424, -2), (key403, 1), (key485, 1), (key334, 2), (key266, -1), (key611, -1), (key311, -1), (key345, -1), (key245, 1), (key588, 1), (key413, 1), (key424, 1), (key392, -1), (key479, -1), (key323, -1), (key334, -1), (key255, 1), (key605, 1), (key309, 1), (key344, 1), (key243, -1), (key587, -1)]

def rawRow419 : Integer.Sparse Key := [(key605, -2), (key611, 1), (key599, 1), (key587, 2), (key616, -1), (key576, -1), (key588, -1), (key581, -1), (key614, 1), (key571, 1), (key479, 2), (key485, -1), (key473, -1), (key344, -2), (key616, 1), (key275, 1), (key345, 1), (key338, 1), (key614, -1), (key270, -1), (key424, -2), (key485, 1), (key403, 1), (key334, 2), (key611, -1), (key266, -1), (key345, -1), (key311, -1), (key588, 1), (key245, 1), (key424, 1), (key413, 1), (key479, -1), (key392, -1), (key334, -1), (key323, -1), (key605, 1), (key255, 1), (key344, 1), (key309, 1), (key587, -1), (key243, -1)]

def rawRow420 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1295, 2), (key1311, 1), (key1315, 1), (key1315, -1), (key1336, -1), (key1324, -2), (key1324, 1), (key1343, 1), (key1386, 1), (key1390, 1), (key1390, -2), (key1541, -1), (key1545, -1), (key1545, 1), (key1771, 1), (key1554, 2), (key1554, -1), (key1778, -1), (key1419, -1), (key1423, -1), (key1423, 1), (key1454, 1), (key1568, 1), (key1572, 1), (key1572, -1), (key1787, -1), (key1622, -1), (key1657, -1), (key1622, 1), (key1815, 1), (key1442, 2), (key1442, -1), (key1464, -1), (key1591, -2), (key1591, 1), (key1796, 1), (key1631, 1), (key1665, 1), (key1631, -1), (key1823, -1)]

def rawRow421 : Integer.Sparse Key := [(key1295, -1), (key1291, -1), (key1295, 2), (key1315, 1), (key1311, 1), (key1336, -1), (key1315, -1), (key1324, -2), (key1343, 1), (key1324, 1), (key1390, 1), (key1386, 1), (key1390, -2), (key1545, -1), (key1541, -1), (key1771, 1), (key1545, 1), (key1554, 2), (key1778, -1), (key1554, -1), (key1423, -1), (key1419, -1), (key1454, 1), (key1423, 1), (key1572, 1), (key1568, 1), (key1787, -1), (key1572, -1), (key1657, -1), (key1622, -1), (key1815, 1), (key1622, 1), (key1442, 2), (key1464, -1), (key1442, -1), (key1591, -2), (key1796, 1), (key1591, 1), (key1665, 1), (key1631, 1), (key1823, -1), (key1631, -1)]

def rawRow423 : Integer.Sparse Key := [(key1311, -1), (key1315, -1), (key1324, 2), (key1291, 1), (key1295, 1), (key1324, -1), (key1343, -1), (key1295, -2), (key1315, 1), (key1336, 1), (key1541, 1), (key1545, 1), (key1554, -2), (key1386, -1), (key1390, -1), (key1554, 1), (key1778, 1), (key1390, 2), (key1545, -1), (key1771, -1), (key1568, -1), (key1572, -1), (key1622, 1), (key1657, 1), (key1419, 1), (key1423, 1), (key1622, -1), (key1815, -1), (key1423, -1), (key1454, -1), (key1572, 1), (key1787, 1), (key1591, 2), (key1631, -1), (key1665, -1), (key1442, -2), (key1631, 1), (key1823, 1), (key1442, 1), (key1464, 1), (key1591, -1), (key1796, -1)]

def rawRow424 : Integer.Sparse Key := [(key1315, -1), (key1311, -1), (key1324, 2), (key1295, 1), (key1291, 1), (key1343, -1), (key1324, -1), (key1295, -2), (key1336, 1), (key1315, 1), (key1545, 1), (key1541, 1), (key1554, -2), (key1390, -1), (key1386, -1), (key1778, 1), (key1554, 1), (key1390, 2), (key1771, -1), (key1545, -1), (key1572, -1), (key1568, -1), (key1657, 1), (key1622, 1), (key1423, 1), (key1419, 1), (key1815, -1), (key1622, -1), (key1454, -1), (key1423, -1), (key1787, 1), (key1572, 1), (key1591, 2), (key1665, -1), (key1631, -1), (key1442, -2), (key1823, 1), (key1631, 1), (key1464, 1), (key1442, 1), (key1796, -1), (key1591, -1)]

def rawRow425 : Integer.Sparse Key := [(key1315, -1), (key1324, -1), (key1311, 2), (key1336, 1), (key1343, 1), (key1291, -1), (key1311, -1), (key1336, -2), (key1295, 1), (key1315, 1), (key1545, 1), (key1554, 1), (key1541, -2), (key1771, -1), (key1778, -1), (key1386, 1), (key1541, 1), (key1771, 2), (key1390, -1), (key1545, -1), (key1654, -1), (key1657, -1), (key1568, 1), (key1617, 1), (key1812, 1), (key1815, 1), (key1419, -1), (key1617, -1), (key1787, -1), (key1812, -1), (key1454, 1), (key1654, 1), (key1665, 2), (key1591, -1), (key1631, -1), (key1823, -2), (key1442, 1), (key1631, 1), (key1796, 1), (key1823, 1), (key1464, -1), (key1665, -1)]

def rawRow426 : Integer.Sparse Key := [(key1324, -1), (key1315, -1), (key1311, 2), (key1343, 1), (key1336, 1), (key1311, -1), (key1291, -1), (key1336, -2), (key1315, 1), (key1295, 1), (key1554, 1), (key1545, 1), (key1541, -2), (key1778, -1), (key1771, -1), (key1541, 1), (key1386, 1), (key1771, 2), (key1545, -1), (key1390, -1), (key1657, -1), (key1654, -1), (key1617, 1), (key1568, 1), (key1815, 1), (key1812, 1), (key1617, -1), (key1419, -1), (key1812, -1), (key1787, -1), (key1654, 1), (key1454, 1), (key1665, 2), (key1631, -1), (key1591, -1), (key1823, -2), (key1631, 1), (key1442, 1), (key1823, 1), (key1796, 1), (key1665, -1), (key1464, -1)]

def rawRow428 : Integer.Sparse Key := [(key1336, -1), (key1343, -1), (key1336, 2), (key1315, 1), (key1324, 1), (key1295, -1), (key1315, -1), (key1311, -2), (key1291, 1), (key1311, 1), (key1771, 1), (key1778, 1), (key1771, -2), (key1545, -1), (key1554, -1), (key1390, 1), (key1545, 1), (key1541, 2), (key1386, -1), (key1541, -1), (key1812, -1), (key1815, -1), (key1787, 1), (key1812, 1), (key1654, 1), (key1657, 1), (key1454, -1), (key1654, -1), (key1568, -1), (key1617, -1), (key1419, 1), (key1617, 1), (key1823, 2), (key1796, -1), (key1823, -1), (key1665, -2), (key1464, 1), (key1665, 1), (key1591, 1), (key1631, 1), (key1442, -1), (key1631, -1)]

def rawRow429 : Integer.Sparse Key := [(key1343, -1), (key1336, -1), (key1336, 2), (key1324, 1), (key1315, 1), (key1315, -1), (key1295, -1), (key1311, -2), (key1311, 1), (key1291, 1), (key1778, 1), (key1771, 1), (key1771, -2), (key1554, -1), (key1545, -1), (key1545, 1), (key1390, 1), (key1541, 2), (key1541, -1), (key1386, -1), (key1815, -1), (key1812, -1), (key1812, 1), (key1787, 1), (key1657, 1), (key1654, 1), (key1654, -1), (key1454, -1), (key1617, -1), (key1568, -1), (key1617, 1), (key1419, 1), (key1823, 2), (key1823, -1), (key1796, -1), (key1665, -2), (key1665, 1), (key1464, 1), (key1631, 1), (key1591, 1), (key1631, -1), (key1442, -1)]

def rawRow430 : Integer.Sparse Key := [(key1386, -1), (key1390, -1), (key1390, 2), (key1419, 1), (key1423, 1), (key1423, -1), (key1454, -1), (key1442, -2), (key1442, 1), (key1464, 1), (key1291, 1), (key1295, 1), (key1295, -2), (key1568, -1), (key1572, -1), (key1572, 1), (key1787, 1), (key1591, 2), (key1591, -1), (key1796, -1), (key1311, -1), (key1315, -1), (key1315, 1), (key1336, 1), (key1541, 1), (key1545, 1), (key1545, -1), (key1771, -1), (key1631, -1), (key1665, -1), (key1631, 1), (key1823, 1), (key1324, 2), (key1324, -1), (key1343, -1), (key1554, -2), (key1554, 1), (key1778, 1), (key1622, 1), (key1657, 1), (key1622, -1), (key1815, -1)]

def rawRow431 : Integer.Sparse Key := [(key1390, -1), (key1386, -1), (key1390, 2), (key1423, 1), (key1419, 1), (key1454, -1), (key1423, -1), (key1442, -2), (key1464, 1), (key1442, 1), (key1295, 1), (key1291, 1), (key1295, -2), (key1572, -1), (key1568, -1), (key1787, 1), (key1572, 1), (key1591, 2), (key1796, -1), (key1591, -1), (key1315, -1), (key1311, -1), (key1336, 1), (key1315, 1), (key1545, 1), (key1541, 1), (key1771, -1), (key1545, -1), (key1665, -1), (key1631, -1), (key1823, 1), (key1631, 1), (key1324, 2), (key1343, -1), (key1324, -1), (key1554, -2), (key1778, 1), (key1554, 1), (key1657, 1), (key1622, 1), (key1815, -1), (key1622, -1)]

def rawRow433 : Integer.Sparse Key := [(key1419, -1), (key1423, -1), (key1442, 2), (key1386, 1), (key1390, 1), (key1442, -1), (key1464, -1), (key1390, -2), (key1423, 1), (key1454, 1), (key1568, 1), (key1572, 1), (key1591, -2), (key1291, -1), (key1295, -1), (key1591, 1), (key1796, 1), (key1295, 2), (key1572, -1), (key1787, -1), (key1541, -1), (key1545, -1), (key1631, 1), (key1665, 1), (key1311, 1), (key1315, 1), (key1631, -1), (key1823, -1), (key1315, -1), (key1336, -1), (key1545, 1), (key1771, 1), (key1554, 2), (key1622, -1), (key1657, -1), (key1324, -2), (key1622, 1), (key1815, 1), (key1324, 1), (key1343, 1), (key1554, -1), (key1778, -1)]

def rawRow434 : Integer.Sparse Key := [(key1423, -1), (key1419, -1), (key1442, 2), (key1390, 1), (key1386, 1), (key1464, -1), (key1442, -1), (key1390, -2), (key1454, 1), (key1423, 1), (key1572, 1), (key1568, 1), (key1591, -2), (key1295, -1), (key1291, -1), (key1796, 1), (key1591, 1), (key1295, 2), (key1787, -1), (key1572, -1), (key1545, -1), (key1541, -1), (key1665, 1), (key1631, 1), (key1315, 1), (key1311, 1), (key1823, -1), (key1631, -1), (key1336, -1), (key1315, -1), (key1771, 1), (key1545, 1), (key1554, 2), (key1657, -1), (key1622, -1), (key1324, -2), (key1815, 1), (key1622, 1), (key1343, 1), (key1324, 1), (key1778, -1), (key1554, -1)]

def rawRow435 : Integer.Sparse Key := [(key1423, -1), (key1442, -1), (key1419, 2), (key1454, 1), (key1464, 1), (key1386, -1), (key1419, -1), (key1454, -2), (key1390, 1), (key1423, 1), (key1572, 1), (key1591, 1), (key1568, -2), (key1787, -1), (key1796, -1), (key1291, 1), (key1568, 1), (key1787, 2), (key1295, -1), (key1572, -1), (key1654, -1), (key1665, -1), (key1541, 1), (key1617, 1), (key1812, 1), (key1823, 1), (key1311, -1), (key1617, -1), (key1771, -1), (key1812, -1), (key1336, 1), (key1654, 1), (key1657, 2), (key1554, -1), (key1622, -1), (key1815, -2), (key1324, 1), (key1622, 1), (key1778, 1), (key1815, 1), (key1343, -1), (key1657, -1)]

def rawRow436 : Integer.Sparse Key := [(key1442, -1), (key1423, -1), (key1419, 2), (key1464, 1), (key1454, 1), (key1419, -1), (key1386, -1), (key1454, -2), (key1423, 1), (key1390, 1), (key1591, 1), (key1572, 1), (key1568, -2), (key1796, -1), (key1787, -1), (key1568, 1), (key1291, 1), (key1787, 2), (key1572, -1), (key1295, -1), (key1665, -1), (key1654, -1), (key1617, 1), (key1541, 1), (key1823, 1), (key1812, 1), (key1617, -1), (key1311, -1), (key1812, -1), (key1771, -1), (key1654, 1), (key1336, 1), (key1657, 2), (key1622, -1), (key1554, -1), (key1815, -2), (key1622, 1), (key1324, 1), (key1815, 1), (key1778, 1), (key1657, -1), (key1343, -1)]

def rawRow438 : Integer.Sparse Key := [(key1454, -1), (key1464, -1), (key1454, 2), (key1423, 1), (key1442, 1), (key1390, -1), (key1423, -1), (key1419, -2), (key1386, 1), (key1419, 1), (key1787, 1), (key1796, 1), (key1787, -2), (key1572, -1), (key1591, -1), (key1295, 1), (key1572, 1), (key1568, 2), (key1291, -1), (key1568, -1), (key1812, -1), (key1823, -1), (key1771, 1), (key1812, 1), (key1654, 1), (key1665, 1), (key1336, -1), (key1654, -1), (key1541, -1), (key1617, -1), (key1311, 1), (key1617, 1), (key1815, 2), (key1778, -1), (key1815, -1), (key1657, -2), (key1343, 1), (key1657, 1), (key1554, 1), (key1622, 1), (key1324, -1), (key1622, -1)]

def rawRow439 : Integer.Sparse Key := [(key1464, -1), (key1454, -1), (key1454, 2), (key1442, 1), (key1423, 1), (key1423, -1), (key1390, -1), (key1419, -2), (key1419, 1), (key1386, 1), (key1796, 1), (key1787, 1), (key1787, -2), (key1591, -1), (key1572, -1), (key1572, 1), (key1295, 1), (key1568, 2), (key1568, -1), (key1291, -1), (key1823, -1), (key1812, -1), (key1812, 1), (key1771, 1), (key1665, 1), (key1654, 1), (key1654, -1), (key1336, -1), (key1617, -1), (key1541, -1), (key1617, 1), (key1311, 1), (key1815, 2), (key1815, -1), (key1778, -1), (key1657, -2), (key1657, 1), (key1343, 1), (key1622, 1), (key1554, 1), (key1622, -1), (key1324, -1)]

def rawRow440 : Integer.Sparse Key := [(key1541, -1), (key1545, -1), (key1554, 2), (key1568, 1), (key1572, 1), (key1622, -1), (key1657, -1), (key1591, -2), (key1631, 1), (key1665, 1), (key1311, 1), (key1315, 1), (key1324, -2), (key1419, -1), (key1423, -1), (key1622, 1), (key1815, 1), (key1442, 2), (key1631, -1), (key1823, -1), (key1291, -1), (key1295, -1), (key1324, 1), (key1343, 1), (key1386, 1), (key1390, 1), (key1554, -1), (key1778, -1), (key1442, -1), (key1464, -1), (key1591, 1), (key1796, 1), (key1295, 2), (key1315, -1), (key1336, -1), (key1390, -2), (key1545, 1), (key1771, 1), (key1423, 1), (key1454, 1), (key1572, -1), (key1787, -1)]

def rawRow441 : Integer.Sparse Key := [(key1545, -1), (key1541, -1), (key1554, 2), (key1572, 1), (key1568, 1), (key1657, -1), (key1622, -1), (key1591, -2), (key1665, 1), (key1631, 1), (key1315, 1), (key1311, 1), (key1324, -2), (key1423, -1), (key1419, -1), (key1815, 1), (key1622, 1), (key1442, 2), (key1823, -1), (key1631, -1), (key1295, -1), (key1291, -1), (key1343, 1), (key1324, 1), (key1390, 1), (key1386, 1), (key1778, -1), (key1554, -1), (key1464, -1), (key1442, -1), (key1796, 1), (key1591, 1), (key1295, 2), (key1336, -1), (key1315, -1), (key1390, -2), (key1771, 1), (key1545, 1), (key1454, 1), (key1423, 1), (key1787, -1), (key1572, -1)]

def rawRow442 : Integer.Sparse Key := [(key1545, -1), (key1554, -1), (key1541, 2), (key1654, 1), (key1657, 1), (key1568, -1), (key1617, -1), (key1665, -2), (key1591, 1), (key1631, 1), (key1315, 1), (key1324, 1), (key1311, -2), (key1812, -1), (key1815, -1), (key1419, 1), (key1617, 1), (key1823, 2), (key1442, -1), (key1631, -1), (key1336, -1), (key1343, -1), (key1291, 1), (key1311, 1), (key1771, 1), (key1778, 1), (key1386, -1), (key1541, -1), (key1796, -1), (key1823, -1), (key1464, 1), (key1665, 1), (key1336, 2), (key1295, -1), (key1315, -1), (key1771, -2), (key1390, 1), (key1545, 1), (key1787, 1), (key1812, 1), (key1454, -1), (key1654, -1)]

def rawRow443 : Integer.Sparse Key := [(key1554, -1), (key1545, -1), (key1541, 2), (key1657, 1), (key1654, 1), (key1617, -1), (key1568, -1), (key1665, -2), (key1631, 1), (key1591, 1), (key1324, 1), (key1315, 1), (key1311, -2), (key1815, -1), (key1812, -1), (key1617, 1), (key1419, 1), (key1823, 2), (key1631, -1), (key1442, -1), (key1343, -1), (key1336, -1), (key1311, 1), (key1291, 1), (key1778, 1), (key1771, 1), (key1541, -1), (key1386, -1), (key1823, -1), (key1796, -1), (key1665, 1), (key1464, 1), (key1336, 2), (key1315, -1), (key1295, -1), (key1771, -2), (key1545, 1), (key1390, 1), (key1812, 1), (key1787, 1), (key1654, -1), (key1454, -1)]

def rawRow444 : Integer.Sparse Key := [(key1568, -1), (key1572, -1), (key1591, 2), (key1541, 1), (key1545, 1), (key1631, -1), (key1665, -1), (key1554, -2), (key1622, 1), (key1657, 1), (key1419, 1), (key1423, 1), (key1442, -2), (key1311, -1), (key1315, -1), (key1631, 1), (key1823, 1), (key1324, 2), (key1622, -1), (key1815, -1), (key1386, -1), (key1390, -1), (key1442, 1), (key1464, 1), (key1291, 1), (key1295, 1), (key1591, -1), (key1796, -1), (key1324, -1), (key1343, -1), (key1554, 1), (key1778, 1), (key1390, 2), (key1423, -1), (key1454, -1), (key1295, -2), (key1572, 1), (key1787, 1), (key1315, 1), (key1336, 1), (key1545, -1), (key1771, -1)]

def rawRow445 : Integer.Sparse Key := [(key1572, -1), (key1568, -1), (key1591, 2), (key1545, 1), (key1541, 1), (key1665, -1), (key1631, -1), (key1554, -2), (key1657, 1), (key1622, 1), (key1423, 1), (key1419, 1), (key1442, -2), (key1315, -1), (key1311, -1), (key1823, 1), (key1631, 1), (key1324, 2), (key1815, -1), (key1622, -1), (key1390, -1), (key1386, -1), (key1464, 1), (key1442, 1), (key1295, 1), (key1291, 1), (key1796, -1), (key1591, -1), (key1343, -1), (key1324, -1), (key1778, 1), (key1554, 1), (key1390, 2), (key1454, -1), (key1423, -1), (key1295, -2), (key1787, 1), (key1572, 1), (key1336, 1), (key1315, 1), (key1771, -1), (key1545, -1)]

def rawRow446 : Integer.Sparse Key := [(key1572, -1), (key1591, -1), (key1568, 2), (key1654, 1), (key1665, 1), (key1541, -1), (key1617, -1), (key1657, -2), (key1554, 1), (key1622, 1), (key1423, 1), (key1442, 1), (key1419, -2), (key1812, -1), (key1823, -1), (key1311, 1), (key1617, 1), (key1815, 2), (key1324, -1), (key1622, -1), (key1454, -1), (key1464, -1), (key1386, 1), (key1419, 1), (key1787, 1), (key1796, 1), (key1291, -1), (key1568, -1), (key1778, -1), (key1815, -1), (key1343, 1), (key1657, 1), (key1454, 2), (key1390, -1), (key1423, -1), (key1787, -2), (key1295, 1), (key1572, 1), (key1771, 1), (key1812, 1), (key1336, -1), (key1654, -1)]

def rawRow447 : Integer.Sparse Key := [(key1591, -1), (key1572, -1), (key1568, 2), (key1665, 1), (key1654, 1), (key1617, -1), (key1541, -1), (key1657, -2), (key1622, 1), (key1554, 1), (key1442, 1), (key1423, 1), (key1419, -2), (key1823, -1), (key1812, -1), (key1617, 1), (key1311, 1), (key1815, 2), (key1622, -1), (key1324, -1), (key1464, -1), (key1454, -1), (key1419, 1), (key1386, 1), (key1796, 1), (key1787, 1), (key1568, -1), (key1291, -1), (key1815, -1), (key1778, -1), (key1657, 1), (key1343, 1), (key1454, 2), (key1423, -1), (key1390, -1), (key1787, -2), (key1572, 1), (key1295, 1), (key1812, 1), (key1771, 1), (key1654, -1), (key1336, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow448 : Integer.Sparse Key := [(key1654, -1), (key1657, -1), (key1665, 2), (key1545, 1), (key1554, 1), (key1591, -1), (key1631, -1), (key1541, -2), (key1568, 1), (key1617, 1), (key1812, 1), (key1815, 1), (key1823, -2), (key1315, -1), (key1324, -1), (key1442, 1), (key1631, 1), (key1311, 2), (key1419, -1), (key1617, -1), (key1771, -1), (key1778, -1), (key1796, 1), (key1823, 1), (key1336, 1), (key1343, 1), (key1464, -1), (key1665, -1), (key1291, -1), (key1311, -1), (key1386, 1), (key1541, 1), (key1771, 2), (key1787, -1), (key1812, -1), (key1336, -2), (key1454, 1), (key1654, 1), (key1295, 1), (key1315, 1), (key1390, -1), (key1545, -1)]

def rawRow449 : Integer.Sparse Key := [(key1657, -1), (key1654, -1), (key1665, 2), (key1554, 1), (key1545, 1), (key1631, -1), (key1591, -1), (key1541, -2), (key1617, 1), (key1568, 1), (key1815, 1), (key1812, 1), (key1823, -2), (key1324, -1), (key1315, -1), (key1631, 1), (key1442, 1), (key1311, 2), (key1617, -1), (key1419, -1), (key1778, -1), (key1771, -1), (key1823, 1), (key1796, 1), (key1343, 1), (key1336, 1), (key1665, -1), (key1464, -1), (key1311, -1), (key1291, -1), (key1541, 1), (key1386, 1), (key1771, 2), (key1812, -1), (key1787, -1), (key1336, -2), (key1654, 1), (key1454, 1), (key1315, 1), (key1295, 1), (key1545, -1), (key1390, -1)]

def rawRow450 : Integer.Sparse Key := [(key1654, -1), (key1665, -1), (key1657, 2), (key1572, 1), (key1591, 1), (key1554, -1), (key1622, -1), (key1568, -2), (key1541, 1), (key1617, 1), (key1812, 1), (key1823, 1), (key1815, -2), (key1423, -1), (key1442, -1), (key1324, 1), (key1622, 1), (key1419, 2), (key1311, -1), (key1617, -1), (key1787, -1), (key1796, -1), (key1778, 1), (key1815, 1), (key1454, 1), (key1464, 1), (key1343, -1), (key1657, -1), (key1386, -1), (key1419, -1), (key1291, 1), (key1568, 1), (key1787, 2), (key1771, -1), (key1812, -1), (key1454, -2), (key1336, 1), (key1654, 1), (key1390, 1), (key1423, 1), (key1295, -1), (key1572, -1)]

def rawRow451 : Integer.Sparse Key := [(key1665, -1), (key1654, -1), (key1657, 2), (key1591, 1), (key1572, 1), (key1622, -1), (key1554, -1), (key1568, -2), (key1617, 1), (key1541, 1), (key1823, 1), (key1812, 1), (key1815, -2), (key1442, -1), (key1423, -1), (key1622, 1), (key1324, 1), (key1419, 2), (key1617, -1), (key1311, -1), (key1796, -1), (key1787, -1), (key1815, 1), (key1778, 1), (key1464, 1), (key1454, 1), (key1657, -1), (key1343, -1), (key1419, -1), (key1386, -1), (key1568, 1), (key1291, 1), (key1787, 2), (key1812, -1), (key1771, -1), (key1454, -2), (key1654, 1), (key1336, 1), (key1423, 1), (key1390, 1), (key1572, -1), (key1295, -1)]

def rawRow453 : Integer.Sparse Key := [(key1771, -1), (key1778, -1), (key1771, 2), (key1812, 1), (key1815, 1), (key1787, -1), (key1812, -1), (key1823, -2), (key1796, 1), (key1823, 1), (key1336, 1), (key1343, 1), (key1336, -2), (key1654, -1), (key1657, -1), (key1454, 1), (key1654, 1), (key1665, 2), (key1464, -1), (key1665, -1), (key1315, -1), (key1324, -1), (key1295, 1), (key1315, 1), (key1545, 1), (key1554, 1), (key1390, -1), (key1545, -1), (key1591, -1), (key1631, -1), (key1442, 1), (key1631, 1), (key1311, 2), (key1291, -1), (key1311, -1), (key1541, -2), (key1386, 1), (key1541, 1), (key1568, 1), (key1617, 1), (key1419, -1), (key1617, -1)]

def rawRow454 : Integer.Sparse Key := [(key1778, -1), (key1771, -1), (key1771, 2), (key1815, 1), (key1812, 1), (key1812, -1), (key1787, -1), (key1823, -2), (key1823, 1), (key1796, 1), (key1343, 1), (key1336, 1), (key1336, -2), (key1657, -1), (key1654, -1), (key1654, 1), (key1454, 1), (key1665, 2), (key1665, -1), (key1464, -1), (key1324, -1), (key1315, -1), (key1315, 1), (key1295, 1), (key1554, 1), (key1545, 1), (key1545, -1), (key1390, -1), (key1631, -1), (key1591, -1), (key1631, 1), (key1442, 1), (key1311, 2), (key1311, -1), (key1291, -1), (key1541, -2), (key1541, 1), (key1386, 1), (key1617, 1), (key1568, 1), (key1617, -1), (key1419, -1)]

def rawRow456 : Integer.Sparse Key := [(key1787, -1), (key1796, -1), (key1787, 2), (key1812, 1), (key1823, 1), (key1771, -1), (key1812, -1), (key1815, -2), (key1778, 1), (key1815, 1), (key1454, 1), (key1464, 1), (key1454, -2), (key1654, -1), (key1665, -1), (key1336, 1), (key1654, 1), (key1657, 2), (key1343, -1), (key1657, -1), (key1423, -1), (key1442, -1), (key1390, 1), (key1423, 1), (key1572, 1), (key1591, 1), (key1295, -1), (key1572, -1), (key1554, -1), (key1622, -1), (key1324, 1), (key1622, 1), (key1419, 2), (key1386, -1), (key1419, -1), (key1568, -2), (key1291, 1), (key1568, 1), (key1541, 1), (key1617, 1), (key1311, -1), (key1617, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3864 : Integer.Sparse Key := [(key252, -1), (key249, -1), (key594, -1), (key436, -1), (key603, -1), (key452, -1), (key262, 2), (key597, 2), (key444, 2), (key240, 1), (key237, 1), (key579, 1), (key407, 1), (key585, 1), (key420, 1), (key273, -1), (key262, -1), (key574, -1), (key399, -1), (key597, -1), (key471, -1), (key240, -2), (key579, -2), (key410, -2), (key268, 1), (key252, 1), (key569, 1), (key389, 1), (key594, 1), (key468, 1)]

def rawRow3865 : Integer.Sparse Key := [(key436, -1), (key452, -1), (key249, -1), (key603, -1), (key252, -1), (key594, -1), (key444, 2), (key262, 2), (key597, 2), (key407, 1), (key420, 1), (key237, 1), (key585, 1), (key240, 1), (key579, 1), (key399, -1), (key471, -1), (key262, -1), (key597, -1), (key273, -1), (key574, -1), (key410, -2), (key240, -2), (key579, -2), (key389, 1), (key468, 1), (key252, 1), (key594, 1), (key268, 1), (key569, 1)]

def rawRow3866 : Integer.Sparse Key := [(key452, -1), (key436, -1), (key603, -1), (key249, -1), (key594, -1), (key252, -1), (key444, 2), (key597, 2), (key262, 2), (key420, 1), (key407, 1), (key585, 1), (key237, 1), (key579, 1), (key240, 1), (key471, -1), (key399, -1), (key597, -1), (key262, -1), (key574, -1), (key273, -1), (key410, -2), (key579, -2), (key240, -2), (key468, 1), (key389, 1), (key594, 1), (key252, 1), (key569, 1), (key268, 1)]

def rawRow3867 : Integer.Sparse Key := [(key594, -1), (key603, -1), (key252, -1), (key452, -1), (key249, -1), (key436, -1), (key597, 2), (key262, 2), (key444, 2), (key579, 1), (key585, 1), (key240, 1), (key420, 1), (key237, 1), (key407, 1), (key574, -1), (key597, -1), (key273, -1), (key471, -1), (key262, -1), (key399, -1), (key579, -2), (key240, -2), (key410, -2), (key569, 1), (key594, 1), (key268, 1), (key468, 1), (key252, 1), (key389, 1)]

def rawRow3868 : Integer.Sparse Key := [(key603, -1), (key594, -1), (key452, -1), (key252, -1), (key436, -1), (key249, -1), (key597, 2), (key444, 2), (key262, 2), (key585, 1), (key579, 1), (key420, 1), (key240, 1), (key407, 1), (key237, 1), (key597, -1), (key574, -1), (key471, -1), (key273, -1), (key399, -1), (key262, -1), (key579, -2), (key410, -2), (key240, -2), (key594, 1), (key569, 1), (key468, 1), (key268, 1), (key389, 1), (key252, 1)]

def rawRow3869 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key320, -1), (key444, -1), (key330, -1), (key452, -1), (key249, 2), (key317, 2), (key436, 2), (key268, 1), (key273, 1), (key336, 1), (key471, 1), (key342, 1), (key477, 1), (key237, -1), (key249, -1), (key303, -1), (key386, -1), (key317, -1), (key407, -1), (key268, -2), (key336, -2), (key468, -2), (key240, 1), (key252, 1), (key306, 1), (key389, 1), (key320, 1), (key410, 1)]

def rawRow3870 : Integer.Sparse Key := [(key262, -1), (key252, -1), (key444, -1), (key320, -1), (key452, -1), (key330, -1), (key249, 2), (key436, 2), (key317, 2), (key273, 1), (key268, 1), (key471, 1), (key336, 1), (key477, 1), (key342, 1), (key249, -1), (key237, -1), (key386, -1), (key303, -1), (key407, -1), (key317, -1), (key268, -2), (key468, -2), (key336, -2), (key252, 1), (key240, 1), (key389, 1), (key306, 1), (key410, 1), (key320, 1)]

def rawRow3871 : Integer.Sparse Key := [(key320, -1), (key330, -1), (key252, -1), (key452, -1), (key262, -1), (key444, -1), (key317, 2), (key249, 2), (key436, 2), (key336, 1), (key342, 1), (key268, 1), (key477, 1), (key273, 1), (key471, 1), (key303, -1), (key317, -1), (key237, -1), (key407, -1), (key249, -1), (key386, -1), (key336, -2), (key268, -2), (key468, -2), (key306, 1), (key320, 1), (key240, 1), (key410, 1), (key252, 1), (key389, 1)]

def rawRow3872 : Integer.Sparse Key := [(key330, -1), (key320, -1), (key452, -1), (key252, -1), (key444, -1), (key262, -1), (key317, 2), (key436, 2), (key249, 2), (key342, 1), (key336, 1), (key477, 1), (key268, 1), (key471, 1), (key273, 1), (key317, -1), (key303, -1), (key407, -1), (key237, -1), (key386, -1), (key249, -1), (key336, -2), (key468, -2), (key268, -2), (key320, 1), (key306, 1), (key410, 1), (key240, 1), (key389, 1), (key252, 1)]

def rawRow3873 : Integer.Sparse Key := [(key444, -1), (key452, -1), (key262, -1), (key330, -1), (key252, -1), (key320, -1), (key436, 2), (key249, 2), (key317, 2), (key471, 1), (key477, 1), (key273, 1), (key342, 1), (key268, 1), (key336, 1), (key386, -1), (key407, -1), (key249, -1), (key317, -1), (key237, -1), (key303, -1), (key468, -2), (key268, -2), (key336, -2), (key389, 1), (key410, 1), (key252, 1), (key320, 1), (key240, 1), (key306, 1)]

def rawRow3874 : Integer.Sparse Key := [(key452, -1), (key444, -1), (key330, -1), (key262, -1), (key320, -1), (key252, -1), (key436, 2), (key317, 2), (key249, 2), (key477, 1), (key471, 1), (key342, 1), (key273, 1), (key336, 1), (key268, 1), (key407, -1), (key386, -1), (key317, -1), (key249, -1), (key303, -1), (key237, -1), (key468, -2), (key336, -2), (key268, -2), (key410, 1), (key389, 1), (key320, 1), (key252, 1), (key306, 1), (key240, 1)]

def rawRow3878 : Integer.Sparse Key := [(key268, -1), (key273, -1), (key336, -1), (key471, -1), (key342, -1), (key477, -1), (key268, 2), (key336, 2), (key468, 2), (key252, 1), (key262, 1), (key320, 1), (key444, 1), (key330, 1), (key452, 1), (key240, -1), (key252, -1), (key306, -1), (key389, -1), (key320, -1), (key410, -1), (key249, -2), (key317, -2), (key436, -2), (key237, 1), (key249, 1), (key303, 1), (key386, 1), (key317, 1), (key407, 1)]

def rawRow3879 : Integer.Sparse Key := [(key273, -1), (key268, -1), (key471, -1), (key336, -1), (key477, -1), (key342, -1), (key268, 2), (key468, 2), (key336, 2), (key262, 1), (key252, 1), (key444, 1), (key320, 1), (key452, 1), (key330, 1), (key252, -1), (key240, -1), (key389, -1), (key306, -1), (key410, -1), (key320, -1), (key249, -2), (key436, -2), (key317, -2), (key249, 1), (key237, 1), (key386, 1), (key303, 1), (key407, 1), (key317, 1)]

def rawRow3880 : Integer.Sparse Key := [(key336, -1), (key342, -1), (key268, -1), (key477, -1), (key273, -1), (key471, -1), (key336, 2), (key268, 2), (key468, 2), (key320, 1), (key330, 1), (key252, 1), (key452, 1), (key262, 1), (key444, 1), (key306, -1), (key320, -1), (key240, -1), (key410, -1), (key252, -1), (key389, -1), (key317, -2), (key249, -2), (key436, -2), (key303, 1), (key317, 1), (key237, 1), (key407, 1), (key249, 1), (key386, 1)]

def rawRow3881 : Integer.Sparse Key := [(key342, -1), (key336, -1), (key477, -1), (key268, -1), (key471, -1), (key273, -1), (key336, 2), (key468, 2), (key268, 2), (key330, 1), (key320, 1), (key452, 1), (key252, 1), (key444, 1), (key262, 1), (key320, -1), (key306, -1), (key410, -1), (key240, -1), (key389, -1), (key252, -1), (key317, -2), (key436, -2), (key249, -2), (key317, 1), (key303, 1), (key407, 1), (key237, 1), (key386, 1), (key249, 1)]

def rawRow3882 : Integer.Sparse Key := [(key471, -1), (key477, -1), (key273, -1), (key342, -1), (key268, -1), (key336, -1), (key468, 2), (key268, 2), (key336, 2), (key444, 1), (key452, 1), (key262, 1), (key330, 1), (key252, 1), (key320, 1), (key389, -1), (key410, -1), (key252, -1), (key320, -1), (key240, -1), (key306, -1), (key436, -2), (key249, -2), (key317, -2), (key386, 1), (key407, 1), (key249, 1), (key317, 1), (key237, 1), (key303, 1)]

def rawRow3883 : Integer.Sparse Key := [(key477, -1), (key471, -1), (key342, -1), (key273, -1), (key336, -1), (key268, -1), (key468, 2), (key336, 2), (key268, 2), (key452, 1), (key444, 1), (key330, 1), (key262, 1), (key320, 1), (key252, 1), (key410, -1), (key389, -1), (key320, -1), (key252, -1), (key306, -1), (key240, -1), (key436, -2), (key317, -2), (key249, -2), (key407, 1), (key386, 1), (key317, 1), (key249, 1), (key303, 1), (key237, 1)]

def rawRow3884 : Integer.Sparse Key := [(key1406, -2), (key1413, -2), (key1909, -2), (key1409, 2), (key1413, 2), (key1587, 2), (key1434, 2), (key1438, 2), (key1924, 2), (key1438, -6), (key1476, -2), (key1478, -2), (key1687, -2), (key1478, 6)]

def rawRow3885 : Integer.Sparse Key := [(key1413, -2), (key1406, -2), (key1909, -2), (key1413, 2), (key1409, 2), (key1587, 2), (key1438, 2), (key1434, 2), (key1924, 2), (key1438, -6), (key1478, -2), (key1476, -2), (key1687, -2), (key1478, 6)]

def rawRow3886 : Integer.Sparse Key := [(key1406, -2), (key1909, -2), (key1413, -2), (key1409, 2), (key1587, 2), (key1413, 2), (key1434, 2), (key1924, 2), (key1438, 2), (key1438, -6), (key1476, -2), (key1687, -2), (key1478, -2), (key1478, 6)]

def rawRow3887 : Integer.Sparse Key := [(key1909, -2), (key1406, -2), (key1413, -2), (key1587, 2), (key1409, 2), (key1413, 2), (key1924, 2), (key1434, 2), (key1438, 2), (key1438, -6), (key1687, -2), (key1476, -2), (key1478, -2), (key1478, 6)]

def rawRow3888 : Integer.Sparse Key := [(key1413, -2), (key1909, -2), (key1406, -2), (key1413, 2), (key1587, 2), (key1409, 2), (key1438, 2), (key1924, 2), (key1434, 2), (key1438, -6), (key1478, -2), (key1687, -2), (key1476, -2), (key1478, 6)]

def rawRow3889 : Integer.Sparse Key := [(key1909, -2), (key1413, -2), (key1406, -2), (key1587, 2), (key1413, 2), (key1409, 2), (key1924, 2), (key1438, 2), (key1434, 2), (key1438, -6), (key1687, -2), (key1478, -2), (key1476, -2), (key1478, 6)]

def rawRow3890 : Integer.Sparse Key := [(key1409, -2), (key1409, -2), (key1907, -2), (key1406, 2), (key1406, 2), (key1583, 2), (key1438, 2), (key1438, 2), (key1924, 2), (key1434, -6), (key1478, -2), (key1478, -2), (key1687, -2), (key1476, 6)]

def rawRow3891 : Integer.Sparse Key := [(key1409, -2), (key1907, -2), (key1409, -2), (key1406, 2), (key1583, 2), (key1406, 2), (key1438, 2), (key1924, 2), (key1438, 2), (key1434, -6), (key1478, -2), (key1687, -2), (key1478, -2), (key1476, 6)]

def rawRow3892 : Integer.Sparse Key := [(key1907, -2), (key1409, -2), (key1409, -2), (key1583, 2), (key1406, 2), (key1406, 2), (key1924, 2), (key1438, 2), (key1438, 2), (key1434, -6), (key1687, -2), (key1478, -2), (key1478, -2), (key1476, 6)]

def rawRow3893 : Integer.Sparse Key := [(key1434, -2), (key1438, -2), (key1924, -2), (key1476, 2), (key1478, 2), (key1687, 2), (key1406, 2), (key1413, 2), (key1909, 2), (key1478, -6), (key1409, -2), (key1413, -2), (key1587, -2), (key1438, 6)]

def rawRow3894 : Integer.Sparse Key := [(key1438, -2), (key1434, -2), (key1924, -2), (key1478, 2), (key1476, 2), (key1687, 2), (key1413, 2), (key1406, 2), (key1909, 2), (key1478, -6), (key1413, -2), (key1409, -2), (key1587, -2), (key1438, 6)]

def rawRow3895 : Integer.Sparse Key := [(key1434, -2), (key1924, -2), (key1438, -2), (key1476, 2), (key1687, 2), (key1478, 2), (key1406, 2), (key1909, 2), (key1413, 2), (key1478, -6), (key1409, -2), (key1587, -2), (key1413, -2), (key1438, 6)]

def rawRow3896 : Integer.Sparse Key := [(key1924, -2), (key1434, -2), (key1438, -2), (key1687, 2), (key1476, 2), (key1478, 2), (key1909, 2), (key1406, 2), (key1413, 2), (key1478, -6), (key1587, -2), (key1409, -2), (key1413, -2), (key1438, 6)]

def rawRow3897 : Integer.Sparse Key := [(key1438, -2), (key1924, -2), (key1434, -2), (key1478, 2), (key1687, 2), (key1476, 2), (key1413, 2), (key1909, 2), (key1406, 2), (key1478, -6), (key1413, -2), (key1587, -2), (key1409, -2), (key1438, 6)]

def rawRow3898 : Integer.Sparse Key := [(key1924, -2), (key1438, -2), (key1434, -2), (key1687, 2), (key1478, 2), (key1476, 2), (key1909, 2), (key1413, 2), (key1406, 2), (key1478, -6), (key1587, -2), (key1413, -2), (key1409, -2), (key1438, 6)]

def rawRow3899 : Integer.Sparse Key := [(key1409, -2), (key1476, -2), (key1907, -2), (key1406, 2), (key1434, 2), (key1583, 2), (key1413, 2), (key1478, 2), (key1909, 2), (key1406, -6), (key1413, -2), (key1438, -2), (key1587, -2), (key1409, 6)]

def rawRow3900 : Integer.Sparse Key := [(key1476, -2), (key1409, -2), (key1907, -2), (key1434, 2), (key1406, 2), (key1583, 2), (key1478, 2), (key1413, 2), (key1909, 2), (key1406, -6), (key1438, -2), (key1413, -2), (key1587, -2), (key1409, 6)]

def rawRow3901 : Integer.Sparse Key := [(key1409, -2), (key1907, -2), (key1476, -2), (key1406, 2), (key1583, 2), (key1434, 2), (key1413, 2), (key1909, 2), (key1478, 2), (key1406, -6), (key1413, -2), (key1587, -2), (key1438, -2), (key1409, 6)]

def rawRow3902 : Integer.Sparse Key := [(key1907, -2), (key1409, -2), (key1476, -2), (key1583, 2), (key1406, 2), (key1434, 2), (key1909, 2), (key1413, 2), (key1478, 2), (key1406, -6), (key1587, -2), (key1413, -2), (key1438, -2), (key1409, 6)]

def rawRow3903 : Integer.Sparse Key := [(key1476, -2), (key1907, -2), (key1409, -2), (key1434, 2), (key1583, 2), (key1406, 2), (key1478, 2), (key1909, 2), (key1413, 2), (key1406, -6), (key1438, -2), (key1587, -2), (key1413, -2), (key1409, 6)]

def rawRow3904 : Integer.Sparse Key := [(key1907, -2), (key1476, -2), (key1409, -2), (key1583, 2), (key1434, 2), (key1406, 2), (key1909, 2), (key1478, 2), (key1413, 2), (key1406, -6), (key1587, -2), (key1438, -2), (key1413, -2), (key1409, 6)]

def rawRow3905 : Integer.Sparse Key := [(key1438, -2), (key1438, -2), (key1924, -2), (key1478, 2), (key1478, 2), (key1687, 2), (key1409, 2), (key1409, 2), (key1907, 2), (key1476, -6), (key1406, -2), (key1406, -2), (key1583, -2), (key1434, 6)]

def rawRow3906 : Integer.Sparse Key := [(key1438, -2), (key1924, -2), (key1438, -2), (key1478, 2), (key1687, 2), (key1478, 2), (key1409, 2), (key1907, 2), (key1409, 2), (key1476, -6), (key1406, -2), (key1583, -2), (key1406, -2), (key1434, 6)]

def rawRow3907 : Integer.Sparse Key := [(key1924, -2), (key1438, -2), (key1438, -2), (key1687, 2), (key1478, 2), (key1478, 2), (key1907, 2), (key1409, 2), (key1409, 2), (key1476, -6), (key1583, -2), (key1406, -2), (key1406, -2), (key1434, 6)]

def rawRow3908 : Integer.Sparse Key := [(key1413, -2), (key1478, -2), (key1909, -2), (key1413, 2), (key1438, 2), (key1587, 2), (key1409, 2), (key1476, 2), (key1907, 2), (key1409, -6), (key1406, -2), (key1434, -2), (key1583, -2), (key1406, 6)]

def rawRow3909 : Integer.Sparse Key := [(key1478, -2), (key1413, -2), (key1909, -2), (key1438, 2), (key1413, 2), (key1587, 2), (key1476, 2), (key1409, 2), (key1907, 2), (key1409, -6), (key1434, -2), (key1406, -2), (key1583, -2), (key1406, 6)]

def rawRow3910 : Integer.Sparse Key := [(key1413, -2), (key1909, -2), (key1478, -2), (key1413, 2), (key1587, 2), (key1438, 2), (key1409, 2), (key1907, 2), (key1476, 2), (key1409, -6), (key1406, -2), (key1583, -2), (key1434, -2), (key1406, 6)]

def rawRow3911 : Integer.Sparse Key := [(key1909, -2), (key1413, -2), (key1478, -2), (key1587, 2), (key1413, 2), (key1438, 2), (key1907, 2), (key1409, 2), (key1476, 2), (key1409, -6), (key1583, -2), (key1406, -2), (key1434, -2), (key1406, 6)]

def rawRow3912 : Integer.Sparse Key := [(key1478, -2), (key1909, -2), (key1413, -2), (key1438, 2), (key1587, 2), (key1413, 2), (key1476, 2), (key1907, 2), (key1409, 2), (key1409, -6), (key1434, -2), (key1583, -2), (key1406, -2), (key1406, 6)]

def rawRow3913 : Integer.Sparse Key := [(key1909, -2), (key1478, -2), (key1413, -2), (key1587, 2), (key1438, 2), (key1413, 2), (key1907, 2), (key1476, 2), (key1409, 2), (key1409, -6), (key1583, -2), (key1434, -2), (key1406, -2), (key1406, 6)]

def rawRow3914 : Integer.Sparse Key := [(key317, -2), (key320, -2), (key330, -2), (key303, 1), (key306, 1), (key317, 1), (key336, 1), (key330, 1), (key342, 1), (key407, 2), (key410, 2), (key420, 2), (key237, -1), (key240, -1), (key407, -1), (key579, -1), (key420, -1), (key585, -1), (key386, -1), (key389, -1), (key436, -1), (key468, -1), (key452, -1), (key477, -1), (key249, 1), (key252, 1), (key436, 1), (key594, 1), (key452, 1), (key603, 1)]

def rawRow3915 : Integer.Sparse Key := [(key320, -2), (key317, -2), (key330, -2), (key306, 1), (key303, 1), (key336, 1), (key317, 1), (key342, 1), (key330, 1), (key410, 2), (key407, 2), (key420, 2), (key240, -1), (key237, -1), (key579, -1), (key407, -1), (key585, -1), (key420, -1), (key389, -1), (key386, -1), (key468, -1), (key436, -1), (key477, -1), (key452, -1), (key252, 1), (key249, 1), (key594, 1), (key436, 1), (key603, 1), (key452, 1)]

def rawRow3916 : Integer.Sparse Key := [(key317, -2), (key330, -2), (key320, -2), (key317, 1), (key330, 1), (key303, 1), (key342, 1), (key306, 1), (key336, 1), (key407, 2), (key420, 2), (key410, 2), (key407, -1), (key420, -1), (key237, -1), (key585, -1), (key240, -1), (key579, -1), (key436, -1), (key452, -1), (key386, -1), (key477, -1), (key389, -1), (key468, -1), (key436, 1), (key452, 1), (key249, 1), (key603, 1), (key252, 1), (key594, 1)]

def rawRow3917 : Integer.Sparse Key := [(key330, -2), (key317, -2), (key320, -2), (key330, 1), (key317, 1), (key342, 1), (key303, 1), (key336, 1), (key306, 1), (key420, 2), (key407, 2), (key410, 2), (key420, -1), (key407, -1), (key585, -1), (key237, -1), (key579, -1), (key240, -1), (key452, -1), (key436, -1), (key477, -1), (key386, -1), (key468, -1), (key389, -1), (key452, 1), (key436, 1), (key603, 1), (key249, 1), (key594, 1), (key252, 1)]

def rawRow3918 : Integer.Sparse Key := [(key320, -2), (key330, -2), (key317, -2), (key336, 1), (key342, 1), (key306, 1), (key330, 1), (key303, 1), (key317, 1), (key410, 2), (key420, 2), (key407, 2), (key579, -1), (key585, -1), (key240, -1), (key420, -1), (key237, -1), (key407, -1), (key468, -1), (key477, -1), (key389, -1), (key452, -1), (key386, -1), (key436, -1), (key594, 1), (key603, 1), (key252, 1), (key452, 1), (key249, 1), (key436, 1)]

def rawRow3919 : Integer.Sparse Key := [(key330, -2), (key320, -2), (key317, -2), (key342, 1), (key336, 1), (key330, 1), (key306, 1), (key317, 1), (key303, 1), (key420, 2), (key410, 2), (key407, 2), (key585, -1), (key579, -1), (key420, -1), (key240, -1), (key407, -1), (key237, -1), (key477, -1), (key468, -1), (key452, -1), (key389, -1), (key436, -1), (key386, -1), (key603, 1), (key594, 1), (key452, 1), (key252, 1), (key436, 1), (key249, 1)]

def rawRow3923 : Integer.Sparse Key := [(key407, -2), (key410, -2), (key420, -2), (key386, 1), (key389, 1), (key436, 1), (key468, 1), (key452, 1), (key477, 1), (key317, 2), (key320, 2), (key330, 2), (key249, -1), (key252, -1), (key436, -1), (key594, -1), (key452, -1), (key603, -1), (key303, -1), (key306, -1), (key317, -1), (key336, -1), (key330, -1), (key342, -1), (key237, 1), (key240, 1), (key407, 1), (key579, 1), (key420, 1), (key585, 1)]

def rawRow3924 : Integer.Sparse Key := [(key410, -2), (key407, -2), (key420, -2), (key389, 1), (key386, 1), (key468, 1), (key436, 1), (key477, 1), (key452, 1), (key320, 2), (key317, 2), (key330, 2), (key252, -1), (key249, -1), (key594, -1), (key436, -1), (key603, -1), (key452, -1), (key306, -1), (key303, -1), (key336, -1), (key317, -1), (key342, -1), (key330, -1), (key240, 1), (key237, 1), (key579, 1), (key407, 1), (key585, 1), (key420, 1)]

def rawRow3925 : Integer.Sparse Key := [(key407, -2), (key420, -2), (key410, -2), (key436, 1), (key452, 1), (key386, 1), (key477, 1), (key389, 1), (key468, 1), (key317, 2), (key330, 2), (key320, 2), (key436, -1), (key452, -1), (key249, -1), (key603, -1), (key252, -1), (key594, -1), (key317, -1), (key330, -1), (key303, -1), (key342, -1), (key306, -1), (key336, -1), (key407, 1), (key420, 1), (key237, 1), (key585, 1), (key240, 1), (key579, 1)]

def rawRow3926 : Integer.Sparse Key := [(key420, -2), (key407, -2), (key410, -2), (key452, 1), (key436, 1), (key477, 1), (key386, 1), (key468, 1), (key389, 1), (key330, 2), (key317, 2), (key320, 2), (key452, -1), (key436, -1), (key603, -1), (key249, -1), (key594, -1), (key252, -1), (key330, -1), (key317, -1), (key342, -1), (key303, -1), (key336, -1), (key306, -1), (key420, 1), (key407, 1), (key585, 1), (key237, 1), (key579, 1), (key240, 1)]

def rawRow3927 : Integer.Sparse Key := [(key410, -2), (key420, -2), (key407, -2), (key468, 1), (key477, 1), (key389, 1), (key452, 1), (key386, 1), (key436, 1), (key320, 2), (key330, 2), (key317, 2), (key594, -1), (key603, -1), (key252, -1), (key452, -1), (key249, -1), (key436, -1), (key336, -1), (key342, -1), (key306, -1), (key330, -1), (key303, -1), (key317, -1), (key579, 1), (key585, 1), (key240, 1), (key420, 1), (key237, 1), (key407, 1)]

def rawRow3928 : Integer.Sparse Key := [(key420, -2), (key410, -2), (key407, -2), (key477, 1), (key468, 1), (key452, 1), (key389, 1), (key436, 1), (key386, 1), (key330, 2), (key320, 2), (key317, 2), (key603, -1), (key594, -1), (key452, -1), (key252, -1), (key436, -1), (key249, -1), (key342, -1), (key336, -1), (key330, -1), (key306, -1), (key317, -1), (key303, -1), (key585, 1), (key579, 1), (key420, 1), (key240, 1), (key407, 1), (key237, 1)]

def rawRow3929 : Integer.Sparse Key := [(key468, -2), (key471, -2), (key477, -2), (key389, 1), (key399, 1), (key410, 1), (key444, 1), (key420, 1), (key452, 1), (key594, 2), (key597, 2), (key603, 2), (key252, -1), (key262, -1), (key320, -1), (key444, -1), (key330, -1), (key452, -1), (key569, -1), (key574, -1), (key579, -1), (key597, -1), (key585, -1), (key603, -1), (key268, 1), (key273, 1), (key336, 1), (key471, 1), (key342, 1), (key477, 1)]

def rawRow3930 : Integer.Sparse Key := [(key471, -2), (key468, -2), (key477, -2), (key399, 1), (key389, 1), (key444, 1), (key410, 1), (key452, 1), (key420, 1), (key597, 2), (key594, 2), (key603, 2), (key262, -1), (key252, -1), (key444, -1), (key320, -1), (key452, -1), (key330, -1), (key574, -1), (key569, -1), (key597, -1), (key579, -1), (key603, -1), (key585, -1), (key273, 1), (key268, 1), (key471, 1), (key336, 1), (key477, 1), (key342, 1)]

def rawRow3931 : Integer.Sparse Key := [(key468, -2), (key477, -2), (key471, -2), (key410, 1), (key420, 1), (key389, 1), (key452, 1), (key399, 1), (key444, 1), (key594, 2), (key603, 2), (key597, 2), (key320, -1), (key330, -1), (key252, -1), (key452, -1), (key262, -1), (key444, -1), (key579, -1), (key585, -1), (key569, -1), (key603, -1), (key574, -1), (key597, -1), (key336, 1), (key342, 1), (key268, 1), (key477, 1), (key273, 1), (key471, 1)]

def rawRow3932 : Integer.Sparse Key := [(key477, -2), (key468, -2), (key471, -2), (key420, 1), (key410, 1), (key452, 1), (key389, 1), (key444, 1), (key399, 1), (key603, 2), (key594, 2), (key597, 2), (key330, -1), (key320, -1), (key452, -1), (key252, -1), (key444, -1), (key262, -1), (key585, -1), (key579, -1), (key603, -1), (key569, -1), (key597, -1), (key574, -1), (key342, 1), (key336, 1), (key477, 1), (key268, 1), (key471, 1), (key273, 1)]

def rawRow3933 : Integer.Sparse Key := [(key471, -2), (key477, -2), (key468, -2), (key444, 1), (key452, 1), (key399, 1), (key420, 1), (key389, 1), (key410, 1), (key597, 2), (key603, 2), (key594, 2), (key444, -1), (key452, -1), (key262, -1), (key330, -1), (key252, -1), (key320, -1), (key597, -1), (key603, -1), (key574, -1), (key585, -1), (key569, -1), (key579, -1), (key471, 1), (key477, 1), (key273, 1), (key342, 1), (key268, 1), (key336, 1)]

def rawRow3934 : Integer.Sparse Key := [(key477, -2), (key471, -2), (key468, -2), (key452, 1), (key444, 1), (key420, 1), (key399, 1), (key410, 1), (key389, 1), (key603, 2), (key597, 2), (key594, 2), (key452, -1), (key444, -1), (key330, -1), (key262, -1), (key320, -1), (key252, -1), (key603, -1), (key597, -1), (key585, -1), (key574, -1), (key579, -1), (key569, -1), (key477, 1), (key471, 1), (key342, 1), (key273, 1), (key336, 1), (key268, 1)]

def rawRow3938 : Integer.Sparse Key := [(key594, -2), (key597, -2), (key603, -2), (key569, 1), (key574, 1), (key579, 1), (key597, 1), (key585, 1), (key603, 1), (key468, 2), (key471, 2), (key477, 2), (key268, -1), (key273, -1), (key336, -1), (key471, -1), (key342, -1), (key477, -1), (key389, -1), (key399, -1), (key410, -1), (key444, -1), (key420, -1), (key452, -1), (key252, 1), (key262, 1), (key320, 1), (key444, 1), (key330, 1), (key452, 1)]

def rawRow3939 : Integer.Sparse Key := [(key597, -2), (key594, -2), (key603, -2), (key574, 1), (key569, 1), (key597, 1), (key579, 1), (key603, 1), (key585, 1), (key471, 2), (key468, 2), (key477, 2), (key273, -1), (key268, -1), (key471, -1), (key336, -1), (key477, -1), (key342, -1), (key399, -1), (key389, -1), (key444, -1), (key410, -1), (key452, -1), (key420, -1), (key262, 1), (key252, 1), (key444, 1), (key320, 1), (key452, 1), (key330, 1)]

def rawRow3940 : Integer.Sparse Key := [(key594, -2), (key603, -2), (key597, -2), (key579, 1), (key585, 1), (key569, 1), (key603, 1), (key574, 1), (key597, 1), (key468, 2), (key477, 2), (key471, 2), (key336, -1), (key342, -1), (key268, -1), (key477, -1), (key273, -1), (key471, -1), (key410, -1), (key420, -1), (key389, -1), (key452, -1), (key399, -1), (key444, -1), (key320, 1), (key330, 1), (key252, 1), (key452, 1), (key262, 1), (key444, 1)]

def rawRow3941 : Integer.Sparse Key := [(key603, -2), (key594, -2), (key597, -2), (key585, 1), (key579, 1), (key603, 1), (key569, 1), (key597, 1), (key574, 1), (key477, 2), (key468, 2), (key471, 2), (key342, -1), (key336, -1), (key477, -1), (key268, -1), (key471, -1), (key273, -1), (key420, -1), (key410, -1), (key452, -1), (key389, -1), (key444, -1), (key399, -1), (key330, 1), (key320, 1), (key452, 1), (key252, 1), (key444, 1), (key262, 1)]

def rawRow3942 : Integer.Sparse Key := [(key597, -2), (key603, -2), (key594, -2), (key597, 1), (key603, 1), (key574, 1), (key585, 1), (key569, 1), (key579, 1), (key471, 2), (key477, 2), (key468, 2), (key471, -1), (key477, -1), (key273, -1), (key342, -1), (key268, -1), (key336, -1), (key444, -1), (key452, -1), (key399, -1), (key420, -1), (key389, -1), (key410, -1), (key444, 1), (key452, 1), (key262, 1), (key330, 1), (key252, 1), (key320, 1)]

def rawRow3943 : Integer.Sparse Key := [(key603, -2), (key597, -2), (key594, -2), (key603, 1), (key597, 1), (key585, 1), (key574, 1), (key579, 1), (key569, 1), (key477, 2), (key471, 2), (key468, 2), (key477, -1), (key471, -1), (key342, -1), (key273, -1), (key336, -1), (key268, -1), (key452, -1), (key444, -1), (key420, -1), (key399, -1), (key410, -1), (key389, -1), (key452, 1), (key444, 1), (key330, 1), (key262, 1), (key320, 1), (key252, 1)]

def rawRow3944 : Integer.Sparse Key := [(key43, -2), (key46, -2), (key71, -2), (key46, 6), (key426, 2), (key429, 2), (key589, 2), (key209, -2), (key429, -2), (key457, -2), (key463, -6), (key214, 2), (key463, 2), (key480, 2)]

def rawRow3945 : Integer.Sparse Key := [(key46, -2), (key43, -2), (key71, -2), (key46, 6), (key429, 2), (key426, 2), (key589, 2), (key209, -2), (key457, -2), (key429, -2), (key463, -6), (key214, 2), (key480, 2), (key463, 2)]

def rawRow3946 : Integer.Sparse Key := [(key43, -2), (key71, -2), (key46, -2), (key46, 6), (key426, 2), (key589, 2), (key429, 2), (key429, -2), (key209, -2), (key457, -2), (key463, -6), (key463, 2), (key214, 2), (key480, 2)]

def rawRow3947 : Integer.Sparse Key := [(key71, -2), (key43, -2), (key46, -2), (key46, 6), (key589, 2), (key426, 2), (key429, 2), (key429, -2), (key457, -2), (key209, -2), (key463, -6), (key463, 2), (key480, 2), (key214, 2)]

def rawRow3948 : Integer.Sparse Key := [(key46, -2), (key71, -2), (key43, -2), (key46, 6), (key429, 2), (key589, 2), (key426, 2), (key457, -2), (key209, -2), (key429, -2), (key463, -6), (key480, 2), (key214, 2), (key463, 2)]

def rawRow3949 : Integer.Sparse Key := [(key71, -2), (key46, -2), (key43, -2), (key46, 6), (key589, 2), (key429, 2), (key426, 2), (key457, -2), (key429, -2), (key209, -2), (key463, -6), (key480, 2), (key463, 2), (key214, 2)]

def rawRow3950 : Integer.Sparse Key := [(key46, -2), (key46, -2), (key71, -2), (key43, 6), (key457, 2), (key457, 2), (key606, 2), (key206, -2), (key426, -2), (key426, -2), (key480, -6), (key214, 2), (key463, 2), (key463, 2)]

def rawRow3951 : Integer.Sparse Key := [(key46, -2), (key71, -2), (key46, -2), (key43, 6), (key457, 2), (key606, 2), (key457, 2), (key426, -2), (key206, -2), (key426, -2), (key480, -6), (key463, 2), (key214, 2), (key463, 2)]

def rawRow3952 : Integer.Sparse Key := [(key71, -2), (key46, -2), (key46, -2), (key43, 6), (key606, 2), (key457, 2), (key457, 2), (key426, -2), (key426, -2), (key206, -2), (key480, -6), (key463, 2), (key463, 2), (key214, 2)]

def rawRow3953 : Integer.Sparse Key := [(key100, -2), (key103, -2), (key134, -2), (key112, 6), (key43, 2), (key46, 2), (key71, 2), (key214, -2), (key463, -2), (key480, -2), (key378, -6), (key209, 2), (key429, 2), (key457, 2)]

def rawRow3954 : Integer.Sparse Key := [(key103, -2), (key100, -2), (key134, -2), (key112, 6), (key46, 2), (key43, 2), (key71, 2), (key214, -2), (key480, -2), (key463, -2), (key378, -6), (key209, 2), (key457, 2), (key429, 2)]

def rawRow3955 : Integer.Sparse Key := [(key100, -2), (key134, -2), (key103, -2), (key112, 6), (key43, 2), (key71, 2), (key46, 2), (key463, -2), (key214, -2), (key480, -2), (key378, -6), (key429, 2), (key209, 2), (key457, 2)]

def rawRow3956 : Integer.Sparse Key := [(key134, -2), (key100, -2), (key103, -2), (key112, 6), (key71, 2), (key43, 2), (key46, 2), (key463, -2), (key480, -2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key209, 2)]

def rawRow3957 : Integer.Sparse Key := [(key103, -2), (key134, -2), (key100, -2), (key112, 6), (key46, 2), (key71, 2), (key43, 2), (key480, -2), (key214, -2), (key463, -2), (key378, -6), (key457, 2), (key209, 2), (key429, 2)]

def rawRow3958 : Integer.Sparse Key := [(key134, -2), (key103, -2), (key100, -2), (key112, 6), (key71, 2), (key46, 2), (key43, 2), (key480, -2), (key463, -2), (key214, -2), (key378, -6), (key457, 2), (key429, 2), (key209, 2)]

def rawRow3959 : Integer.Sparse Key := [(key103, -2), (key112, -2), (key134, -2), (key100, 6), (key171, 2), (key174, 2), (key179, 2), (key18, -2), (key375, -2), (key426, -2), (key457, -6), (key209, 2), (key378, 2), (key429, 2)]

def rawRow3960 : Integer.Sparse Key := [(key112, -2), (key103, -2), (key134, -2), (key100, 6), (key174, 2), (key171, 2), (key179, 2), (key18, -2), (key426, -2), (key375, -2), (key457, -6), (key209, 2), (key429, 2), (key378, 2)]

def rawRow3961 : Integer.Sparse Key := [(key103, -2), (key134, -2), (key112, -2), (key100, 6), (key171, 2), (key179, 2), (key174, 2), (key43, -2), (key206, -2), (key426, -2), (key457, -6), (key378, 2), (key209, 2), (key429, 2)]

def rawRow3962 : Integer.Sparse Key := [(key134, -2), (key103, -2), (key112, -2), (key100, 6), (key179, 2), (key171, 2), (key174, 2), (key43, -2), (key426, -2), (key206, -2), (key457, -6), (key378, 2), (key429, 2), (key209, 2)]

def rawRow3963 : Integer.Sparse Key := [(key112, -2), (key134, -2), (key103, -2), (key100, 6), (key174, 2), (key179, 2), (key171, 2), (key100, -2), (key18, -2), (key375, -2), (key457, -6), (key429, 2), (key209, 2), (key378, 2)]

def rawRow3964 : Integer.Sparse Key := [(key134, -2), (key112, -2), (key103, -2), (key100, 6), (key179, 2), (key174, 2), (key171, 2), (key100, -2), (key43, -2), (key206, -2), (key457, -6), (key429, 2), (key378, 2), (key209, 2)]

def rawRow3965 : Integer.Sparse Key := [(key171, -2), (key171, -2), (key179, -2), (key174, 6), (key46, 2), (key46, 2), (key71, 2), (key32, -2), (key112, -2), (key112, -2), (key43, -6), (key206, 2), (key426, 2), (key426, 2)]

def rawRow3966 : Integer.Sparse Key := [(key171, -2), (key179, -2), (key171, -2), (key174, 6), (key46, 2), (key71, 2), (key46, 2), (key112, -2), (key32, -2), (key112, -2), (key43, -6), (key426, 2), (key206, 2), (key426, 2)]

def rawRow3967 : Integer.Sparse Key := [(key179, -2), (key171, -2), (key171, -2), (key174, 6), (key71, 2), (key46, 2), (key46, 2), (key112, -2), (key112, -2), (key32, -2), (key43, -6), (key426, 2), (key426, 2), (key206, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3969 : Integer.Sparse Key := [(key174, -2), (key171, -2), (key179, -2), (key171, 6), (key112, 2), (key103, 2), (key134, 2), (key21, -2), (key103, -2), (key46, -2), (key100, -6), (key18, 2), (key426, 2), (key375, 2)]

def rawRow3970 : Integer.Sparse Key := [(key171, -2), (key179, -2), (key174, -2), (key171, 6), (key103, 2), (key134, 2), (key112, 2), (key46, -2), (key21, -2), (key103, -2), (key100, -6), (key43, 2), (key206, 2), (key426, 2)]

def rawRow3971 : Integer.Sparse Key := [(key179, -2), (key171, -2), (key174, -2), (key171, 6), (key134, 2), (key103, 2), (key112, 2), (key46, -2), (key103, -2), (key21, -2), (key100, -6), (key43, 2), (key426, 2), (key206, 2)]

def rawRow3972 : Integer.Sparse Key := [(key174, -2), (key179, -2), (key171, -2), (key171, 6), (key112, 2), (key134, 2), (key103, 2), (key103, -2), (key21, -2), (key46, -2), (key100, -6), (key100, 2), (key18, 2), (key375, 2)]

def rawRow3973 : Integer.Sparse Key := [(key179, -2), (key174, -2), (key171, -2), (key171, 6), (key134, 2), (key112, 2), (key103, 2), (key103, -2), (key46, -2), (key21, -2), (key100, -6), (key100, 2), (key43, 2), (key206, 2)]

def rawRow3974 : Integer.Sparse Key := [(key1391, -2), (key1772, -2), (key1780, -2), (key1391, 1), (key1397, 1), (key1546, 1), (key1559, 1), (key1774, 1), (key1780, 1), (key1424, 2), (key1813, 2), (key1817, 2), (key1316, -1), (key1329, -1), (key1424, -1), (key1447, -1), (key1817, -1), (key1825, -1), (key1455, -1), (key1457, -1), (key1655, -1), (key1659, -1), (key1839, -1), (key1841, -1), (key1337, 1), (key1345, 1), (key1455, 1), (key1466, 1), (key1841, 1), (key1844, 1)]

def rawRow3975 : Integer.Sparse Key := [(key1391, -2), (key1780, -2), (key1772, -2), (key1397, 1), (key1391, 1), (key1559, 1), (key1546, 1), (key1780, 1), (key1774, 1), (key1424, 2), (key1817, 2), (key1813, 2), (key1329, -1), (key1316, -1), (key1447, -1), (key1424, -1), (key1825, -1), (key1817, -1), (key1457, -1), (key1455, -1), (key1659, -1), (key1655, -1), (key1841, -1), (key1839, -1), (key1345, 1), (key1337, 1), (key1466, 1), (key1455, 1), (key1844, 1), (key1841, 1)]

def rawRow3976 : Integer.Sparse Key := [(key1772, -2), (key1391, -2), (key1780, -2), (key1546, 1), (key1774, 1), (key1391, 1), (key1780, 1), (key1397, 1), (key1559, 1), (key1813, 2), (key1424, 2), (key1817, 2), (key1424, -1), (key1817, -1), (key1316, -1), (key1825, -1), (key1329, -1), (key1447, -1), (key1655, -1), (key1839, -1), (key1455, -1), (key1841, -1), (key1457, -1), (key1659, -1), (key1455, 1), (key1841, 1), (key1337, 1), (key1844, 1), (key1345, 1), (key1466, 1)]

def rawRow3977 : Integer.Sparse Key := [(key1772, -2), (key1780, -2), (key1391, -2), (key1774, 1), (key1546, 1), (key1780, 1), (key1391, 1), (key1559, 1), (key1397, 1), (key1813, 2), (key1817, 2), (key1424, 2), (key1817, -1), (key1424, -1), (key1825, -1), (key1316, -1), (key1447, -1), (key1329, -1), (key1839, -1), (key1655, -1), (key1841, -1), (key1455, -1), (key1659, -1), (key1457, -1), (key1841, 1), (key1455, 1), (key1844, 1), (key1337, 1), (key1466, 1), (key1345, 1)]

def rawRow3978 : Integer.Sparse Key := [(key1780, -2), (key1391, -2), (key1772, -2), (key1559, 1), (key1780, 1), (key1397, 1), (key1774, 1), (key1391, 1), (key1546, 1), (key1817, 2), (key1424, 2), (key1813, 2), (key1447, -1), (key1825, -1), (key1329, -1), (key1817, -1), (key1316, -1), (key1424, -1), (key1659, -1), (key1841, -1), (key1457, -1), (key1839, -1), (key1455, -1), (key1655, -1), (key1466, 1), (key1844, 1), (key1345, 1), (key1841, 1), (key1337, 1), (key1455, 1)]

def rawRow3979 : Integer.Sparse Key := [(key1780, -2), (key1772, -2), (key1391, -2), (key1780, 1), (key1559, 1), (key1774, 1), (key1397, 1), (key1546, 1), (key1391, 1), (key1817, 2), (key1813, 2), (key1424, 2), (key1825, -1), (key1447, -1), (key1817, -1), (key1329, -1), (key1424, -1), (key1316, -1), (key1841, -1), (key1659, -1), (key1839, -1), (key1457, -1), (key1655, -1), (key1455, -1), (key1844, 1), (key1466, 1), (key1841, 1), (key1345, 1), (key1455, 1), (key1337, 1)]

def rawRow3983 : Integer.Sparse Key := [(key1424, -2), (key1813, -2), (key1817, -2), (key1455, 1), (key1457, 1), (key1655, 1), (key1659, 1), (key1839, 1), (key1841, 1), (key1391, 2), (key1772, 2), (key1780, 2), (key1337, -1), (key1345, -1), (key1455, -1), (key1466, -1), (key1841, -1), (key1844, -1), (key1391, -1), (key1397, -1), (key1546, -1), (key1559, -1), (key1774, -1), (key1780, -1), (key1316, 1), (key1329, 1), (key1424, 1), (key1447, 1), (key1817, 1), (key1825, 1)]

def rawRow3984 : Integer.Sparse Key := [(key1424, -2), (key1817, -2), (key1813, -2), (key1457, 1), (key1455, 1), (key1659, 1), (key1655, 1), (key1841, 1), (key1839, 1), (key1391, 2), (key1780, 2), (key1772, 2), (key1345, -1), (key1337, -1), (key1466, -1), (key1455, -1), (key1844, -1), (key1841, -1), (key1397, -1), (key1391, -1), (key1559, -1), (key1546, -1), (key1780, -1), (key1774, -1), (key1329, 1), (key1316, 1), (key1447, 1), (key1424, 1), (key1825, 1), (key1817, 1)]

def rawRow3985 : Integer.Sparse Key := [(key1813, -2), (key1424, -2), (key1817, -2), (key1655, 1), (key1839, 1), (key1455, 1), (key1841, 1), (key1457, 1), (key1659, 1), (key1772, 2), (key1391, 2), (key1780, 2), (key1455, -1), (key1841, -1), (key1337, -1), (key1844, -1), (key1345, -1), (key1466, -1), (key1546, -1), (key1774, -1), (key1391, -1), (key1780, -1), (key1397, -1), (key1559, -1), (key1424, 1), (key1817, 1), (key1316, 1), (key1825, 1), (key1329, 1), (key1447, 1)]

def rawRow3986 : Integer.Sparse Key := [(key1813, -2), (key1817, -2), (key1424, -2), (key1839, 1), (key1655, 1), (key1841, 1), (key1455, 1), (key1659, 1), (key1457, 1), (key1772, 2), (key1780, 2), (key1391, 2), (key1841, -1), (key1455, -1), (key1844, -1), (key1337, -1), (key1466, -1), (key1345, -1), (key1774, -1), (key1546, -1), (key1780, -1), (key1391, -1), (key1559, -1), (key1397, -1), (key1817, 1), (key1424, 1), (key1825, 1), (key1316, 1), (key1447, 1), (key1329, 1)]

def rawRow3987 : Integer.Sparse Key := [(key1817, -2), (key1424, -2), (key1813, -2), (key1659, 1), (key1841, 1), (key1457, 1), (key1839, 1), (key1455, 1), (key1655, 1), (key1780, 2), (key1391, 2), (key1772, 2), (key1466, -1), (key1844, -1), (key1345, -1), (key1841, -1), (key1337, -1), (key1455, -1), (key1559, -1), (key1780, -1), (key1397, -1), (key1774, -1), (key1391, -1), (key1546, -1), (key1447, 1), (key1825, 1), (key1329, 1), (key1817, 1), (key1316, 1), (key1424, 1)]

def rawRow3988 : Integer.Sparse Key := [(key1817, -2), (key1813, -2), (key1424, -2), (key1841, 1), (key1659, 1), (key1839, 1), (key1457, 1), (key1655, 1), (key1455, 1), (key1780, 2), (key1772, 2), (key1391, 2), (key1844, -1), (key1466, -1), (key1841, -1), (key1345, -1), (key1455, -1), (key1337, -1), (key1780, -1), (key1559, -1), (key1774, -1), (key1397, -1), (key1546, -1), (key1391, -1), (key1825, 1), (key1447, 1), (key1817, 1), (key1329, 1), (key1424, 1), (key1316, 1)]

def rawRow3989 : Integer.Sparse Key := [(key1457, -2), (key1790, -2), (key1839, -2), (key1424, 1), (key1455, 1), (key1573, 1), (key1655, 1), (key1788, 1), (key1813, 1), (key1466, 2), (key1798, 2), (key1844, 2), (key1296, -1), (key1337, -1), (key1391, -1), (key1455, -1), (key1772, -1), (key1788, -1), (key1447, -1), (key1466, -1), (key1596, -1), (key1667, -1), (key1798, -1), (key1825, -1), (key1302, 1), (key1339, 1), (key1397, 1), (key1457, 1), (key1774, 1), (key1790, 1)]

def rawRow3990 : Integer.Sparse Key := [(key1457, -2), (key1839, -2), (key1790, -2), (key1455, 1), (key1424, 1), (key1655, 1), (key1573, 1), (key1813, 1), (key1788, 1), (key1466, 2), (key1844, 2), (key1798, 2), (key1337, -1), (key1296, -1), (key1455, -1), (key1391, -1), (key1788, -1), (key1772, -1), (key1466, -1), (key1447, -1), (key1667, -1), (key1596, -1), (key1825, -1), (key1798, -1), (key1339, 1), (key1302, 1), (key1457, 1), (key1397, 1), (key1790, 1), (key1774, 1)]

def rawRow3991 : Integer.Sparse Key := [(key1790, -2), (key1457, -2), (key1839, -2), (key1573, 1), (key1788, 1), (key1424, 1), (key1813, 1), (key1455, 1), (key1655, 1), (key1798, 2), (key1466, 2), (key1844, 2), (key1391, -1), (key1772, -1), (key1296, -1), (key1788, -1), (key1337, -1), (key1455, -1), (key1596, -1), (key1798, -1), (key1447, -1), (key1825, -1), (key1466, -1), (key1667, -1), (key1397, 1), (key1774, 1), (key1302, 1), (key1790, 1), (key1339, 1), (key1457, 1)]

def rawRow3992 : Integer.Sparse Key := [(key1790, -2), (key1839, -2), (key1457, -2), (key1788, 1), (key1573, 1), (key1813, 1), (key1424, 1), (key1655, 1), (key1455, 1), (key1798, 2), (key1844, 2), (key1466, 2), (key1772, -1), (key1391, -1), (key1788, -1), (key1296, -1), (key1455, -1), (key1337, -1), (key1798, -1), (key1596, -1), (key1825, -1), (key1447, -1), (key1667, -1), (key1466, -1), (key1774, 1), (key1397, 1), (key1790, 1), (key1302, 1), (key1457, 1), (key1339, 1)]

def rawRow3993 : Integer.Sparse Key := [(key1839, -2), (key1457, -2), (key1790, -2), (key1655, 1), (key1813, 1), (key1455, 1), (key1788, 1), (key1424, 1), (key1573, 1), (key1844, 2), (key1466, 2), (key1798, 2), (key1455, -1), (key1788, -1), (key1337, -1), (key1772, -1), (key1296, -1), (key1391, -1), (key1667, -1), (key1825, -1), (key1466, -1), (key1798, -1), (key1447, -1), (key1596, -1), (key1457, 1), (key1790, 1), (key1339, 1), (key1774, 1), (key1302, 1), (key1397, 1)]

def rawRow3994 : Integer.Sparse Key := [(key1839, -2), (key1790, -2), (key1457, -2), (key1813, 1), (key1655, 1), (key1788, 1), (key1455, 1), (key1573, 1), (key1424, 1), (key1844, 2), (key1798, 2), (key1466, 2), (key1788, -1), (key1455, -1), (key1772, -1), (key1337, -1), (key1391, -1), (key1296, -1), (key1825, -1), (key1667, -1), (key1798, -1), (key1466, -1), (key1596, -1), (key1447, -1), (key1790, 1), (key1457, 1), (key1774, 1), (key1339, 1), (key1397, 1), (key1302, 1)]

def rawRow3998 : Integer.Sparse Key := [(key1466, -2), (key1798, -2), (key1844, -2), (key1447, 1), (key1466, 1), (key1596, 1), (key1667, 1), (key1798, 1), (key1825, 1), (key1457, 2), (key1790, 2), (key1839, 2), (key1302, -1), (key1339, -1), (key1397, -1), (key1457, -1), (key1774, -1), (key1790, -1), (key1424, -1), (key1455, -1), (key1573, -1), (key1655, -1), (key1788, -1), (key1813, -1), (key1296, 1), (key1337, 1), (key1391, 1), (key1455, 1), (key1772, 1), (key1788, 1)]

def rawRow3999 : Integer.Sparse Key := [(key1466, -2), (key1844, -2), (key1798, -2), (key1466, 1), (key1447, 1), (key1667, 1), (key1596, 1), (key1825, 1), (key1798, 1), (key1457, 2), (key1839, 2), (key1790, 2), (key1339, -1), (key1302, -1), (key1457, -1), (key1397, -1), (key1790, -1), (key1774, -1), (key1455, -1), (key1424, -1), (key1655, -1), (key1573, -1), (key1813, -1), (key1788, -1), (key1337, 1), (key1296, 1), (key1455, 1), (key1391, 1), (key1788, 1), (key1772, 1)]

def rawRow4000 : Integer.Sparse Key := [(key1798, -2), (key1466, -2), (key1844, -2), (key1596, 1), (key1798, 1), (key1447, 1), (key1825, 1), (key1466, 1), (key1667, 1), (key1790, 2), (key1457, 2), (key1839, 2), (key1397, -1), (key1774, -1), (key1302, -1), (key1790, -1), (key1339, -1), (key1457, -1), (key1573, -1), (key1788, -1), (key1424, -1), (key1813, -1), (key1455, -1), (key1655, -1), (key1391, 1), (key1772, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1455, 1)]

def rawRow4001 : Integer.Sparse Key := [(key1798, -2), (key1844, -2), (key1466, -2), (key1798, 1), (key1596, 1), (key1825, 1), (key1447, 1), (key1667, 1), (key1466, 1), (key1790, 2), (key1839, 2), (key1457, 2), (key1774, -1), (key1397, -1), (key1790, -1), (key1302, -1), (key1457, -1), (key1339, -1), (key1788, -1), (key1573, -1), (key1813, -1), (key1424, -1), (key1655, -1), (key1455, -1), (key1772, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1455, 1), (key1337, 1)]

def rawRow4002 : Integer.Sparse Key := [(key1844, -2), (key1466, -2), (key1798, -2), (key1667, 1), (key1825, 1), (key1466, 1), (key1798, 1), (key1447, 1), (key1596, 1), (key1839, 2), (key1457, 2), (key1790, 2), (key1457, -1), (key1790, -1), (key1339, -1), (key1774, -1), (key1302, -1), (key1397, -1), (key1655, -1), (key1813, -1), (key1455, -1), (key1788, -1), (key1424, -1), (key1573, -1), (key1455, 1), (key1788, 1), (key1337, 1), (key1772, 1), (key1296, 1), (key1391, 1)]

def rawRow4003 : Integer.Sparse Key := [(key1844, -2), (key1798, -2), (key1466, -2), (key1825, 1), (key1667, 1), (key1798, 1), (key1466, 1), (key1596, 1), (key1447, 1), (key1839, 2), (key1790, 2), (key1457, 2), (key1790, -1), (key1457, -1), (key1774, -1), (key1339, -1), (key1397, -1), (key1302, -1), (key1813, -1), (key1655, -1), (key1788, -1), (key1455, -1), (key1573, -1), (key1424, -1), (key1788, 1), (key1455, 1), (key1772, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

def rawRow4004 : Integer.Sparse Key := [(key1527, -2), (key1533, -2), (key1893, -2), (key1533, 6), (key1605, 2), (key1611, 2), (key1915, 2), (key1258, -2), (key1611, -2), (key1639, -2), (key1678, -6), (key1270, 2), (key1678, 2), (key1692, 2)]

def rawRow4005 : Integer.Sparse Key := [(key1533, -2), (key1527, -2), (key1893, -2), (key1533, 6), (key1611, 2), (key1605, 2), (key1915, 2), (key1258, -2), (key1639, -2), (key1611, -2), (key1678, -6), (key1270, 2), (key1692, 2), (key1678, 2)]

def rawRow4006 : Integer.Sparse Key := [(key1527, -2), (key1893, -2), (key1533, -2), (key1533, 6), (key1605, 2), (key1915, 2), (key1611, 2), (key1611, -2), (key1258, -2), (key1639, -2), (key1678, -6), (key1678, 2), (key1270, 2), (key1692, 2)]

def rawRow4007 : Integer.Sparse Key := [(key1893, -2), (key1527, -2), (key1533, -2), (key1533, 6), (key1915, 2), (key1605, 2), (key1611, 2), (key1611, -2), (key1639, -2), (key1258, -2), (key1678, -6), (key1678, 2), (key1692, 2), (key1270, 2)]

def rawRow4008 : Integer.Sparse Key := [(key1533, -2), (key1893, -2), (key1527, -2), (key1533, 6), (key1611, 2), (key1915, 2), (key1605, 2), (key1639, -2), (key1258, -2), (key1611, -2), (key1678, -6), (key1692, 2), (key1270, 2), (key1678, 2)]

def rawRow4009 : Integer.Sparse Key := [(key1893, -2), (key1533, -2), (key1527, -2), (key1533, 6), (key1915, 2), (key1611, 2), (key1605, 2), (key1639, -2), (key1611, -2), (key1258, -2), (key1678, -6), (key1692, 2), (key1678, 2), (key1270, 2)]

def rawRow4010 : Integer.Sparse Key := [(key1533, -2), (key1533, -2), (key1893, -2), (key1527, 6), (key1639, 2), (key1639, 2), (key1929, 2), (key1252, -2), (key1605, -2), (key1605, -2), (key1692, -6), (key1270, 2), (key1678, 2), (key1678, 2)]

def rawRow4011 : Integer.Sparse Key := [(key1533, -2), (key1893, -2), (key1533, -2), (key1527, 6), (key1639, 2), (key1929, 2), (key1639, 2), (key1605, -2), (key1252, -2), (key1605, -2), (key1692, -6), (key1678, 2), (key1270, 2), (key1678, 2)]

def rawRow4012 : Integer.Sparse Key := [(key1893, -2), (key1533, -2), (key1533, -2), (key1527, 6), (key1929, 2), (key1639, 2), (key1639, 2), (key1605, -2), (key1605, -2), (key1252, -2), (key1692, -6), (key1678, 2), (key1678, 2), (key1270, 2)]

def rawRow4013 : Integer.Sparse Key := [(key1605, -2), (key1611, -2), (key1915, -2), (key1678, 6), (key1527, 2), (key1533, 2), (key1893, 2), (key1270, -2), (key1678, -2), (key1692, -2), (key1533, -6), (key1258, 2), (key1611, 2), (key1639, 2)]

def rawRow4014 : Integer.Sparse Key := [(key1611, -2), (key1605, -2), (key1915, -2), (key1678, 6), (key1533, 2), (key1527, 2), (key1893, 2), (key1270, -2), (key1692, -2), (key1678, -2), (key1533, -6), (key1258, 2), (key1639, 2), (key1611, 2)]

def rawRow4015 : Integer.Sparse Key := [(key1605, -2), (key1915, -2), (key1611, -2), (key1678, 6), (key1527, 2), (key1893, 2), (key1533, 2), (key1678, -2), (key1270, -2), (key1692, -2), (key1533, -6), (key1611, 2), (key1258, 2), (key1639, 2)]

def rawRow4016 : Integer.Sparse Key := [(key1915, -2), (key1605, -2), (key1611, -2), (key1678, 6), (key1893, 2), (key1527, 2), (key1533, 2), (key1678, -2), (key1692, -2), (key1270, -2), (key1533, -6), (key1611, 2), (key1639, 2), (key1258, 2)]

def rawRow4017 : Integer.Sparse Key := [(key1611, -2), (key1915, -2), (key1605, -2), (key1678, 6), (key1533, 2), (key1893, 2), (key1527, 2), (key1692, -2), (key1270, -2), (key1678, -2), (key1533, -6), (key1639, 2), (key1258, 2), (key1611, 2)]

def rawRow4018 : Integer.Sparse Key := [(key1915, -2), (key1611, -2), (key1605, -2), (key1678, 6), (key1893, 2), (key1533, 2), (key1527, 2), (key1692, -2), (key1678, -2), (key1270, -2), (key1533, -6), (key1639, 2), (key1611, 2), (key1258, 2)]

def rawRow4019 : Integer.Sparse Key := [(key1611, -2), (key1678, -2), (key1915, -2), (key1605, 6), (key1639, 2), (key1692, 2), (key1929, 2), (key1252, -2), (key1527, -2), (key1605, -2), (key1639, -6), (key1258, 2), (key1533, 2), (key1611, 2)]

def rawRow4020 : Integer.Sparse Key := [(key1678, -2), (key1611, -2), (key1915, -2), (key1605, 6), (key1692, 2), (key1639, 2), (key1929, 2), (key1252, -2), (key1605, -2), (key1527, -2), (key1639, -6), (key1258, 2), (key1611, 2), (key1533, 2)]

def rawRow4021 : Integer.Sparse Key := [(key1611, -2), (key1915, -2), (key1678, -2), (key1605, 6), (key1639, 2), (key1929, 2), (key1692, 2), (key1527, -2), (key1252, -2), (key1605, -2), (key1639, -6), (key1533, 2), (key1258, 2), (key1611, 2)]

def rawRow4022 : Integer.Sparse Key := [(key1915, -2), (key1611, -2), (key1678, -2), (key1605, 6), (key1929, 2), (key1639, 2), (key1692, 2), (key1527, -2), (key1605, -2), (key1252, -2), (key1639, -6), (key1533, 2), (key1611, 2), (key1258, 2)]

def rawRow4023 : Integer.Sparse Key := [(key1678, -2), (key1915, -2), (key1611, -2), (key1605, 6), (key1692, 2), (key1929, 2), (key1639, 2), (key1605, -2), (key1252, -2), (key1527, -2), (key1639, -6), (key1611, 2), (key1258, 2), (key1533, 2)]

def rawRow4024 : Integer.Sparse Key := [(key1915, -2), (key1678, -2), (key1611, -2), (key1605, 6), (key1929, 2), (key1692, 2), (key1639, 2), (key1605, -2), (key1527, -2), (key1252, -2), (key1639, -6), (key1611, 2), (key1533, 2), (key1258, 2)]

def rawRow4025 : Integer.Sparse Key := [(key1639, -2), (key1639, -2), (key1929, -2), (key1692, 6), (key1533, 2), (key1533, 2), (key1893, 2), (key1270, -2), (key1678, -2), (key1678, -2), (key1527, -6), (key1252, 2), (key1605, 2), (key1605, 2)]

def rawRow4026 : Integer.Sparse Key := [(key1639, -2), (key1929, -2), (key1639, -2), (key1692, 6), (key1533, 2), (key1893, 2), (key1533, 2), (key1678, -2), (key1270, -2), (key1678, -2), (key1527, -6), (key1605, 2), (key1252, 2), (key1605, 2)]

def rawRow4027 : Integer.Sparse Key := [(key1929, -2), (key1639, -2), (key1639, -2), (key1692, 6), (key1893, 2), (key1533, 2), (key1533, 2), (key1678, -2), (key1678, -2), (key1270, -2), (key1527, -6), (key1605, 2), (key1605, 2), (key1252, 2)]

def rawRow4028 : Integer.Sparse Key := [(key1639, -2), (key1692, -2), (key1929, -2), (key1639, 6), (key1611, 2), (key1678, 2), (key1915, 2), (key1258, -2), (key1533, -2), (key1611, -2), (key1605, -6), (key1252, 2), (key1527, 2), (key1605, 2)]

def rawRow4029 : Integer.Sparse Key := [(key1692, -2), (key1639, -2), (key1929, -2), (key1639, 6), (key1678, 2), (key1611, 2), (key1915, 2), (key1258, -2), (key1611, -2), (key1533, -2), (key1605, -6), (key1252, 2), (key1605, 2), (key1527, 2)]

def rawRow4030 : Integer.Sparse Key := [(key1639, -2), (key1929, -2), (key1692, -2), (key1639, 6), (key1611, 2), (key1915, 2), (key1678, 2), (key1533, -2), (key1258, -2), (key1611, -2), (key1605, -6), (key1527, 2), (key1252, 2), (key1605, 2)]

def rawRow4031 : Integer.Sparse Key := [(key1929, -2), (key1639, -2), (key1692, -2), (key1639, 6), (key1915, 2), (key1611, 2), (key1678, 2), (key1533, -2), (key1611, -2), (key1258, -2), (key1605, -6), (key1527, 2), (key1605, 2), (key1252, 2)]

def rawRow4032 : Integer.Sparse Key := [(key1692, -2), (key1929, -2), (key1639, -2), (key1639, 6), (key1678, 2), (key1915, 2), (key1611, 2), (key1611, -2), (key1258, -2), (key1533, -2), (key1605, -6), (key1605, 2), (key1252, 2), (key1527, 2)]

def rawRow4033 : Integer.Sparse Key := [(key1929, -2), (key1692, -2), (key1639, -2), (key1639, 6), (key1915, 2), (key1678, 2), (key1611, 2), (key1611, -2), (key1533, -2), (key1258, -2), (key1605, -6), (key1605, 2), (key1527, 2), (key1252, 2)]

def rawRow4034 : Integer.Sparse Key := [(key1526, -2), (key1530, -2), (key1764, -2), (key1530, 6), (key1604, 2), (key1608, 2), (key1805, 2), (key1255, -2), (key1608, -2), (key1637, -2), (key1647, -6), (key1264, 2), (key1647, 2), (key1671, 2)]

def rawRow4035 : Integer.Sparse Key := [(key1530, -2), (key1526, -2), (key1764, -2), (key1530, 6), (key1608, 2), (key1604, 2), (key1805, 2), (key1255, -2), (key1637, -2), (key1608, -2), (key1647, -6), (key1264, 2), (key1671, 2), (key1647, 2)]

def rawRow4036 : Integer.Sparse Key := [(key1526, -2), (key1764, -2), (key1530, -2), (key1530, 6), (key1604, 2), (key1805, 2), (key1608, 2), (key1608, -2), (key1255, -2), (key1637, -2), (key1647, -6), (key1647, 2), (key1264, 2), (key1671, 2)]

def rawRow4037 : Integer.Sparse Key := [(key1764, -2), (key1526, -2), (key1530, -2), (key1530, 6), (key1805, 2), (key1604, 2), (key1608, 2), (key1608, -2), (key1637, -2), (key1255, -2), (key1647, -6), (key1647, 2), (key1671, 2), (key1264, 2)]

def rawRow4038 : Integer.Sparse Key := [(key1530, -2), (key1764, -2), (key1526, -2), (key1530, 6), (key1608, 2), (key1805, 2), (key1604, 2), (key1637, -2), (key1255, -2), (key1608, -2), (key1647, -6), (key1671, 2), (key1264, 2), (key1647, 2)]

def rawRow4039 : Integer.Sparse Key := [(key1764, -2), (key1530, -2), (key1526, -2), (key1530, 6), (key1805, 2), (key1608, 2), (key1604, 2), (key1637, -2), (key1608, -2), (key1255, -2), (key1647, -6), (key1671, 2), (key1647, 2), (key1264, 2)]

def rawRow4040 : Integer.Sparse Key := [(key1530, -2), (key1530, -2), (key1764, -2), (key1526, 6), (key1637, 2), (key1637, 2), (key1829, 2), (key1251, -2), (key1604, -2), (key1604, -2), (key1671, -6), (key1264, 2), (key1647, 2), (key1647, 2)]

def rawRow4041 : Integer.Sparse Key := [(key1530, -2), (key1764, -2), (key1530, -2), (key1526, 6), (key1637, 2), (key1829, 2), (key1637, 2), (key1604, -2), (key1251, -2), (key1604, -2), (key1671, -6), (key1647, 2), (key1264, 2), (key1647, 2)]

def rawRow4042 : Integer.Sparse Key := [(key1764, -2), (key1530, -2), (key1530, -2), (key1526, 6), (key1829, 2), (key1637, 2), (key1637, 2), (key1604, -2), (key1604, -2), (key1251, -2), (key1671, -6), (key1647, 2), (key1647, 2), (key1264, 2)]

def rawRow4043 : Integer.Sparse Key := [(key1604, -2), (key1608, -2), (key1805, -2), (key1647, 6), (key1526, 2), (key1530, 2), (key1764, 2), (key1264, -2), (key1647, -2), (key1671, -2), (key1530, -6), (key1255, 2), (key1608, 2), (key1637, 2)]

def rawRow4044 : Integer.Sparse Key := [(key1608, -2), (key1604, -2), (key1805, -2), (key1647, 6), (key1530, 2), (key1526, 2), (key1764, 2), (key1264, -2), (key1671, -2), (key1647, -2), (key1530, -6), (key1255, 2), (key1637, 2), (key1608, 2)]

def rawRow4045 : Integer.Sparse Key := [(key1604, -2), (key1805, -2), (key1608, -2), (key1647, 6), (key1526, 2), (key1764, 2), (key1530, 2), (key1647, -2), (key1264, -2), (key1671, -2), (key1530, -6), (key1608, 2), (key1255, 2), (key1637, 2)]

def rawRow4046 : Integer.Sparse Key := [(key1805, -2), (key1604, -2), (key1608, -2), (key1647, 6), (key1764, 2), (key1526, 2), (key1530, 2), (key1647, -2), (key1671, -2), (key1264, -2), (key1530, -6), (key1608, 2), (key1637, 2), (key1255, 2)]

def rawRow4047 : Integer.Sparse Key := [(key1608, -2), (key1805, -2), (key1604, -2), (key1647, 6), (key1530, 2), (key1764, 2), (key1526, 2), (key1671, -2), (key1264, -2), (key1647, -2), (key1530, -6), (key1637, 2), (key1255, 2), (key1608, 2)]

def rawRow4048 : Integer.Sparse Key := [(key1805, -2), (key1608, -2), (key1604, -2), (key1647, 6), (key1764, 2), (key1530, 2), (key1526, 2), (key1671, -2), (key1647, -2), (key1264, -2), (key1530, -6), (key1637, 2), (key1608, 2), (key1255, 2)]

def rawRow4049 : Integer.Sparse Key := [(key1608, -2), (key1647, -2), (key1805, -2), (key1604, 6), (key1637, 2), (key1671, 2), (key1829, 2), (key1251, -2), (key1526, -2), (key1604, -2), (key1637, -6), (key1255, 2), (key1530, 2), (key1608, 2)]

def rawRow4050 : Integer.Sparse Key := [(key1647, -2), (key1608, -2), (key1805, -2), (key1604, 6), (key1671, 2), (key1637, 2), (key1829, 2), (key1251, -2), (key1604, -2), (key1526, -2), (key1637, -6), (key1255, 2), (key1608, 2), (key1530, 2)]

def rawRow4051 : Integer.Sparse Key := [(key1608, -2), (key1805, -2), (key1647, -2), (key1604, 6), (key1637, 2), (key1829, 2), (key1671, 2), (key1526, -2), (key1251, -2), (key1604, -2), (key1637, -6), (key1530, 2), (key1255, 2), (key1608, 2)]

def rawRow4052 : Integer.Sparse Key := [(key1805, -2), (key1608, -2), (key1647, -2), (key1604, 6), (key1829, 2), (key1637, 2), (key1671, 2), (key1526, -2), (key1604, -2), (key1251, -2), (key1637, -6), (key1530, 2), (key1608, 2), (key1255, 2)]

def rawRow4053 : Integer.Sparse Key := [(key1647, -2), (key1805, -2), (key1608, -2), (key1604, 6), (key1671, 2), (key1829, 2), (key1637, 2), (key1604, -2), (key1251, -2), (key1526, -2), (key1637, -6), (key1608, 2), (key1255, 2), (key1530, 2)]

def rawRow4054 : Integer.Sparse Key := [(key1805, -2), (key1647, -2), (key1608, -2), (key1604, 6), (key1829, 2), (key1671, 2), (key1637, 2), (key1604, -2), (key1526, -2), (key1251, -2), (key1637, -6), (key1608, 2), (key1530, 2), (key1255, 2)]

def rawRow4055 : Integer.Sparse Key := [(key1637, -2), (key1637, -2), (key1829, -2), (key1671, 6), (key1530, 2), (key1530, 2), (key1764, 2), (key1264, -2), (key1647, -2), (key1647, -2), (key1526, -6), (key1251, 2), (key1604, 2), (key1604, 2)]

def rawRow4056 : Integer.Sparse Key := [(key1637, -2), (key1829, -2), (key1637, -2), (key1671, 6), (key1530, 2), (key1764, 2), (key1530, 2), (key1647, -2), (key1264, -2), (key1647, -2), (key1526, -6), (key1604, 2), (key1251, 2), (key1604, 2)]

def rawRow4057 : Integer.Sparse Key := [(key1829, -2), (key1637, -2), (key1637, -2), (key1671, 6), (key1764, 2), (key1530, 2), (key1530, 2), (key1647, -2), (key1647, -2), (key1264, -2), (key1526, -6), (key1604, 2), (key1604, 2), (key1251, 2)]

def rawRow4058 : Integer.Sparse Key := [(key1637, -2), (key1671, -2), (key1829, -2), (key1637, 6), (key1608, 2), (key1647, 2), (key1805, 2), (key1255, -2), (key1530, -2), (key1608, -2), (key1604, -6), (key1251, 2), (key1526, 2), (key1604, 2)]

def rawRow4059 : Integer.Sparse Key := [(key1671, -2), (key1637, -2), (key1829, -2), (key1637, 6), (key1647, 2), (key1608, 2), (key1805, 2), (key1255, -2), (key1608, -2), (key1530, -2), (key1604, -6), (key1251, 2), (key1604, 2), (key1526, 2)]

def rawRow4060 : Integer.Sparse Key := [(key1637, -2), (key1829, -2), (key1671, -2), (key1637, 6), (key1608, 2), (key1805, 2), (key1647, 2), (key1530, -2), (key1255, -2), (key1608, -2), (key1604, -6), (key1526, 2), (key1251, 2), (key1604, 2)]

def rawRow4061 : Integer.Sparse Key := [(key1829, -2), (key1637, -2), (key1671, -2), (key1637, 6), (key1805, 2), (key1608, 2), (key1647, 2), (key1530, -2), (key1608, -2), (key1255, -2), (key1604, -6), (key1526, 2), (key1604, 2), (key1251, 2)]

def rawRow4062 : Integer.Sparse Key := [(key1671, -2), (key1829, -2), (key1637, -2), (key1637, 6), (key1647, 2), (key1805, 2), (key1608, 2), (key1608, -2), (key1255, -2), (key1530, -2), (key1604, -6), (key1604, 2), (key1251, 2), (key1526, 2)]

def rawRow4063 : Integer.Sparse Key := [(key1829, -2), (key1671, -2), (key1637, -2), (key1637, 6), (key1805, 2), (key1647, 2), (key1608, 2), (key1608, -2), (key1530, -2), (key1255, -2), (key1604, -6), (key1604, 2), (key1526, 2), (key1251, 2)]

def rawRow4064 : Integer.Sparse Key := [(key1541, -2), (key1545, -2), (key1771, -2), (key1386, 1), (key1390, 1), (key1541, 1), (key1554, 1), (key1771, 1), (key1778, 1), (key1568, 2), (key1572, 2), (key1787, 2), (key1291, -1), (key1295, -1), (key1568, -1), (key1591, -1), (key1787, -1), (key1796, -1), (key1419, -1), (key1423, -1), (key1617, -1), (key1622, -1), (key1812, -1), (key1815, -1), (key1311, 1), (key1315, 1), (key1617, 1), (key1631, 1), (key1812, 1), (key1823, 1)]

def rawRow4065 : Integer.Sparse Key := [(key1545, -2), (key1541, -2), (key1771, -2), (key1390, 1), (key1386, 1), (key1554, 1), (key1541, 1), (key1778, 1), (key1771, 1), (key1572, 2), (key1568, 2), (key1787, 2), (key1295, -1), (key1291, -1), (key1591, -1), (key1568, -1), (key1796, -1), (key1787, -1), (key1423, -1), (key1419, -1), (key1622, -1), (key1617, -1), (key1815, -1), (key1812, -1), (key1315, 1), (key1311, 1), (key1631, 1), (key1617, 1), (key1823, 1), (key1812, 1)]

def rawRow4066 : Integer.Sparse Key := [(key1541, -2), (key1771, -2), (key1545, -2), (key1541, 1), (key1771, 1), (key1386, 1), (key1778, 1), (key1390, 1), (key1554, 1), (key1568, 2), (key1787, 2), (key1572, 2), (key1568, -1), (key1787, -1), (key1291, -1), (key1796, -1), (key1295, -1), (key1591, -1), (key1617, -1), (key1812, -1), (key1419, -1), (key1815, -1), (key1423, -1), (key1622, -1), (key1617, 1), (key1812, 1), (key1311, 1), (key1823, 1), (key1315, 1), (key1631, 1)]

def rawRow4067 : Integer.Sparse Key := [(key1771, -2), (key1541, -2), (key1545, -2), (key1771, 1), (key1541, 1), (key1778, 1), (key1386, 1), (key1554, 1), (key1390, 1), (key1787, 2), (key1568, 2), (key1572, 2), (key1787, -1), (key1568, -1), (key1796, -1), (key1291, -1), (key1591, -1), (key1295, -1), (key1812, -1), (key1617, -1), (key1815, -1), (key1419, -1), (key1622, -1), (key1423, -1), (key1812, 1), (key1617, 1), (key1823, 1), (key1311, 1), (key1631, 1), (key1315, 1)]

def rawRow4068 : Integer.Sparse Key := [(key1545, -2), (key1771, -2), (key1541, -2), (key1554, 1), (key1778, 1), (key1390, 1), (key1771, 1), (key1386, 1), (key1541, 1), (key1572, 2), (key1787, 2), (key1568, 2), (key1591, -1), (key1796, -1), (key1295, -1), (key1787, -1), (key1291, -1), (key1568, -1), (key1622, -1), (key1815, -1), (key1423, -1), (key1812, -1), (key1419, -1), (key1617, -1), (key1631, 1), (key1823, 1), (key1315, 1), (key1812, 1), (key1311, 1), (key1617, 1)]

def rawRow4069 : Integer.Sparse Key := [(key1771, -2), (key1545, -2), (key1541, -2), (key1778, 1), (key1554, 1), (key1771, 1), (key1390, 1), (key1541, 1), (key1386, 1), (key1787, 2), (key1572, 2), (key1568, 2), (key1796, -1), (key1591, -1), (key1787, -1), (key1295, -1), (key1568, -1), (key1291, -1), (key1815, -1), (key1622, -1), (key1812, -1), (key1423, -1), (key1617, -1), (key1419, -1), (key1823, 1), (key1631, 1), (key1812, 1), (key1315, 1), (key1617, 1), (key1311, 1)]

def rawRow4073 : Integer.Sparse Key := [(key1568, -2), (key1572, -2), (key1787, -2), (key1419, 1), (key1423, 1), (key1617, 1), (key1622, 1), (key1812, 1), (key1815, 1), (key1541, 2), (key1545, 2), (key1771, 2), (key1311, -1), (key1315, -1), (key1617, -1), (key1631, -1), (key1812, -1), (key1823, -1), (key1386, -1), (key1390, -1), (key1541, -1), (key1554, -1), (key1771, -1), (key1778, -1), (key1291, 1), (key1295, 1), (key1568, 1), (key1591, 1), (key1787, 1), (key1796, 1)]

def rawRow4074 : Integer.Sparse Key := [(key1572, -2), (key1568, -2), (key1787, -2), (key1423, 1), (key1419, 1), (key1622, 1), (key1617, 1), (key1815, 1), (key1812, 1), (key1545, 2), (key1541, 2), (key1771, 2), (key1315, -1), (key1311, -1), (key1631, -1), (key1617, -1), (key1823, -1), (key1812, -1), (key1390, -1), (key1386, -1), (key1554, -1), (key1541, -1), (key1778, -1), (key1771, -1), (key1295, 1), (key1291, 1), (key1591, 1), (key1568, 1), (key1796, 1), (key1787, 1)]

def rawRow4075 : Integer.Sparse Key := [(key1568, -2), (key1787, -2), (key1572, -2), (key1617, 1), (key1812, 1), (key1419, 1), (key1815, 1), (key1423, 1), (key1622, 1), (key1541, 2), (key1771, 2), (key1545, 2), (key1617, -1), (key1812, -1), (key1311, -1), (key1823, -1), (key1315, -1), (key1631, -1), (key1541, -1), (key1771, -1), (key1386, -1), (key1778, -1), (key1390, -1), (key1554, -1), (key1568, 1), (key1787, 1), (key1291, 1), (key1796, 1), (key1295, 1), (key1591, 1)]

def rawRow4076 : Integer.Sparse Key := [(key1787, -2), (key1568, -2), (key1572, -2), (key1812, 1), (key1617, 1), (key1815, 1), (key1419, 1), (key1622, 1), (key1423, 1), (key1771, 2), (key1541, 2), (key1545, 2), (key1812, -1), (key1617, -1), (key1823, -1), (key1311, -1), (key1631, -1), (key1315, -1), (key1771, -1), (key1541, -1), (key1778, -1), (key1386, -1), (key1554, -1), (key1390, -1), (key1787, 1), (key1568, 1), (key1796, 1), (key1291, 1), (key1591, 1), (key1295, 1)]

def rawRow4077 : Integer.Sparse Key := [(key1572, -2), (key1787, -2), (key1568, -2), (key1622, 1), (key1815, 1), (key1423, 1), (key1812, 1), (key1419, 1), (key1617, 1), (key1545, 2), (key1771, 2), (key1541, 2), (key1631, -1), (key1823, -1), (key1315, -1), (key1812, -1), (key1311, -1), (key1617, -1), (key1554, -1), (key1778, -1), (key1390, -1), (key1771, -1), (key1386, -1), (key1541, -1), (key1591, 1), (key1796, 1), (key1295, 1), (key1787, 1), (key1291, 1), (key1568, 1)]

def rawRow4078 : Integer.Sparse Key := [(key1787, -2), (key1572, -2), (key1568, -2), (key1815, 1), (key1622, 1), (key1812, 1), (key1423, 1), (key1617, 1), (key1419, 1), (key1771, 2), (key1545, 2), (key1541, 2), (key1823, -1), (key1631, -1), (key1812, -1), (key1315, -1), (key1617, -1), (key1311, -1), (key1778, -1), (key1554, -1), (key1771, -1), (key1390, -1), (key1541, -1), (key1386, -1), (key1796, 1), (key1591, 1), (key1787, 1), (key1295, 1), (key1568, 1), (key1291, 1)]

def rawRow4079 : Integer.Sparse Key := [(key1622, -2), (key1657, -2), (key1815, -2), (key1423, 1), (key1454, 1), (key1572, 1), (key1654, 1), (key1787, 1), (key1812, 1), (key1631, 2), (key1665, 2), (key1823, 2), (key1315, -1), (key1336, -1), (key1545, -1), (key1654, -1), (key1771, -1), (key1812, -1), (key1442, -1), (key1464, -1), (key1591, -1), (key1665, -1), (key1796, -1), (key1823, -1), (key1324, 1), (key1343, 1), (key1554, 1), (key1657, 1), (key1778, 1), (key1815, 1)]

def rawRow4080 : Integer.Sparse Key := [(key1657, -2), (key1622, -2), (key1815, -2), (key1454, 1), (key1423, 1), (key1654, 1), (key1572, 1), (key1812, 1), (key1787, 1), (key1665, 2), (key1631, 2), (key1823, 2), (key1336, -1), (key1315, -1), (key1654, -1), (key1545, -1), (key1812, -1), (key1771, -1), (key1464, -1), (key1442, -1), (key1665, -1), (key1591, -1), (key1823, -1), (key1796, -1), (key1343, 1), (key1324, 1), (key1657, 1), (key1554, 1), (key1815, 1), (key1778, 1)]

def rawRow4081 : Integer.Sparse Key := [(key1622, -2), (key1815, -2), (key1657, -2), (key1572, 1), (key1787, 1), (key1423, 1), (key1812, 1), (key1454, 1), (key1654, 1), (key1631, 2), (key1823, 2), (key1665, 2), (key1545, -1), (key1771, -1), (key1315, -1), (key1812, -1), (key1336, -1), (key1654, -1), (key1591, -1), (key1796, -1), (key1442, -1), (key1823, -1), (key1464, -1), (key1665, -1), (key1554, 1), (key1778, 1), (key1324, 1), (key1815, 1), (key1343, 1), (key1657, 1)]

def rawRow4082 : Integer.Sparse Key := [(key1815, -2), (key1622, -2), (key1657, -2), (key1787, 1), (key1572, 1), (key1812, 1), (key1423, 1), (key1654, 1), (key1454, 1), (key1823, 2), (key1631, 2), (key1665, 2), (key1771, -1), (key1545, -1), (key1812, -1), (key1315, -1), (key1654, -1), (key1336, -1), (key1796, -1), (key1591, -1), (key1823, -1), (key1442, -1), (key1665, -1), (key1464, -1), (key1778, 1), (key1554, 1), (key1815, 1), (key1324, 1), (key1657, 1), (key1343, 1)]

def rawRow4083 : Integer.Sparse Key := [(key1657, -2), (key1815, -2), (key1622, -2), (key1654, 1), (key1812, 1), (key1454, 1), (key1787, 1), (key1423, 1), (key1572, 1), (key1665, 2), (key1823, 2), (key1631, 2), (key1654, -1), (key1812, -1), (key1336, -1), (key1771, -1), (key1315, -1), (key1545, -1), (key1665, -1), (key1823, -1), (key1464, -1), (key1796, -1), (key1442, -1), (key1591, -1), (key1657, 1), (key1815, 1), (key1343, 1), (key1778, 1), (key1324, 1), (key1554, 1)]

def rawRow4084 : Integer.Sparse Key := [(key1815, -2), (key1657, -2), (key1622, -2), (key1812, 1), (key1654, 1), (key1787, 1), (key1454, 1), (key1572, 1), (key1423, 1), (key1823, 2), (key1665, 2), (key1631, 2), (key1812, -1), (key1654, -1), (key1771, -1), (key1336, -1), (key1545, -1), (key1315, -1), (key1823, -1), (key1665, -1), (key1796, -1), (key1464, -1), (key1591, -1), (key1442, -1), (key1815, 1), (key1657, 1), (key1778, 1), (key1343, 1), (key1554, 1), (key1324, 1)]

def rawRow4088 : Integer.Sparse Key := [(key1631, -2), (key1665, -2), (key1823, -2), (key1442, 1), (key1464, 1), (key1591, 1), (key1665, 1), (key1796, 1), (key1823, 1), (key1622, 2), (key1657, 2), (key1815, 2), (key1324, -1), (key1343, -1), (key1554, -1), (key1657, -1), (key1778, -1), (key1815, -1), (key1423, -1), (key1454, -1), (key1572, -1), (key1654, -1), (key1787, -1), (key1812, -1), (key1315, 1), (key1336, 1), (key1545, 1), (key1654, 1), (key1771, 1), (key1812, 1)]

def rawRow4089 : Integer.Sparse Key := [(key1665, -2), (key1631, -2), (key1823, -2), (key1464, 1), (key1442, 1), (key1665, 1), (key1591, 1), (key1823, 1), (key1796, 1), (key1657, 2), (key1622, 2), (key1815, 2), (key1343, -1), (key1324, -1), (key1657, -1), (key1554, -1), (key1815, -1), (key1778, -1), (key1454, -1), (key1423, -1), (key1654, -1), (key1572, -1), (key1812, -1), (key1787, -1), (key1336, 1), (key1315, 1), (key1654, 1), (key1545, 1), (key1812, 1), (key1771, 1)]

def rawRow4090 : Integer.Sparse Key := [(key1631, -2), (key1823, -2), (key1665, -2), (key1591, 1), (key1796, 1), (key1442, 1), (key1823, 1), (key1464, 1), (key1665, 1), (key1622, 2), (key1815, 2), (key1657, 2), (key1554, -1), (key1778, -1), (key1324, -1), (key1815, -1), (key1343, -1), (key1657, -1), (key1572, -1), (key1787, -1), (key1423, -1), (key1812, -1), (key1454, -1), (key1654, -1), (key1545, 1), (key1771, 1), (key1315, 1), (key1812, 1), (key1336, 1), (key1654, 1)]

def rawRow4091 : Integer.Sparse Key := [(key1823, -2), (key1631, -2), (key1665, -2), (key1796, 1), (key1591, 1), (key1823, 1), (key1442, 1), (key1665, 1), (key1464, 1), (key1815, 2), (key1622, 2), (key1657, 2), (key1778, -1), (key1554, -1), (key1815, -1), (key1324, -1), (key1657, -1), (key1343, -1), (key1787, -1), (key1572, -1), (key1812, -1), (key1423, -1), (key1654, -1), (key1454, -1), (key1771, 1), (key1545, 1), (key1812, 1), (key1315, 1), (key1654, 1), (key1336, 1)]

def rawRow4092 : Integer.Sparse Key := [(key1665, -2), (key1823, -2), (key1631, -2), (key1665, 1), (key1823, 1), (key1464, 1), (key1796, 1), (key1442, 1), (key1591, 1), (key1657, 2), (key1815, 2), (key1622, 2), (key1657, -1), (key1815, -1), (key1343, -1), (key1778, -1), (key1324, -1), (key1554, -1), (key1654, -1), (key1812, -1), (key1454, -1), (key1787, -1), (key1423, -1), (key1572, -1), (key1654, 1), (key1812, 1), (key1336, 1), (key1771, 1), (key1315, 1), (key1545, 1)]

def rawRow4093 : Integer.Sparse Key := [(key1823, -2), (key1665, -2), (key1631, -2), (key1823, 1), (key1665, 1), (key1796, 1), (key1464, 1), (key1591, 1), (key1442, 1), (key1815, 2), (key1657, 2), (key1622, 2), (key1815, -1), (key1657, -1), (key1778, -1), (key1343, -1), (key1554, -1), (key1324, -1), (key1812, -1), (key1654, -1), (key1787, -1), (key1454, -1), (key1572, -1), (key1423, -1), (key1812, 1), (key1654, 1), (key1771, 1), (key1336, 1), (key1545, 1), (key1315, 1)]

def rawRow4094 : Integer.Sparse Key := [(key830, -2), (key831, -2), (key840, -2), (key831, 6), (key924, 2), (key925, 2), (key935, 2), (key747, -2), (key925, -2), (key960, -2), (key928, -6), (key751, 2), (key928, 2), (key962, 2)]

def rawRow4095 : Integer.Sparse Key := [(key831, -2), (key830, -2), (key840, -2), (key831, 6), (key925, 2), (key924, 2), (key935, 2), (key747, -2), (key960, -2), (key925, -2), (key928, -6), (key751, 2), (key962, 2), (key928, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4096 : Integer.Sparse Key := [(key830, -2), (key840, -2), (key831, -2), (key831, 6), (key924, 2), (key935, 2), (key925, 2), (key925, -2), (key747, -2), (key960, -2), (key928, -6), (key928, 2), (key751, 2), (key962, 2)]

def rawRow4097 : Integer.Sparse Key := [(key840, -2), (key830, -2), (key831, -2), (key831, 6), (key935, 2), (key924, 2), (key925, 2), (key925, -2), (key960, -2), (key747, -2), (key928, -6), (key928, 2), (key962, 2), (key751, 2)]

def rawRow4098 : Integer.Sparse Key := [(key831, -2), (key840, -2), (key830, -2), (key831, 6), (key925, 2), (key935, 2), (key924, 2), (key960, -2), (key747, -2), (key925, -2), (key928, -6), (key962, 2), (key751, 2), (key928, 2)]

def rawRow4099 : Integer.Sparse Key := [(key840, -2), (key831, -2), (key830, -2), (key831, 6), (key935, 2), (key925, 2), (key924, 2), (key960, -2), (key925, -2), (key747, -2), (key928, -6), (key962, 2), (key928, 2), (key751, 2)]

def rawRow4100 : Integer.Sparse Key := [(key831, -2), (key831, -2), (key840, -2), (key830, 6), (key960, 2), (key960, 2), (key964, 2), (key746, -2), (key924, -2), (key924, -2), (key962, -6), (key751, 2), (key928, 2), (key928, 2)]

def rawRow4101 : Integer.Sparse Key := [(key831, -2), (key840, -2), (key831, -2), (key830, 6), (key960, 2), (key964, 2), (key960, 2), (key924, -2), (key746, -2), (key924, -2), (key962, -6), (key928, 2), (key751, 2), (key928, 2)]

def rawRow4102 : Integer.Sparse Key := [(key840, -2), (key831, -2), (key831, -2), (key830, 6), (key964, 2), (key960, 2), (key960, 2), (key924, -2), (key924, -2), (key746, -2), (key962, -6), (key928, 2), (key928, 2), (key751, 2)]

def rawRow4103 : Integer.Sparse Key := [(key924, -2), (key925, -2), (key935, -2), (key928, 6), (key830, 2), (key831, 2), (key840, 2), (key751, -2), (key928, -2), (key962, -2), (key831, -6), (key747, 2), (key925, 2), (key960, 2)]

def rawRow4104 : Integer.Sparse Key := [(key925, -2), (key924, -2), (key935, -2), (key928, 6), (key831, 2), (key830, 2), (key840, 2), (key751, -2), (key962, -2), (key928, -2), (key831, -6), (key747, 2), (key960, 2), (key925, 2)]

def rawRow4105 : Integer.Sparse Key := [(key924, -2), (key935, -2), (key925, -2), (key928, 6), (key830, 2), (key840, 2), (key831, 2), (key928, -2), (key751, -2), (key962, -2), (key831, -6), (key925, 2), (key747, 2), (key960, 2)]

def rawRow4106 : Integer.Sparse Key := [(key935, -2), (key924, -2), (key925, -2), (key928, 6), (key840, 2), (key830, 2), (key831, 2), (key928, -2), (key962, -2), (key751, -2), (key831, -6), (key925, 2), (key960, 2), (key747, 2)]

def rawRow4107 : Integer.Sparse Key := [(key925, -2), (key935, -2), (key924, -2), (key928, 6), (key831, 2), (key840, 2), (key830, 2), (key962, -2), (key751, -2), (key928, -2), (key831, -6), (key960, 2), (key747, 2), (key925, 2)]

def rawRow4108 : Integer.Sparse Key := [(key935, -2), (key925, -2), (key924, -2), (key928, 6), (key840, 2), (key831, 2), (key830, 2), (key962, -2), (key928, -2), (key751, -2), (key831, -6), (key960, 2), (key925, 2), (key747, 2)]

def rawRow4109 : Integer.Sparse Key := [(key925, -2), (key928, -2), (key935, -2), (key924, 6), (key960, 2), (key962, 2), (key964, 2), (key746, -2), (key830, -2), (key924, -2), (key960, -6), (key747, 2), (key831, 2), (key925, 2)]

def rawRow4110 : Integer.Sparse Key := [(key928, -2), (key925, -2), (key935, -2), (key924, 6), (key962, 2), (key960, 2), (key964, 2), (key746, -2), (key924, -2), (key830, -2), (key960, -6), (key747, 2), (key925, 2), (key831, 2)]

def rawRow4111 : Integer.Sparse Key := [(key925, -2), (key935, -2), (key928, -2), (key924, 6), (key960, 2), (key964, 2), (key962, 2), (key830, -2), (key746, -2), (key924, -2), (key960, -6), (key831, 2), (key747, 2), (key925, 2)]

def rawRow4112 : Integer.Sparse Key := [(key935, -2), (key925, -2), (key928, -2), (key924, 6), (key964, 2), (key960, 2), (key962, 2), (key830, -2), (key924, -2), (key746, -2), (key960, -6), (key831, 2), (key925, 2), (key747, 2)]

def rawRow4113 : Integer.Sparse Key := [(key928, -2), (key935, -2), (key925, -2), (key924, 6), (key962, 2), (key964, 2), (key960, 2), (key924, -2), (key746, -2), (key830, -2), (key960, -6), (key925, 2), (key747, 2), (key831, 2)]

def rawRow4114 : Integer.Sparse Key := [(key935, -2), (key928, -2), (key925, -2), (key924, 6), (key964, 2), (key962, 2), (key960, 2), (key924, -2), (key830, -2), (key746, -2), (key960, -6), (key925, 2), (key831, 2), (key747, 2)]

def rawRow4115 : Integer.Sparse Key := [(key960, -2), (key960, -2), (key964, -2), (key962, 6), (key831, 2), (key831, 2), (key840, 2), (key751, -2), (key928, -2), (key928, -2), (key830, -6), (key746, 2), (key924, 2), (key924, 2)]

def rawRow4116 : Integer.Sparse Key := [(key960, -2), (key964, -2), (key960, -2), (key962, 6), (key831, 2), (key840, 2), (key831, 2), (key928, -2), (key751, -2), (key928, -2), (key830, -6), (key924, 2), (key746, 2), (key924, 2)]

def rawRow4117 : Integer.Sparse Key := [(key964, -2), (key960, -2), (key960, -2), (key962, 6), (key840, 2), (key831, 2), (key831, 2), (key928, -2), (key928, -2), (key751, -2), (key830, -6), (key924, 2), (key924, 2), (key746, 2)]

def rawRow4118 : Integer.Sparse Key := [(key960, -2), (key962, -2), (key964, -2), (key960, 6), (key925, 2), (key928, 2), (key935, 2), (key747, -2), (key831, -2), (key925, -2), (key924, -6), (key746, 2), (key830, 2), (key924, 2)]

def rawRow4119 : Integer.Sparse Key := [(key962, -2), (key960, -2), (key964, -2), (key960, 6), (key928, 2), (key925, 2), (key935, 2), (key747, -2), (key925, -2), (key831, -2), (key924, -6), (key746, 2), (key924, 2), (key830, 2)]

def rawRow4120 : Integer.Sparse Key := [(key960, -2), (key964, -2), (key962, -2), (key960, 6), (key925, 2), (key935, 2), (key928, 2), (key831, -2), (key747, -2), (key925, -2), (key924, -6), (key830, 2), (key746, 2), (key924, 2)]

def rawRow4121 : Integer.Sparse Key := [(key964, -2), (key960, -2), (key962, -2), (key960, 6), (key935, 2), (key925, 2), (key928, 2), (key831, -2), (key925, -2), (key747, -2), (key924, -6), (key830, 2), (key924, 2), (key746, 2)]

def rawRow4122 : Integer.Sparse Key := [(key962, -2), (key964, -2), (key960, -2), (key960, 6), (key928, 2), (key935, 2), (key925, 2), (key925, -2), (key747, -2), (key831, -2), (key924, -6), (key924, 2), (key746, 2), (key830, 2)]

def rawRow4123 : Integer.Sparse Key := [(key964, -2), (key962, -2), (key960, -2), (key960, 6), (key935, 2), (key928, 2), (key925, 2), (key925, -2), (key831, -2), (key747, -2), (key924, -6), (key924, 2), (key830, 2), (key746, 2)]

def rawRow4124 : Integer.Sparse Key := [(key1531, -2), (key1765, -2), (key1767, -2), (key1531, 2), (key1535, 2), (key1767, 2), (key1609, 2), (key1806, 2), (key1808, 2), (key1256, -1), (key1260, -1), (key1609, -1), (key1641, -1), (key1808, -1), (key1831, -1), (key1648, -2), (key1650, -2), (key1836, -2), (key1265, 1), (key1267, 1), (key1648, 1), (key1673, 1), (key1836, 1), (key1847, 1)]

def rawRow4125 : Integer.Sparse Key := [(key1531, -2), (key1767, -2), (key1765, -2), (key1535, 2), (key1531, 2), (key1767, 2), (key1609, 2), (key1808, 2), (key1806, 2), (key1260, -1), (key1256, -1), (key1641, -1), (key1609, -1), (key1831, -1), (key1808, -1), (key1650, -2), (key1648, -2), (key1836, -2), (key1267, 1), (key1265, 1), (key1673, 1), (key1648, 1), (key1847, 1), (key1836, 1)]

def rawRow4126 : Integer.Sparse Key := [(key1765, -2), (key1531, -2), (key1767, -2), (key1531, 2), (key1767, 2), (key1535, 2), (key1806, 2), (key1609, 2), (key1808, 2), (key1609, -1), (key1808, -1), (key1256, -1), (key1831, -1), (key1260, -1), (key1641, -1), (key1648, -2), (key1836, -2), (key1650, -2), (key1648, 1), (key1836, 1), (key1265, 1), (key1847, 1), (key1267, 1), (key1673, 1)]

def rawRow4127 : Integer.Sparse Key := [(key1765, -2), (key1767, -2), (key1531, -2), (key1767, 2), (key1531, 2), (key1535, 2), (key1806, 2), (key1808, 2), (key1609, 2), (key1808, -1), (key1609, -1), (key1831, -1), (key1256, -1), (key1641, -1), (key1260, -1), (key1836, -2), (key1648, -2), (key1650, -2), (key1836, 1), (key1648, 1), (key1847, 1), (key1265, 1), (key1673, 1), (key1267, 1)]

def rawRow4128 : Integer.Sparse Key := [(key1767, -2), (key1531, -2), (key1765, -2), (key1535, 2), (key1767, 2), (key1531, 2), (key1808, 2), (key1609, 2), (key1806, 2), (key1641, -1), (key1831, -1), (key1260, -1), (key1808, -1), (key1256, -1), (key1609, -1), (key1650, -2), (key1836, -2), (key1648, -2), (key1673, 1), (key1847, 1), (key1267, 1), (key1836, 1), (key1265, 1), (key1648, 1)]

def rawRow4129 : Integer.Sparse Key := [(key1767, -2), (key1765, -2), (key1531, -2), (key1767, 2), (key1535, 2), (key1531, 2), (key1808, 2), (key1806, 2), (key1609, 2), (key1831, -1), (key1641, -1), (key1808, -1), (key1260, -1), (key1609, -1), (key1256, -1), (key1836, -2), (key1650, -2), (key1648, -2), (key1847, 1), (key1673, 1), (key1836, 1), (key1267, 1), (key1648, 1), (key1265, 1)]

def rawRow4130 : Integer.Sparse Key := [(key1535, -2), (key1767, -2), (key1767, -2), (key1531, 2), (key1531, 2), (key1765, 2), (key1641, 2), (key1831, 2), (key1831, 2), (key1256, -1), (key1256, -1), (key1609, -1), (key1609, -1), (key1806, -1), (key1806, -1), (key1673, -2), (key1673, -2), (key1847, -2), (key1267, 1), (key1267, 1), (key1650, 1), (key1650, 1), (key1836, 1), (key1836, 1)]

def rawRow4131 : Integer.Sparse Key := [(key1767, -2), (key1535, -2), (key1767, -2), (key1531, 2), (key1765, 2), (key1531, 2), (key1831, 2), (key1641, 2), (key1831, 2), (key1609, -1), (key1806, -1), (key1256, -1), (key1806, -1), (key1256, -1), (key1609, -1), (key1673, -2), (key1847, -2), (key1673, -2), (key1650, 1), (key1836, 1), (key1267, 1), (key1836, 1), (key1267, 1), (key1650, 1)]

def rawRow4132 : Integer.Sparse Key := [(key1767, -2), (key1767, -2), (key1535, -2), (key1765, 2), (key1531, 2), (key1531, 2), (key1831, 2), (key1831, 2), (key1641, 2), (key1806, -1), (key1609, -1), (key1806, -1), (key1256, -1), (key1609, -1), (key1256, -1), (key1847, -2), (key1673, -2), (key1673, -2), (key1836, 1), (key1650, 1), (key1836, 1), (key1267, 1), (key1650, 1), (key1267, 1)]

def rawRow4133 : Integer.Sparse Key := [(key1609, -2), (key1806, -2), (key1808, -2), (key1648, 2), (key1650, 2), (key1836, 2), (key1531, 2), (key1765, 2), (key1767, 2), (key1265, -1), (key1267, -1), (key1648, -1), (key1673, -1), (key1836, -1), (key1847, -1), (key1531, -2), (key1535, -2), (key1767, -2), (key1256, 1), (key1260, 1), (key1609, 1), (key1641, 1), (key1808, 1), (key1831, 1)]

def rawRow4134 : Integer.Sparse Key := [(key1609, -2), (key1808, -2), (key1806, -2), (key1650, 2), (key1648, 2), (key1836, 2), (key1531, 2), (key1767, 2), (key1765, 2), (key1267, -1), (key1265, -1), (key1673, -1), (key1648, -1), (key1847, -1), (key1836, -1), (key1535, -2), (key1531, -2), (key1767, -2), (key1260, 1), (key1256, 1), (key1641, 1), (key1609, 1), (key1831, 1), (key1808, 1)]

def rawRow4135 : Integer.Sparse Key := [(key1806, -2), (key1609, -2), (key1808, -2), (key1648, 2), (key1836, 2), (key1650, 2), (key1765, 2), (key1531, 2), (key1767, 2), (key1648, -1), (key1836, -1), (key1265, -1), (key1847, -1), (key1267, -1), (key1673, -1), (key1531, -2), (key1767, -2), (key1535, -2), (key1609, 1), (key1808, 1), (key1256, 1), (key1831, 1), (key1260, 1), (key1641, 1)]

def rawRow4136 : Integer.Sparse Key := [(key1806, -2), (key1808, -2), (key1609, -2), (key1836, 2), (key1648, 2), (key1650, 2), (key1765, 2), (key1767, 2), (key1531, 2), (key1836, -1), (key1648, -1), (key1847, -1), (key1265, -1), (key1673, -1), (key1267, -1), (key1767, -2), (key1531, -2), (key1535, -2), (key1808, 1), (key1609, 1), (key1831, 1), (key1256, 1), (key1641, 1), (key1260, 1)]

def rawRow4137 : Integer.Sparse Key := [(key1808, -2), (key1609, -2), (key1806, -2), (key1650, 2), (key1836, 2), (key1648, 2), (key1767, 2), (key1531, 2), (key1765, 2), (key1673, -1), (key1847, -1), (key1267, -1), (key1836, -1), (key1265, -1), (key1648, -1), (key1535, -2), (key1767, -2), (key1531, -2), (key1641, 1), (key1831, 1), (key1260, 1), (key1808, 1), (key1256, 1), (key1609, 1)]

def rawRow4138 : Integer.Sparse Key := [(key1808, -2), (key1806, -2), (key1609, -2), (key1836, 2), (key1650, 2), (key1648, 2), (key1767, 2), (key1765, 2), (key1531, 2), (key1847, -1), (key1673, -1), (key1836, -1), (key1267, -1), (key1648, -1), (key1265, -1), (key1767, -2), (key1535, -2), (key1531, -2), (key1831, 1), (key1641, 1), (key1808, 1), (key1260, 1), (key1609, 1), (key1256, 1)]

def rawRow4139 : Integer.Sparse Key := [(key1650, -2), (key1808, -2), (key1836, -2), (key1609, 2), (key1648, 2), (key1806, 2), (key1673, 2), (key1831, 2), (key1847, 2), (key1256, -1), (key1265, -1), (key1531, -1), (key1648, -1), (key1765, -1), (key1806, -1), (key1641, -2), (key1673, -2), (key1831, -2), (key1260, 1), (key1267, 1), (key1535, 1), (key1650, 1), (key1767, 1), (key1808, 1)]

def rawRow4140 : Integer.Sparse Key := [(key1650, -2), (key1836, -2), (key1808, -2), (key1648, 2), (key1609, 2), (key1806, 2), (key1673, 2), (key1847, 2), (key1831, 2), (key1265, -1), (key1256, -1), (key1648, -1), (key1531, -1), (key1806, -1), (key1765, -1), (key1673, -2), (key1641, -2), (key1831, -2), (key1267, 1), (key1260, 1), (key1650, 1), (key1535, 1), (key1808, 1), (key1767, 1)]

def rawRow4141 : Integer.Sparse Key := [(key1808, -2), (key1650, -2), (key1836, -2), (key1609, 2), (key1806, 2), (key1648, 2), (key1831, 2), (key1673, 2), (key1847, 2), (key1531, -1), (key1765, -1), (key1256, -1), (key1806, -1), (key1265, -1), (key1648, -1), (key1641, -2), (key1831, -2), (key1673, -2), (key1535, 1), (key1767, 1), (key1260, 1), (key1808, 1), (key1267, 1), (key1650, 1)]

def rawRow4142 : Integer.Sparse Key := [(key1808, -2), (key1836, -2), (key1650, -2), (key1806, 2), (key1609, 2), (key1648, 2), (key1831, 2), (key1847, 2), (key1673, 2), (key1765, -1), (key1531, -1), (key1806, -1), (key1256, -1), (key1648, -1), (key1265, -1), (key1831, -2), (key1641, -2), (key1673, -2), (key1767, 1), (key1535, 1), (key1808, 1), (key1260, 1), (key1650, 1), (key1267, 1)]

def rawRow4143 : Integer.Sparse Key := [(key1836, -2), (key1650, -2), (key1808, -2), (key1648, 2), (key1806, 2), (key1609, 2), (key1847, 2), (key1673, 2), (key1831, 2), (key1648, -1), (key1806, -1), (key1265, -1), (key1765, -1), (key1256, -1), (key1531, -1), (key1673, -2), (key1831, -2), (key1641, -2), (key1650, 1), (key1808, 1), (key1267, 1), (key1767, 1), (key1260, 1), (key1535, 1)]

def rawRow4144 : Integer.Sparse Key := [(key1836, -2), (key1808, -2), (key1650, -2), (key1806, 2), (key1648, 2), (key1609, 2), (key1847, 2), (key1831, 2), (key1673, 2), (key1806, -1), (key1648, -1), (key1765, -1), (key1265, -1), (key1531, -1), (key1256, -1), (key1831, -2), (key1673, -2), (key1641, -2), (key1808, 1), (key1650, 1), (key1767, 1), (key1267, 1), (key1535, 1), (key1260, 1)]

def rawRow4145 : Integer.Sparse Key := [(key1641, -2), (key1831, -2), (key1831, -2), (key1673, 2), (key1673, 2), (key1847, 2), (key1535, 2), (key1767, 2), (key1767, 2), (key1267, -1), (key1267, -1), (key1650, -1), (key1650, -1), (key1836, -1), (key1836, -1), (key1531, -2), (key1531, -2), (key1765, -2), (key1256, 1), (key1256, 1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1)]

def rawRow4146 : Integer.Sparse Key := [(key1831, -2), (key1641, -2), (key1831, -2), (key1673, 2), (key1847, 2), (key1673, 2), (key1767, 2), (key1535, 2), (key1767, 2), (key1650, -1), (key1836, -1), (key1267, -1), (key1836, -1), (key1267, -1), (key1650, -1), (key1531, -2), (key1765, -2), (key1531, -2), (key1609, 1), (key1806, 1), (key1256, 1), (key1806, 1), (key1256, 1), (key1609, 1)]

def rawRow4147 : Integer.Sparse Key := [(key1831, -2), (key1831, -2), (key1641, -2), (key1847, 2), (key1673, 2), (key1673, 2), (key1767, 2), (key1767, 2), (key1535, 2), (key1836, -1), (key1650, -1), (key1836, -1), (key1267, -1), (key1650, -1), (key1267, -1), (key1765, -2), (key1531, -2), (key1531, -2), (key1806, 1), (key1609, 1), (key1806, 1), (key1256, 1), (key1609, 1), (key1256, 1)]

def rawRow4148 : Integer.Sparse Key := [(key1673, -2), (key1831, -2), (key1847, -2), (key1641, 2), (key1673, 2), (key1831, 2), (key1650, 2), (key1808, 2), (key1836, 2), (key1260, -1), (key1267, -1), (key1535, -1), (key1650, -1), (key1767, -1), (key1808, -1), (key1609, -2), (key1648, -2), (key1806, -2), (key1256, 1), (key1265, 1), (key1531, 1), (key1648, 1), (key1765, 1), (key1806, 1)]

def rawRow4149 : Integer.Sparse Key := [(key1673, -2), (key1847, -2), (key1831, -2), (key1673, 2), (key1641, 2), (key1831, 2), (key1650, 2), (key1836, 2), (key1808, 2), (key1267, -1), (key1260, -1), (key1650, -1), (key1535, -1), (key1808, -1), (key1767, -1), (key1648, -2), (key1609, -2), (key1806, -2), (key1265, 1), (key1256, 1), (key1648, 1), (key1531, 1), (key1806, 1), (key1765, 1)]

def rawRow4150 : Integer.Sparse Key := [(key1831, -2), (key1673, -2), (key1847, -2), (key1641, 2), (key1831, 2), (key1673, 2), (key1808, 2), (key1650, 2), (key1836, 2), (key1535, -1), (key1767, -1), (key1260, -1), (key1808, -1), (key1267, -1), (key1650, -1), (key1609, -2), (key1806, -2), (key1648, -2), (key1531, 1), (key1765, 1), (key1256, 1), (key1806, 1), (key1265, 1), (key1648, 1)]

def rawRow4151 : Integer.Sparse Key := [(key1831, -2), (key1847, -2), (key1673, -2), (key1831, 2), (key1641, 2), (key1673, 2), (key1808, 2), (key1836, 2), (key1650, 2), (key1767, -1), (key1535, -1), (key1808, -1), (key1260, -1), (key1650, -1), (key1267, -1), (key1806, -2), (key1609, -2), (key1648, -2), (key1765, 1), (key1531, 1), (key1806, 1), (key1256, 1), (key1648, 1), (key1265, 1)]

def rawRow4152 : Integer.Sparse Key := [(key1847, -2), (key1673, -2), (key1831, -2), (key1673, 2), (key1831, 2), (key1641, 2), (key1836, 2), (key1650, 2), (key1808, 2), (key1650, -1), (key1808, -1), (key1267, -1), (key1767, -1), (key1260, -1), (key1535, -1), (key1648, -2), (key1806, -2), (key1609, -2), (key1648, 1), (key1806, 1), (key1265, 1), (key1765, 1), (key1256, 1), (key1531, 1)]

def rawRow4153 : Integer.Sparse Key := [(key1847, -2), (key1831, -2), (key1673, -2), (key1831, 2), (key1673, 2), (key1641, 2), (key1836, 2), (key1808, 2), (key1650, 2), (key1808, -1), (key1650, -1), (key1767, -1), (key1267, -1), (key1535, -1), (key1260, -1), (key1806, -2), (key1648, -2), (key1609, -2), (key1806, 1), (key1648, 1), (key1765, 1), (key1265, 1), (key1531, 1), (key1256, 1)]

def rawRow4154 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1569, -1), (key1593, -1), (key1903, -1), (key1911, -1), (key1298, 2), (key1575, 2), (key1593, 2), (key1312, 1), (key1318, 1), (key1618, 1), (key1633, 1), (key1918, 1), (key1926, 1), (key1318, -1), (key1326, -1), (key1426, -1), (key1444, -1), (key1624, -1), (key1633, -1), (key1351, -2), (key1681, -2), (key1689, -2), (key1351, 1), (key1354, 1), (key1472, 1), (key1480, 1), (key1683, 1), (key1689, 1)]

def rawRow4155 : Integer.Sparse Key := [(key1298, -1), (key1292, -1), (key1593, -1), (key1569, -1), (key1911, -1), (key1903, -1), (key1298, 2), (key1593, 2), (key1575, 2), (key1318, 1), (key1312, 1), (key1633, 1), (key1618, 1), (key1926, 1), (key1918, 1), (key1326, -1), (key1318, -1), (key1444, -1), (key1426, -1), (key1633, -1), (key1624, -1), (key1351, -2), (key1689, -2), (key1681, -2), (key1354, 1), (key1351, 1), (key1480, 1), (key1472, 1), (key1689, 1), (key1683, 1)]

def rawRow4156 : Integer.Sparse Key := [(key1569, -1), (key1903, -1), (key1292, -1), (key1911, -1), (key1298, -1), (key1593, -1), (key1575, 2), (key1298, 2), (key1593, 2), (key1618, 1), (key1918, 1), (key1312, 1), (key1926, 1), (key1318, 1), (key1633, 1), (key1426, -1), (key1624, -1), (key1318, -1), (key1633, -1), (key1326, -1), (key1444, -1), (key1681, -2), (key1351, -2), (key1689, -2), (key1472, 1), (key1683, 1), (key1351, 1), (key1689, 1), (key1354, 1), (key1480, 1)]

def rawRow4157 : Integer.Sparse Key := [(key1903, -1), (key1569, -1), (key1911, -1), (key1292, -1), (key1593, -1), (key1298, -1), (key1575, 2), (key1593, 2), (key1298, 2), (key1918, 1), (key1618, 1), (key1926, 1), (key1312, 1), (key1633, 1), (key1318, 1), (key1624, -1), (key1426, -1), (key1633, -1), (key1318, -1), (key1444, -1), (key1326, -1), (key1681, -2), (key1689, -2), (key1351, -2), (key1683, 1), (key1472, 1), (key1689, 1), (key1351, 1), (key1480, 1), (key1354, 1)]

def rawRow4158 : Integer.Sparse Key := [(key1593, -1), (key1911, -1), (key1298, -1), (key1903, -1), (key1292, -1), (key1569, -1), (key1593, 2), (key1298, 2), (key1575, 2), (key1633, 1), (key1926, 1), (key1318, 1), (key1918, 1), (key1312, 1), (key1618, 1), (key1444, -1), (key1633, -1), (key1326, -1), (key1624, -1), (key1318, -1), (key1426, -1), (key1689, -2), (key1351, -2), (key1681, -2), (key1480, 1), (key1689, 1), (key1354, 1), (key1683, 1), (key1351, 1), (key1472, 1)]

def rawRow4159 : Integer.Sparse Key := [(key1911, -1), (key1593, -1), (key1903, -1), (key1298, -1), (key1569, -1), (key1292, -1), (key1593, 2), (key1575, 2), (key1298, 2), (key1926, 1), (key1633, 1), (key1918, 1), (key1318, 1), (key1618, 1), (key1312, 1), (key1633, -1), (key1444, -1), (key1624, -1), (key1326, -1), (key1426, -1), (key1318, -1), (key1689, -2), (key1681, -2), (key1351, -2), (key1689, 1), (key1480, 1), (key1683, 1), (key1354, 1), (key1472, 1), (key1351, 1)]

def rawRow4163 : Integer.Sparse Key := [(key1312, -1), (key1318, -1), (key1618, -1), (key1633, -1), (key1918, -1), (key1926, -1), (key1351, 2), (key1681, 2), (key1689, 2), (key1292, 1), (key1298, 1), (key1569, 1), (key1593, 1), (key1903, 1), (key1911, 1), (key1351, -1), (key1354, -1), (key1472, -1), (key1480, -1), (key1683, -1), (key1689, -1), (key1298, -2), (key1575, -2), (key1593, -2), (key1318, 1), (key1326, 1), (key1426, 1), (key1444, 1), (key1624, 1), (key1633, 1)]

def rawRow4164 : Integer.Sparse Key := [(key1318, -1), (key1312, -1), (key1633, -1), (key1618, -1), (key1926, -1), (key1918, -1), (key1351, 2), (key1689, 2), (key1681, 2), (key1298, 1), (key1292, 1), (key1593, 1), (key1569, 1), (key1911, 1), (key1903, 1), (key1354, -1), (key1351, -1), (key1480, -1), (key1472, -1), (key1689, -1), (key1683, -1), (key1298, -2), (key1593, -2), (key1575, -2), (key1326, 1), (key1318, 1), (key1444, 1), (key1426, 1), (key1633, 1), (key1624, 1)]

def rawRow4165 : Integer.Sparse Key := [(key1618, -1), (key1918, -1), (key1312, -1), (key1926, -1), (key1318, -1), (key1633, -1), (key1681, 2), (key1351, 2), (key1689, 2), (key1569, 1), (key1903, 1), (key1292, 1), (key1911, 1), (key1298, 1), (key1593, 1), (key1472, -1), (key1683, -1), (key1351, -1), (key1689, -1), (key1354, -1), (key1480, -1), (key1575, -2), (key1298, -2), (key1593, -2), (key1426, 1), (key1624, 1), (key1318, 1), (key1633, 1), (key1326, 1), (key1444, 1)]

def rawRow4166 : Integer.Sparse Key := [(key1918, -1), (key1618, -1), (key1926, -1), (key1312, -1), (key1633, -1), (key1318, -1), (key1681, 2), (key1689, 2), (key1351, 2), (key1903, 1), (key1569, 1), (key1911, 1), (key1292, 1), (key1593, 1), (key1298, 1), (key1683, -1), (key1472, -1), (key1689, -1), (key1351, -1), (key1480, -1), (key1354, -1), (key1575, -2), (key1593, -2), (key1298, -2), (key1624, 1), (key1426, 1), (key1633, 1), (key1318, 1), (key1444, 1), (key1326, 1)]

def rawRow4167 : Integer.Sparse Key := [(key1633, -1), (key1926, -1), (key1318, -1), (key1918, -1), (key1312, -1), (key1618, -1), (key1689, 2), (key1351, 2), (key1681, 2), (key1593, 1), (key1911, 1), (key1298, 1), (key1903, 1), (key1292, 1), (key1569, 1), (key1480, -1), (key1689, -1), (key1354, -1), (key1683, -1), (key1351, -1), (key1472, -1), (key1593, -2), (key1298, -2), (key1575, -2), (key1444, 1), (key1633, 1), (key1326, 1), (key1624, 1), (key1318, 1), (key1426, 1)]

def rawRow4168 : Integer.Sparse Key := [(key1926, -1), (key1633, -1), (key1918, -1), (key1318, -1), (key1618, -1), (key1312, -1), (key1689, 2), (key1681, 2), (key1351, 2), (key1911, 1), (key1593, 1), (key1903, 1), (key1298, 1), (key1569, 1), (key1292, 1), (key1689, -1), (key1480, -1), (key1683, -1), (key1354, -1), (key1472, -1), (key1351, -1), (key1593, -2), (key1575, -2), (key1298, -2), (key1633, 1), (key1444, 1), (key1624, 1), (key1326, 1), (key1426, 1), (key1318, 1)]

def rawRow4169 : Integer.Sparse Key := [(key1318, -1), (key1351, -1), (key1548, -1), (key1681, -1), (key1896, -1), (key1918, -1), (key1312, 2), (key1542, 2), (key1618, 2), (key1326, 1), (key1354, 1), (key1556, 1), (key1683, 1), (key1899, 1), (key1920, 1), (key1292, -1), (key1312, -1), (key1387, -1), (key1420, -1), (key1542, -1), (key1569, -1), (key1326, -2), (key1556, -2), (key1624, -2), (key1298, 1), (key1318, 1), (key1393, 1), (key1426, 1), (key1548, 1), (key1575, 1)]

def rawRow4170 : Integer.Sparse Key := [(key1351, -1), (key1318, -1), (key1681, -1), (key1548, -1), (key1918, -1), (key1896, -1), (key1312, 2), (key1618, 2), (key1542, 2), (key1354, 1), (key1326, 1), (key1683, 1), (key1556, 1), (key1920, 1), (key1899, 1), (key1312, -1), (key1292, -1), (key1420, -1), (key1387, -1), (key1569, -1), (key1542, -1), (key1326, -2), (key1624, -2), (key1556, -2), (key1318, 1), (key1298, 1), (key1426, 1), (key1393, 1), (key1575, 1), (key1548, 1)]

def rawRow4171 : Integer.Sparse Key := [(key1548, -1), (key1896, -1), (key1318, -1), (key1918, -1), (key1351, -1), (key1681, -1), (key1542, 2), (key1312, 2), (key1618, 2), (key1556, 1), (key1899, 1), (key1326, 1), (key1920, 1), (key1354, 1), (key1683, 1), (key1387, -1), (key1542, -1), (key1292, -1), (key1569, -1), (key1312, -1), (key1420, -1), (key1556, -2), (key1326, -2), (key1624, -2), (key1393, 1), (key1548, 1), (key1298, 1), (key1575, 1), (key1318, 1), (key1426, 1)]

def rawRow4172 : Integer.Sparse Key := [(key1896, -1), (key1548, -1), (key1918, -1), (key1318, -1), (key1681, -1), (key1351, -1), (key1542, 2), (key1618, 2), (key1312, 2), (key1899, 1), (key1556, 1), (key1920, 1), (key1326, 1), (key1683, 1), (key1354, 1), (key1542, -1), (key1387, -1), (key1569, -1), (key1292, -1), (key1420, -1), (key1312, -1), (key1556, -2), (key1624, -2), (key1326, -2), (key1548, 1), (key1393, 1), (key1575, 1), (key1298, 1), (key1426, 1), (key1318, 1)]

def rawRow4173 : Integer.Sparse Key := [(key1681, -1), (key1918, -1), (key1351, -1), (key1896, -1), (key1318, -1), (key1548, -1), (key1618, 2), (key1312, 2), (key1542, 2), (key1683, 1), (key1920, 1), (key1354, 1), (key1899, 1), (key1326, 1), (key1556, 1), (key1420, -1), (key1569, -1), (key1312, -1), (key1542, -1), (key1292, -1), (key1387, -1), (key1624, -2), (key1326, -2), (key1556, -2), (key1426, 1), (key1575, 1), (key1318, 1), (key1548, 1), (key1298, 1), (key1393, 1)]

def rawRow4174 : Integer.Sparse Key := [(key1918, -1), (key1681, -1), (key1896, -1), (key1351, -1), (key1548, -1), (key1318, -1), (key1618, 2), (key1542, 2), (key1312, 2), (key1920, 1), (key1683, 1), (key1899, 1), (key1354, 1), (key1556, 1), (key1326, 1), (key1569, -1), (key1420, -1), (key1542, -1), (key1312, -1), (key1387, -1), (key1292, -1), (key1624, -2), (key1556, -2), (key1326, -2), (key1575, 1), (key1426, 1), (key1548, 1), (key1318, 1), (key1393, 1), (key1298, 1)]

def rawRow4178 : Integer.Sparse Key := [(key1326, -1), (key1354, -1), (key1556, -1), (key1683, -1), (key1899, -1), (key1920, -1), (key1326, 2), (key1556, 2), (key1624, 2), (key1318, 1), (key1351, 1), (key1548, 1), (key1681, 1), (key1896, 1), (key1918, 1), (key1298, -1), (key1318, -1), (key1393, -1), (key1426, -1), (key1548, -1), (key1575, -1), (key1312, -2), (key1542, -2), (key1618, -2), (key1292, 1), (key1312, 1), (key1387, 1), (key1420, 1), (key1542, 1), (key1569, 1)]

def rawRow4179 : Integer.Sparse Key := [(key1354, -1), (key1326, -1), (key1683, -1), (key1556, -1), (key1920, -1), (key1899, -1), (key1326, 2), (key1624, 2), (key1556, 2), (key1351, 1), (key1318, 1), (key1681, 1), (key1548, 1), (key1918, 1), (key1896, 1), (key1318, -1), (key1298, -1), (key1426, -1), (key1393, -1), (key1575, -1), (key1548, -1), (key1312, -2), (key1618, -2), (key1542, -2), (key1312, 1), (key1292, 1), (key1420, 1), (key1387, 1), (key1569, 1), (key1542, 1)]

def rawRow4180 : Integer.Sparse Key := [(key1556, -1), (key1899, -1), (key1326, -1), (key1920, -1), (key1354, -1), (key1683, -1), (key1556, 2), (key1326, 2), (key1624, 2), (key1548, 1), (key1896, 1), (key1318, 1), (key1918, 1), (key1351, 1), (key1681, 1), (key1393, -1), (key1548, -1), (key1298, -1), (key1575, -1), (key1318, -1), (key1426, -1), (key1542, -2), (key1312, -2), (key1618, -2), (key1387, 1), (key1542, 1), (key1292, 1), (key1569, 1), (key1312, 1), (key1420, 1)]

def rawRow4181 : Integer.Sparse Key := [(key1899, -1), (key1556, -1), (key1920, -1), (key1326, -1), (key1683, -1), (key1354, -1), (key1556, 2), (key1624, 2), (key1326, 2), (key1896, 1), (key1548, 1), (key1918, 1), (key1318, 1), (key1681, 1), (key1351, 1), (key1548, -1), (key1393, -1), (key1575, -1), (key1298, -1), (key1426, -1), (key1318, -1), (key1542, -2), (key1618, -2), (key1312, -2), (key1542, 1), (key1387, 1), (key1569, 1), (key1292, 1), (key1420, 1), (key1312, 1)]

def rawRow4182 : Integer.Sparse Key := [(key1683, -1), (key1920, -1), (key1354, -1), (key1899, -1), (key1326, -1), (key1556, -1), (key1624, 2), (key1326, 2), (key1556, 2), (key1681, 1), (key1918, 1), (key1351, 1), (key1896, 1), (key1318, 1), (key1548, 1), (key1426, -1), (key1575, -1), (key1318, -1), (key1548, -1), (key1298, -1), (key1393, -1), (key1618, -2), (key1312, -2), (key1542, -2), (key1420, 1), (key1569, 1), (key1312, 1), (key1542, 1), (key1292, 1), (key1387, 1)]

def rawRow4183 : Integer.Sparse Key := [(key1920, -1), (key1683, -1), (key1899, -1), (key1354, -1), (key1556, -1), (key1326, -1), (key1624, 2), (key1556, 2), (key1326, 2), (key1918, 1), (key1681, 1), (key1896, 1), (key1351, 1), (key1548, 1), (key1318, 1), (key1575, -1), (key1426, -1), (key1548, -1), (key1318, -1), (key1393, -1), (key1298, -1), (key1618, -2), (key1542, -2), (key1312, -2), (key1569, 1), (key1420, 1), (key1542, 1), (key1312, 1), (key1387, 1), (key1292, 1)]

def rawRow4214 : Integer.Sparse Key := [(key236, -1), (key239, -1), (key406, -1), (key418, -1), (key578, -1), (key583, -1), (key239, 2), (key409, 2), (key418, 2), (key248, 1), (key251, 1), (key435, 1), (key450, 1), (key593, 1), (key601, 1), (key251, -1), (key260, -1), (key319, -1), (key328, -1), (key442, -1), (key450, -1), (key267, -2), (key467, -2), (key475, -2), (key267, 1), (key271, 1), (key335, 1), (key340, 1), (key469, 1), (key475, 1)]

def rawRow4215 : Integer.Sparse Key := [(key239, -1), (key236, -1), (key418, -1), (key406, -1), (key583, -1), (key578, -1), (key239, 2), (key418, 2), (key409, 2), (key251, 1), (key248, 1), (key450, 1), (key435, 1), (key601, 1), (key593, 1), (key260, -1), (key251, -1), (key328, -1), (key319, -1), (key450, -1), (key442, -1), (key267, -2), (key475, -2), (key467, -2), (key271, 1), (key267, 1), (key340, 1), (key335, 1), (key475, 1), (key469, 1)]

def rawRow4216 : Integer.Sparse Key := [(key406, -1), (key418, -1), (key236, -1), (key583, -1), (key239, -1), (key418, -1), (key409, 2), (key239, 2), (key418, 2), (key435, 1), (key593, 1), (key248, 1), (key601, 1), (key251, 1), (key450, 1), (key319, -1), (key442, -1), (key251, -1), (key450, -1), (key260, -1), (key328, -1), (key467, -2), (key267, -2), (key475, -2), (key335, 1), (key469, 1), (key267, 1), (key475, 1), (key271, 1), (key340, 1)]

def rawRow4217 : Integer.Sparse Key := [(key418, -1), (key406, -1), (key583, -1), (key236, -1), (key418, -1), (key239, -1), (key409, 2), (key418, 2), (key239, 2), (key593, 1), (key435, 1), (key601, 1), (key248, 1), (key450, 1), (key251, 1), (key442, -1), (key319, -1), (key450, -1), (key251, -1), (key328, -1), (key260, -1), (key467, -2), (key475, -2), (key267, -2), (key469, 1), (key335, 1), (key475, 1), (key267, 1), (key340, 1), (key271, 1)]

def rawRow4218 : Integer.Sparse Key := [(key578, -1), (key583, -1), (key239, -1), (key418, -1), (key236, -1), (key406, -1), (key418, 2), (key239, 2), (key409, 2), (key450, 1), (key601, 1), (key251, 1), (key593, 1), (key248, 1), (key435, 1), (key328, -1), (key450, -1), (key260, -1), (key442, -1), (key251, -1), (key319, -1), (key475, -2), (key267, -2), (key467, -2), (key340, 1), (key475, 1), (key271, 1), (key469, 1), (key267, 1), (key335, 1)]

def rawRow4219 : Integer.Sparse Key := [(key583, -1), (key578, -1), (key418, -1), (key239, -1), (key406, -1), (key236, -1), (key418, 2), (key409, 2), (key239, 2), (key601, 1), (key450, 1), (key593, 1), (key251, 1), (key435, 1), (key248, 1), (key450, -1), (key328, -1), (key442, -1), (key260, -1), (key319, -1), (key251, -1), (key475, -2), (key467, -2), (key267, -2), (key475, 1), (key340, 1), (key469, 1), (key271, 1), (key335, 1), (key267, 1)]

def rawRow4223 : Integer.Sparse Key := [(key248, -1), (key251, -1), (key435, -1), (key593, -1), (key450, -1), (key601, -1), (key260, 2), (key442, 2), (key595, 2), (key236, 1), (key239, 1), (key406, 1), (key418, 1), (key578, 1), (key583, 1), (key267, -1), (key271, -1), (key335, -1), (key340, -1), (key469, -1), (key475, -1), (key239, -2), (key409, -2), (key418, -2), (key251, 1), (key260, 1), (key319, 1), (key328, 1), (key442, 1), (key450, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4224 : Integer.Sparse Key := [(key251, -1), (key248, -1), (key593, -1), (key435, -1), (key601, -1), (key450, -1), (key260, 2), (key595, 2), (key442, 2), (key239, 1), (key236, 1), (key418, 1), (key406, 1), (key583, 1), (key578, 1), (key271, -1), (key267, -1), (key340, -1), (key335, -1), (key475, -1), (key469, -1), (key239, -2), (key418, -2), (key409, -2), (key260, 1), (key251, 1), (key328, 1), (key319, 1), (key450, 1), (key442, 1)]

def rawRow4225 : Integer.Sparse Key := [(key435, -1), (key450, -1), (key248, -1), (key601, -1), (key251, -1), (key593, -1), (key442, 2), (key260, 2), (key595, 2), (key406, 1), (key418, 1), (key236, 1), (key583, 1), (key239, 1), (key418, 1), (key335, -1), (key469, -1), (key267, -1), (key475, -1), (key271, -1), (key340, -1), (key409, -2), (key239, -2), (key418, -2), (key319, 1), (key442, 1), (key251, 1), (key450, 1), (key260, 1), (key328, 1)]

def rawRow4226 : Integer.Sparse Key := [(key450, -1), (key435, -1), (key601, -1), (key248, -1), (key593, -1), (key251, -1), (key442, 2), (key595, 2), (key260, 2), (key418, 1), (key406, 1), (key583, 1), (key236, 1), (key418, 1), (key239, 1), (key469, -1), (key335, -1), (key475, -1), (key267, -1), (key340, -1), (key271, -1), (key409, -2), (key418, -2), (key239, -2), (key442, 1), (key319, 1), (key450, 1), (key251, 1), (key328, 1), (key260, 1)]

def rawRow4227 : Integer.Sparse Key := [(key593, -1), (key601, -1), (key251, -1), (key450, -1), (key248, -1), (key435, -1), (key595, 2), (key260, 2), (key442, 2), (key578, 1), (key583, 1), (key239, 1), (key418, 1), (key236, 1), (key406, 1), (key340, -1), (key475, -1), (key271, -1), (key469, -1), (key267, -1), (key335, -1), (key418, -2), (key239, -2), (key409, -2), (key328, 1), (key450, 1), (key260, 1), (key442, 1), (key251, 1), (key319, 1)]

def rawRow4228 : Integer.Sparse Key := [(key601, -1), (key593, -1), (key450, -1), (key251, -1), (key435, -1), (key248, -1), (key595, 2), (key442, 2), (key260, 2), (key583, 1), (key578, 1), (key418, 1), (key239, 1), (key406, 1), (key236, 1), (key475, -1), (key340, -1), (key469, -1), (key271, -1), (key335, -1), (key267, -1), (key418, -2), (key409, -2), (key239, -2), (key450, 1), (key328, 1), (key442, 1), (key260, 1), (key319, 1), (key251, 1)]

def rawRow4229 : Integer.Sparse Key := [(key251, -1), (key260, -1), (key319, -1), (key442, -1), (key328, -1), (key450, -1), (key248, 2), (key316, 2), (key435, 2), (key267, 1), (key271, 1), (key335, 1), (key469, 1), (key340, 1), (key475, 1), (key236, -1), (key248, -1), (key302, -1), (key316, -1), (key385, -1), (key406, -1), (key260, -2), (key397, -2), (key442, -2), (key239, 1), (key251, 1), (key305, 1), (key319, 1), (key388, 1), (key409, 1)]

def rawRow4230 : Integer.Sparse Key := [(key260, -1), (key251, -1), (key442, -1), (key319, -1), (key450, -1), (key328, -1), (key248, 2), (key435, 2), (key316, 2), (key271, 1), (key267, 1), (key469, 1), (key335, 1), (key475, 1), (key340, 1), (key248, -1), (key236, -1), (key316, -1), (key302, -1), (key406, -1), (key385, -1), (key260, -2), (key442, -2), (key397, -2), (key251, 1), (key239, 1), (key319, 1), (key305, 1), (key409, 1), (key388, 1)]

def rawRow4231 : Integer.Sparse Key := [(key319, -1), (key328, -1), (key251, -1), (key450, -1), (key260, -1), (key442, -1), (key316, 2), (key248, 2), (key435, 2), (key335, 1), (key340, 1), (key267, 1), (key475, 1), (key271, 1), (key469, 1), (key302, -1), (key316, -1), (key236, -1), (key406, -1), (key248, -1), (key316, -1), (key397, -2), (key260, -2), (key442, -2), (key305, 1), (key388, 1), (key239, 1), (key409, 1), (key251, 1), (key319, 1)]

def rawRow4232 : Integer.Sparse Key := [(key328, -1), (key319, -1), (key450, -1), (key251, -1), (key442, -1), (key260, -1), (key316, 2), (key435, 2), (key248, 2), (key340, 1), (key335, 1), (key475, 1), (key267, 1), (key469, 1), (key271, 1), (key316, -1), (key302, -1), (key406, -1), (key236, -1), (key316, -1), (key248, -1), (key397, -2), (key442, -2), (key260, -2), (key388, 1), (key305, 1), (key409, 1), (key239, 1), (key319, 1), (key251, 1)]

def rawRow4233 : Integer.Sparse Key := [(key442, -1), (key450, -1), (key260, -1), (key328, -1), (key251, -1), (key319, -1), (key435, 2), (key248, 2), (key316, 2), (key469, 1), (key475, 1), (key271, 1), (key340, 1), (key267, 1), (key335, 1), (key385, -1), (key406, -1), (key248, -1), (key316, -1), (key236, -1), (key302, -1), (key442, -2), (key260, -2), (key397, -2), (key319, 1), (key409, 1), (key251, 1), (key388, 1), (key239, 1), (key305, 1)]

def rawRow4234 : Integer.Sparse Key := [(key450, -1), (key442, -1), (key328, -1), (key260, -1), (key319, -1), (key251, -1), (key435, 2), (key316, 2), (key248, 2), (key475, 1), (key469, 1), (key340, 1), (key271, 1), (key335, 1), (key267, 1), (key406, -1), (key385, -1), (key316, -1), (key248, -1), (key302, -1), (key236, -1), (key442, -2), (key397, -2), (key260, -2), (key409, 1), (key319, 1), (key388, 1), (key251, 1), (key305, 1), (key239, 1)]

def rawRow4238 : Integer.Sparse Key := [(key267, -1), (key271, -1), (key335, -1), (key469, -1), (key340, -1), (key475, -1), (key267, 2), (key335, 2), (key467, 2), (key251, 1), (key260, 1), (key319, 1), (key442, 1), (key328, 1), (key450, 1), (key239, -1), (key251, -1), (key305, -1), (key388, -1), (key319, -1), (key409, -1), (key248, -2), (key316, -2), (key435, -2), (key236, 1), (key248, 1), (key302, 1), (key316, 1), (key385, 1), (key406, 1)]

def rawRow4239 : Integer.Sparse Key := [(key271, -1), (key267, -1), (key469, -1), (key335, -1), (key475, -1), (key340, -1), (key267, 2), (key467, 2), (key335, 2), (key260, 1), (key251, 1), (key442, 1), (key319, 1), (key450, 1), (key328, 1), (key251, -1), (key239, -1), (key388, -1), (key305, -1), (key409, -1), (key319, -1), (key248, -2), (key435, -2), (key316, -2), (key248, 1), (key236, 1), (key316, 1), (key302, 1), (key406, 1), (key385, 1)]

def rawRow4240 : Integer.Sparse Key := [(key335, -1), (key340, -1), (key267, -1), (key475, -1), (key271, -1), (key469, -1), (key335, 2), (key267, 2), (key467, 2), (key319, 1), (key328, 1), (key251, 1), (key450, 1), (key260, 1), (key442, 1), (key305, -1), (key319, -1), (key239, -1), (key409, -1), (key251, -1), (key388, -1), (key316, -2), (key248, -2), (key435, -2), (key302, 1), (key316, 1), (key236, 1), (key406, 1), (key248, 1), (key316, 1)]

def rawRow4241 : Integer.Sparse Key := [(key340, -1), (key335, -1), (key475, -1), (key267, -1), (key469, -1), (key271, -1), (key335, 2), (key467, 2), (key267, 2), (key328, 1), (key319, 1), (key450, 1), (key251, 1), (key442, 1), (key260, 1), (key319, -1), (key305, -1), (key409, -1), (key239, -1), (key388, -1), (key251, -1), (key316, -2), (key435, -2), (key248, -2), (key316, 1), (key302, 1), (key406, 1), (key236, 1), (key316, 1), (key248, 1)]

def rawRow4242 : Integer.Sparse Key := [(key469, -1), (key475, -1), (key271, -1), (key340, -1), (key267, -1), (key335, -1), (key467, 2), (key267, 2), (key335, 2), (key442, 1), (key450, 1), (key260, 1), (key328, 1), (key251, 1), (key319, 1), (key388, -1), (key409, -1), (key251, -1), (key319, -1), (key239, -1), (key305, -1), (key435, -2), (key248, -2), (key316, -2), (key385, 1), (key406, 1), (key248, 1), (key316, 1), (key236, 1), (key302, 1)]

def rawRow4243 : Integer.Sparse Key := [(key475, -1), (key469, -1), (key340, -1), (key271, -1), (key335, -1), (key267, -1), (key467, 2), (key335, 2), (key267, 2), (key450, 1), (key442, 1), (key328, 1), (key260, 1), (key319, 1), (key251, 1), (key409, -1), (key388, -1), (key319, -1), (key251, -1), (key305, -1), (key239, -1), (key435, -2), (key316, -2), (key248, -2), (key406, 1), (key385, 1), (key316, 1), (key248, 1), (key302, 1), (key236, 1)]

def rawRow4256 : Integer.Sparse Key := [(key1652, -6), (key1538, 2), (key1565, 2), (key1614, 2), (key1810, 6), (key1308, -2), (key1416, -2), (key1614, -2), (key1769, -2), (key1785, -2), (key1810, -2), (key1334, 2), (key1452, 2), (key1652, 2)]

def rawRow4257 : Integer.Sparse Key := [(key1652, -6), (key1538, 2), (key1614, 2), (key1565, 2), (key1810, 6), (key1308, -2), (key1614, -2), (key1416, -2), (key1769, -2), (key1810, -2), (key1785, -2), (key1334, 2), (key1652, 2), (key1452, 2)]

def rawRow4258 : Integer.Sparse Key := [(key1652, -6), (key1565, 2), (key1538, 2), (key1614, 2), (key1810, 6), (key1416, -2), (key1308, -2), (key1614, -2), (key1785, -2), (key1769, -2), (key1810, -2), (key1452, 2), (key1334, 2), (key1652, 2)]

def rawRow4259 : Integer.Sparse Key := [(key1652, -6), (key1565, 2), (key1614, 2), (key1538, 2), (key1810, 6), (key1416, -2), (key1614, -2), (key1308, -2), (key1785, -2), (key1810, -2), (key1769, -2), (key1452, 2), (key1652, 2), (key1334, 2)]

def rawRow4260 : Integer.Sparse Key := [(key1652, -6), (key1614, 2), (key1538, 2), (key1565, 2), (key1810, 6), (key1614, -2), (key1308, -2), (key1416, -2), (key1810, -2), (key1769, -2), (key1785, -2), (key1652, 2), (key1334, 2), (key1452, 2)]

def rawRow4261 : Integer.Sparse Key := [(key1652, -6), (key1614, 2), (key1565, 2), (key1538, 2), (key1810, 6), (key1614, -2), (key1416, -2), (key1308, -2), (key1810, -2), (key1785, -2), (key1769, -2), (key1652, 2), (key1452, 2), (key1334, 2)]

def rawRow4262 : Integer.Sparse Key := [(key1810, -6), (key1769, 2), (key1785, 2), (key1810, 2), (key1652, 6), (key1334, -2), (key1452, -2), (key1652, -2), (key1538, -2), (key1565, -2), (key1614, -2), (key1308, 2), (key1416, 2), (key1614, 2)]

def rawRow4263 : Integer.Sparse Key := [(key1810, -6), (key1769, 2), (key1810, 2), (key1785, 2), (key1652, 6), (key1334, -2), (key1652, -2), (key1452, -2), (key1538, -2), (key1614, -2), (key1565, -2), (key1308, 2), (key1614, 2), (key1416, 2)]

def rawRow4264 : Integer.Sparse Key := [(key1810, -6), (key1785, 2), (key1769, 2), (key1810, 2), (key1652, 6), (key1452, -2), (key1334, -2), (key1652, -2), (key1565, -2), (key1538, -2), (key1614, -2), (key1416, 2), (key1308, 2), (key1614, 2)]

def rawRow4265 : Integer.Sparse Key := [(key1810, -6), (key1785, 2), (key1810, 2), (key1769, 2), (key1652, 6), (key1452, -2), (key1652, -2), (key1334, -2), (key1565, -2), (key1614, -2), (key1538, -2), (key1416, 2), (key1614, 2), (key1308, 2)]

def rawRow4266 : Integer.Sparse Key := [(key1810, -6), (key1810, 2), (key1769, 2), (key1785, 2), (key1652, 6), (key1652, -2), (key1334, -2), (key1452, -2), (key1614, -2), (key1538, -2), (key1565, -2), (key1614, 2), (key1308, 2), (key1416, 2)]

def rawRow4267 : Integer.Sparse Key := [(key1810, -6), (key1810, 2), (key1785, 2), (key1769, 2), (key1652, 6), (key1652, -2), (key1452, -2), (key1334, -2), (key1614, -2), (key1565, -2), (key1538, -2), (key1614, 2), (key1416, 2), (key1308, 2)]

def rawRow4280 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1148, -2), (key1107, 6), (key1191, 2), (key1197, 2), (key1210, 2), (key994, -2), (key1029, -2), (key1107, -2), (key1191, -6), (key999, 2), (key1034, 2), (key1112, 2)]

def rawRow4281 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1148, -2), (key1107, 6), (key1197, 2), (key1191, 2), (key1210, 2), (key994, -2), (key1107, -2), (key1029, -2), (key1191, -6), (key999, 2), (key1112, 2), (key1034, 2)]

def rawRow4282 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1121, -2), (key1107, 6), (key1191, 2), (key1210, 2), (key1197, 2), (key1029, -2), (key994, -2), (key1107, -2), (key1191, -6), (key1034, 2), (key999, 2), (key1112, 2)]

def rawRow4283 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1121, -2), (key1107, 6), (key1210, 2), (key1191, 2), (key1197, 2), (key1029, -2), (key1107, -2), (key994, -2), (key1191, -6), (key1034, 2), (key1112, 2), (key999, 2)]

def rawRow4284 : Integer.Sparse Key := [(key1121, -2), (key1148, -2), (key1112, -2), (key1107, 6), (key1197, 2), (key1210, 2), (key1191, 2), (key1107, -2), (key994, -2), (key1029, -2), (key1191, -6), (key1112, 2), (key999, 2), (key1034, 2)]

def rawRow4285 : Integer.Sparse Key := [(key1148, -2), (key1121, -2), (key1112, -2), (key1107, 6), (key1210, 2), (key1197, 2), (key1191, 2), (key1107, -2), (key1029, -2), (key994, -2), (key1191, -6), (key1112, 2), (key1034, 2), (key999, 2)]

def rawRow4286 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1210, -2), (key1191, 6), (key1112, 2), (key1121, 2), (key1148, 2), (key999, -2), (key1034, -2), (key1112, -2), (key1107, -6), (key994, 2), (key1029, 2), (key1107, 2)]

def rawRow4287 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1210, -2), (key1191, 6), (key1121, 2), (key1112, 2), (key1148, 2), (key999, -2), (key1112, -2), (key1034, -2), (key1107, -6), (key994, 2), (key1107, 2), (key1029, 2)]

def rawRow4288 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1197, -2), (key1191, 6), (key1112, 2), (key1148, 2), (key1121, 2), (key1034, -2), (key999, -2), (key1112, -2), (key1107, -6), (key1029, 2), (key994, 2), (key1107, 2)]

def rawRow4289 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1197, -2), (key1191, 6), (key1148, 2), (key1112, 2), (key1121, 2), (key1034, -2), (key1112, -2), (key999, -2), (key1107, -6), (key1029, 2), (key1107, 2), (key994, 2)]

def rawRow4290 : Integer.Sparse Key := [(key1197, -2), (key1210, -2), (key1191, -2), (key1191, 6), (key1121, 2), (key1148, 2), (key1112, 2), (key1112, -2), (key999, -2), (key1034, -2), (key1107, -6), (key1107, 2), (key994, 2), (key1029, 2)]

def rawRow4291 : Integer.Sparse Key := [(key1210, -2), (key1197, -2), (key1191, -2), (key1191, 6), (key1148, 2), (key1121, 2), (key1112, 2), (key1112, -2), (key1034, -2), (key999, -2), (key1107, -6), (key1107, 2), (key1029, 2), (key994, 2)]

def rawRow4292 : Integer.Sparse Key := [(key2854, -6), (key2697, 2), (key2800, 2), (key2850, 2), (key2864, 6), (key2623, -2), (key2777, -2), (key2850, -2), (key2720, -2), (key2823, -2), (key2864, -2), (key2634, 2), (key2788, 2), (key2854, 2)]

def rawRow4293 : Integer.Sparse Key := [(key2854, -6), (key2697, 2), (key2850, 2), (key2800, 2), (key2864, 6), (key2623, -2), (key2850, -2), (key2777, -2), (key2720, -2), (key2864, -2), (key2823, -2), (key2634, 2), (key2854, 2), (key2788, 2)]

def rawRow4294 : Integer.Sparse Key := [(key2854, -6), (key2800, 2), (key2697, 2), (key2850, 2), (key2864, 6), (key2777, -2), (key2623, -2), (key2850, -2), (key2823, -2), (key2720, -2), (key2864, -2), (key2788, 2), (key2634, 2), (key2854, 2)]

def rawRow4295 : Integer.Sparse Key := [(key2854, -6), (key2800, 2), (key2850, 2), (key2697, 2), (key2864, 6), (key2777, -2), (key2850, -2), (key2623, -2), (key2823, -2), (key2864, -2), (key2720, -2), (key2788, 2), (key2854, 2), (key2634, 2)]

def rawRow4296 : Integer.Sparse Key := [(key2854, -6), (key2850, 2), (key2697, 2), (key2800, 2), (key2864, 6), (key2850, -2), (key2623, -2), (key2777, -2), (key2864, -2), (key2720, -2), (key2823, -2), (key2854, 2), (key2634, 2), (key2788, 2)]

def rawRow4297 : Integer.Sparse Key := [(key2854, -6), (key2850, 2), (key2800, 2), (key2697, 2), (key2864, 6), (key2850, -2), (key2777, -2), (key2623, -2), (key2864, -2), (key2823, -2), (key2720, -2), (key2854, 2), (key2788, 2), (key2634, 2)]

def rawRow4298 : Integer.Sparse Key := [(key2864, -6), (key2720, 2), (key2823, 2), (key2864, 2), (key2854, 6), (key2634, -2), (key2788, -2), (key2854, -2), (key2697, -2), (key2800, -2), (key2850, -2), (key2623, 2), (key2777, 2), (key2850, 2)]

def rawRow4299 : Integer.Sparse Key := [(key2864, -6), (key2720, 2), (key2864, 2), (key2823, 2), (key2854, 6), (key2634, -2), (key2854, -2), (key2788, -2), (key2697, -2), (key2850, -2), (key2800, -2), (key2623, 2), (key2850, 2), (key2777, 2)]

def rawRow4300 : Integer.Sparse Key := [(key2864, -6), (key2823, 2), (key2720, 2), (key2864, 2), (key2854, 6), (key2788, -2), (key2634, -2), (key2854, -2), (key2800, -2), (key2697, -2), (key2850, -2), (key2777, 2), (key2623, 2), (key2850, 2)]

def rawRow4301 : Integer.Sparse Key := [(key2864, -6), (key2823, 2), (key2864, 2), (key2720, 2), (key2854, 6), (key2788, -2), (key2854, -2), (key2634, -2), (key2800, -2), (key2850, -2), (key2697, -2), (key2777, 2), (key2850, 2), (key2623, 2)]

def rawRow4302 : Integer.Sparse Key := [(key2864, -6), (key2864, 2), (key2720, 2), (key2823, 2), (key2854, 6), (key2854, -2), (key2634, -2), (key2788, -2), (key2850, -2), (key2697, -2), (key2800, -2), (key2850, 2), (key2623, 2), (key2777, 2)]

def rawRow4303 : Integer.Sparse Key := [(key2864, -6), (key2864, 2), (key2823, 2), (key2720, 2), (key2854, 6), (key2854, -2), (key2788, -2), (key2634, -2), (key2850, -2), (key2800, -2), (key2697, -2), (key2850, 2), (key2777, 2), (key2623, 2)]

def rawRow4316 : Integer.Sparse Key := [(key3052, -2), (key3067, -2), (key3104, -2), (key3048, 2), (key3062, 2), (key3097, 2), (key3056, 2), (key3073, 2), (key3111, 2), (key3048, -6), (key3056, -2), (key3071, -2), (key3108, -2), (key3052, 6)]

def rawRow4317 : Integer.Sparse Key := [(key3067, -2), (key3052, -2), (key3104, -2), (key3062, 2), (key3048, 2), (key3097, 2), (key3073, 2), (key3056, 2), (key3111, 2), (key3048, -6), (key3071, -2), (key3056, -2), (key3108, -2), (key3052, 6)]

def rawRow4318 : Integer.Sparse Key := [(key3052, -2), (key3104, -2), (key3067, -2), (key3048, 2), (key3097, 2), (key3062, 2), (key3056, 2), (key3111, 2), (key3073, 2), (key3048, -6), (key3056, -2), (key3108, -2), (key3071, -2), (key3052, 6)]

def rawRow4319 : Integer.Sparse Key := [(key3104, -2), (key3052, -2), (key3067, -2), (key3097, 2), (key3048, 2), (key3062, 2), (key3111, 2), (key3056, 2), (key3073, 2), (key3048, -6), (key3108, -2), (key3056, -2), (key3071, -2), (key3052, 6)]

def rawRow4320 : Integer.Sparse Key := [(key3067, -2), (key3104, -2), (key3052, -2), (key3062, 2), (key3097, 2), (key3048, 2), (key3073, 2), (key3111, 2), (key3056, 2), (key3048, -6), (key3071, -2), (key3108, -2), (key3056, -2), (key3052, 6)]

def rawRow4321 : Integer.Sparse Key := [(key3104, -2), (key3067, -2), (key3052, -2), (key3097, 2), (key3062, 2), (key3048, 2), (key3111, 2), (key3073, 2), (key3056, 2), (key3048, -6), (key3108, -2), (key3071, -2), (key3056, -2), (key3052, 6)]

def rawRow4322 : Integer.Sparse Key := [(key3056, -2), (key3073, -2), (key3111, -2), (key3056, 2), (key3071, 2), (key3108, 2), (key3052, 2), (key3067, 2), (key3104, 2), (key3052, -6), (key3048, -2), (key3062, -2), (key3097, -2), (key3048, 6)]

def rawRow4323 : Integer.Sparse Key := [(key3073, -2), (key3056, -2), (key3111, -2), (key3071, 2), (key3056, 2), (key3108, 2), (key3067, 2), (key3052, 2), (key3104, 2), (key3052, -6), (key3062, -2), (key3048, -2), (key3097, -2), (key3048, 6)]

def rawRow4324 : Integer.Sparse Key := [(key3056, -2), (key3111, -2), (key3073, -2), (key3056, 2), (key3108, 2), (key3071, 2), (key3052, 2), (key3104, 2), (key3067, 2), (key3052, -6), (key3048, -2), (key3097, -2), (key3062, -2), (key3048, 6)]

def rawRow4325 : Integer.Sparse Key := [(key3111, -2), (key3056, -2), (key3073, -2), (key3108, 2), (key3056, 2), (key3071, 2), (key3104, 2), (key3052, 2), (key3067, 2), (key3052, -6), (key3097, -2), (key3048, -2), (key3062, -2), (key3048, 6)]

def rawRow4326 : Integer.Sparse Key := [(key3073, -2), (key3111, -2), (key3056, -2), (key3071, 2), (key3108, 2), (key3056, 2), (key3067, 2), (key3104, 2), (key3052, 2), (key3052, -6), (key3062, -2), (key3097, -2), (key3048, -2), (key3048, 6)]

def rawRow4327 : Integer.Sparse Key := [(key3111, -2), (key3073, -2), (key3056, -2), (key3108, 2), (key3071, 2), (key3056, 2), (key3104, 2), (key3067, 2), (key3052, 2), (key3052, -6), (key3097, -2), (key3062, -2), (key3048, -2), (key3048, 6)]

def rawRow4340 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1147, -2), (key1106, 6), (key1189, 2), (key1196, 2), (key1209, 2), (key993, -2), (key1028, -2), (key1106, -2), (key1189, -6), (key997, 2), (key1032, 2), (key1110, 2)]

def rawRow4341 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1147, -2), (key1106, 6), (key1196, 2), (key1189, 2), (key1209, 2), (key993, -2), (key1106, -2), (key1028, -2), (key1189, -6), (key997, 2), (key1110, 2), (key1032, 2)]

def rawRow4342 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1120, -2), (key1106, 6), (key1189, 2), (key1209, 2), (key1196, 2), (key1028, -2), (key993, -2), (key1106, -2), (key1189, -6), (key1032, 2), (key997, 2), (key1110, 2)]

def rawRow4343 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1120, -2), (key1106, 6), (key1209, 2), (key1189, 2), (key1196, 2), (key1028, -2), (key1106, -2), (key993, -2), (key1189, -6), (key1032, 2), (key1110, 2), (key997, 2)]

def rawRow4344 : Integer.Sparse Key := [(key1120, -2), (key1147, -2), (key1110, -2), (key1106, 6), (key1196, 2), (key1209, 2), (key1189, 2), (key1106, -2), (key993, -2), (key1028, -2), (key1189, -6), (key1110, 2), (key997, 2), (key1032, 2)]

def rawRow4345 : Integer.Sparse Key := [(key1147, -2), (key1120, -2), (key1110, -2), (key1106, 6), (key1209, 2), (key1196, 2), (key1189, 2), (key1106, -2), (key1028, -2), (key993, -2), (key1189, -6), (key1110, 2), (key1032, 2), (key997, 2)]

def rawRow4346 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1209, -2), (key1189, 6), (key1110, 2), (key1120, 2), (key1147, 2), (key997, -2), (key1032, -2), (key1110, -2), (key1106, -6), (key993, 2), (key1028, 2), (key1106, 2)]

def rawRow4347 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1209, -2), (key1189, 6), (key1120, 2), (key1110, 2), (key1147, 2), (key997, -2), (key1110, -2), (key1032, -2), (key1106, -6), (key993, 2), (key1106, 2), (key1028, 2)]

def rawRow4348 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1196, -2), (key1189, 6), (key1110, 2), (key1147, 2), (key1120, 2), (key1032, -2), (key997, -2), (key1110, -2), (key1106, -6), (key1028, 2), (key993, 2), (key1106, 2)]

def rawRow4349 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1196, -2), (key1189, 6), (key1147, 2), (key1110, 2), (key1120, 2), (key1032, -2), (key1110, -2), (key997, -2), (key1106, -6), (key1028, 2), (key1106, 2), (key993, 2)]

def rawRow4350 : Integer.Sparse Key := [(key1196, -2), (key1209, -2), (key1189, -2), (key1189, 6), (key1120, 2), (key1147, 2), (key1110, 2), (key1110, -2), (key997, -2), (key1032, -2), (key1106, -6), (key1106, 2), (key993, 2), (key1028, 2)]

def rawRow4351 : Integer.Sparse Key := [(key1209, -2), (key1196, -2), (key1189, -2), (key1189, 6), (key1147, 2), (key1120, 2), (key1110, 2), (key1110, -2), (key1032, -2), (key997, -2), (key1106, -6), (key1106, 2), (key1028, 2), (key993, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4364 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2500, -2), (key2465, 6), (key2536, 2), (key2541, 2), (key2552, 2), (key2371, -2), (key2399, -2), (key2465, -2), (key2536, -6), (key2375, 2), (key2403, 2), (key2469, 2)]

def rawRow4365 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2500, -2), (key2465, 6), (key2541, 2), (key2536, 2), (key2552, 2), (key2371, -2), (key2465, -2), (key2399, -2), (key2536, -6), (key2375, 2), (key2469, 2), (key2403, 2)]

def rawRow4366 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2477, -2), (key2465, 6), (key2536, 2), (key2552, 2), (key2541, 2), (key2399, -2), (key2371, -2), (key2465, -2), (key2536, -6), (key2403, 2), (key2375, 2), (key2469, 2)]

def rawRow4367 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2477, -2), (key2465, 6), (key2552, 2), (key2536, 2), (key2541, 2), (key2399, -2), (key2465, -2), (key2371, -2), (key2536, -6), (key2403, 2), (key2469, 2), (key2375, 2)]

def rawRow4368 : Integer.Sparse Key := [(key2477, -2), (key2500, -2), (key2469, -2), (key2465, 6), (key2541, 2), (key2552, 2), (key2536, 2), (key2465, -2), (key2371, -2), (key2399, -2), (key2536, -6), (key2469, 2), (key2375, 2), (key2403, 2)]

def rawRow4369 : Integer.Sparse Key := [(key2500, -2), (key2477, -2), (key2469, -2), (key2465, 6), (key2552, 2), (key2541, 2), (key2536, 2), (key2465, -2), (key2399, -2), (key2371, -2), (key2536, -6), (key2469, 2), (key2403, 2), (key2375, 2)]

def rawRow4370 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2552, -2), (key2536, 6), (key2469, 2), (key2477, 2), (key2500, 2), (key2375, -2), (key2403, -2), (key2469, -2), (key2465, -6), (key2371, 2), (key2399, 2), (key2465, 2)]

def rawRow4371 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2552, -2), (key2536, 6), (key2477, 2), (key2469, 2), (key2500, 2), (key2375, -2), (key2469, -2), (key2403, -2), (key2465, -6), (key2371, 2), (key2465, 2), (key2399, 2)]

def rawRow4372 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2541, -2), (key2536, 6), (key2469, 2), (key2500, 2), (key2477, 2), (key2403, -2), (key2375, -2), (key2469, -2), (key2465, -6), (key2399, 2), (key2371, 2), (key2465, 2)]

def rawRow4373 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2541, -2), (key2536, 6), (key2500, 2), (key2469, 2), (key2477, 2), (key2403, -2), (key2469, -2), (key2375, -2), (key2465, -6), (key2399, 2), (key2465, 2), (key2371, 2)]

def rawRow4374 : Integer.Sparse Key := [(key2541, -2), (key2552, -2), (key2536, -2), (key2536, 6), (key2477, 2), (key2500, 2), (key2469, 2), (key2469, -2), (key2375, -2), (key2403, -2), (key2465, -6), (key2465, 2), (key2371, 2), (key2399, 2)]

def rawRow4375 : Integer.Sparse Key := [(key2552, -2), (key2541, -2), (key2536, -2), (key2536, 6), (key2500, 2), (key2477, 2), (key2469, 2), (key2469, -2), (key2403, -2), (key2375, -2), (key2465, -6), (key2465, 2), (key2399, 2), (key2371, 2)]

def rawRow4376 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2499, -2), (key2464, 6), (key2534, 2), (key2540, 2), (key2551, 2), (key2370, -2), (key2762, -2), (key2839, -2), (key2874, -6), (key2586, 2), (key2765, 2), (key2842, 2)]

def rawRow4377 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2499, -2), (key2464, 6), (key2540, 2), (key2534, 2), (key2551, 2), (key2370, -2), (key2839, -2), (key2762, -2), (key2874, -6), (key2586, 2), (key2842, 2), (key2765, 2)]

def rawRow4378 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2476, -2), (key2464, 6), (key2534, 2), (key2551, 2), (key2540, 2), (key2398, -2), (key2583, -2), (key2839, -2), (key2874, -6), (key2765, 2), (key2586, 2), (key2842, 2)]

def rawRow4379 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2476, -2), (key2464, 6), (key2551, 2), (key2534, 2), (key2540, 2), (key2398, -2), (key2839, -2), (key2583, -2), (key2874, -6), (key2765, 2), (key2842, 2), (key2586, 2)]

def rawRow4380 : Integer.Sparse Key := [(key2476, -2), (key2499, -2), (key2467, -2), (key2464, 6), (key2540, 2), (key2551, 2), (key2534, 2), (key2464, -2), (key2370, -2), (key2762, -2), (key2874, -6), (key2842, 2), (key2586, 2), (key2765, 2)]

def rawRow4381 : Integer.Sparse Key := [(key2499, -2), (key2476, -2), (key2467, -2), (key2464, 6), (key2551, 2), (key2540, 2), (key2534, 2), (key2464, -2), (key2398, -2), (key2583, -2), (key2874, -6), (key2842, 2), (key2765, 2), (key2586, 2)]

def rawRow4382 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2551, -2), (key2534, 6), (key2467, 2), (key2476, 2), (key2499, 2), (key2373, -2), (key2401, -2), (key2467, -2), (key2464, -6), (key2370, 2), (key2762, 2), (key2839, 2)]

def rawRow4383 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2551, -2), (key2534, 6), (key2476, 2), (key2467, 2), (key2499, 2), (key2373, -2), (key2467, -2), (key2401, -2), (key2464, -6), (key2370, 2), (key2839, 2), (key2762, 2)]

def rawRow4384 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2540, -2), (key2534, 6), (key2467, 2), (key2499, 2), (key2476, 2), (key2401, -2), (key2373, -2), (key2467, -2), (key2464, -6), (key2398, 2), (key2583, 2), (key2839, 2)]

def rawRow4385 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2540, -2), (key2534, 6), (key2499, 2), (key2467, 2), (key2476, 2), (key2401, -2), (key2467, -2), (key2373, -2), (key2464, -6), (key2398, 2), (key2839, 2), (key2583, 2)]

def rawRow4386 : Integer.Sparse Key := [(key2540, -2), (key2551, -2), (key2534, -2), (key2534, 6), (key2476, 2), (key2499, 2), (key2467, 2), (key2467, -2), (key2373, -2), (key2401, -2), (key2464, -6), (key2464, 2), (key2370, 2), (key2762, 2)]

def rawRow4387 : Integer.Sparse Key := [(key2551, -2), (key2540, -2), (key2534, -2), (key2534, 6), (key2499, 2), (key2476, 2), (key2467, 2), (key2467, -2), (key2401, -2), (key2373, -2), (key2464, -6), (key2464, 2), (key2398, 2), (key2583, 2)]

def rawRow4400 : Integer.Sparse Key := [(key2193, -2), (key2194, -2), (key2200, -2), (key2194, 6), (key2302, 2), (key2303, 2), (key2310, 2), (key2092, -2), (key2303, -2), (key2341, -2), (key2305, -6), (key2095, 2), (key2305, 2), (key2343, 2)]

def rawRow4401 : Integer.Sparse Key := [(key2194, -2), (key2193, -2), (key2200, -2), (key2194, 6), (key2303, 2), (key2302, 2), (key2310, 2), (key2092, -2), (key2341, -2), (key2303, -2), (key2305, -6), (key2095, 2), (key2343, 2), (key2305, 2)]

def rawRow4402 : Integer.Sparse Key := [(key2193, -2), (key2200, -2), (key2194, -2), (key2194, 6), (key2302, 2), (key2310, 2), (key2303, 2), (key2303, -2), (key2092, -2), (key2341, -2), (key2305, -6), (key2305, 2), (key2095, 2), (key2343, 2)]

def rawRow4403 : Integer.Sparse Key := [(key2200, -2), (key2193, -2), (key2194, -2), (key2194, 6), (key2310, 2), (key2302, 2), (key2303, 2), (key2303, -2), (key2341, -2), (key2092, -2), (key2305, -6), (key2305, 2), (key2343, 2), (key2095, 2)]

def rawRow4404 : Integer.Sparse Key := [(key2194, -2), (key2200, -2), (key2193, -2), (key2194, 6), (key2303, 2), (key2310, 2), (key2302, 2), (key2341, -2), (key2092, -2), (key2303, -2), (key2305, -6), (key2343, 2), (key2095, 2), (key2305, 2)]

def rawRow4405 : Integer.Sparse Key := [(key2200, -2), (key2194, -2), (key2193, -2), (key2194, 6), (key2310, 2), (key2303, 2), (key2302, 2), (key2341, -2), (key2303, -2), (key2092, -2), (key2305, -6), (key2343, 2), (key2305, 2), (key2095, 2)]

def rawRow4406 : Integer.Sparse Key := [(key2302, -2), (key2303, -2), (key2310, -2), (key2305, 6), (key2193, 2), (key2194, 2), (key2200, 2), (key2095, -2), (key2305, -2), (key2343, -2), (key2194, -6), (key2092, 2), (key2303, 2), (key2341, 2)]

def rawRow4407 : Integer.Sparse Key := [(key2303, -2), (key2302, -2), (key2310, -2), (key2305, 6), (key2194, 2), (key2193, 2), (key2200, 2), (key2095, -2), (key2343, -2), (key2305, -2), (key2194, -6), (key2092, 2), (key2341, 2), (key2303, 2)]

def rawRow4408 : Integer.Sparse Key := [(key2302, -2), (key2310, -2), (key2303, -2), (key2305, 6), (key2193, 2), (key2200, 2), (key2194, 2), (key2305, -2), (key2095, -2), (key2343, -2), (key2194, -6), (key2303, 2), (key2092, 2), (key2341, 2)]

def rawRow4409 : Integer.Sparse Key := [(key2310, -2), (key2302, -2), (key2303, -2), (key2305, 6), (key2200, 2), (key2193, 2), (key2194, 2), (key2305, -2), (key2343, -2), (key2095, -2), (key2194, -6), (key2303, 2), (key2341, 2), (key2092, 2)]

def rawRow4410 : Integer.Sparse Key := [(key2303, -2), (key2310, -2), (key2302, -2), (key2305, 6), (key2194, 2), (key2200, 2), (key2193, 2), (key2343, -2), (key2095, -2), (key2305, -2), (key2194, -6), (key2341, 2), (key2092, 2), (key2303, 2)]

def rawRow4411 : Integer.Sparse Key := [(key2310, -2), (key2303, -2), (key2302, -2), (key2305, 6), (key2200, 2), (key2194, 2), (key2193, 2), (key2343, -2), (key2305, -2), (key2095, -2), (key2194, -6), (key2341, 2), (key2303, 2), (key2092, 2)]

def rawRow4412 : Integer.Sparse Key := [(key2303, -2), (key2305, -2), (key2310, -2), (key2302, 6), (key2341, 2), (key2343, 2), (key2347, 2), (key2091, -2), (key2193, -2), (key2302, -2), (key2341, -6), (key2092, 2), (key2194, 2), (key2303, 2)]

def rawRow4413 : Integer.Sparse Key := [(key2305, -2), (key2303, -2), (key2310, -2), (key2302, 6), (key2343, 2), (key2341, 2), (key2347, 2), (key2091, -2), (key2302, -2), (key2193, -2), (key2341, -6), (key2092, 2), (key2303, 2), (key2194, 2)]

def rawRow4414 : Integer.Sparse Key := [(key2303, -2), (key2310, -2), (key2305, -2), (key2302, 6), (key2341, 2), (key2347, 2), (key2343, 2), (key2193, -2), (key2091, -2), (key2302, -2), (key2341, -6), (key2194, 2), (key2092, 2), (key2303, 2)]

def rawRow4415 : Integer.Sparse Key := [(key2310, -2), (key2303, -2), (key2305, -2), (key2302, 6), (key2347, 2), (key2341, 2), (key2343, 2), (key2193, -2), (key2302, -2), (key2091, -2), (key2341, -6), (key2194, 2), (key2303, 2), (key2092, 2)]

def rawRow4416 : Integer.Sparse Key := [(key2305, -2), (key2310, -2), (key2303, -2), (key2302, 6), (key2343, 2), (key2347, 2), (key2341, 2), (key2302, -2), (key2091, -2), (key2193, -2), (key2341, -6), (key2303, 2), (key2092, 2), (key2194, 2)]

def rawRow4417 : Integer.Sparse Key := [(key2310, -2), (key2305, -2), (key2303, -2), (key2302, 6), (key2347, 2), (key2343, 2), (key2341, 2), (key2302, -2), (key2193, -2), (key2091, -2), (key2341, -6), (key2303, 2), (key2194, 2), (key2092, 2)]

def rawRow4418 : Integer.Sparse Key := [(key2341, -2), (key2343, -2), (key2347, -2), (key2341, 6), (key2303, 2), (key2305, 2), (key2310, 2), (key2092, -2), (key2194, -2), (key2303, -2), (key2302, -6), (key2091, 2), (key2193, 2), (key2302, 2)]

def rawRow4419 : Integer.Sparse Key := [(key2343, -2), (key2341, -2), (key2347, -2), (key2341, 6), (key2305, 2), (key2303, 2), (key2310, 2), (key2092, -2), (key2303, -2), (key2194, -2), (key2302, -6), (key2091, 2), (key2302, 2), (key2193, 2)]

def rawRow4420 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2343, -2), (key2341, 6), (key2303, 2), (key2310, 2), (key2305, 2), (key2194, -2), (key2092, -2), (key2303, -2), (key2302, -6), (key2193, 2), (key2091, 2), (key2302, 2)]

def rawRow4421 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2343, -2), (key2341, 6), (key2310, 2), (key2303, 2), (key2305, 2), (key2194, -2), (key2303, -2), (key2092, -2), (key2302, -6), (key2193, 2), (key2302, 2), (key2091, 2)]

def rawRow4422 : Integer.Sparse Key := [(key2343, -2), (key2347, -2), (key2341, -2), (key2341, 6), (key2305, 2), (key2310, 2), (key2303, 2), (key2303, -2), (key2092, -2), (key2194, -2), (key2302, -6), (key2302, 2), (key2091, 2), (key2193, 2)]

def rawRow4423 : Integer.Sparse Key := [(key2347, -2), (key2343, -2), (key2341, -2), (key2341, 6), (key2310, 2), (key2305, 2), (key2303, 2), (key2303, -2), (key2194, -2), (key2092, -2), (key2302, -6), (key2302, 2), (key2193, 2), (key2091, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4496 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1568, -1), (key1787, -1), (key1591, -1), (key1796, -1), (key1295, 2), (key1572, 2), (key1787, 2), (key1311, 1), (key1315, 1), (key1617, 1), (key1812, 1), (key1631, 1), (key1823, 1), (key1315, -1), (key1336, -1), (key1545, -1), (key1771, -1), (key1654, -1), (key1812, -1), (key1324, -2), (key1622, -2), (key1815, -2), (key1324, 1), (key1343, 1), (key1554, 1), (key1778, 1), (key1657, 1), (key1815, 1)]

def rawRow4497 : Integer.Sparse Key := [(key1295, -1), (key1291, -1), (key1787, -1), (key1568, -1), (key1796, -1), (key1591, -1), (key1295, 2), (key1787, 2), (key1572, 2), (key1315, 1), (key1311, 1), (key1812, 1), (key1617, 1), (key1823, 1), (key1631, 1), (key1336, -1), (key1315, -1), (key1771, -1), (key1545, -1), (key1812, -1), (key1654, -1), (key1324, -2), (key1815, -2), (key1622, -2), (key1343, 1), (key1324, 1), (key1778, 1), (key1554, 1), (key1815, 1), (key1657, 1)]

def rawRow4498 : Integer.Sparse Key := [(key1568, -1), (key1591, -1), (key1291, -1), (key1796, -1), (key1295, -1), (key1787, -1), (key1572, 2), (key1295, 2), (key1787, 2), (key1617, 1), (key1631, 1), (key1311, 1), (key1823, 1), (key1315, 1), (key1812, 1), (key1545, -1), (key1654, -1), (key1315, -1), (key1812, -1), (key1336, -1), (key1771, -1), (key1622, -2), (key1324, -2), (key1815, -2), (key1554, 1), (key1657, 1), (key1324, 1), (key1815, 1), (key1343, 1), (key1778, 1)]

def rawRow4499 : Integer.Sparse Key := [(key1591, -1), (key1568, -1), (key1796, -1), (key1291, -1), (key1787, -1), (key1295, -1), (key1572, 2), (key1787, 2), (key1295, 2), (key1631, 1), (key1617, 1), (key1823, 1), (key1311, 1), (key1812, 1), (key1315, 1), (key1654, -1), (key1545, -1), (key1812, -1), (key1315, -1), (key1771, -1), (key1336, -1), (key1622, -2), (key1815, -2), (key1324, -2), (key1657, 1), (key1554, 1), (key1815, 1), (key1324, 1), (key1778, 1), (key1343, 1)]

def rawRow4500 : Integer.Sparse Key := [(key1787, -1), (key1796, -1), (key1295, -1), (key1591, -1), (key1291, -1), (key1568, -1), (key1787, 2), (key1295, 2), (key1572, 2), (key1812, 1), (key1823, 1), (key1315, 1), (key1631, 1), (key1311, 1), (key1617, 1), (key1771, -1), (key1812, -1), (key1336, -1), (key1654, -1), (key1315, -1), (key1545, -1), (key1815, -2), (key1324, -2), (key1622, -2), (key1778, 1), (key1815, 1), (key1343, 1), (key1657, 1), (key1324, 1), (key1554, 1)]

def rawRow4501 : Integer.Sparse Key := [(key1796, -1), (key1787, -1), (key1591, -1), (key1295, -1), (key1568, -1), (key1291, -1), (key1787, 2), (key1572, 2), (key1295, 2), (key1823, 1), (key1812, 1), (key1631, 1), (key1315, 1), (key1617, 1), (key1311, 1), (key1812, -1), (key1771, -1), (key1654, -1), (key1336, -1), (key1545, -1), (key1315, -1), (key1815, -2), (key1622, -2), (key1324, -2), (key1815, 1), (key1778, 1), (key1657, 1), (key1343, 1), (key1554, 1), (key1324, 1)]

def rawRow4505 : Integer.Sparse Key := [(key1311, -1), (key1315, -1), (key1617, -1), (key1812, -1), (key1631, -1), (key1823, -1), (key1324, 2), (key1622, 2), (key1815, 2), (key1291, 1), (key1295, 1), (key1568, 1), (key1787, 1), (key1591, 1), (key1796, 1), (key1324, -1), (key1343, -1), (key1554, -1), (key1778, -1), (key1657, -1), (key1815, -1), (key1295, -2), (key1572, -2), (key1787, -2), (key1315, 1), (key1336, 1), (key1545, 1), (key1771, 1), (key1654, 1), (key1812, 1)]

def rawRow4506 : Integer.Sparse Key := [(key1315, -1), (key1311, -1), (key1812, -1), (key1617, -1), (key1823, -1), (key1631, -1), (key1324, 2), (key1815, 2), (key1622, 2), (key1295, 1), (key1291, 1), (key1787, 1), (key1568, 1), (key1796, 1), (key1591, 1), (key1343, -1), (key1324, -1), (key1778, -1), (key1554, -1), (key1815, -1), (key1657, -1), (key1295, -2), (key1787, -2), (key1572, -2), (key1336, 1), (key1315, 1), (key1771, 1), (key1545, 1), (key1812, 1), (key1654, 1)]

def rawRow4507 : Integer.Sparse Key := [(key1617, -1), (key1631, -1), (key1311, -1), (key1823, -1), (key1315, -1), (key1812, -1), (key1622, 2), (key1324, 2), (key1815, 2), (key1568, 1), (key1591, 1), (key1291, 1), (key1796, 1), (key1295, 1), (key1787, 1), (key1554, -1), (key1657, -1), (key1324, -1), (key1815, -1), (key1343, -1), (key1778, -1), (key1572, -2), (key1295, -2), (key1787, -2), (key1545, 1), (key1654, 1), (key1315, 1), (key1812, 1), (key1336, 1), (key1771, 1)]

def rawRow4508 : Integer.Sparse Key := [(key1631, -1), (key1617, -1), (key1823, -1), (key1311, -1), (key1812, -1), (key1315, -1), (key1622, 2), (key1815, 2), (key1324, 2), (key1591, 1), (key1568, 1), (key1796, 1), (key1291, 1), (key1787, 1), (key1295, 1), (key1657, -1), (key1554, -1), (key1815, -1), (key1324, -1), (key1778, -1), (key1343, -1), (key1572, -2), (key1787, -2), (key1295, -2), (key1654, 1), (key1545, 1), (key1812, 1), (key1315, 1), (key1771, 1), (key1336, 1)]

def rawRow4509 : Integer.Sparse Key := [(key1812, -1), (key1823, -1), (key1315, -1), (key1631, -1), (key1311, -1), (key1617, -1), (key1815, 2), (key1324, 2), (key1622, 2), (key1787, 1), (key1796, 1), (key1295, 1), (key1591, 1), (key1291, 1), (key1568, 1), (key1778, -1), (key1815, -1), (key1343, -1), (key1657, -1), (key1324, -1), (key1554, -1), (key1787, -2), (key1295, -2), (key1572, -2), (key1771, 1), (key1812, 1), (key1336, 1), (key1654, 1), (key1315, 1), (key1545, 1)]

def rawRow4510 : Integer.Sparse Key := [(key1823, -1), (key1812, -1), (key1631, -1), (key1315, -1), (key1617, -1), (key1311, -1), (key1815, 2), (key1622, 2), (key1324, 2), (key1796, 1), (key1787, 1), (key1591, 1), (key1295, 1), (key1568, 1), (key1291, 1), (key1815, -1), (key1778, -1), (key1657, -1), (key1343, -1), (key1554, -1), (key1324, -1), (key1787, -2), (key1572, -2), (key1295, -2), (key1812, 1), (key1771, 1), (key1654, 1), (key1336, 1), (key1545, 1), (key1315, 1)]

def rawRow4511 : Integer.Sparse Key := [(key1315, -1), (key1324, -1), (key1423, -1), (key1622, -1), (key1442, -1), (key1631, -1), (key1311, 2), (key1419, 2), (key1617, 2), (key1336, 1), (key1343, 1), (key1454, 1), (key1657, 1), (key1464, 1), (key1665, 1), (key1291, -1), (key1311, -1), (key1386, -1), (key1541, -1), (key1419, -1), (key1568, -1), (key1336, -2), (key1454, -2), (key1654, -2), (key1295, 1), (key1315, 1), (key1390, 1), (key1545, 1), (key1423, 1), (key1572, 1)]

def rawRow4512 : Integer.Sparse Key := [(key1324, -1), (key1315, -1), (key1622, -1), (key1423, -1), (key1631, -1), (key1442, -1), (key1311, 2), (key1617, 2), (key1419, 2), (key1343, 1), (key1336, 1), (key1657, 1), (key1454, 1), (key1665, 1), (key1464, 1), (key1311, -1), (key1291, -1), (key1541, -1), (key1386, -1), (key1568, -1), (key1419, -1), (key1336, -2), (key1654, -2), (key1454, -2), (key1315, 1), (key1295, 1), (key1545, 1), (key1390, 1), (key1572, 1), (key1423, 1)]

def rawRow4513 : Integer.Sparse Key := [(key1423, -1), (key1442, -1), (key1315, -1), (key1631, -1), (key1324, -1), (key1622, -1), (key1419, 2), (key1311, 2), (key1617, 2), (key1454, 1), (key1464, 1), (key1336, 1), (key1665, 1), (key1343, 1), (key1657, 1), (key1386, -1), (key1419, -1), (key1291, -1), (key1568, -1), (key1311, -1), (key1541, -1), (key1454, -2), (key1336, -2), (key1654, -2), (key1390, 1), (key1423, 1), (key1295, 1), (key1572, 1), (key1315, 1), (key1545, 1)]

def rawRow4514 : Integer.Sparse Key := [(key1442, -1), (key1423, -1), (key1631, -1), (key1315, -1), (key1622, -1), (key1324, -1), (key1419, 2), (key1617, 2), (key1311, 2), (key1464, 1), (key1454, 1), (key1665, 1), (key1336, 1), (key1657, 1), (key1343, 1), (key1419, -1), (key1386, -1), (key1568, -1), (key1291, -1), (key1541, -1), (key1311, -1), (key1454, -2), (key1654, -2), (key1336, -2), (key1423, 1), (key1390, 1), (key1572, 1), (key1295, 1), (key1545, 1), (key1315, 1)]

def rawRow4515 : Integer.Sparse Key := [(key1622, -1), (key1631, -1), (key1324, -1), (key1442, -1), (key1315, -1), (key1423, -1), (key1617, 2), (key1311, 2), (key1419, 2), (key1657, 1), (key1665, 1), (key1343, 1), (key1464, 1), (key1336, 1), (key1454, 1), (key1541, -1), (key1568, -1), (key1311, -1), (key1419, -1), (key1291, -1), (key1386, -1), (key1654, -2), (key1336, -2), (key1454, -2), (key1545, 1), (key1572, 1), (key1315, 1), (key1423, 1), (key1295, 1), (key1390, 1)]

def rawRow4516 : Integer.Sparse Key := [(key1631, -1), (key1622, -1), (key1442, -1), (key1324, -1), (key1423, -1), (key1315, -1), (key1617, 2), (key1419, 2), (key1311, 2), (key1665, 1), (key1657, 1), (key1464, 1), (key1343, 1), (key1454, 1), (key1336, 1), (key1568, -1), (key1541, -1), (key1419, -1), (key1311, -1), (key1386, -1), (key1291, -1), (key1654, -2), (key1454, -2), (key1336, -2), (key1572, 1), (key1545, 1), (key1423, 1), (key1315, 1), (key1390, 1), (key1295, 1)]

def rawRow4520 : Integer.Sparse Key := [(key1336, -1), (key1343, -1), (key1454, -1), (key1657, -1), (key1464, -1), (key1665, -1), (key1336, 2), (key1454, 2), (key1654, 2), (key1315, 1), (key1324, 1), (key1423, 1), (key1622, 1), (key1442, 1), (key1631, 1), (key1295, -1), (key1315, -1), (key1390, -1), (key1545, -1), (key1423, -1), (key1572, -1), (key1311, -2), (key1419, -2), (key1617, -2), (key1291, 1), (key1311, 1), (key1386, 1), (key1541, 1), (key1419, 1), (key1568, 1)]

def rawRow4521 : Integer.Sparse Key := [(key1343, -1), (key1336, -1), (key1657, -1), (key1454, -1), (key1665, -1), (key1464, -1), (key1336, 2), (key1654, 2), (key1454, 2), (key1324, 1), (key1315, 1), (key1622, 1), (key1423, 1), (key1631, 1), (key1442, 1), (key1315, -1), (key1295, -1), (key1545, -1), (key1390, -1), (key1572, -1), (key1423, -1), (key1311, -2), (key1617, -2), (key1419, -2), (key1311, 1), (key1291, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1419, 1)]

def rawRow4522 : Integer.Sparse Key := [(key1454, -1), (key1464, -1), (key1336, -1), (key1665, -1), (key1343, -1), (key1657, -1), (key1454, 2), (key1336, 2), (key1654, 2), (key1423, 1), (key1442, 1), (key1315, 1), (key1631, 1), (key1324, 1), (key1622, 1), (key1390, -1), (key1423, -1), (key1295, -1), (key1572, -1), (key1315, -1), (key1545, -1), (key1419, -2), (key1311, -2), (key1617, -2), (key1386, 1), (key1419, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1541, 1)]

def rawRow4523 : Integer.Sparse Key := [(key1464, -1), (key1454, -1), (key1665, -1), (key1336, -1), (key1657, -1), (key1343, -1), (key1454, 2), (key1654, 2), (key1336, 2), (key1442, 1), (key1423, 1), (key1631, 1), (key1315, 1), (key1622, 1), (key1324, 1), (key1423, -1), (key1390, -1), (key1572, -1), (key1295, -1), (key1545, -1), (key1315, -1), (key1419, -2), (key1617, -2), (key1311, -2), (key1419, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1541, 1), (key1311, 1)]

def rawRow4524 : Integer.Sparse Key := [(key1657, -1), (key1665, -1), (key1343, -1), (key1464, -1), (key1336, -1), (key1454, -1), (key1654, 2), (key1336, 2), (key1454, 2), (key1622, 1), (key1631, 1), (key1324, 1), (key1442, 1), (key1315, 1), (key1423, 1), (key1545, -1), (key1572, -1), (key1315, -1), (key1423, -1), (key1295, -1), (key1390, -1), (key1617, -2), (key1311, -2), (key1419, -2), (key1541, 1), (key1568, 1), (key1311, 1), (key1419, 1), (key1291, 1), (key1386, 1)]

def rawRow4525 : Integer.Sparse Key := [(key1665, -1), (key1657, -1), (key1464, -1), (key1343, -1), (key1454, -1), (key1336, -1), (key1654, 2), (key1454, 2), (key1336, 2), (key1631, 1), (key1622, 1), (key1442, 1), (key1324, 1), (key1423, 1), (key1315, 1), (key1572, -1), (key1545, -1), (key1423, -1), (key1315, -1), (key1390, -1), (key1295, -1), (key1617, -2), (key1419, -2), (key1311, -2), (key1568, 1), (key1541, 1), (key1419, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

def rawRow4556 : Integer.Sparse Key := [(key1492, -2), (key1492, -2), (key1519, -2), (key1492, 1), (key1496, 1), (key1492, 1), (key1519, 1), (key1496, 1), (key1519, 1), (key1718, 2), (key1718, 2), (key1747, 2), (key1718, -1), (key1728, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1747, -1), (key1863, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1880, -1), (key1863, 1), (key1870, 1), (key1863, 1), (key1880, 1), (key1870, 1), (key1880, 1)]

def rawRow4557 : Integer.Sparse Key := [(key1492, -2), (key1519, -2), (key1492, -2), (key1496, 1), (key1492, 1), (key1519, 1), (key1492, 1), (key1519, 1), (key1496, 1), (key1718, 2), (key1747, 2), (key1718, 2), (key1728, -1), (key1718, -1), (key1747, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1870, 1), (key1863, 1), (key1880, 1), (key1863, 1), (key1880, 1), (key1870, 1)]

def rawRow4558 : Integer.Sparse Key := [(key1519, -2), (key1492, -2), (key1492, -2), (key1519, 1), (key1519, 1), (key1496, 1), (key1496, 1), (key1492, 1), (key1492, 1), (key1747, 2), (key1718, 2), (key1718, 2), (key1747, -1), (key1747, -1), (key1728, -1), (key1728, -1), (key1718, -1), (key1718, -1), (key1880, -1), (key1880, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1880, 1), (key1880, 1), (key1870, 1), (key1870, 1), (key1863, 1), (key1863, 1)]

def rawRow4560 : Integer.Sparse Key := [(key1718, -2), (key1718, -2), (key1747, -2), (key1863, 1), (key1865, 1), (key1863, 1), (key1880, 1), (key1865, 1), (key1880, 1), (key1492, 2), (key1492, 2), (key1519, 2), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1492, -1), (key1496, -1), (key1492, -1), (key1519, -1), (key1496, -1), (key1519, -1), (key1718, 1), (key1728, 1), (key1718, 1), (key1747, 1), (key1728, 1), (key1747, 1)]

def rawRow4561 : Integer.Sparse Key := [(key1718, -2), (key1747, -2), (key1718, -2), (key1865, 1), (key1863, 1), (key1880, 1), (key1863, 1), (key1880, 1), (key1865, 1), (key1492, 2), (key1519, 2), (key1492, 2), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1496, -1), (key1492, -1), (key1519, -1), (key1492, -1), (key1519, -1), (key1496, -1), (key1728, 1), (key1718, 1), (key1747, 1), (key1718, 1), (key1747, 1), (key1728, 1)]

def rawRow4562 : Integer.Sparse Key := [(key1747, -2), (key1718, -2), (key1718, -2), (key1880, 1), (key1880, 1), (key1865, 1), (key1865, 1), (key1863, 1), (key1863, 1), (key1519, 2), (key1492, 2), (key1492, 2), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1519, -1), (key1519, -1), (key1496, -1), (key1496, -1), (key1492, -1), (key1492, -1), (key1747, 1), (key1747, 1), (key1728, 1), (key1728, 1), (key1718, 1), (key1718, 1)]

def rawRow4563 : Integer.Sparse Key := [(key1370, -2), (key1865, -2), (key1865, -2), (key1366, 1), (key1366, 1), (key1718, 1), (key1718, 1), (key1863, 1), (key1863, 1), (key1379, 2), (key1870, 2), (key1870, 2), (key1366, -1), (key1366, -1), (key1492, -1), (key1492, -1), (key1863, -1), (key1863, -1), (key1379, -1), (key1379, -1), (key1728, -1), (key1728, -1), (key1870, -1), (key1870, -1), (key1370, 1), (key1370, 1), (key1496, 1), (key1496, 1), (key1865, 1), (key1865, 1)]

def rawRow4564 : Integer.Sparse Key := [(key1865, -2), (key1370, -2), (key1865, -2), (key1718, 1), (key1863, 1), (key1366, 1), (key1863, 1), (key1366, 1), (key1718, 1), (key1870, 2), (key1379, 2), (key1870, 2), (key1492, -1), (key1863, -1), (key1366, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1728, -1), (key1870, -1), (key1379, -1), (key1870, -1), (key1379, -1), (key1728, -1), (key1496, 1), (key1865, 1), (key1370, 1), (key1865, 1), (key1370, 1), (key1496, 1)]

def rawRow4565 : Integer.Sparse Key := [(key1865, -2), (key1865, -2), (key1370, -2), (key1863, 1), (key1718, 1), (key1863, 1), (key1366, 1), (key1718, 1), (key1366, 1), (key1870, 2), (key1870, 2), (key1379, 2), (key1863, -1), (key1492, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1366, -1), (key1870, -1), (key1728, -1), (key1870, -1), (key1379, -1), (key1728, -1), (key1379, -1), (key1865, 1), (key1496, 1), (key1865, 1), (key1370, 1), (key1496, 1), (key1370, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow386 : Integer.Sparse Key := [(key275, -2), (key270, 1), (key276, 1), (key266, 2), (key245, -1), (key276, -1), (key255, -1), (key266, -1), (key243, 1), (key275, 1), (key344, 2), (key334, -1), (key345, -1), (key338, -2), (key311, 1), (key345, 1), (key323, 1), (key338, 1), (key309, -1), (key344, -1), (key479, -2), (key424, 1), (key485, 1), (key473, 2), (key403, -1), (key485, -1), (key413, -1), (key473, -1), (key392, 1), (key479, 1), (key605, 1), (key614, 1), (key587, -1), (key616, -1), (key599, -1), (key613, -1), (key576, 1), (key616, 1), (key581, 1), (key613, 1), (key571, -1), (key614, -1)]

def rawRow387 : Integer.Sparse Key := [(key275, -2), (key276, 1), (key270, 1), (key266, 2), (key276, -1), (key245, -1), (key266, -1), (key255, -1), (key275, 1), (key243, 1), (key344, 2), (key345, -1), (key334, -1), (key338, -2), (key345, 1), (key311, 1), (key338, 1), (key323, 1), (key344, -1), (key309, -1), (key479, -2), (key485, 1), (key424, 1), (key473, 2), (key485, -1), (key403, -1), (key473, -1), (key413, -1), (key479, 1), (key392, 1), (key614, 1), (key605, 1), (key616, -1), (key587, -1), (key613, -1), (key599, -1), (key616, 1), (key576, 1), (key613, 1), (key581, 1), (key614, -1), (key571, -1)]

def rawRow389 : Integer.Sparse Key := [(key311, -2), (key309, 1), (key311, 1), (key338, 2), (key323, -1), (key338, -1), (key344, -1), (key345, -1), (key334, 1), (key345, 1), (key245, 2), (key243, -1), (key245, -1), (key424, -2), (key413, 1), (key424, 1), (key587, 1), (key588, 1), (key581, -1), (key588, -1), (key266, -2), (key255, 1), (key266, 1), (key334, 2), (key323, -1), (key334, -1), (key605, -1), (key611, -1), (key599, 1), (key611, 1), (key275, 1), (key276, 1), (key270, -1), (key276, -1), (key344, -1), (key345, -1), (key338, 1), (key345, 1), (key479, 1), (key485, 1), (key473, -1), (key485, -1)]

def rawRow390 : Integer.Sparse Key := [(key311, -2), (key311, 1), (key309, 1), (key338, 2), (key338, -1), (key323, -1), (key345, -1), (key344, -1), (key345, 1), (key334, 1), (key245, 2), (key245, -1), (key243, -1), (key424, -2), (key424, 1), (key413, 1), (key588, 1), (key587, 1), (key588, -1), (key581, -1), (key266, -2), (key266, 1), (key255, 1), (key334, 2), (key334, -1), (key323, -1), (key611, -1), (key605, -1), (key611, 1), (key599, 1), (key276, 1), (key275, 1), (key276, -1), (key270, -1), (key345, -1), (key344, -1), (key345, 1), (key338, 1), (key485, 1), (key479, 1), (key485, -1), (key473, -1)]

def rawRow392 : Integer.Sparse Key := [(key334, -2), (key323, 1), (key334, 1), (key344, 2), (key309, -1), (key344, -1), (key338, -1), (key345, -1), (key311, 1), (key345, 1), (key424, 2), (key413, -1), (key424, -1), (key587, -2), (key243, 1), (key587, 1), (key424, 1), (key588, 1), (key245, -1), (key588, -1), (key599, -2), (key323, 1), (key599, 1), (key605, 2), (key255, -1), (key605, -1), (key334, -1), (key611, -1), (key266, 1), (key611, 1), (key473, 1), (key613, 1), (key338, -1), (key613, -1), (key479, -1), (key614, -1), (key270, 1), (key614, 1), (key344, 1), (key616, 1), (key275, -1), (key616, -1)]

def rawRow393 : Integer.Sparse Key := [(key334, -2), (key334, 1), (key323, 1), (key344, 2), (key344, -1), (key309, -1), (key345, -1), (key338, -1), (key345, 1), (key311, 1), (key424, 2), (key424, -1), (key413, -1), (key587, -2), (key587, 1), (key243, 1), (key588, 1), (key424, 1), (key588, -1), (key245, -1), (key599, -2), (key599, 1), (key323, 1), (key605, 2), (key605, -1), (key255, -1), (key611, -1), (key334, -1), (key611, 1), (key266, 1), (key613, 1), (key473, 1), (key613, -1), (key338, -1), (key614, -1), (key479, -1), (key614, 1), (key270, 1), (key616, 1), (key344, 1), (key616, -1), (key275, -1)]

def rawRow394 : Integer.Sparse Key := [(key338, -2), (key344, 1), (key345, 1), (key311, 2), (key334, -1), (key345, -1), (key309, -1), (key311, -1), (key323, 1), (key338, 1), (key581, 2), (key587, -1), (key588, -1), (key245, -2), (key424, 1), (key588, 1), (key243, 1), (key245, 1), (key413, -1), (key424, -1), (key334, -2), (key605, 1), (key611, 1), (key266, 2), (key599, -1), (key611, -1), (key255, -1), (key266, -1), (key323, 1), (key334, 1), (key344, 1), (key345, 1), (key479, -1), (key485, -1), (key275, -1), (key276, -1), (key473, 1), (key485, 1), (key270, 1), (key276, 1), (key338, -1), (key345, -1)]

def rawRow395 : Integer.Sparse Key := [(key338, -2), (key345, 1), (key344, 1), (key311, 2), (key345, -1), (key334, -1), (key311, -1), (key309, -1), (key338, 1), (key323, 1), (key581, 2), (key588, -1), (key587, -1), (key245, -2), (key588, 1), (key424, 1), (key245, 1), (key243, 1), (key424, -1), (key413, -1), (key334, -2), (key611, 1), (key605, 1), (key266, 2), (key611, -1), (key599, -1), (key266, -1), (key255, -1), (key334, 1), (key323, 1), (key345, 1), (key344, 1), (key485, -1), (key479, -1), (key276, -1), (key275, -1), (key485, 1), (key473, 1), (key276, 1), (key270, 1), (key345, -1), (key338, -1)]

def rawRow396 : Integer.Sparse Key := [(key344, -2), (key338, 1), (key345, 1), (key334, 2), (key311, -1), (key345, -1), (key323, -1), (key334, -1), (key309, 1), (key344, 1), (key587, 2), (key581, -1), (key588, -1), (key424, -2), (key245, 1), (key588, 1), (key413, 1), (key424, 1), (key243, -1), (key587, -1), (key605, -2), (key334, 1), (key611, 1), (key599, 2), (key266, -1), (key611, -1), (key323, -1), (key599, -1), (key255, 1), (key605, 1), (key479, 1), (key614, 1), (key344, -1), (key616, -1), (key473, -1), (key613, -1), (key275, 1), (key616, 1), (key338, 1), (key613, 1), (key270, -1), (key614, -1)]

def rawRow397 : Integer.Sparse Key := [(key344, -2), (key345, 1), (key338, 1), (key334, 2), (key345, -1), (key311, -1), (key334, -1), (key323, -1), (key344, 1), (key309, 1), (key587, 2), (key588, -1), (key581, -1), (key424, -2), (key588, 1), (key245, 1), (key424, 1), (key413, 1), (key587, -1), (key243, -1), (key605, -2), (key611, 1), (key334, 1), (key599, 2), (key611, -1), (key266, -1), (key599, -1), (key323, -1), (key605, 1), (key255, 1), (key614, 1), (key479, 1), (key616, -1), (key344, -1), (key613, -1), (key473, -1), (key616, 1), (key275, 1), (key613, 1), (key338, 1), (key614, -1), (key270, -1)]

def rawRow399 : Integer.Sparse Key := [(key403, -2), (key392, 1), (key403, 1), (key473, 2), (key413, -1), (key473, -1), (key479, -1), (key485, -1), (key424, 1), (key485, 1), (key266, 2), (key255, -1), (key266, -1), (key599, -2), (key323, 1), (key599, 1), (key605, 1), (key611, 1), (key334, -1), (key611, -1), (key275, -2), (key243, 1), (key275, 1), (key344, 2), (key309, -1), (key344, -1), (key587, -1), (key616, -1), (key576, 1), (key616, 1), (key266, 1), (key276, 1), (key245, -1), (key276, -1), (key334, -1), (key345, -1), (key311, 1), (key345, 1), (key424, 1), (key485, 1), (key403, -1), (key485, -1)]

def rawRow400 : Integer.Sparse Key := [(key403, -2), (key403, 1), (key392, 1), (key473, 2), (key473, -1), (key413, -1), (key485, -1), (key479, -1), (key485, 1), (key424, 1), (key266, 2), (key266, -1), (key255, -1), (key599, -2), (key599, 1), (key323, 1), (key611, 1), (key605, 1), (key611, -1), (key334, -1), (key275, -2), (key275, 1), (key243, 1), (key344, 2), (key344, -1), (key309, -1), (key616, -1), (key587, -1), (key616, 1), (key576, 1), (key276, 1), (key266, 1), (key276, -1), (key245, -1), (key345, -1), (key334, -1), (key345, 1), (key311, 1), (key485, 1), (key424, 1), (key485, -1), (key403, -1)]

def rawRow402 : Integer.Sparse Key := [(key424, -2), (key413, 1), (key424, 1), (key479, 2), (key392, -1), (key479, -1), (key473, -1), (key485, -1), (key403, 1), (key485, 1), (key334, 2), (key323, -1), (key334, -1), (key605, -2), (key255, 1), (key605, 1), (key599, 1), (key611, 1), (key266, -1), (key611, -1), (key344, -2), (key309, 1), (key344, 1), (key587, 2), (key243, -1), (key587, -1), (key344, -1), (key616, -1), (key275, 1), (key616, 1), (key403, 1), (key577, 1), (key311, -1), (key577, -1), (key424, -1), (key588, -1), (key245, 1), (key588, 1), (key334, 1), (key611, 1), (key266, -1), (key611, -1)]

def rawRow403 : Integer.Sparse Key := [(key424, -2), (key424, 1), (key413, 1), (key479, 2), (key479, -1), (key392, -1), (key485, -1), (key473, -1), (key485, 1), (key403, 1), (key334, 2), (key334, -1), (key323, -1), (key605, -2), (key605, 1), (key255, 1), (key611, 1), (key599, 1), (key611, -1), (key266, -1), (key344, -2), (key344, 1), (key309, 1), (key587, 2), (key587, -1), (key243, -1), (key616, -1), (key344, -1), (key616, 1), (key275, 1), (key577, 1), (key403, 1), (key577, -1), (key311, -1), (key588, -1), (key424, -1), (key588, 1), (key245, 1), (key611, 1), (key334, 1), (key611, -1), (key266, -1)]

def rawRow404 : Integer.Sparse Key := [(key473, -2), (key479, 1), (key485, 1), (key403, 2), (key424, -1), (key485, -1), (key392, -1), (key403, -1), (key413, 1), (key473, 1), (key599, 2), (key605, -1), (key611, -1), (key266, -2), (key334, 1), (key611, 1), (key255, 1), (key266, 1), (key323, -1), (key599, -1), (key576, -2), (key587, 1), (key616, 1), (key275, 2), (key344, -1), (key616, -1), (key243, -1), (key275, -1), (key309, 1), (key344, 1), (key334, 1), (key345, 1), (key424, -1), (key485, -1), (key266, -1), (key276, -1), (key403, 1), (key485, 1), (key245, 1), (key276, 1), (key311, -1), (key345, -1)]

def rawRow405 : Integer.Sparse Key := [(key473, -2), (key485, 1), (key479, 1), (key403, 2), (key485, -1), (key424, -1), (key403, -1), (key392, -1), (key473, 1), (key413, 1), (key599, 2), (key611, -1), (key605, -1), (key266, -2), (key611, 1), (key334, 1), (key266, 1), (key255, 1), (key599, -1), (key323, -1), (key576, -2), (key616, 1), (key587, 1), (key275, 2), (key616, -1), (key344, -1), (key275, -1), (key243, -1), (key344, 1), (key309, 1), (key345, 1), (key334, 1), (key485, -1), (key424, -1), (key276, -1), (key266, -1), (key485, 1), (key403, 1), (key276, 1), (key245, 1), (key345, -1), (key311, -1)]

def rawRow406 : Integer.Sparse Key := [(key479, -2), (key473, 1), (key485, 1), (key424, 2), (key403, -1), (key485, -1), (key413, -1), (key424, -1), (key392, 1), (key479, 1), (key605, 2), (key599, -1), (key611, -1), (key334, -2), (key266, 1), (key611, 1), (key323, 1), (key334, 1), (key255, -1), (key605, -1), (key587, -2), (key576, 1), (key616, 1), (key344, 2), (key275, -1), (key616, -1), (key309, -1), (key344, -1), (key243, 1), (key587, 1), (key424, 1), (key588, 1), (key334, -1), (key611, -1), (key403, -1), (key577, -1), (key266, 1), (key611, 1), (key311, 1), (key577, 1), (key245, -1), (key588, -1)]

def rawRow407 : Integer.Sparse Key := [(key479, -2), (key485, 1), (key473, 1), (key424, 2), (key485, -1), (key403, -1), (key424, -1), (key413, -1), (key479, 1), (key392, 1), (key605, 2), (key611, -1), (key599, -1), (key334, -2), (key611, 1), (key266, 1), (key334, 1), (key323, 1), (key605, -1), (key255, -1), (key587, -2), (key616, 1), (key576, 1), (key344, 2), (key616, -1), (key275, -1), (key344, -1), (key309, -1), (key587, 1), (key243, 1), (key588, 1), (key424, 1), (key611, -1), (key334, -1), (key577, -1), (key403, -1), (key611, 1), (key266, 1), (key577, 1), (key311, 1), (key588, -1), (key245, -1)]

def rawRow408 : Integer.Sparse Key := [(key571, -2), (key576, 1), (key577, 1), (key581, 2), (key599, -1), (key613, -1), (key587, -1), (key588, -1), (key605, 1), (key614, 1), (key270, 2), (key275, -1), (key276, -1), (key338, -2), (key473, 1), (key613, 1), (key344, 1), (key345, 1), (key479, -1), (key614, -1), (key245, -2), (key266, 1), (key276, 1), (key311, 2), (key403, -1), (key577, -1), (key334, -1), (key345, -1), (key424, 1), (key588, 1), (key243, 1), (key245, 1), (key255, -1), (key266, -1), (key309, -1), (key311, -1), (key323, 1), (key334, 1), (key392, 1), (key403, 1), (key413, -1), (key424, -1)]

def rawRow409 : Integer.Sparse Key := [(key571, -2), (key577, 1), (key576, 1), (key581, 2), (key613, -1), (key599, -1), (key588, -1), (key587, -1), (key614, 1), (key605, 1), (key270, 2), (key276, -1), (key275, -1), (key338, -2), (key613, 1), (key473, 1), (key345, 1), (key344, 1), (key614, -1), (key479, -1), (key245, -2), (key276, 1), (key266, 1), (key311, 2), (key577, -1), (key403, -1), (key345, -1), (key334, -1), (key588, 1), (key424, 1), (key245, 1), (key243, 1), (key266, -1), (key255, -1), (key311, -1), (key309, -1), (key334, 1), (key323, 1), (key403, 1), (key392, 1), (key424, -1), (key413, -1)]

def rawRow410 : Integer.Sparse Key := [(key576, -2), (key571, 1), (key577, 1), (key599, 2), (key581, -1), (key613, -1), (key605, -1), (key611, -1), (key587, 1), (key616, 1), (key275, 2), (key270, -1), (key276, -1), (key473, -2), (key338, 1), (key613, 1), (key479, 1), (key485, 1), (key344, -1), (key616, -1), (key266, -2), (key245, 1), (key276, 1), (key403, 2), (key311, -1), (key577, -1), (key424, -1), (key485, -1), (key334, 1), (key611, 1), (key255, 1), (key266, 1), (key243, -1), (key275, -1), (key323, -1), (key338, -1), (key309, 1), (key344, 1), (key413, 1), (key473, 1), (key392, -1), (key479, -1)]

def rawRow411 : Integer.Sparse Key := [(key576, -2), (key577, 1), (key571, 1), (key599, 2), (key613, -1), (key581, -1), (key611, -1), (key605, -1), (key616, 1), (key587, 1), (key275, 2), (key276, -1), (key270, -1), (key473, -2), (key613, 1), (key338, 1), (key485, 1), (key479, 1), (key616, -1), (key344, -1), (key266, -2), (key276, 1), (key245, 1), (key403, 2), (key577, -1), (key311, -1), (key485, -1), (key424, -1), (key611, 1), (key334, 1), (key266, 1), (key255, 1), (key275, -1), (key243, -1), (key338, -1), (key323, -1), (key344, 1), (key309, 1), (key473, 1), (key413, 1), (key479, -1), (key392, -1)]

def rawRow412 : Integer.Sparse Key := [(key581, -2), (key587, 1), (key588, 1), (key571, 2), (key605, -1), (key614, -1), (key576, -1), (key577, -1), (key599, 1), (key613, 1), (key338, 2), (key344, -1), (key345, -1), (key270, -2), (key479, 1), (key614, 1), (key275, 1), (key276, 1), (key473, -1), (key613, -1), (key311, -2), (key334, 1), (key345, 1), (key245, 2), (key424, -1), (key588, -1), (key266, -1), (key276, -1), (key403, 1), (key577, 1), (key309, 1), (key311, 1), (key323, -1), (key338, -1), (key243, -1), (key245, -1), (key413, 1), (key424, 1), (key255, 1), (key266, 1), (key323, -1), (key334, -1)]

def rawRow413 : Integer.Sparse Key := [(key581, -2), (key588, 1), (key587, 1), (key571, 2), (key614, -1), (key605, -1), (key577, -1), (key576, -1), (key613, 1), (key599, 1), (key338, 2), (key345, -1), (key344, -1), (key270, -2), (key614, 1), (key479, 1), (key276, 1), (key275, 1), (key613, -1), (key473, -1), (key311, -2), (key345, 1), (key334, 1), (key245, 2), (key588, -1), (key424, -1), (key276, -1), (key266, -1), (key577, 1), (key403, 1), (key311, 1), (key309, 1), (key338, -1), (key323, -1), (key245, -1), (key243, -1), (key424, 1), (key413, 1), (key266, 1), (key255, 1), (key334, -1), (key323, -1)]

def rawRow414 : Integer.Sparse Key := [(key587, -2), (key581, 1), (key588, 1), (key605, 2), (key571, -1), (key614, -1), (key599, -1), (key611, -1), (key576, 1), (key616, 1), (key344, 2), (key338, -1), (key345, -1), (key479, -2), (key270, 1), (key614, 1), (key473, 1), (key485, 1), (key275, -1), (key616, -1), (key334, -2), (key311, 1), (key345, 1), (key424, 2), (key245, -1), (key588, -1), (key403, -1), (key485, -1), (key266, 1), (key611, 1), (key323, 1), (key334, 1), (key309, -1), (key344, -1), (key413, -1), (key424, -1), (key243, 1), (key587, 1), (key323, 1), (key599, 1), (key255, -1), (key605, -1)]

def rawRow415 : Integer.Sparse Key := [(key587, -2), (key588, 1), (key581, 1), (key605, 2), (key614, -1), (key571, -1), (key611, -1), (key599, -1), (key616, 1), (key576, 1), (key344, 2), (key345, -1), (key338, -1), (key479, -2), (key614, 1), (key270, 1), (key485, 1), (key473, 1), (key616, -1), (key275, -1), (key334, -2), (key345, 1), (key311, 1), (key424, 2), (key588, -1), (key245, -1), (key485, -1), (key403, -1), (key611, 1), (key266, 1), (key334, 1), (key323, 1), (key344, -1), (key309, -1), (key424, -1), (key413, -1), (key587, 1), (key243, 1), (key599, 1), (key323, 1), (key605, -1), (key255, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8857 : Integer.Sparse Key := [(key724, -24), (key942, 6), (key942, 6), (key942, 6), (key946, 6)]

end MUB6.Certificate.GramRows

end OAI
end


