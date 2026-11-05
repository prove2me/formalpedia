-- Prove2me | Definitions.Def_OAIQ106E052
-- name    : OAIQ106E052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:05:11.609307+00:00
-- url     : https://prove2.me/theorems/62fedf7a-bbf4-438f-a5d4-19962d288269
-- title:
--   Definitions bundle OAIQ106E052 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1561 declarations of OpenAI's Lean: 1561 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow3705`, `OAI.MUB6.Certificate.GramRows.rawRow3706`, `OAI.MUB6.Certificate.GramRows.rawRow3707`, `OAI.MUB6.Certificate.GramRows.rawRow3708`, `OAI.MUB6.Certificate.GramRows.rawRow3709`, `OAI.MUB6.Certificate.GramRows.rawRow371`, `OAI.MUB6.Certificate.GramRows.rawRow3710`, `OAI.MUB6.Certificate.GramRows.rawRow3711`, `OAI.MUB6.Certificate.GramRows.rawRow3712`, `OAI.MUB6.Certificate.GramRows.rawRow3713`, `OAI.MUB6.Certificate.GramRows.rawRow3714`, `OAI.MUB6.Certificate.GramRows.rawRow3715`, `OAI.MUB6.Certificate.GramRows.rawRow3716`, `OAI.MUB6.Certificate.GramRows.rawRow3717`, `OAI.MUB6.Certificate.GramRows.rawRow3718`, `OAI.MUB6.Certificate.GramRows.rawRow3719`, `OAI.MUB6.Certificate.GramRows.rawRow372`, `OAI.MUB6.Certificate.GramRows.rawRow3720`, `OAI.MUB6.Certificate.GramRows.rawRow3721`, `OAI.MUB6.Certificate.GramRows.rawRow3722`, `OAI.MUB6.Certificate.GramRows.rawRow3723`, `OAI.MUB6.Certificate.GramRows.rawRow3724`, `OAI.MUB6.Certificate.GramRows.rawRow3725`, `OAI.MUB6.Certificate.GramRows.rawRow3726`, `OAI.MUB6.Certificate.GramRows.rawRow3727`, `OAI.MUB6.Certificate.GramRows.rawRow3728`, `OAI.MUB6.Certificate.GramRows.rawRow3729`, `OAI.MUB6.Certificate.GramRows.rawRow373`, `OAI.MUB6.Certificate.GramRows.rawRow3730`, `OAI.MUB6.Certificate.GramRows.rawRow3731`, `OAI.MUB6.Certificate.GramRows.rawRow3732`, `OAI.MUB6.Certificate.GramRows.rawRow3733`, `OAI.MUB6.Certificate.GramRows.rawRow3735`, `OAI.MUB6.Certificate.GramRows.rawRow3736`, `OAI.MUB6.Certificate.GramRows.rawRow3737`, `OAI.MUB6.Certificate.GramRows.rawRow3738`, `OAI.MUB6.Certificate.GramRows.rawRow3739`, `OAI.MUB6.Certificate.GramRows.rawRow374`, `OAI.MUB6.Certificate.GramRows.rawRow3740`, `OAI.MUB6.Certificate.GramRows.rawRow3741` and 1521 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block10`, `MutuallyUnbiased_GramRows_Block11`, `MutuallyUnbiased_GramRows_Block12`, `MutuallyUnbiased_GramRows_Block52`, `MutuallyUnbiased_GramRows_Block53`, `MutuallyUnbiased_GramRows_Block54`, `MutuallyUnbiased_GramRows_Block55`, `MutuallyUnbiased_GramRows_Block56`, `MutuallyUnbiased_GramRows_Block57`, `MutuallyUnbiased_GramRows_Block58`, `MutuallyUnbiased_GramRows_Block59`, `MutuallyUnbiased_GramRows_Block60`, `MutuallyUnbiased_GramRows_Block61`, `MutuallyUnbiased_GramRows_Block62`, `MutuallyUnbiased_GramRows_Block63`, `MutuallyUnbiased_GramRows_Block8`, `MutuallyUnbiased_GramRows_Block9`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block0.polynomial_interpretation_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval3_3_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval4_2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval19_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_19_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E000
import Definitions.Def_OAIQ106E002

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

def rawRow5 : Integer.Sparse Key := [(key251, -1), (key260, -1), (key248, 2), (key267, 1), (key271, 1), (key236, -1), (key248, -1), (key260, -2), (key239, 1), (key251, 1), (key319, 1), (key335, 1), (key316, -2), (key328, -1), (key340, -1), (key302, 1), (key316, 1), (key328, 2), (key305, -1), (key319, -1), (key442, -1), (key469, -1), (key406, 1), (key435, 1), (key450, 1), (key475, 1), (key385, -1), (key435, -1), (key418, -1), (key450, -1), (key397, 1), (key442, 1), (key595, 2), (key578, -1), (key593, -1), (key601, -2), (key568, 1), (key593, 1), (key583, 1), (key601, 1), (key572, -1), (key595, -1)]

def rawRow38 : Integer.Sparse Key := [(key593, -1), (key595, -1), (key601, 2), (key568, 1), (key572, 1), (key583, -1), (key601, -1), (key568, -2), (key578, 1), (key593, 1), (key467, 1), (key469, 1), (key475, -2), (key267, -1), (key271, -1), (key340, 1), (key475, 1), (key267, 2), (key335, -1), (key467, -1), (key388, -1), (key397, -1), (key418, 1), (key450, 1), (key251, 1), (key260, 1), (key328, -1), (key450, -1), (key239, -1), (key251, -1), (key305, 1), (key388, 1), (key385, 2), (key406, -1), (key435, -1), (key248, -2), (key316, 1), (key435, 1), (key236, 1), (key248, 1), (key302, -1), (key316, -1)]

def rawRow39 : Integer.Sparse Key := [(key595, -1), (key593, -1), (key601, 2), (key572, 1), (key568, 1), (key601, -1), (key583, -1), (key568, -2), (key593, 1), (key578, 1), (key469, 1), (key467, 1), (key475, -2), (key271, -1), (key267, -1), (key475, 1), (key340, 1), (key267, 2), (key467, -1), (key335, -1), (key397, -1), (key388, -1), (key450, 1), (key418, 1), (key260, 1), (key251, 1), (key450, -1), (key328, -1), (key251, -1), (key239, -1), (key388, 1), (key305, 1), (key385, 2), (key435, -1), (key406, -1), (key248, -2), (key435, 1), (key316, 1), (key248, 1), (key236, 1), (key316, -1), (key302, -1)]

def rawRow40 : Integer.Sparse Key := [(key593, -1), (key601, -1), (key595, 2), (key578, 1), (key583, 1), (key572, -1), (key595, -1), (key578, -2), (key568, 1), (key593, 1), (key467, 1), (key475, 1), (key469, -2), (key335, -1), (key340, -1), (key271, 1), (key469, 1), (key335, 2), (key267, -1), (key467, -1), (key409, -1), (key418, -1), (key397, 1), (key442, 1), (key319, 1), (key328, 1), (key260, -1), (key442, -1), (key305, -1), (key319, -1), (key239, 1), (key409, 1), (key406, 2), (key385, -1), (key435, -1), (key316, -2), (key248, 1), (key435, 1), (key302, 1), (key316, 1), (key236, -1), (key406, -1)]

def rawRow41 : Integer.Sparse Key := [(key601, -1), (key593, -1), (key595, 2), (key583, 1), (key578, 1), (key595, -1), (key572, -1), (key578, -2), (key593, 1), (key568, 1), (key475, 1), (key467, 1), (key469, -2), (key340, -1), (key335, -1), (key469, 1), (key271, 1), (key335, 2), (key467, -1), (key267, -1), (key418, -1), (key409, -1), (key442, 1), (key397, 1), (key328, 1), (key319, 1), (key442, -1), (key260, -1), (key319, -1), (key305, -1), (key409, 1), (key239, 1), (key406, 2), (key435, -1), (key385, -1), (key316, -2), (key435, 1), (key248, 1), (key316, 1), (key302, 1), (key406, -1), (key236, -1)]

def rawRow42 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1302, 2), (key1316, 1), (key1316, 1), (key1339, -1), (key1339, -1), (key1329, -2), (key1345, 1), (key1345, 1), (key1391, 1), (key1391, 1), (key1397, -2), (key1546, -1), (key1546, -1), (key1774, 1), (key1774, 1), (key1559, 2), (key1780, -1), (key1780, -1), (key1424, -1), (key1424, -1), (key1457, 1), (key1457, 1), (key1573, 1), (key1573, 1), (key1790, -1), (key1790, -1), (key1659, -1), (key1659, -1), (key1817, 1), (key1817, 1), (key1447, 2), (key1466, -1), (key1466, -1), (key1596, -2), (key1798, 1), (key1798, 1), (key1667, 1), (key1667, 1), (key1825, -1), (key1825, -1)]

def rawRow43 : Integer.Sparse Key := [(key1296, -1), (key1302, -1), (key1296, 2), (key1337, 1), (key1339, 1), (key1316, -1), (key1337, -1), (key1345, -2), (key1329, 1), (key1345, 1), (key1391, 1), (key1397, 1), (key1391, -2), (key1772, -1), (key1774, -1), (key1546, 1), (key1772, 1), (key1780, 2), (key1559, -1), (key1780, -1), (key1455, -1), (key1457, -1), (key1424, 1), (key1455, 1), (key1788, 1), (key1790, 1), (key1573, -1), (key1788, -1), (key1817, -1), (key1841, -1), (key1659, 1), (key1841, 1), (key1466, 2), (key1447, -1), (key1466, -1), (key1798, -2), (key1596, 1), (key1798, 1), (key1825, 1), (key1844, 1), (key1667, -1), (key1844, -1)]

def rawRow44 : Integer.Sparse Key := [(key1302, -1), (key1296, -1), (key1296, 2), (key1339, 1), (key1337, 1), (key1337, -1), (key1316, -1), (key1345, -2), (key1345, 1), (key1329, 1), (key1397, 1), (key1391, 1), (key1391, -2), (key1774, -1), (key1772, -1), (key1772, 1), (key1546, 1), (key1780, 2), (key1780, -1), (key1559, -1), (key1457, -1), (key1455, -1), (key1455, 1), (key1424, 1), (key1790, 1), (key1788, 1), (key1788, -1), (key1573, -1), (key1841, -1), (key1817, -1), (key1841, 1), (key1659, 1), (key1466, 2), (key1466, -1), (key1447, -1), (key1798, -2), (key1798, 1), (key1596, 1), (key1844, 1), (key1825, 1), (key1844, -1), (key1667, -1)]

def rawRow45 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1329, 2), (key1296, 1), (key1296, 1), (key1345, -1), (key1345, -1), (key1302, -2), (key1339, 1), (key1339, 1), (key1546, 1), (key1546, 1), (key1559, -2), (key1391, -1), (key1391, -1), (key1780, 1), (key1780, 1), (key1397, 2), (key1774, -1), (key1774, -1), (key1573, -1), (key1573, -1), (key1659, 1), (key1659, 1), (key1424, 1), (key1424, 1), (key1817, -1), (key1817, -1), (key1457, -1), (key1457, -1), (key1790, 1), (key1790, 1), (key1596, 2), (key1667, -1), (key1667, -1), (key1447, -2), (key1825, 1), (key1825, 1), (key1466, 1), (key1466, 1), (key1798, -1), (key1798, -1)]

def rawRow46 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1316, 2), (key1337, 1), (key1345, 1), (key1296, -1), (key1337, -1), (key1339, -2), (key1302, 1), (key1339, 1), (key1546, 1), (key1559, 1), (key1546, -2), (key1772, -1), (key1780, -1), (key1391, 1), (key1772, 1), (key1774, 2), (key1397, -1), (key1774, -1), (key1655, -1), (key1659, -1), (key1573, 1), (key1655, 1), (key1813, 1), (key1817, 1), (key1424, -1), (key1813, -1), (key1790, -1), (key1839, -1), (key1457, 1), (key1839, 1), (key1667, 2), (key1596, -1), (key1667, -1), (key1825, -2), (key1447, 1), (key1825, 1), (key1798, 1), (key1844, 1), (key1466, -1), (key1844, -1)]

def rawRow47 : Integer.Sparse Key := [(key1329, -1), (key1316, -1), (key1316, 2), (key1345, 1), (key1337, 1), (key1337, -1), (key1296, -1), (key1339, -2), (key1339, 1), (key1302, 1), (key1559, 1), (key1546, 1), (key1546, -2), (key1780, -1), (key1772, -1), (key1772, 1), (key1391, 1), (key1774, 2), (key1774, -1), (key1397, -1), (key1659, -1), (key1655, -1), (key1655, 1), (key1573, 1), (key1817, 1), (key1813, 1), (key1813, -1), (key1424, -1), (key1839, -1), (key1790, -1), (key1839, 1), (key1457, 1), (key1667, 2), (key1667, -1), (key1596, -1), (key1825, -2), (key1825, 1), (key1447, 1), (key1844, 1), (key1798, 1), (key1844, -1), (key1466, -1)]

def rawRow48 : Integer.Sparse Key := [(key1337, -1), (key1339, -1), (key1345, 2), (key1296, 1), (key1302, 1), (key1329, -1), (key1345, -1), (key1296, -2), (key1316, 1), (key1337, 1), (key1772, 1), (key1774, 1), (key1780, -2), (key1391, -1), (key1397, -1), (key1559, 1), (key1780, 1), (key1391, 2), (key1546, -1), (key1772, -1), (key1788, -1), (key1790, -1), (key1817, 1), (key1841, 1), (key1455, 1), (key1457, 1), (key1659, -1), (key1841, -1), (key1424, -1), (key1455, -1), (key1573, 1), (key1788, 1), (key1798, 2), (key1825, -1), (key1844, -1), (key1466, -2), (key1667, 1), (key1844, 1), (key1447, 1), (key1466, 1), (key1596, -1), (key1798, -1)]

def rawRow49 : Integer.Sparse Key := [(key1339, -1), (key1337, -1), (key1345, 2), (key1302, 1), (key1296, 1), (key1345, -1), (key1329, -1), (key1296, -2), (key1337, 1), (key1316, 1), (key1774, 1), (key1772, 1), (key1780, -2), (key1397, -1), (key1391, -1), (key1780, 1), (key1559, 1), (key1391, 2), (key1772, -1), (key1546, -1), (key1790, -1), (key1788, -1), (key1841, 1), (key1817, 1), (key1457, 1), (key1455, 1), (key1841, -1), (key1659, -1), (key1455, -1), (key1424, -1), (key1788, 1), (key1573, 1), (key1798, 2), (key1844, -1), (key1825, -1), (key1466, -2), (key1844, 1), (key1667, 1), (key1466, 1), (key1447, 1), (key1798, -1), (key1596, -1)]

def rawRow50 : Integer.Sparse Key := [(key1337, -1), (key1345, -1), (key1339, 2), (key1316, 1), (key1329, 1), (key1302, -1), (key1339, -1), (key1316, -2), (key1296, 1), (key1337, 1), (key1772, 1), (key1780, 1), (key1774, -2), (key1546, -1), (key1559, -1), (key1397, 1), (key1774, 1), (key1546, 2), (key1391, -1), (key1772, -1), (key1813, -1), (key1817, -1), (key1790, 1), (key1839, 1), (key1655, 1), (key1659, 1), (key1457, -1), (key1839, -1), (key1573, -1), (key1655, -1), (key1424, 1), (key1813, 1), (key1825, 2), (key1798, -1), (key1844, -1), (key1667, -2), (key1466, 1), (key1844, 1), (key1596, 1), (key1667, 1), (key1447, -1), (key1825, -1)]

def rawRow51 : Integer.Sparse Key := [(key1345, -1), (key1337, -1), (key1339, 2), (key1329, 1), (key1316, 1), (key1339, -1), (key1302, -1), (key1316, -2), (key1337, 1), (key1296, 1), (key1780, 1), (key1772, 1), (key1774, -2), (key1559, -1), (key1546, -1), (key1774, 1), (key1397, 1), (key1546, 2), (key1772, -1), (key1391, -1), (key1817, -1), (key1813, -1), (key1839, 1), (key1790, 1), (key1659, 1), (key1655, 1), (key1839, -1), (key1457, -1), (key1655, -1), (key1573, -1), (key1813, 1), (key1424, 1), (key1825, 2), (key1844, -1), (key1798, -1), (key1667, -2), (key1844, 1), (key1466, 1), (key1667, 1), (key1596, 1), (key1825, -1), (key1447, -1)]

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

def rawRow422 : Integer.Sparse Key := [(key1295, -1), (key1295, -1), (key1291, 2), (key1336, 1), (key1336, 1), (key1311, -1), (key1311, -1), (key1343, -2), (key1324, 1), (key1324, 1), (key1390, 1), (key1390, 1), (key1386, -2), (key1771, -1), (key1771, -1), (key1541, 1), (key1541, 1), (key1778, 2), (key1554, -1), (key1554, -1), (key1454, -1), (key1454, -1), (key1419, 1), (key1419, 1), (key1787, 1), (key1787, 1), (key1568, -1), (key1568, -1), (key1815, -1), (key1815, -1), (key1657, 1), (key1657, 1), (key1464, 2), (key1442, -1), (key1442, -1), (key1796, -2), (key1591, 1), (key1591, 1), (key1823, 1), (key1823, 1), (key1665, -1), (key1665, -1)]

def rawRow423 : Integer.Sparse Key := [(key1311, -1), (key1315, -1), (key1324, 2), (key1291, 1), (key1295, 1), (key1324, -1), (key1343, -1), (key1295, -2), (key1315, 1), (key1336, 1), (key1541, 1), (key1545, 1), (key1554, -2), (key1386, -1), (key1390, -1), (key1554, 1), (key1778, 1), (key1390, 2), (key1545, -1), (key1771, -1), (key1568, -1), (key1572, -1), (key1622, 1), (key1657, 1), (key1419, 1), (key1423, 1), (key1622, -1), (key1815, -1), (key1423, -1), (key1454, -1), (key1572, 1), (key1787, 1), (key1591, 2), (key1631, -1), (key1665, -1), (key1442, -2), (key1631, 1), (key1823, 1), (key1442, 1), (key1464, 1), (key1591, -1), (key1796, -1)]

def rawRow424 : Integer.Sparse Key := [(key1315, -1), (key1311, -1), (key1324, 2), (key1295, 1), (key1291, 1), (key1343, -1), (key1324, -1), (key1295, -2), (key1336, 1), (key1315, 1), (key1545, 1), (key1541, 1), (key1554, -2), (key1390, -1), (key1386, -1), (key1778, 1), (key1554, 1), (key1390, 2), (key1771, -1), (key1545, -1), (key1572, -1), (key1568, -1), (key1657, 1), (key1622, 1), (key1423, 1), (key1419, 1), (key1815, -1), (key1622, -1), (key1454, -1), (key1423, -1), (key1787, 1), (key1572, 1), (key1591, 2), (key1665, -1), (key1631, -1), (key1442, -2), (key1823, 1), (key1631, 1), (key1464, 1), (key1442, 1), (key1796, -1), (key1591, -1)]

def rawRow425 : Integer.Sparse Key := [(key1315, -1), (key1324, -1), (key1311, 2), (key1336, 1), (key1343, 1), (key1291, -1), (key1311, -1), (key1336, -2), (key1295, 1), (key1315, 1), (key1545, 1), (key1554, 1), (key1541, -2), (key1771, -1), (key1778, -1), (key1386, 1), (key1541, 1), (key1771, 2), (key1390, -1), (key1545, -1), (key1654, -1), (key1657, -1), (key1568, 1), (key1617, 1), (key1812, 1), (key1815, 1), (key1419, -1), (key1617, -1), (key1787, -1), (key1812, -1), (key1454, 1), (key1654, 1), (key1665, 2), (key1591, -1), (key1631, -1), (key1823, -2), (key1442, 1), (key1631, 1), (key1796, 1), (key1823, 1), (key1464, -1), (key1665, -1)]

def rawRow426 : Integer.Sparse Key := [(key1324, -1), (key1315, -1), (key1311, 2), (key1343, 1), (key1336, 1), (key1311, -1), (key1291, -1), (key1336, -2), (key1315, 1), (key1295, 1), (key1554, 1), (key1545, 1), (key1541, -2), (key1778, -1), (key1771, -1), (key1541, 1), (key1386, 1), (key1771, 2), (key1545, -1), (key1390, -1), (key1657, -1), (key1654, -1), (key1617, 1), (key1568, 1), (key1815, 1), (key1812, 1), (key1617, -1), (key1419, -1), (key1812, -1), (key1787, -1), (key1654, 1), (key1454, 1), (key1665, 2), (key1631, -1), (key1591, -1), (key1823, -2), (key1631, 1), (key1442, 1), (key1823, 1), (key1796, 1), (key1665, -1), (key1464, -1)]

def rawRow427 : Integer.Sparse Key := [(key1336, -1), (key1336, -1), (key1343, 2), (key1295, 1), (key1295, 1), (key1324, -1), (key1324, -1), (key1291, -2), (key1311, 1), (key1311, 1), (key1771, 1), (key1771, 1), (key1778, -2), (key1390, -1), (key1390, -1), (key1554, 1), (key1554, 1), (key1386, 2), (key1541, -1), (key1541, -1), (key1787, -1), (key1787, -1), (key1815, 1), (key1815, 1), (key1454, 1), (key1454, 1), (key1657, -1), (key1657, -1), (key1419, -1), (key1419, -1), (key1568, 1), (key1568, 1), (key1796, 2), (key1823, -1), (key1823, -1), (key1464, -2), (key1665, 1), (key1665, 1), (key1442, 1), (key1442, 1), (key1591, -1), (key1591, -1)]

def rawRow428 : Integer.Sparse Key := [(key1336, -1), (key1343, -1), (key1336, 2), (key1315, 1), (key1324, 1), (key1295, -1), (key1315, -1), (key1311, -2), (key1291, 1), (key1311, 1), (key1771, 1), (key1778, 1), (key1771, -2), (key1545, -1), (key1554, -1), (key1390, 1), (key1545, 1), (key1541, 2), (key1386, -1), (key1541, -1), (key1812, -1), (key1815, -1), (key1787, 1), (key1812, 1), (key1654, 1), (key1657, 1), (key1454, -1), (key1654, -1), (key1568, -1), (key1617, -1), (key1419, 1), (key1617, 1), (key1823, 2), (key1796, -1), (key1823, -1), (key1665, -2), (key1464, 1), (key1665, 1), (key1591, 1), (key1631, 1), (key1442, -1), (key1631, -1)]

def rawRow429 : Integer.Sparse Key := [(key1343, -1), (key1336, -1), (key1336, 2), (key1324, 1), (key1315, 1), (key1315, -1), (key1295, -1), (key1311, -2), (key1311, 1), (key1291, 1), (key1778, 1), (key1771, 1), (key1771, -2), (key1554, -1), (key1545, -1), (key1545, 1), (key1390, 1), (key1541, 2), (key1541, -1), (key1386, -1), (key1815, -1), (key1812, -1), (key1812, 1), (key1787, 1), (key1657, 1), (key1654, 1), (key1654, -1), (key1454, -1), (key1617, -1), (key1568, -1), (key1617, 1), (key1419, 1), (key1823, 2), (key1823, -1), (key1796, -1), (key1665, -2), (key1665, 1), (key1464, 1), (key1631, 1), (key1591, 1), (key1631, -1), (key1442, -1)]

def rawRow430 : Integer.Sparse Key := [(key1386, -1), (key1390, -1), (key1390, 2), (key1419, 1), (key1423, 1), (key1423, -1), (key1454, -1), (key1442, -2), (key1442, 1), (key1464, 1), (key1291, 1), (key1295, 1), (key1295, -2), (key1568, -1), (key1572, -1), (key1572, 1), (key1787, 1), (key1591, 2), (key1591, -1), (key1796, -1), (key1311, -1), (key1315, -1), (key1315, 1), (key1336, 1), (key1541, 1), (key1545, 1), (key1545, -1), (key1771, -1), (key1631, -1), (key1665, -1), (key1631, 1), (key1823, 1), (key1324, 2), (key1324, -1), (key1343, -1), (key1554, -2), (key1554, 1), (key1778, 1), (key1622, 1), (key1657, 1), (key1622, -1), (key1815, -1)]

def rawRow431 : Integer.Sparse Key := [(key1390, -1), (key1386, -1), (key1390, 2), (key1423, 1), (key1419, 1), (key1454, -1), (key1423, -1), (key1442, -2), (key1464, 1), (key1442, 1), (key1295, 1), (key1291, 1), (key1295, -2), (key1572, -1), (key1568, -1), (key1787, 1), (key1572, 1), (key1591, 2), (key1796, -1), (key1591, -1), (key1315, -1), (key1311, -1), (key1336, 1), (key1315, 1), (key1545, 1), (key1541, 1), (key1771, -1), (key1545, -1), (key1665, -1), (key1631, -1), (key1823, 1), (key1631, 1), (key1324, 2), (key1343, -1), (key1324, -1), (key1554, -2), (key1778, 1), (key1554, 1), (key1657, 1), (key1622, 1), (key1815, -1), (key1622, -1)]

def rawRow432 : Integer.Sparse Key := [(key1390, -1), (key1390, -1), (key1386, 2), (key1454, 1), (key1454, 1), (key1419, -1), (key1419, -1), (key1464, -2), (key1442, 1), (key1442, 1), (key1295, 1), (key1295, 1), (key1291, -2), (key1787, -1), (key1787, -1), (key1568, 1), (key1568, 1), (key1796, 2), (key1591, -1), (key1591, -1), (key1336, -1), (key1336, -1), (key1311, 1), (key1311, 1), (key1771, 1), (key1771, 1), (key1541, -1), (key1541, -1), (key1823, -1), (key1823, -1), (key1665, 1), (key1665, 1), (key1343, 2), (key1324, -1), (key1324, -1), (key1778, -2), (key1554, 1), (key1554, 1), (key1815, 1), (key1815, 1), (key1657, -1), (key1657, -1)]

def rawRow433 : Integer.Sparse Key := [(key1419, -1), (key1423, -1), (key1442, 2), (key1386, 1), (key1390, 1), (key1442, -1), (key1464, -1), (key1390, -2), (key1423, 1), (key1454, 1), (key1568, 1), (key1572, 1), (key1591, -2), (key1291, -1), (key1295, -1), (key1591, 1), (key1796, 1), (key1295, 2), (key1572, -1), (key1787, -1), (key1541, -1), (key1545, -1), (key1631, 1), (key1665, 1), (key1311, 1), (key1315, 1), (key1631, -1), (key1823, -1), (key1315, -1), (key1336, -1), (key1545, 1), (key1771, 1), (key1554, 2), (key1622, -1), (key1657, -1), (key1324, -2), (key1622, 1), (key1815, 1), (key1324, 1), (key1343, 1), (key1554, -1), (key1778, -1)]

def rawRow434 : Integer.Sparse Key := [(key1423, -1), (key1419, -1), (key1442, 2), (key1390, 1), (key1386, 1), (key1464, -1), (key1442, -1), (key1390, -2), (key1454, 1), (key1423, 1), (key1572, 1), (key1568, 1), (key1591, -2), (key1295, -1), (key1291, -1), (key1796, 1), (key1591, 1), (key1295, 2), (key1787, -1), (key1572, -1), (key1545, -1), (key1541, -1), (key1665, 1), (key1631, 1), (key1315, 1), (key1311, 1), (key1823, -1), (key1631, -1), (key1336, -1), (key1315, -1), (key1771, 1), (key1545, 1), (key1554, 2), (key1657, -1), (key1622, -1), (key1324, -2), (key1815, 1), (key1622, 1), (key1343, 1), (key1324, 1), (key1778, -1), (key1554, -1)]

def rawRow435 : Integer.Sparse Key := [(key1423, -1), (key1442, -1), (key1419, 2), (key1454, 1), (key1464, 1), (key1386, -1), (key1419, -1), (key1454, -2), (key1390, 1), (key1423, 1), (key1572, 1), (key1591, 1), (key1568, -2), (key1787, -1), (key1796, -1), (key1291, 1), (key1568, 1), (key1787, 2), (key1295, -1), (key1572, -1), (key1654, -1), (key1665, -1), (key1541, 1), (key1617, 1), (key1812, 1), (key1823, 1), (key1311, -1), (key1617, -1), (key1771, -1), (key1812, -1), (key1336, 1), (key1654, 1), (key1657, 2), (key1554, -1), (key1622, -1), (key1815, -2), (key1324, 1), (key1622, 1), (key1778, 1), (key1815, 1), (key1343, -1), (key1657, -1)]

def rawRow436 : Integer.Sparse Key := [(key1442, -1), (key1423, -1), (key1419, 2), (key1464, 1), (key1454, 1), (key1419, -1), (key1386, -1), (key1454, -2), (key1423, 1), (key1390, 1), (key1591, 1), (key1572, 1), (key1568, -2), (key1796, -1), (key1787, -1), (key1568, 1), (key1291, 1), (key1787, 2), (key1572, -1), (key1295, -1), (key1665, -1), (key1654, -1), (key1617, 1), (key1541, 1), (key1823, 1), (key1812, 1), (key1617, -1), (key1311, -1), (key1812, -1), (key1771, -1), (key1654, 1), (key1336, 1), (key1657, 2), (key1622, -1), (key1554, -1), (key1815, -2), (key1622, 1), (key1324, 1), (key1815, 1), (key1778, 1), (key1657, -1), (key1343, -1)]

def rawRow437 : Integer.Sparse Key := [(key1454, -1), (key1454, -1), (key1464, 2), (key1390, 1), (key1390, 1), (key1442, -1), (key1442, -1), (key1386, -2), (key1419, 1), (key1419, 1), (key1787, 1), (key1787, 1), (key1796, -2), (key1295, -1), (key1295, -1), (key1591, 1), (key1591, 1), (key1291, 2), (key1568, -1), (key1568, -1), (key1771, -1), (key1771, -1), (key1823, 1), (key1823, 1), (key1336, 1), (key1336, 1), (key1665, -1), (key1665, -1), (key1311, -1), (key1311, -1), (key1541, 1), (key1541, 1), (key1778, 2), (key1815, -1), (key1815, -1), (key1343, -2), (key1657, 1), (key1657, 1), (key1324, 1), (key1324, 1), (key1554, -1), (key1554, -1)]

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

def rawRow452 : Integer.Sparse Key := [(key1771, -1), (key1771, -1), (key1778, 2), (key1787, 1), (key1787, 1), (key1815, -1), (key1815, -1), (key1796, -2), (key1823, 1), (key1823, 1), (key1336, 1), (key1336, 1), (key1343, -2), (key1454, -1), (key1454, -1), (key1657, 1), (key1657, 1), (key1464, 2), (key1665, -1), (key1665, -1), (key1295, -1), (key1295, -1), (key1324, 1), (key1324, 1), (key1390, 1), (key1390, 1), (key1554, -1), (key1554, -1), (key1442, -1), (key1442, -1), (key1591, 1), (key1591, 1), (key1291, 2), (key1311, -1), (key1311, -1), (key1386, -2), (key1541, 1), (key1541, 1), (key1419, 1), (key1419, 1), (key1568, -1), (key1568, -1)]

def rawRow453 : Integer.Sparse Key := [(key1771, -1), (key1778, -1), (key1771, 2), (key1812, 1), (key1815, 1), (key1787, -1), (key1812, -1), (key1823, -2), (key1796, 1), (key1823, 1), (key1336, 1), (key1343, 1), (key1336, -2), (key1654, -1), (key1657, -1), (key1454, 1), (key1654, 1), (key1665, 2), (key1464, -1), (key1665, -1), (key1315, -1), (key1324, -1), (key1295, 1), (key1315, 1), (key1545, 1), (key1554, 1), (key1390, -1), (key1545, -1), (key1591, -1), (key1631, -1), (key1442, 1), (key1631, 1), (key1311, 2), (key1291, -1), (key1311, -1), (key1541, -2), (key1386, 1), (key1541, 1), (key1568, 1), (key1617, 1), (key1419, -1), (key1617, -1)]

def rawRow454 : Integer.Sparse Key := [(key1778, -1), (key1771, -1), (key1771, 2), (key1815, 1), (key1812, 1), (key1812, -1), (key1787, -1), (key1823, -2), (key1823, 1), (key1796, 1), (key1343, 1), (key1336, 1), (key1336, -2), (key1657, -1), (key1654, -1), (key1654, 1), (key1454, 1), (key1665, 2), (key1665, -1), (key1464, -1), (key1324, -1), (key1315, -1), (key1315, 1), (key1295, 1), (key1554, 1), (key1545, 1), (key1545, -1), (key1390, -1), (key1631, -1), (key1591, -1), (key1631, 1), (key1442, 1), (key1311, 2), (key1311, -1), (key1291, -1), (key1541, -2), (key1541, 1), (key1386, 1), (key1617, 1), (key1568, 1), (key1617, -1), (key1419, -1)]

def rawRow455 : Integer.Sparse Key := [(key1787, -1), (key1787, -1), (key1796, 2), (key1771, 1), (key1771, 1), (key1823, -1), (key1823, -1), (key1778, -2), (key1815, 1), (key1815, 1), (key1454, 1), (key1454, 1), (key1464, -2), (key1336, -1), (key1336, -1), (key1665, 1), (key1665, 1), (key1343, 2), (key1657, -1), (key1657, -1), (key1390, -1), (key1390, -1), (key1442, 1), (key1442, 1), (key1295, 1), (key1295, 1), (key1591, -1), (key1591, -1), (key1324, -1), (key1324, -1), (key1554, 1), (key1554, 1), (key1386, 2), (key1419, -1), (key1419, -1), (key1291, -2), (key1568, 1), (key1568, 1), (key1311, 1), (key1311, 1), (key1541, -1), (key1541, -1)]

def rawRow456 : Integer.Sparse Key := [(key1787, -1), (key1796, -1), (key1787, 2), (key1812, 1), (key1823, 1), (key1771, -1), (key1812, -1), (key1815, -2), (key1778, 1), (key1815, 1), (key1454, 1), (key1464, 1), (key1454, -2), (key1654, -1), (key1665, -1), (key1336, 1), (key1654, 1), (key1657, 2), (key1343, -1), (key1657, -1), (key1423, -1), (key1442, -1), (key1390, 1), (key1423, 1), (key1572, 1), (key1591, 1), (key1295, -1), (key1572, -1), (key1554, -1), (key1622, -1), (key1324, 1), (key1622, 1), (key1419, 2), (key1386, -1), (key1419, -1), (key1568, -2), (key1291, 1), (key1568, 1), (key1541, 1), (key1617, 1), (key1311, -1), (key1617, -1)]

def rawRow457 : Integer.Sparse Key := [(key1796, -1), (key1787, -1), (key1787, 2), (key1823, 1), (key1812, 1), (key1812, -1), (key1771, -1), (key1815, -2), (key1815, 1), (key1778, 1), (key1464, 1), (key1454, 1), (key1454, -2), (key1665, -1), (key1654, -1), (key1654, 1), (key1336, 1), (key1657, 2), (key1657, -1), (key1343, -1), (key1442, -1), (key1423, -1), (key1423, 1), (key1390, 1), (key1591, 1), (key1572, 1), (key1572, -1), (key1295, -1), (key1622, -1), (key1554, -1), (key1622, 1), (key1324, 1), (key1419, 2), (key1419, -1), (key1386, -1), (key1568, -2), (key1568, 1), (key1291, 1), (key1617, 1), (key1541, 1), (key1617, -1), (key1311, -1)]

def rawRow458 : Integer.Sparse Key := [(key1812, -1), (key1815, -1), (key1823, 2), (key1771, 1), (key1778, 1), (key1796, -1), (key1823, -1), (key1771, -2), (key1787, 1), (key1812, 1), (key1654, 1), (key1657, 1), (key1665, -2), (key1336, -1), (key1343, -1), (key1464, 1), (key1665, 1), (key1336, 2), (key1454, -1), (key1654, -1), (key1545, -1), (key1554, -1), (key1591, 1), (key1631, 1), (key1315, 1), (key1324, 1), (key1442, -1), (key1631, -1), (key1295, -1), (key1315, -1), (key1390, 1), (key1545, 1), (key1541, 2), (key1568, -1), (key1617, -1), (key1311, -2), (key1419, 1), (key1617, 1), (key1291, 1), (key1311, 1), (key1386, -1), (key1541, -1)]

def rawRow459 : Integer.Sparse Key := [(key1815, -1), (key1812, -1), (key1823, 2), (key1778, 1), (key1771, 1), (key1823, -1), (key1796, -1), (key1771, -2), (key1812, 1), (key1787, 1), (key1657, 1), (key1654, 1), (key1665, -2), (key1343, -1), (key1336, -1), (key1665, 1), (key1464, 1), (key1336, 2), (key1654, -1), (key1454, -1), (key1554, -1), (key1545, -1), (key1631, 1), (key1591, 1), (key1324, 1), (key1315, 1), (key1631, -1), (key1442, -1), (key1315, -1), (key1295, -1), (key1545, 1), (key1390, 1), (key1541, 2), (key1617, -1), (key1568, -1), (key1311, -2), (key1617, 1), (key1419, 1), (key1311, 1), (key1291, 1), (key1541, -1), (key1386, -1)]

def rawRow460 : Integer.Sparse Key := [(key1812, -1), (key1823, -1), (key1815, 2), (key1787, 1), (key1796, 1), (key1778, -1), (key1815, -1), (key1787, -2), (key1771, 1), (key1812, 1), (key1654, 1), (key1665, 1), (key1657, -2), (key1454, -1), (key1464, -1), (key1343, 1), (key1657, 1), (key1454, 2), (key1336, -1), (key1654, -1), (key1572, -1), (key1591, -1), (key1554, 1), (key1622, 1), (key1423, 1), (key1442, 1), (key1324, -1), (key1622, -1), (key1390, -1), (key1423, -1), (key1295, 1), (key1572, 1), (key1568, 2), (key1541, -1), (key1617, -1), (key1419, -2), (key1311, 1), (key1617, 1), (key1386, 1), (key1419, 1), (key1291, -1), (key1568, -1)]

def rawRow461 : Integer.Sparse Key := [(key1823, -1), (key1812, -1), (key1815, 2), (key1796, 1), (key1787, 1), (key1815, -1), (key1778, -1), (key1787, -2), (key1812, 1), (key1771, 1), (key1665, 1), (key1654, 1), (key1657, -2), (key1464, -1), (key1454, -1), (key1657, 1), (key1343, 1), (key1454, 2), (key1654, -1), (key1336, -1), (key1591, -1), (key1572, -1), (key1622, 1), (key1554, 1), (key1442, 1), (key1423, 1), (key1622, -1), (key1324, -1), (key1423, -1), (key1390, -1), (key1572, 1), (key1295, 1), (key1568, 2), (key1617, -1), (key1541, -1), (key1419, -2), (key1617, 1), (key1311, 1), (key1419, 1), (key1386, 1), (key1568, -1), (key1291, -1)]

def rawRow462 : Integer.Sparse Key := [(key2616, -2), (key2616, 1), (key2619, 1), (key2632, 2), (key2632, -1), (key2649, -1), (key2640, -1), (key2642, -1), (key2640, 1), (key2654, 1), (key2671, 2), (key2671, -1), (key2674, -1), (key2786, -2), (key2786, 1), (key2939, 1), (key2794, 1), (key2796, 1), (key2794, -1), (key2944, -1), (key2706, -2), (key2706, 1), (key2738, 1), (key2809, 2), (key2809, -1), (key2951, -1), (key2860, -1), (key2898, -1), (key2860, 1), (key2977, 1), (key2726, 1), (key2729, 1), (key2726, -1), (key2748, -1), (key2829, -1), (key2832, -1), (key2829, 1), (key2961, 1), (key2870, 1), (key2905, 1), (key2870, -1), (key2984, -1)]

def rawRow463 : Integer.Sparse Key := [(key2616, -2), (key2619, 1), (key2616, 1), (key2632, 2), (key2649, -1), (key2632, -1), (key2642, -1), (key2640, -1), (key2654, 1), (key2640, 1), (key2671, 2), (key2674, -1), (key2671, -1), (key2786, -2), (key2939, 1), (key2786, 1), (key2796, 1), (key2794, 1), (key2944, -1), (key2794, -1), (key2706, -2), (key2738, 1), (key2706, 1), (key2809, 2), (key2951, -1), (key2809, -1), (key2898, -1), (key2860, -1), (key2977, 1), (key2860, 1), (key2729, 1), (key2726, 1), (key2748, -1), (key2726, -1), (key2832, -1), (key2829, -1), (key2961, 1), (key2829, 1), (key2905, 1), (key2870, 1), (key2984, -1), (key2870, -1)]

def rawRow464 : Integer.Sparse Key := [(key2619, -2), (key2616, 1), (key2616, 1), (key2649, 2), (key2632, -1), (key2632, -1), (key2654, -1), (key2654, -1), (key2642, 1), (key2642, 1), (key2674, 2), (key2671, -1), (key2671, -1), (key2939, -2), (key2786, 1), (key2786, 1), (key2944, 1), (key2944, 1), (key2796, -1), (key2796, -1), (key2738, -2), (key2706, 1), (key2706, 1), (key2951, 2), (key2809, -1), (key2809, -1), (key2977, -1), (key2977, -1), (key2898, 1), (key2898, 1), (key2748, 1), (key2748, 1), (key2729, -1), (key2729, -1), (key2961, -1), (key2961, -1), (key2832, 1), (key2832, 1), (key2984, 1), (key2984, 1), (key2905, -1), (key2905, -1)]

def rawRow465 : Integer.Sparse Key := [(key2632, -2), (key2640, 1), (key2642, 1), (key2616, 2), (key2640, -1), (key2654, -1), (key2616, -1), (key2619, -1), (key2632, 1), (key2649, 1), (key2786, 2), (key2794, -1), (key2796, -1), (key2671, -2), (key2794, 1), (key2944, 1), (key2671, 1), (key2674, 1), (key2786, -1), (key2939, -1), (key2809, -2), (key2860, 1), (key2898, 1), (key2706, 2), (key2860, -1), (key2977, -1), (key2706, -1), (key2738, -1), (key2809, 1), (key2951, 1), (key2829, 1), (key2832, 1), (key2870, -1), (key2905, -1), (key2726, -1), (key2729, -1), (key2870, 1), (key2984, 1), (key2726, 1), (key2748, 1), (key2829, -1), (key2961, -1)]

def rawRow466 : Integer.Sparse Key := [(key2632, -2), (key2642, 1), (key2640, 1), (key2616, 2), (key2654, -1), (key2640, -1), (key2619, -1), (key2616, -1), (key2649, 1), (key2632, 1), (key2786, 2), (key2796, -1), (key2794, -1), (key2671, -2), (key2944, 1), (key2794, 1), (key2674, 1), (key2671, 1), (key2939, -1), (key2786, -1), (key2809, -2), (key2898, 1), (key2860, 1), (key2706, 2), (key2977, -1), (key2860, -1), (key2738, -1), (key2706, -1), (key2951, 1), (key2809, 1), (key2832, 1), (key2829, 1), (key2905, -1), (key2870, -1), (key2729, -1), (key2726, -1), (key2984, 1), (key2870, 1), (key2748, 1), (key2726, 1), (key2961, -1), (key2829, -1)]

def rawRow467 : Integer.Sparse Key := [(key2642, -2), (key2632, 1), (key2640, 1), (key2654, 2), (key2616, -1), (key2640, -1), (key2649, -1), (key2654, -1), (key2619, 1), (key2642, 1), (key2796, 2), (key2786, -1), (key2794, -1), (key2944, -2), (key2671, 1), (key2794, 1), (key2939, 1), (key2944, 1), (key2674, -1), (key2796, -1), (key2898, -2), (key2809, 1), (key2860, 1), (key2977, 2), (key2706, -1), (key2860, -1), (key2951, -1), (key2977, -1), (key2738, 1), (key2898, 1), (key2905, 1), (key2913, 1), (key2832, -1), (key2883, -1), (key2984, -1), (key2992, -1), (key2729, 1), (key2883, 1), (key2961, 1), (key2992, 1), (key2748, -1), (key2913, -1)]

def rawRow468 : Integer.Sparse Key := [(key2642, -2), (key2640, 1), (key2632, 1), (key2654, 2), (key2640, -1), (key2616, -1), (key2654, -1), (key2649, -1), (key2642, 1), (key2619, 1), (key2796, 2), (key2794, -1), (key2786, -1), (key2944, -2), (key2794, 1), (key2671, 1), (key2944, 1), (key2939, 1), (key2796, -1), (key2674, -1), (key2898, -2), (key2860, 1), (key2809, 1), (key2977, 2), (key2860, -1), (key2706, -1), (key2977, -1), (key2951, -1), (key2898, 1), (key2738, 1), (key2913, 1), (key2905, 1), (key2883, -1), (key2832, -1), (key2992, -1), (key2984, -1), (key2883, 1), (key2729, 1), (key2992, 1), (key2961, 1), (key2913, -1), (key2748, -1)]

def rawRow469 : Integer.Sparse Key := [(key2649, -2), (key2654, 1), (key2654, 1), (key2619, 2), (key2642, -1), (key2642, -1), (key2616, -1), (key2616, -1), (key2632, 1), (key2632, 1), (key2939, 2), (key2944, -1), (key2944, -1), (key2674, -2), (key2796, 1), (key2796, 1), (key2671, 1), (key2671, 1), (key2786, -1), (key2786, -1), (key2951, -2), (key2977, 1), (key2977, 1), (key2738, 2), (key2898, -1), (key2898, -1), (key2706, -1), (key2706, -1), (key2809, 1), (key2809, 1), (key2961, 1), (key2961, 1), (key2984, -1), (key2984, -1), (key2748, -1), (key2748, -1), (key2905, 1), (key2905, 1), (key2729, 1), (key2729, 1), (key2832, -1), (key2832, -1)]

def rawRow470 : Integer.Sparse Key := [(key2654, -2), (key2649, 1), (key2654, 1), (key2642, 2), (key2619, -1), (key2642, -1), (key2632, -1), (key2640, -1), (key2616, 1), (key2640, 1), (key2944, 2), (key2939, -1), (key2944, -1), (key2796, -2), (key2674, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2671, -1), (key2794, -1), (key2977, -2), (key2951, 1), (key2977, 1), (key2898, 2), (key2738, -1), (key2898, -1), (key2809, -1), (key2860, -1), (key2706, 1), (key2860, 1), (key2984, 1), (key2992, 1), (key2961, -1), (key2992, -1), (key2905, -1), (key2913, -1), (key2748, 1), (key2913, 1), (key2832, 1), (key2883, 1), (key2729, -1), (key2883, -1)]

def rawRow471 : Integer.Sparse Key := [(key2654, -2), (key2654, 1), (key2649, 1), (key2642, 2), (key2642, -1), (key2619, -1), (key2640, -1), (key2632, -1), (key2640, 1), (key2616, 1), (key2944, 2), (key2944, -1), (key2939, -1), (key2796, -2), (key2796, 1), (key2674, 1), (key2794, 1), (key2786, 1), (key2794, -1), (key2671, -1), (key2977, -2), (key2977, 1), (key2951, 1), (key2898, 2), (key2898, -1), (key2738, -1), (key2860, -1), (key2809, -1), (key2860, 1), (key2706, 1), (key2992, 1), (key2984, 1), (key2992, -1), (key2961, -1), (key2913, -1), (key2905, -1), (key2913, 1), (key2748, 1), (key2883, 1), (key2832, 1), (key2883, -1), (key2729, -1)]

def rawRow472 : Integer.Sparse Key := [(key2671, -2), (key2671, 1), (key2674, 1), (key2706, 2), (key2706, -1), (key2738, -1), (key2726, -1), (key2729, -1), (key2726, 1), (key2748, 1), (key2616, 2), (key2616, -1), (key2619, -1), (key2809, -2), (key2809, 1), (key2951, 1), (key2829, 1), (key2832, 1), (key2829, -1), (key2961, -1), (key2632, -2), (key2632, 1), (key2649, 1), (key2786, 2), (key2786, -1), (key2939, -1), (key2870, -1), (key2905, -1), (key2870, 1), (key2984, 1), (key2640, 1), (key2642, 1), (key2640, -1), (key2654, -1), (key2794, -1), (key2796, -1), (key2794, 1), (key2944, 1), (key2860, 1), (key2898, 1), (key2860, -1), (key2977, -1)]

def rawRow473 : Integer.Sparse Key := [(key2671, -2), (key2674, 1), (key2671, 1), (key2706, 2), (key2738, -1), (key2706, -1), (key2729, -1), (key2726, -1), (key2748, 1), (key2726, 1), (key2616, 2), (key2619, -1), (key2616, -1), (key2809, -2), (key2951, 1), (key2809, 1), (key2832, 1), (key2829, 1), (key2961, -1), (key2829, -1), (key2632, -2), (key2649, 1), (key2632, 1), (key2786, 2), (key2939, -1), (key2786, -1), (key2905, -1), (key2870, -1), (key2984, 1), (key2870, 1), (key2642, 1), (key2640, 1), (key2654, -1), (key2640, -1), (key2796, -1), (key2794, -1), (key2944, 1), (key2794, 1), (key2898, 1), (key2860, 1), (key2977, -1), (key2860, -1)]

def rawRow474 : Integer.Sparse Key := [(key2674, -2), (key2671, 1), (key2671, 1), (key2738, 2), (key2706, -1), (key2706, -1), (key2748, -1), (key2748, -1), (key2729, 1), (key2729, 1), (key2619, 2), (key2616, -1), (key2616, -1), (key2951, -2), (key2809, 1), (key2809, 1), (key2961, 1), (key2961, 1), (key2832, -1), (key2832, -1), (key2649, -2), (key2632, 1), (key2632, 1), (key2939, 2), (key2786, -1), (key2786, -1), (key2984, -1), (key2984, -1), (key2905, 1), (key2905, 1), (key2654, 1), (key2654, 1), (key2642, -1), (key2642, -1), (key2944, -1), (key2944, -1), (key2796, 1), (key2796, 1), (key2977, 1), (key2977, 1), (key2898, -1), (key2898, -1)]

def rawRow475 : Integer.Sparse Key := [(key2706, -2), (key2726, 1), (key2729, 1), (key2671, 2), (key2726, -1), (key2748, -1), (key2671, -1), (key2674, -1), (key2706, 1), (key2738, 1), (key2809, 2), (key2829, -1), (key2832, -1), (key2616, -2), (key2829, 1), (key2961, 1), (key2616, 1), (key2619, 1), (key2809, -1), (key2951, -1), (key2786, -2), (key2870, 1), (key2905, 1), (key2632, 2), (key2870, -1), (key2984, -1), (key2632, -1), (key2649, -1), (key2786, 1), (key2939, 1), (key2794, 1), (key2796, 1), (key2860, -1), (key2898, -1), (key2640, -1), (key2642, -1), (key2860, 1), (key2977, 1), (key2640, 1), (key2654, 1), (key2794, -1), (key2944, -1)]

def rawRow476 : Integer.Sparse Key := [(key2706, -2), (key2729, 1), (key2726, 1), (key2671, 2), (key2748, -1), (key2726, -1), (key2674, -1), (key2671, -1), (key2738, 1), (key2706, 1), (key2809, 2), (key2832, -1), (key2829, -1), (key2616, -2), (key2961, 1), (key2829, 1), (key2619, 1), (key2616, 1), (key2951, -1), (key2809, -1), (key2786, -2), (key2905, 1), (key2870, 1), (key2632, 2), (key2984, -1), (key2870, -1), (key2649, -1), (key2632, -1), (key2939, 1), (key2786, 1), (key2796, 1), (key2794, 1), (key2898, -1), (key2860, -1), (key2642, -1), (key2640, -1), (key2977, 1), (key2860, 1), (key2654, 1), (key2640, 1), (key2944, -1), (key2794, -1)]

def rawRow477 : Integer.Sparse Key := [(key2729, -2), (key2706, 1), (key2726, 1), (key2748, 2), (key2671, -1), (key2726, -1), (key2738, -1), (key2748, -1), (key2674, 1), (key2729, 1), (key2832, 2), (key2809, -1), (key2829, -1), (key2961, -2), (key2616, 1), (key2829, 1), (key2951, 1), (key2961, 1), (key2619, -1), (key2832, -1), (key2905, -2), (key2786, 1), (key2870, 1), (key2984, 2), (key2632, -1), (key2870, -1), (key2939, -1), (key2984, -1), (key2649, 1), (key2905, 1), (key2898, 1), (key2913, 1), (key2796, -1), (key2883, -1), (key2977, -1), (key2992, -1), (key2642, 1), (key2883, 1), (key2944, 1), (key2992, 1), (key2654, -1), (key2913, -1)]

def rawRow478 : Integer.Sparse Key := [(key2729, -2), (key2726, 1), (key2706, 1), (key2748, 2), (key2726, -1), (key2671, -1), (key2748, -1), (key2738, -1), (key2729, 1), (key2674, 1), (key2832, 2), (key2829, -1), (key2809, -1), (key2961, -2), (key2829, 1), (key2616, 1), (key2961, 1), (key2951, 1), (key2832, -1), (key2619, -1), (key2905, -2), (key2870, 1), (key2786, 1), (key2984, 2), (key2870, -1), (key2632, -1), (key2984, -1), (key2939, -1), (key2905, 1), (key2649, 1), (key2913, 1), (key2898, 1), (key2883, -1), (key2796, -1), (key2992, -1), (key2977, -1), (key2883, 1), (key2642, 1), (key2992, 1), (key2944, 1), (key2913, -1), (key2654, -1)]

def rawRow479 : Integer.Sparse Key := [(key2738, -2), (key2748, 1), (key2748, 1), (key2674, 2), (key2729, -1), (key2729, -1), (key2671, -1), (key2671, -1), (key2706, 1), (key2706, 1), (key2951, 2), (key2961, -1), (key2961, -1), (key2619, -2), (key2832, 1), (key2832, 1), (key2616, 1), (key2616, 1), (key2809, -1), (key2809, -1), (key2939, -2), (key2984, 1), (key2984, 1), (key2649, 2), (key2905, -1), (key2905, -1), (key2632, -1), (key2632, -1), (key2786, 1), (key2786, 1), (key2944, 1), (key2944, 1), (key2977, -1), (key2977, -1), (key2654, -1), (key2654, -1), (key2898, 1), (key2898, 1), (key2642, 1), (key2642, 1), (key2796, -1), (key2796, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow480 : Integer.Sparse Key := [(key2748, -2), (key2738, 1), (key2748, 1), (key2729, 2), (key2674, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2671, 1), (key2726, 1), (key2961, 2), (key2951, -1), (key2961, -1), (key2832, -2), (key2619, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2616, -1), (key2829, -1), (key2984, -2), (key2939, 1), (key2984, 1), (key2905, 2), (key2649, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2632, 1), (key2870, 1), (key2977, 1), (key2992, 1), (key2944, -1), (key2992, -1), (key2898, -1), (key2913, -1), (key2654, 1), (key2913, 1), (key2796, 1), (key2883, 1), (key2642, -1), (key2883, -1)]

def rawRow481 : Integer.Sparse Key := [(key2748, -2), (key2748, 1), (key2738, 1), (key2729, 2), (key2729, -1), (key2674, -1), (key2726, -1), (key2706, -1), (key2726, 1), (key2671, 1), (key2961, 2), (key2961, -1), (key2951, -1), (key2832, -2), (key2832, 1), (key2619, 1), (key2829, 1), (key2809, 1), (key2829, -1), (key2616, -1), (key2984, -2), (key2984, 1), (key2939, 1), (key2905, 2), (key2905, -1), (key2649, -1), (key2870, -1), (key2786, -1), (key2870, 1), (key2632, 1), (key2992, 1), (key2977, 1), (key2992, -1), (key2944, -1), (key2913, -1), (key2898, -1), (key2913, 1), (key2654, 1), (key2883, 1), (key2796, 1), (key2883, -1), (key2642, -1)]

def rawRow482 : Integer.Sparse Key := [(key2786, -2), (key2794, 1), (key2796, 1), (key2809, 2), (key2860, -1), (key2898, -1), (key2829, -1), (key2832, -1), (key2870, 1), (key2905, 1), (key2632, 2), (key2640, -1), (key2642, -1), (key2706, -2), (key2860, 1), (key2977, 1), (key2726, 1), (key2729, 1), (key2870, -1), (key2984, -1), (key2616, -2), (key2640, 1), (key2654, 1), (key2671, 2), (key2794, -1), (key2944, -1), (key2726, -1), (key2748, -1), (key2829, 1), (key2961, 1), (key2616, 1), (key2619, 1), (key2632, -1), (key2649, -1), (key2671, -1), (key2674, -1), (key2786, 1), (key2939, 1), (key2706, 1), (key2738, 1), (key2809, -1), (key2951, -1)]

def rawRow483 : Integer.Sparse Key := [(key2786, -2), (key2796, 1), (key2794, 1), (key2809, 2), (key2898, -1), (key2860, -1), (key2832, -1), (key2829, -1), (key2905, 1), (key2870, 1), (key2632, 2), (key2642, -1), (key2640, -1), (key2706, -2), (key2977, 1), (key2860, 1), (key2729, 1), (key2726, 1), (key2984, -1), (key2870, -1), (key2616, -2), (key2654, 1), (key2640, 1), (key2671, 2), (key2944, -1), (key2794, -1), (key2748, -1), (key2726, -1), (key2961, 1), (key2829, 1), (key2619, 1), (key2616, 1), (key2649, -1), (key2632, -1), (key2674, -1), (key2671, -1), (key2939, 1), (key2786, 1), (key2738, 1), (key2706, 1), (key2951, -1), (key2809, -1)]

def rawRow484 : Integer.Sparse Key := [(key2796, -2), (key2786, 1), (key2794, 1), (key2898, 2), (key2809, -1), (key2860, -1), (key2905, -1), (key2913, -1), (key2832, 1), (key2883, 1), (key2642, 2), (key2632, -1), (key2640, -1), (key2977, -2), (key2706, 1), (key2860, 1), (key2984, 1), (key2992, 1), (key2729, -1), (key2883, -1), (key2654, -2), (key2616, 1), (key2640, 1), (key2944, 2), (key2671, -1), (key2794, -1), (key2961, -1), (key2992, -1), (key2748, 1), (key2913, 1), (key2649, 1), (key2654, 1), (key2619, -1), (key2642, -1), (key2939, -1), (key2944, -1), (key2674, 1), (key2796, 1), (key2951, 1), (key2977, 1), (key2738, -1), (key2898, -1)]

def rawRow485 : Integer.Sparse Key := [(key2796, -2), (key2794, 1), (key2786, 1), (key2898, 2), (key2860, -1), (key2809, -1), (key2913, -1), (key2905, -1), (key2883, 1), (key2832, 1), (key2642, 2), (key2640, -1), (key2632, -1), (key2977, -2), (key2860, 1), (key2706, 1), (key2992, 1), (key2984, 1), (key2883, -1), (key2729, -1), (key2654, -2), (key2640, 1), (key2616, 1), (key2944, 2), (key2794, -1), (key2671, -1), (key2992, -1), (key2961, -1), (key2913, 1), (key2748, 1), (key2654, 1), (key2649, 1), (key2642, -1), (key2619, -1), (key2944, -1), (key2939, -1), (key2796, 1), (key2674, 1), (key2977, 1), (key2951, 1), (key2898, -1), (key2738, -1)]

def rawRow486 : Integer.Sparse Key := [(key2809, -2), (key2829, 1), (key2832, 1), (key2786, 2), (key2870, -1), (key2905, -1), (key2794, -1), (key2796, -1), (key2860, 1), (key2898, 1), (key2706, 2), (key2726, -1), (key2729, -1), (key2632, -2), (key2870, 1), (key2984, 1), (key2640, 1), (key2642, 1), (key2860, -1), (key2977, -1), (key2671, -2), (key2726, 1), (key2748, 1), (key2616, 2), (key2829, -1), (key2961, -1), (key2640, -1), (key2654, -1), (key2794, 1), (key2944, 1), (key2671, 1), (key2674, 1), (key2706, -1), (key2738, -1), (key2616, -1), (key2619, -1), (key2809, 1), (key2951, 1), (key2632, 1), (key2649, 1), (key2786, -1), (key2939, -1)]

def rawRow487 : Integer.Sparse Key := [(key2809, -2), (key2832, 1), (key2829, 1), (key2786, 2), (key2905, -1), (key2870, -1), (key2796, -1), (key2794, -1), (key2898, 1), (key2860, 1), (key2706, 2), (key2729, -1), (key2726, -1), (key2632, -2), (key2984, 1), (key2870, 1), (key2642, 1), (key2640, 1), (key2977, -1), (key2860, -1), (key2671, -2), (key2748, 1), (key2726, 1), (key2616, 2), (key2961, -1), (key2829, -1), (key2654, -1), (key2640, -1), (key2944, 1), (key2794, 1), (key2674, 1), (key2671, 1), (key2738, -1), (key2706, -1), (key2619, -1), (key2616, -1), (key2951, 1), (key2809, 1), (key2649, 1), (key2632, 1), (key2939, -1), (key2786, -1)]

def rawRow488 : Integer.Sparse Key := [(key2832, -2), (key2809, 1), (key2829, 1), (key2905, 2), (key2786, -1), (key2870, -1), (key2898, -1), (key2913, -1), (key2796, 1), (key2883, 1), (key2729, 2), (key2706, -1), (key2726, -1), (key2984, -2), (key2632, 1), (key2870, 1), (key2977, 1), (key2992, 1), (key2642, -1), (key2883, -1), (key2748, -2), (key2671, 1), (key2726, 1), (key2961, 2), (key2616, -1), (key2829, -1), (key2944, -1), (key2992, -1), (key2654, 1), (key2913, 1), (key2738, 1), (key2748, 1), (key2674, -1), (key2729, -1), (key2951, -1), (key2961, -1), (key2619, 1), (key2832, 1), (key2939, 1), (key2984, 1), (key2649, -1), (key2905, -1)]

def rawRow489 : Integer.Sparse Key := [(key2832, -2), (key2829, 1), (key2809, 1), (key2905, 2), (key2870, -1), (key2786, -1), (key2913, -1), (key2898, -1), (key2883, 1), (key2796, 1), (key2729, 2), (key2726, -1), (key2706, -1), (key2984, -2), (key2870, 1), (key2632, 1), (key2992, 1), (key2977, 1), (key2883, -1), (key2642, -1), (key2748, -2), (key2726, 1), (key2671, 1), (key2961, 2), (key2829, -1), (key2616, -1), (key2992, -1), (key2944, -1), (key2913, 1), (key2654, 1), (key2748, 1), (key2738, 1), (key2729, -1), (key2674, -1), (key2961, -1), (key2951, -1), (key2832, 1), (key2619, 1), (key2984, 1), (key2939, 1), (key2905, -1), (key2649, -1)]

def rawRow490 : Integer.Sparse Key := [(key2898, -2), (key2905, 1), (key2913, 1), (key2796, 2), (key2832, -1), (key2883, -1), (key2786, -1), (key2794, -1), (key2809, 1), (key2860, 1), (key2977, 2), (key2984, -1), (key2992, -1), (key2642, -2), (key2729, 1), (key2883, 1), (key2632, 1), (key2640, 1), (key2706, -1), (key2860, -1), (key2944, -2), (key2961, 1), (key2992, 1), (key2654, 2), (key2748, -1), (key2913, -1), (key2616, -1), (key2640, -1), (key2671, 1), (key2794, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2977, -1), (key2649, -1), (key2654, -1), (key2738, 1), (key2898, 1), (key2619, 1), (key2642, 1), (key2674, -1), (key2796, -1)]

def rawRow491 : Integer.Sparse Key := [(key2898, -2), (key2913, 1), (key2905, 1), (key2796, 2), (key2883, -1), (key2832, -1), (key2794, -1), (key2786, -1), (key2860, 1), (key2809, 1), (key2977, 2), (key2992, -1), (key2984, -1), (key2642, -2), (key2883, 1), (key2729, 1), (key2640, 1), (key2632, 1), (key2860, -1), (key2706, -1), (key2944, -2), (key2992, 1), (key2961, 1), (key2654, 2), (key2913, -1), (key2748, -1), (key2640, -1), (key2616, -1), (key2794, 1), (key2671, 1), (key2944, 1), (key2939, 1), (key2977, -1), (key2951, -1), (key2654, -1), (key2649, -1), (key2898, 1), (key2738, 1), (key2642, 1), (key2619, 1), (key2796, -1), (key2674, -1)]

def rawRow492 : Integer.Sparse Key := [(key2905, -2), (key2898, 1), (key2913, 1), (key2832, 2), (key2796, -1), (key2883, -1), (key2809, -1), (key2829, -1), (key2786, 1), (key2870, 1), (key2984, 2), (key2977, -1), (key2992, -1), (key2729, -2), (key2642, 1), (key2883, 1), (key2706, 1), (key2726, 1), (key2632, -1), (key2870, -1), (key2961, -2), (key2944, 1), (key2992, 1), (key2748, 2), (key2654, -1), (key2913, -1), (key2671, -1), (key2726, -1), (key2616, 1), (key2829, 1), (key2951, 1), (key2961, 1), (key2939, -1), (key2984, -1), (key2738, -1), (key2748, -1), (key2649, 1), (key2905, 1), (key2674, 1), (key2729, 1), (key2619, -1), (key2832, -1)]

def rawRow493 : Integer.Sparse Key := [(key2905, -2), (key2913, 1), (key2898, 1), (key2832, 2), (key2883, -1), (key2796, -1), (key2829, -1), (key2809, -1), (key2870, 1), (key2786, 1), (key2984, 2), (key2992, -1), (key2977, -1), (key2729, -2), (key2883, 1), (key2642, 1), (key2726, 1), (key2706, 1), (key2870, -1), (key2632, -1), (key2961, -2), (key2992, 1), (key2944, 1), (key2748, 2), (key2913, -1), (key2654, -1), (key2726, -1), (key2671, -1), (key2829, 1), (key2616, 1), (key2961, 1), (key2951, 1), (key2984, -1), (key2939, -1), (key2748, -1), (key2738, -1), (key2905, 1), (key2649, 1), (key2729, 1), (key2674, 1), (key2832, -1), (key2619, -1)]

def rawRow494 : Integer.Sparse Key := [(key2939, -2), (key2944, 1), (key2944, 1), (key2951, 2), (key2977, -1), (key2977, -1), (key2961, -1), (key2961, -1), (key2984, 1), (key2984, 1), (key2649, 2), (key2654, -1), (key2654, -1), (key2738, -2), (key2898, 1), (key2898, 1), (key2748, 1), (key2748, 1), (key2905, -1), (key2905, -1), (key2619, -2), (key2642, 1), (key2642, 1), (key2674, 2), (key2796, -1), (key2796, -1), (key2729, -1), (key2729, -1), (key2832, 1), (key2832, 1), (key2616, 1), (key2616, 1), (key2632, -1), (key2632, -1), (key2671, -1), (key2671, -1), (key2786, 1), (key2786, 1), (key2706, 1), (key2706, 1), (key2809, -1), (key2809, -1)]

def rawRow495 : Integer.Sparse Key := [(key2944, -2), (key2939, 1), (key2944, 1), (key2977, 2), (key2951, -1), (key2977, -1), (key2984, -1), (key2992, -1), (key2961, 1), (key2992, 1), (key2654, 2), (key2649, -1), (key2654, -1), (key2898, -2), (key2738, 1), (key2898, 1), (key2905, 1), (key2913, 1), (key2748, -1), (key2913, -1), (key2642, -2), (key2619, 1), (key2642, 1), (key2796, 2), (key2674, -1), (key2796, -1), (key2832, -1), (key2883, -1), (key2729, 1), (key2883, 1), (key2632, 1), (key2640, 1), (key2616, -1), (key2640, -1), (key2786, -1), (key2794, -1), (key2671, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2706, -1), (key2860, -1)]

def rawRow496 : Integer.Sparse Key := [(key2944, -2), (key2944, 1), (key2939, 1), (key2977, 2), (key2977, -1), (key2951, -1), (key2992, -1), (key2984, -1), (key2992, 1), (key2961, 1), (key2654, 2), (key2654, -1), (key2649, -1), (key2898, -2), (key2898, 1), (key2738, 1), (key2913, 1), (key2905, 1), (key2913, -1), (key2748, -1), (key2642, -2), (key2642, 1), (key2619, 1), (key2796, 2), (key2796, -1), (key2674, -1), (key2883, -1), (key2832, -1), (key2883, 1), (key2729, 1), (key2640, 1), (key2632, 1), (key2640, -1), (key2616, -1), (key2794, -1), (key2786, -1), (key2794, 1), (key2671, 1), (key2860, 1), (key2809, 1), (key2860, -1), (key2706, -1)]

def rawRow497 : Integer.Sparse Key := [(key2951, -2), (key2961, 1), (key2961, 1), (key2939, 2), (key2984, -1), (key2984, -1), (key2944, -1), (key2944, -1), (key2977, 1), (key2977, 1), (key2738, 2), (key2748, -1), (key2748, -1), (key2649, -2), (key2905, 1), (key2905, 1), (key2654, 1), (key2654, 1), (key2898, -1), (key2898, -1), (key2674, -2), (key2729, 1), (key2729, 1), (key2619, 2), (key2832, -1), (key2832, -1), (key2642, -1), (key2642, -1), (key2796, 1), (key2796, 1), (key2671, 1), (key2671, 1), (key2706, -1), (key2706, -1), (key2616, -1), (key2616, -1), (key2809, 1), (key2809, 1), (key2632, 1), (key2632, 1), (key2786, -1), (key2786, -1)]

def rawRow498 : Integer.Sparse Key := [(key2961, -2), (key2951, 1), (key2961, 1), (key2984, 2), (key2939, -1), (key2984, -1), (key2977, -1), (key2992, -1), (key2944, 1), (key2992, 1), (key2748, 2), (key2738, -1), (key2748, -1), (key2905, -2), (key2649, 1), (key2905, 1), (key2898, 1), (key2913, 1), (key2654, -1), (key2913, -1), (key2729, -2), (key2674, 1), (key2729, 1), (key2832, 2), (key2619, -1), (key2832, -1), (key2796, -1), (key2883, -1), (key2642, 1), (key2883, 1), (key2706, 1), (key2726, 1), (key2671, -1), (key2726, -1), (key2809, -1), (key2829, -1), (key2616, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2632, -1), (key2870, -1)]

def rawRow499 : Integer.Sparse Key := [(key2961, -2), (key2961, 1), (key2951, 1), (key2984, 2), (key2984, -1), (key2939, -1), (key2992, -1), (key2977, -1), (key2992, 1), (key2944, 1), (key2748, 2), (key2748, -1), (key2738, -1), (key2905, -2), (key2905, 1), (key2649, 1), (key2913, 1), (key2898, 1), (key2913, -1), (key2654, -1), (key2729, -2), (key2729, 1), (key2674, 1), (key2832, 2), (key2832, -1), (key2619, -1), (key2883, -1), (key2796, -1), (key2883, 1), (key2642, 1), (key2726, 1), (key2706, 1), (key2726, -1), (key2671, -1), (key2829, -1), (key2809, -1), (key2829, 1), (key2616, 1), (key2870, 1), (key2786, 1), (key2870, -1), (key2632, -1)]

def rawRow500 : Integer.Sparse Key := [(key2977, -2), (key2984, 1), (key2992, 1), (key2944, 2), (key2961, -1), (key2992, -1), (key2939, -1), (key2944, -1), (key2951, 1), (key2977, 1), (key2898, 2), (key2905, -1), (key2913, -1), (key2654, -2), (key2748, 1), (key2913, 1), (key2649, 1), (key2654, 1), (key2738, -1), (key2898, -1), (key2796, -2), (key2832, 1), (key2883, 1), (key2642, 2), (key2729, -1), (key2883, -1), (key2619, -1), (key2642, -1), (key2674, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2809, -1), (key2860, -1), (key2632, -1), (key2640, -1), (key2706, 1), (key2860, 1), (key2616, 1), (key2640, 1), (key2671, -1), (key2794, -1)]

def rawRow501 : Integer.Sparse Key := [(key2977, -2), (key2992, 1), (key2984, 1), (key2944, 2), (key2992, -1), (key2961, -1), (key2944, -1), (key2939, -1), (key2977, 1), (key2951, 1), (key2898, 2), (key2913, -1), (key2905, -1), (key2654, -2), (key2913, 1), (key2748, 1), (key2654, 1), (key2649, 1), (key2898, -1), (key2738, -1), (key2796, -2), (key2883, 1), (key2832, 1), (key2642, 2), (key2883, -1), (key2729, -1), (key2642, -1), (key2619, -1), (key2796, 1), (key2674, 1), (key2794, 1), (key2786, 1), (key2860, -1), (key2809, -1), (key2640, -1), (key2632, -1), (key2860, 1), (key2706, 1), (key2640, 1), (key2616, 1), (key2794, -1), (key2671, -1)]

def rawRow502 : Integer.Sparse Key := [(key2984, -2), (key2977, 1), (key2992, 1), (key2961, 2), (key2944, -1), (key2992, -1), (key2951, -1), (key2961, -1), (key2939, 1), (key2984, 1), (key2905, 2), (key2898, -1), (key2913, -1), (key2748, -2), (key2654, 1), (key2913, 1), (key2738, 1), (key2748, 1), (key2649, -1), (key2905, -1), (key2832, -2), (key2796, 1), (key2883, 1), (key2729, 2), (key2642, -1), (key2883, -1), (key2674, -1), (key2729, -1), (key2619, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2786, -1), (key2870, -1), (key2706, -1), (key2726, -1), (key2632, 1), (key2870, 1), (key2671, 1), (key2726, 1), (key2616, -1), (key2829, -1)]

def rawRow503 : Integer.Sparse Key := [(key2984, -2), (key2992, 1), (key2977, 1), (key2961, 2), (key2992, -1), (key2944, -1), (key2961, -1), (key2951, -1), (key2984, 1), (key2939, 1), (key2905, 2), (key2913, -1), (key2898, -1), (key2748, -2), (key2913, 1), (key2654, 1), (key2748, 1), (key2738, 1), (key2905, -1), (key2649, -1), (key2832, -2), (key2883, 1), (key2796, 1), (key2729, 2), (key2883, -1), (key2642, -1), (key2729, -1), (key2674, -1), (key2832, 1), (key2619, 1), (key2829, 1), (key2809, 1), (key2870, -1), (key2786, -1), (key2726, -1), (key2706, -1), (key2870, 1), (key2632, 1), (key2726, 1), (key2671, 1), (key2829, -1), (key2616, -1)]

def rawRow504 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2613, 2), (key2625, 1), (key2629, 1), (key2629, -1), (key2647, -1), (key2637, -2), (key2637, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2668, -2), (key2779, -1), (key2783, -1), (key2783, 1), (key2937, 1), (key2791, 2), (key2791, -1), (key2942, -1), (key2699, -1), (key2703, -1), (key2703, 1), (key2736, 1), (key2802, 1), (key2806, 1), (key2806, -1), (key2949, -1), (key2857, -1), (key2896, -1), (key2857, 1), (key2975, 1), (key2723, 2), (key2723, -1), (key2746, -1), (key2826, -2), (key2826, 1), (key2959, 1), (key2867, 1), (key2903, 1), (key2867, -1), (key2982, -1)]

def rawRow505 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2613, 2), (key2629, 1), (key2625, 1), (key2647, -1), (key2629, -1), (key2637, -2), (key2652, 1), (key2637, 1), (key2668, 1), (key2664, 1), (key2668, -2), (key2783, -1), (key2779, -1), (key2937, 1), (key2783, 1), (key2791, 2), (key2942, -1), (key2791, -1), (key2703, -1), (key2699, -1), (key2736, 1), (key2703, 1), (key2806, 1), (key2802, 1), (key2949, -1), (key2806, -1), (key2896, -1), (key2857, -1), (key2975, 1), (key2857, 1), (key2723, 2), (key2746, -1), (key2723, -1), (key2826, -2), (key2959, 1), (key2826, 1), (key2903, 1), (key2867, 1), (key2982, -1), (key2867, -1)]

def rawRow506 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2609, 2), (key2647, 1), (key2647, 1), (key2625, -1), (key2625, -1), (key2652, -2), (key2637, 1), (key2637, 1), (key2668, 1), (key2668, 1), (key2664, -2), (key2937, -1), (key2937, -1), (key2779, 1), (key2779, 1), (key2942, 2), (key2791, -1), (key2791, -1), (key2736, -1), (key2736, -1), (key2699, 1), (key2699, 1), (key2949, 1), (key2949, 1), (key2802, -1), (key2802, -1), (key2975, -1), (key2975, -1), (key2896, 1), (key2896, 1), (key2746, 2), (key2723, -1), (key2723, -1), (key2959, -2), (key2826, 1), (key2826, 1), (key2982, 1), (key2982, 1), (key2903, -1), (key2903, -1)]

def rawRow507 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2637, 2), (key2609, 1), (key2613, 1), (key2637, -1), (key2652, -1), (key2613, -2), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2791, -2), (key2664, -1), (key2668, -1), (key2791, 1), (key2942, 1), (key2668, 2), (key2783, -1), (key2937, -1), (key2802, -1), (key2806, -1), (key2857, 1), (key2896, 1), (key2699, 1), (key2703, 1), (key2857, -1), (key2975, -1), (key2703, -1), (key2736, -1), (key2806, 1), (key2949, 1), (key2826, 2), (key2867, -1), (key2903, -1), (key2723, -2), (key2867, 1), (key2982, 1), (key2723, 1), (key2746, 1), (key2826, -1), (key2959, -1)]

def rawRow508 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2637, 2), (key2613, 1), (key2609, 1), (key2652, -1), (key2637, -1), (key2613, -2), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2791, -2), (key2668, -1), (key2664, -1), (key2942, 1), (key2791, 1), (key2668, 2), (key2937, -1), (key2783, -1), (key2806, -1), (key2802, -1), (key2896, 1), (key2857, 1), (key2703, 1), (key2699, 1), (key2975, -1), (key2857, -1), (key2736, -1), (key2703, -1), (key2949, 1), (key2806, 1), (key2826, 2), (key2903, -1), (key2867, -1), (key2723, -2), (key2982, 1), (key2867, 1), (key2746, 1), (key2723, 1), (key2959, -1), (key2826, -1)]

def rawRow509 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2625, 2), (key2647, 1), (key2652, 1), (key2609, -1), (key2625, -1), (key2647, -2), (key2613, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2779, -2), (key2937, -1), (key2942, -1), (key2664, 1), (key2779, 1), (key2937, 2), (key2668, -1), (key2783, -1), (key2894, -1), (key2896, -1), (key2802, 1), (key2852, 1), (key2973, 1), (key2975, 1), (key2699, -1), (key2852, -1), (key2949, -1), (key2973, -1), (key2736, 1), (key2894, 1), (key2903, 2), (key2826, -1), (key2867, -1), (key2982, -2), (key2723, 1), (key2867, 1), (key2959, 1), (key2982, 1), (key2746, -1), (key2903, -1)]

def rawRow510 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2625, 2), (key2652, 1), (key2647, 1), (key2625, -1), (key2609, -1), (key2647, -2), (key2629, 1), (key2613, 1), (key2791, 1), (key2783, 1), (key2779, -2), (key2942, -1), (key2937, -1), (key2779, 1), (key2664, 1), (key2937, 2), (key2783, -1), (key2668, -1), (key2896, -1), (key2894, -1), (key2852, 1), (key2802, 1), (key2975, 1), (key2973, 1), (key2852, -1), (key2699, -1), (key2973, -1), (key2949, -1), (key2894, 1), (key2736, 1), (key2903, 2), (key2867, -1), (key2826, -1), (key2982, -2), (key2867, 1), (key2723, 1), (key2982, 1), (key2959, 1), (key2903, -1), (key2746, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3705 : Integer.Sparse Key := [(key1296, -2), (key1798, -2), (key1788, -2), (key1302, 1), (key1296, 1), (key1596, 1), (key1573, 1), (key1798, 1), (key1790, 1), (key1316, 2), (key1825, 2), (key1813, 2), (key1329, -1), (key1316, -1), (key1447, -1), (key1424, -1), (key1825, -1), (key1817, -1), (key1339, -1), (key1337, -1), (key1667, -1), (key1655, -1), (key1844, -1), (key1839, -1), (key1345, 1), (key1337, 1), (key1466, 1), (key1455, 1), (key1844, 1), (key1841, 1)]

def rawRow3706 : Integer.Sparse Key := [(key1788, -2), (key1296, -2), (key1798, -2), (key1573, 1), (key1790, 1), (key1296, 1), (key1798, 1), (key1302, 1), (key1596, 1), (key1813, 2), (key1316, 2), (key1825, 2), (key1424, -1), (key1817, -1), (key1316, -1), (key1825, -1), (key1329, -1), (key1447, -1), (key1655, -1), (key1839, -1), (key1337, -1), (key1844, -1), (key1339, -1), (key1667, -1), (key1455, 1), (key1841, 1), (key1337, 1), (key1844, 1), (key1345, 1), (key1466, 1)]

def rawRow3707 : Integer.Sparse Key := [(key1788, -2), (key1798, -2), (key1296, -2), (key1790, 1), (key1573, 1), (key1798, 1), (key1296, 1), (key1596, 1), (key1302, 1), (key1813, 2), (key1825, 2), (key1316, 2), (key1817, -1), (key1424, -1), (key1825, -1), (key1316, -1), (key1447, -1), (key1329, -1), (key1839, -1), (key1655, -1), (key1844, -1), (key1337, -1), (key1667, -1), (key1339, -1), (key1841, 1), (key1455, 1), (key1844, 1), (key1337, 1), (key1466, 1), (key1345, 1)]

def rawRow3708 : Integer.Sparse Key := [(key1798, -2), (key1296, -2), (key1788, -2), (key1596, 1), (key1798, 1), (key1302, 1), (key1790, 1), (key1296, 1), (key1573, 1), (key1825, 2), (key1316, 2), (key1813, 2), (key1447, -1), (key1825, -1), (key1329, -1), (key1817, -1), (key1316, -1), (key1424, -1), (key1667, -1), (key1844, -1), (key1339, -1), (key1839, -1), (key1337, -1), (key1655, -1), (key1466, 1), (key1844, 1), (key1345, 1), (key1841, 1), (key1337, 1), (key1455, 1)]

def rawRow3709 : Integer.Sparse Key := [(key1798, -2), (key1788, -2), (key1296, -2), (key1798, 1), (key1596, 1), (key1790, 1), (key1302, 1), (key1573, 1), (key1296, 1), (key1825, 2), (key1813, 2), (key1316, 2), (key1825, -1), (key1447, -1), (key1817, -1), (key1329, -1), (key1424, -1), (key1316, -1), (key1844, -1), (key1667, -1), (key1839, -1), (key1339, -1), (key1655, -1), (key1337, -1), (key1844, 1), (key1466, 1), (key1841, 1), (key1345, 1), (key1455, 1), (key1337, 1)]

def rawRow3710 : Integer.Sparse Key := [(key1302, -2), (key1790, -2), (key1790, -2), (key1296, 1), (key1296, 1), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1329, 2), (key1817, 2), (key1817, 2), (key1316, -1), (key1316, -1), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1345, -1), (key1345, -1), (key1659, -1), (key1659, -1), (key1841, -1), (key1841, -1), (key1339, 1), (key1339, 1), (key1457, 1), (key1457, 1), (key1839, 1), (key1839, 1)]

def rawRow3711 : Integer.Sparse Key := [(key1790, -2), (key1302, -2), (key1790, -2), (key1573, 1), (key1788, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1817, 2), (key1329, 2), (key1817, 2), (key1424, -1), (key1813, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1659, -1), (key1841, -1), (key1345, -1), (key1841, -1), (key1345, -1), (key1659, -1), (key1457, 1), (key1839, 1), (key1339, 1), (key1839, 1), (key1339, 1), (key1457, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3712 : Integer.Sparse Key := [(key1790, -2), (key1790, -2), (key1302, -2), (key1788, 1), (key1573, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1296, 1), (key1817, 2), (key1817, 2), (key1329, 2), (key1813, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1316, -1), (key1841, -1), (key1659, -1), (key1841, -1), (key1345, -1), (key1659, -1), (key1345, -1), (key1839, 1), (key1457, 1), (key1839, 1), (key1339, 1), (key1457, 1), (key1339, 1)]

def rawRow3713 : Integer.Sparse Key := [(key1316, -2), (key1813, -2), (key1825, -2), (key1337, 1), (key1339, 1), (key1655, 1), (key1667, 1), (key1839, 1), (key1844, 1), (key1296, 2), (key1788, 2), (key1798, 2), (key1337, -1), (key1345, -1), (key1455, -1), (key1466, -1), (key1841, -1), (key1844, -1), (key1296, -1), (key1302, -1), (key1573, -1), (key1596, -1), (key1790, -1), (key1798, -1), (key1316, 1), (key1329, 1), (key1424, 1), (key1447, 1), (key1817, 1), (key1825, 1)]

def rawRow3714 : Integer.Sparse Key := [(key1316, -2), (key1825, -2), (key1813, -2), (key1339, 1), (key1337, 1), (key1667, 1), (key1655, 1), (key1844, 1), (key1839, 1), (key1296, 2), (key1798, 2), (key1788, 2), (key1345, -1), (key1337, -1), (key1466, -1), (key1455, -1), (key1844, -1), (key1841, -1), (key1302, -1), (key1296, -1), (key1596, -1), (key1573, -1), (key1798, -1), (key1790, -1), (key1329, 1), (key1316, 1), (key1447, 1), (key1424, 1), (key1825, 1), (key1817, 1)]

def rawRow3715 : Integer.Sparse Key := [(key1813, -2), (key1316, -2), (key1825, -2), (key1655, 1), (key1839, 1), (key1337, 1), (key1844, 1), (key1339, 1), (key1667, 1), (key1788, 2), (key1296, 2), (key1798, 2), (key1455, -1), (key1841, -1), (key1337, -1), (key1844, -1), (key1345, -1), (key1466, -1), (key1573, -1), (key1790, -1), (key1296, -1), (key1798, -1), (key1302, -1), (key1596, -1), (key1424, 1), (key1817, 1), (key1316, 1), (key1825, 1), (key1329, 1), (key1447, 1)]

def rawRow3716 : Integer.Sparse Key := [(key1813, -2), (key1825, -2), (key1316, -2), (key1839, 1), (key1655, 1), (key1844, 1), (key1337, 1), (key1667, 1), (key1339, 1), (key1788, 2), (key1798, 2), (key1296, 2), (key1841, -1), (key1455, -1), (key1844, -1), (key1337, -1), (key1466, -1), (key1345, -1), (key1790, -1), (key1573, -1), (key1798, -1), (key1296, -1), (key1596, -1), (key1302, -1), (key1817, 1), (key1424, 1), (key1825, 1), (key1316, 1), (key1447, 1), (key1329, 1)]

def rawRow3717 : Integer.Sparse Key := [(key1825, -2), (key1316, -2), (key1813, -2), (key1667, 1), (key1844, 1), (key1339, 1), (key1839, 1), (key1337, 1), (key1655, 1), (key1798, 2), (key1296, 2), (key1788, 2), (key1466, -1), (key1844, -1), (key1345, -1), (key1841, -1), (key1337, -1), (key1455, -1), (key1596, -1), (key1798, -1), (key1302, -1), (key1790, -1), (key1296, -1), (key1573, -1), (key1447, 1), (key1825, 1), (key1329, 1), (key1817, 1), (key1316, 1), (key1424, 1)]

def rawRow3718 : Integer.Sparse Key := [(key1825, -2), (key1813, -2), (key1316, -2), (key1844, 1), (key1667, 1), (key1839, 1), (key1339, 1), (key1655, 1), (key1337, 1), (key1798, 2), (key1788, 2), (key1296, 2), (key1844, -1), (key1466, -1), (key1841, -1), (key1345, -1), (key1455, -1), (key1337, -1), (key1798, -1), (key1596, -1), (key1790, -1), (key1302, -1), (key1573, -1), (key1296, -1), (key1825, 1), (key1447, 1), (key1817, 1), (key1329, 1), (key1424, 1), (key1316, 1)]

def rawRow3719 : Integer.Sparse Key := [(key1339, -2), (key1774, -2), (key1839, -2), (key1316, 1), (key1337, 1), (key1546, 1), (key1655, 1), (key1772, 1), (key1813, 1), (key1345, 2), (key1780, 2), (key1841, 2), (key1296, -1), (key1337, -1), (key1391, -1), (key1455, -1), (key1772, -1), (key1788, -1), (key1329, -1), (key1345, -1), (key1559, -1), (key1659, -1), (key1780, -1), (key1817, -1), (key1302, 1), (key1339, 1), (key1397, 1), (key1457, 1), (key1774, 1), (key1790, 1)]

def rawRow3720 : Integer.Sparse Key := [(key1339, -2), (key1839, -2), (key1774, -2), (key1337, 1), (key1316, 1), (key1655, 1), (key1546, 1), (key1813, 1), (key1772, 1), (key1345, 2), (key1841, 2), (key1780, 2), (key1337, -1), (key1296, -1), (key1455, -1), (key1391, -1), (key1788, -1), (key1772, -1), (key1345, -1), (key1329, -1), (key1659, -1), (key1559, -1), (key1817, -1), (key1780, -1), (key1339, 1), (key1302, 1), (key1457, 1), (key1397, 1), (key1790, 1), (key1774, 1)]

def rawRow3721 : Integer.Sparse Key := [(key1774, -2), (key1339, -2), (key1839, -2), (key1546, 1), (key1772, 1), (key1316, 1), (key1813, 1), (key1337, 1), (key1655, 1), (key1780, 2), (key1345, 2), (key1841, 2), (key1391, -1), (key1772, -1), (key1296, -1), (key1788, -1), (key1337, -1), (key1455, -1), (key1559, -1), (key1780, -1), (key1329, -1), (key1817, -1), (key1345, -1), (key1659, -1), (key1397, 1), (key1774, 1), (key1302, 1), (key1790, 1), (key1339, 1), (key1457, 1)]

def rawRow3722 : Integer.Sparse Key := [(key1774, -2), (key1839, -2), (key1339, -2), (key1772, 1), (key1546, 1), (key1813, 1), (key1316, 1), (key1655, 1), (key1337, 1), (key1780, 2), (key1841, 2), (key1345, 2), (key1772, -1), (key1391, -1), (key1788, -1), (key1296, -1), (key1455, -1), (key1337, -1), (key1780, -1), (key1559, -1), (key1817, -1), (key1329, -1), (key1659, -1), (key1345, -1), (key1774, 1), (key1397, 1), (key1790, 1), (key1302, 1), (key1457, 1), (key1339, 1)]

def rawRow3723 : Integer.Sparse Key := [(key1839, -2), (key1339, -2), (key1774, -2), (key1655, 1), (key1813, 1), (key1337, 1), (key1772, 1), (key1316, 1), (key1546, 1), (key1841, 2), (key1345, 2), (key1780, 2), (key1455, -1), (key1788, -1), (key1337, -1), (key1772, -1), (key1296, -1), (key1391, -1), (key1659, -1), (key1817, -1), (key1345, -1), (key1780, -1), (key1329, -1), (key1559, -1), (key1457, 1), (key1790, 1), (key1339, 1), (key1774, 1), (key1302, 1), (key1397, 1)]

def rawRow3724 : Integer.Sparse Key := [(key1839, -2), (key1774, -2), (key1339, -2), (key1813, 1), (key1655, 1), (key1772, 1), (key1337, 1), (key1546, 1), (key1316, 1), (key1841, 2), (key1780, 2), (key1345, 2), (key1788, -1), (key1455, -1), (key1772, -1), (key1337, -1), (key1391, -1), (key1296, -1), (key1817, -1), (key1659, -1), (key1780, -1), (key1345, -1), (key1559, -1), (key1329, -1), (key1790, 1), (key1457, 1), (key1774, 1), (key1339, 1), (key1397, 1), (key1302, 1)]

def rawRow3725 : Integer.Sparse Key := [(key1329, -2), (key1817, -2), (key1817, -2), (key1345, 1), (key1345, 1), (key1659, 1), (key1659, 1), (key1841, 1), (key1841, 1), (key1302, 2), (key1790, 2), (key1790, 2), (key1339, -1), (key1339, -1), (key1457, -1), (key1457, -1), (key1839, -1), (key1839, -1), (key1296, -1), (key1296, -1), (key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1316, 1), (key1316, 1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1)]

def rawRow3726 : Integer.Sparse Key := [(key1817, -2), (key1329, -2), (key1817, -2), (key1659, 1), (key1841, 1), (key1345, 1), (key1841, 1), (key1345, 1), (key1659, 1), (key1790, 2), (key1302, 2), (key1790, 2), (key1457, -1), (key1839, -1), (key1339, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1424, 1), (key1813, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1424, 1)]

def rawRow3727 : Integer.Sparse Key := [(key1817, -2), (key1817, -2), (key1329, -2), (key1841, 1), (key1659, 1), (key1841, 1), (key1345, 1), (key1659, 1), (key1345, 1), (key1790, 2), (key1790, 2), (key1302, 2), (key1839, -1), (key1457, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1339, -1), (key1788, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1296, -1), (key1813, 1), (key1424, 1), (key1813, 1), (key1316, 1), (key1424, 1), (key1316, 1)]

def rawRow3728 : Integer.Sparse Key := [(key1345, -2), (key1780, -2), (key1841, -2), (key1329, 1), (key1345, 1), (key1559, 1), (key1659, 1), (key1780, 1), (key1817, 1), (key1339, 2), (key1774, 2), (key1839, 2), (key1302, -1), (key1339, -1), (key1397, -1), (key1457, -1), (key1774, -1), (key1790, -1), (key1316, -1), (key1337, -1), (key1546, -1), (key1655, -1), (key1772, -1), (key1813, -1), (key1296, 1), (key1337, 1), (key1391, 1), (key1455, 1), (key1772, 1), (key1788, 1)]

def rawRow3729 : Integer.Sparse Key := [(key1345, -2), (key1841, -2), (key1780, -2), (key1345, 1), (key1329, 1), (key1659, 1), (key1559, 1), (key1817, 1), (key1780, 1), (key1339, 2), (key1839, 2), (key1774, 2), (key1339, -1), (key1302, -1), (key1457, -1), (key1397, -1), (key1790, -1), (key1774, -1), (key1337, -1), (key1316, -1), (key1655, -1), (key1546, -1), (key1813, -1), (key1772, -1), (key1337, 1), (key1296, 1), (key1455, 1), (key1391, 1), (key1788, 1), (key1772, 1)]

def rawRow3730 : Integer.Sparse Key := [(key1780, -2), (key1345, -2), (key1841, -2), (key1559, 1), (key1780, 1), (key1329, 1), (key1817, 1), (key1345, 1), (key1659, 1), (key1774, 2), (key1339, 2), (key1839, 2), (key1397, -1), (key1774, -1), (key1302, -1), (key1790, -1), (key1339, -1), (key1457, -1), (key1546, -1), (key1772, -1), (key1316, -1), (key1813, -1), (key1337, -1), (key1655, -1), (key1391, 1), (key1772, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1455, 1)]

def rawRow3731 : Integer.Sparse Key := [(key1780, -2), (key1841, -2), (key1345, -2), (key1780, 1), (key1559, 1), (key1817, 1), (key1329, 1), (key1659, 1), (key1345, 1), (key1774, 2), (key1839, 2), (key1339, 2), (key1774, -1), (key1397, -1), (key1790, -1), (key1302, -1), (key1457, -1), (key1339, -1), (key1772, -1), (key1546, -1), (key1813, -1), (key1316, -1), (key1655, -1), (key1337, -1), (key1772, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1455, 1), (key1337, 1)]

def rawRow3732 : Integer.Sparse Key := [(key1841, -2), (key1345, -2), (key1780, -2), (key1659, 1), (key1817, 1), (key1345, 1), (key1780, 1), (key1329, 1), (key1559, 1), (key1839, 2), (key1339, 2), (key1774, 2), (key1457, -1), (key1790, -1), (key1339, -1), (key1774, -1), (key1302, -1), (key1397, -1), (key1655, -1), (key1813, -1), (key1337, -1), (key1772, -1), (key1316, -1), (key1546, -1), (key1455, 1), (key1788, 1), (key1337, 1), (key1772, 1), (key1296, 1), (key1391, 1)]

def rawRow3733 : Integer.Sparse Key := [(key1841, -2), (key1780, -2), (key1345, -2), (key1817, 1), (key1659, 1), (key1780, 1), (key1345, 1), (key1559, 1), (key1329, 1), (key1839, 2), (key1774, 2), (key1339, 2), (key1790, -1), (key1457, -1), (key1774, -1), (key1339, -1), (key1397, -1), (key1302, -1), (key1813, -1), (key1655, -1), (key1772, -1), (key1337, -1), (key1546, -1), (key1316, -1), (key1788, 1), (key1455, 1), (key1772, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

def rawRow3735 : Integer.Sparse Key := [(key384, -6), (key301, 2), (key393, 2), (key384, 2), (key405, 6), (key235, -2), (key416, -2), (key405, -2), (key315, -2), (key438, -2), (key434, -2), (key247, 2), (key448, 2), (key434, 2)]

def rawRow3736 : Integer.Sparse Key := [(key384, -6), (key384, 2), (key301, 2), (key393, 2), (key405, 6), (key405, -2), (key235, -2), (key416, -2), (key434, -2), (key315, -2), (key438, -2), (key434, 2), (key247, 2), (key448, 2)]

def rawRow3737 : Integer.Sparse Key := [(key384, -6), (key384, 2), (key393, 2), (key301, 2), (key405, 6), (key405, -2), (key416, -2), (key235, -2), (key434, -2), (key438, -2), (key315, -2), (key434, 2), (key448, 2), (key247, 2)]

def rawRow3738 : Integer.Sparse Key := [(key384, -6), (key393, 2), (key301, 2), (key384, 2), (key405, 6), (key416, -2), (key235, -2), (key405, -2), (key438, -2), (key315, -2), (key434, -2), (key448, 2), (key247, 2), (key434, 2)]

def rawRow3739 : Integer.Sparse Key := [(key384, -6), (key393, 2), (key384, 2), (key301, 2), (key405, 6), (key416, -2), (key405, -2), (key235, -2), (key438, -2), (key434, -2), (key315, -2), (key448, 2), (key434, 2), (key247, 2)]

def rawRow3740 : Integer.Sparse Key := [(key393, -6), (key301, 2), (key384, 2), (key384, 2), (key416, 6), (key235, -2), (key405, -2), (key405, -2), (key326, -2), (key448, -2), (key448, -2), (key256, 2), (key438, 2), (key438, 2)]

def rawRow3741 : Integer.Sparse Key := [(key393, -6), (key384, 2), (key301, 2), (key384, 2), (key416, 6), (key405, -2), (key235, -2), (key405, -2), (key448, -2), (key326, -2), (key448, -2), (key438, 2), (key256, 2), (key438, 2)]

def rawRow3742 : Integer.Sparse Key := [(key393, -6), (key384, 2), (key384, 2), (key301, 2), (key416, 6), (key405, -2), (key405, -2), (key235, -2), (key448, -2), (key448, -2), (key326, -2), (key438, 2), (key438, 2), (key256, 2)]

def rawRow3743 : Integer.Sparse Key := [(key405, -6), (key315, 2), (key434, 2), (key438, 2), (key384, 6), (key247, -2), (key434, -2), (key448, -2), (key301, -2), (key384, -2), (key393, -2), (key235, 2), (key405, 2), (key416, 2)]

def rawRow3744 : Integer.Sparse Key := [(key405, -6), (key315, 2), (key438, 2), (key434, 2), (key384, 6), (key247, -2), (key448, -2), (key434, -2), (key301, -2), (key393, -2), (key384, -2), (key235, 2), (key416, 2), (key405, 2)]

def rawRow3745 : Integer.Sparse Key := [(key405, -6), (key434, 2), (key315, 2), (key438, 2), (key384, 6), (key434, -2), (key247, -2), (key448, -2), (key384, -2), (key301, -2), (key393, -2), (key405, 2), (key235, 2), (key416, 2)]

def rawRow3746 : Integer.Sparse Key := [(key405, -6), (key434, 2), (key438, 2), (key315, 2), (key384, 6), (key434, -2), (key448, -2), (key247, -2), (key384, -2), (key393, -2), (key301, -2), (key405, 2), (key416, 2), (key235, 2)]

def rawRow3747 : Integer.Sparse Key := [(key405, -6), (key438, 2), (key315, 2), (key434, 2), (key384, 6), (key448, -2), (key247, -2), (key434, -2), (key393, -2), (key301, -2), (key384, -2), (key416, 2), (key235, 2), (key405, 2)]

def rawRow3748 : Integer.Sparse Key := [(key405, -6), (key438, 2), (key434, 2), (key315, 2), (key384, 6), (key448, -2), (key434, -2), (key247, -2), (key393, -2), (key384, -2), (key301, -2), (key416, 2), (key405, 2), (key235, 2)]

def rawRow3749 : Integer.Sparse Key := [(key438, -6), (key315, 2), (key405, 2), (key434, 2), (key448, 6), (key247, -2), (key384, -2), (key434, -2), (key326, -2), (key416, -2), (key448, -2), (key256, 2), (key393, 2), (key438, 2)]

def rawRow3750 : Integer.Sparse Key := [(key438, -6), (key315, 2), (key434, 2), (key405, 2), (key448, 6), (key247, -2), (key434, -2), (key384, -2), (key326, -2), (key448, -2), (key416, -2), (key256, 2), (key438, 2), (key393, 2)]

def rawRow3751 : Integer.Sparse Key := [(key438, -6), (key405, 2), (key315, 2), (key434, 2), (key448, 6), (key384, -2), (key247, -2), (key434, -2), (key416, -2), (key326, -2), (key448, -2), (key393, 2), (key256, 2), (key438, 2)]

def rawRow3752 : Integer.Sparse Key := [(key438, -6), (key405, 2), (key434, 2), (key315, 2), (key448, 6), (key384, -2), (key434, -2), (key247, -2), (key416, -2), (key448, -2), (key326, -2), (key393, 2), (key438, 2), (key256, 2)]

def rawRow3753 : Integer.Sparse Key := [(key438, -6), (key434, 2), (key315, 2), (key405, 2), (key448, 6), (key434, -2), (key247, -2), (key384, -2), (key448, -2), (key326, -2), (key416, -2), (key438, 2), (key256, 2), (key393, 2)]

def rawRow3754 : Integer.Sparse Key := [(key438, -6), (key434, 2), (key405, 2), (key315, 2), (key448, 6), (key434, -2), (key384, -2), (key247, -2), (key448, -2), (key416, -2), (key326, -2), (key438, 2), (key393, 2), (key256, 2)]

def rawRow3755 : Integer.Sparse Key := [(key416, -6), (key326, 2), (key448, 2), (key448, 2), (key393, 6), (key256, -2), (key438, -2), (key438, -2), (key301, -2), (key384, -2), (key384, -2), (key235, 2), (key405, 2), (key405, 2)]

def rawRow3756 : Integer.Sparse Key := [(key416, -6), (key448, 2), (key326, 2), (key448, 2), (key393, 6), (key438, -2), (key256, -2), (key438, -2), (key384, -2), (key301, -2), (key384, -2), (key405, 2), (key235, 2), (key405, 2)]

def rawRow3757 : Integer.Sparse Key := [(key416, -6), (key448, 2), (key448, 2), (key326, 2), (key393, 6), (key438, -2), (key438, -2), (key256, -2), (key384, -2), (key384, -2), (key301, -2), (key405, 2), (key405, 2), (key235, 2)]

def rawRow3758 : Integer.Sparse Key := [(key448, -6), (key326, 2), (key416, 2), (key448, 2), (key438, 6), (key256, -2), (key393, -2), (key438, -2), (key315, -2), (key405, -2), (key434, -2), (key247, 2), (key384, 2), (key434, 2)]

def rawRow3759 : Integer.Sparse Key := [(key448, -6), (key326, 2), (key448, 2), (key416, 2), (key438, 6), (key256, -2), (key438, -2), (key393, -2), (key315, -2), (key434, -2), (key405, -2), (key247, 2), (key434, 2), (key384, 2)]

def rawRow3760 : Integer.Sparse Key := [(key448, -6), (key416, 2), (key326, 2), (key448, 2), (key438, 6), (key393, -2), (key256, -2), (key438, -2), (key405, -2), (key315, -2), (key434, -2), (key384, 2), (key247, 2), (key434, 2)]

def rawRow3761 : Integer.Sparse Key := [(key448, -6), (key416, 2), (key448, 2), (key326, 2), (key438, 6), (key393, -2), (key438, -2), (key256, -2), (key405, -2), (key434, -2), (key315, -2), (key384, 2), (key434, 2), (key247, 2)]

def rawRow3762 : Integer.Sparse Key := [(key448, -6), (key448, 2), (key326, 2), (key416, 2), (key438, 6), (key438, -2), (key256, -2), (key393, -2), (key434, -2), (key315, -2), (key405, -2), (key434, 2), (key247, 2), (key384, 2)]

def rawRow3763 : Integer.Sparse Key := [(key448, -6), (key448, 2), (key416, 2), (key326, 2), (key438, 6), (key438, -2), (key393, -2), (key256, -2), (key434, -2), (key405, -2), (key315, -2), (key434, 2), (key384, 2), (key247, 2)]

def rawRow3764 : Integer.Sparse Key := [(key1542, -2), (key1548, -2), (key1896, -2), (key1387, 1), (key1393, 1), (key1542, 1), (key1556, 1), (key1896, 1), (key1899, 1), (key1569, 2), (key1575, 2), (key1903, 2), (key1292, -1), (key1298, -1), (key1569, -1), (key1593, -1), (key1903, -1), (key1911, -1), (key1420, -1), (key1426, -1), (key1618, -1), (key1624, -1), (key1918, -1), (key1920, -1), (key1312, 1), (key1318, 1), (key1618, 1), (key1633, 1), (key1918, 1), (key1926, 1)]

def rawRow3765 : Integer.Sparse Key := [(key1548, -2), (key1542, -2), (key1896, -2), (key1393, 1), (key1387, 1), (key1556, 1), (key1542, 1), (key1899, 1), (key1896, 1), (key1575, 2), (key1569, 2), (key1903, 2), (key1298, -1), (key1292, -1), (key1593, -1), (key1569, -1), (key1911, -1), (key1903, -1), (key1426, -1), (key1420, -1), (key1624, -1), (key1618, -1), (key1920, -1), (key1918, -1), (key1318, 1), (key1312, 1), (key1633, 1), (key1618, 1), (key1926, 1), (key1918, 1)]

def rawRow3766 : Integer.Sparse Key := [(key1542, -2), (key1896, -2), (key1548, -2), (key1542, 1), (key1896, 1), (key1387, 1), (key1899, 1), (key1393, 1), (key1556, 1), (key1569, 2), (key1903, 2), (key1575, 2), (key1569, -1), (key1903, -1), (key1292, -1), (key1911, -1), (key1298, -1), (key1593, -1), (key1618, -1), (key1918, -1), (key1420, -1), (key1920, -1), (key1426, -1), (key1624, -1), (key1618, 1), (key1918, 1), (key1312, 1), (key1926, 1), (key1318, 1), (key1633, 1)]

def rawRow3767 : Integer.Sparse Key := [(key1896, -2), (key1542, -2), (key1548, -2), (key1896, 1), (key1542, 1), (key1899, 1), (key1387, 1), (key1556, 1), (key1393, 1), (key1903, 2), (key1569, 2), (key1575, 2), (key1903, -1), (key1569, -1), (key1911, -1), (key1292, -1), (key1593, -1), (key1298, -1), (key1918, -1), (key1618, -1), (key1920, -1), (key1420, -1), (key1624, -1), (key1426, -1), (key1918, 1), (key1618, 1), (key1926, 1), (key1312, 1), (key1633, 1), (key1318, 1)]

def rawRow3768 : Integer.Sparse Key := [(key1548, -2), (key1896, -2), (key1542, -2), (key1556, 1), (key1899, 1), (key1393, 1), (key1896, 1), (key1387, 1), (key1542, 1), (key1575, 2), (key1903, 2), (key1569, 2), (key1593, -1), (key1911, -1), (key1298, -1), (key1903, -1), (key1292, -1), (key1569, -1), (key1624, -1), (key1920, -1), (key1426, -1), (key1918, -1), (key1420, -1), (key1618, -1), (key1633, 1), (key1926, 1), (key1318, 1), (key1918, 1), (key1312, 1), (key1618, 1)]

def rawRow3769 : Integer.Sparse Key := [(key1896, -2), (key1548, -2), (key1542, -2), (key1899, 1), (key1556, 1), (key1896, 1), (key1393, 1), (key1542, 1), (key1387, 1), (key1903, 2), (key1575, 2), (key1569, 2), (key1911, -1), (key1593, -1), (key1903, -1), (key1298, -1), (key1569, -1), (key1292, -1), (key1920, -1), (key1624, -1), (key1918, -1), (key1426, -1), (key1618, -1), (key1420, -1), (key1926, 1), (key1633, 1), (key1918, 1), (key1318, 1), (key1618, 1), (key1312, 1)]

def rawRow3770 : Integer.Sparse Key := [(key1556, -2), (key1556, -2), (key1899, -2), (key1393, 1), (key1393, 1), (key1548, 1), (key1548, 1), (key1896, 1), (key1896, 1), (key1593, 2), (key1593, 2), (key1911, 2), (key1298, -1), (key1298, -1), (key1575, -1), (key1575, -1), (key1903, -1), (key1903, -1), (key1444, -1), (key1444, -1), (key1633, -1), (key1633, -1), (key1926, -1), (key1926, -1), (key1326, 1), (key1326, 1), (key1624, 1), (key1624, 1), (key1920, 1), (key1920, 1)]

def rawRow3771 : Integer.Sparse Key := [(key1556, -2), (key1899, -2), (key1556, -2), (key1548, 1), (key1896, 1), (key1393, 1), (key1896, 1), (key1393, 1), (key1548, 1), (key1593, 2), (key1911, 2), (key1593, 2), (key1575, -1), (key1903, -1), (key1298, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1633, -1), (key1926, -1), (key1444, -1), (key1926, -1), (key1444, -1), (key1633, -1), (key1624, 1), (key1920, 1), (key1326, 1), (key1920, 1), (key1326, 1), (key1624, 1)]

def rawRow3772 : Integer.Sparse Key := [(key1899, -2), (key1556, -2), (key1556, -2), (key1896, 1), (key1548, 1), (key1896, 1), (key1393, 1), (key1548, 1), (key1393, 1), (key1911, 2), (key1593, 2), (key1593, 2), (key1903, -1), (key1575, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1298, -1), (key1926, -1), (key1633, -1), (key1926, -1), (key1444, -1), (key1633, -1), (key1444, -1), (key1920, 1), (key1624, 1), (key1920, 1), (key1326, 1), (key1624, 1), (key1326, 1)]

def rawRow3773 : Integer.Sparse Key := [(key1569, -2), (key1575, -2), (key1903, -2), (key1420, 1), (key1426, 1), (key1618, 1), (key1624, 1), (key1918, 1), (key1920, 1), (key1542, 2), (key1548, 2), (key1896, 2), (key1312, -1), (key1318, -1), (key1618, -1), (key1633, -1), (key1918, -1), (key1926, -1), (key1387, -1), (key1393, -1), (key1542, -1), (key1556, -1), (key1896, -1), (key1899, -1), (key1292, 1), (key1298, 1), (key1569, 1), (key1593, 1), (key1903, 1), (key1911, 1)]

def rawRow3774 : Integer.Sparse Key := [(key1575, -2), (key1569, -2), (key1903, -2), (key1426, 1), (key1420, 1), (key1624, 1), (key1618, 1), (key1920, 1), (key1918, 1), (key1548, 2), (key1542, 2), (key1896, 2), (key1318, -1), (key1312, -1), (key1633, -1), (key1618, -1), (key1926, -1), (key1918, -1), (key1393, -1), (key1387, -1), (key1556, -1), (key1542, -1), (key1899, -1), (key1896, -1), (key1298, 1), (key1292, 1), (key1593, 1), (key1569, 1), (key1911, 1), (key1903, 1)]

def rawRow3775 : Integer.Sparse Key := [(key1569, -2), (key1903, -2), (key1575, -2), (key1618, 1), (key1918, 1), (key1420, 1), (key1920, 1), (key1426, 1), (key1624, 1), (key1542, 2), (key1896, 2), (key1548, 2), (key1618, -1), (key1918, -1), (key1312, -1), (key1926, -1), (key1318, -1), (key1633, -1), (key1542, -1), (key1896, -1), (key1387, -1), (key1899, -1), (key1393, -1), (key1556, -1), (key1569, 1), (key1903, 1), (key1292, 1), (key1911, 1), (key1298, 1), (key1593, 1)]

def rawRow3776 : Integer.Sparse Key := [(key1903, -2), (key1569, -2), (key1575, -2), (key1918, 1), (key1618, 1), (key1920, 1), (key1420, 1), (key1624, 1), (key1426, 1), (key1896, 2), (key1542, 2), (key1548, 2), (key1918, -1), (key1618, -1), (key1926, -1), (key1312, -1), (key1633, -1), (key1318, -1), (key1896, -1), (key1542, -1), (key1899, -1), (key1387, -1), (key1556, -1), (key1393, -1), (key1903, 1), (key1569, 1), (key1911, 1), (key1292, 1), (key1593, 1), (key1298, 1)]

def rawRow3777 : Integer.Sparse Key := [(key1575, -2), (key1903, -2), (key1569, -2), (key1624, 1), (key1920, 1), (key1426, 1), (key1918, 1), (key1420, 1), (key1618, 1), (key1548, 2), (key1896, 2), (key1542, 2), (key1633, -1), (key1926, -1), (key1318, -1), (key1918, -1), (key1312, -1), (key1618, -1), (key1556, -1), (key1899, -1), (key1393, -1), (key1896, -1), (key1387, -1), (key1542, -1), (key1593, 1), (key1911, 1), (key1298, 1), (key1903, 1), (key1292, 1), (key1569, 1)]

def rawRow3778 : Integer.Sparse Key := [(key1903, -2), (key1575, -2), (key1569, -2), (key1920, 1), (key1624, 1), (key1918, 1), (key1426, 1), (key1618, 1), (key1420, 1), (key1896, 2), (key1548, 2), (key1542, 2), (key1926, -1), (key1633, -1), (key1918, -1), (key1318, -1), (key1618, -1), (key1312, -1), (key1899, -1), (key1556, -1), (key1896, -1), (key1393, -1), (key1542, -1), (key1387, -1), (key1911, 1), (key1593, 1), (key1903, 1), (key1298, 1), (key1569, 1), (key1292, 1)]

def rawRow3779 : Integer.Sparse Key := [(key1624, -2), (key1683, -2), (key1920, -2), (key1426, 1), (key1472, 1), (key1575, 1), (key1681, 1), (key1903, 1), (key1918, 1), (key1633, 2), (key1689, 2), (key1926, 2), (key1318, -1), (key1351, -1), (key1548, -1), (key1681, -1), (key1896, -1), (key1918, -1), (key1444, -1), (key1480, -1), (key1593, -1), (key1689, -1), (key1911, -1), (key1926, -1), (key1326, 1), (key1354, 1), (key1556, 1), (key1683, 1), (key1899, 1), (key1920, 1)]

def rawRow3780 : Integer.Sparse Key := [(key1683, -2), (key1624, -2), (key1920, -2), (key1472, 1), (key1426, 1), (key1681, 1), (key1575, 1), (key1918, 1), (key1903, 1), (key1689, 2), (key1633, 2), (key1926, 2), (key1351, -1), (key1318, -1), (key1681, -1), (key1548, -1), (key1918, -1), (key1896, -1), (key1480, -1), (key1444, -1), (key1689, -1), (key1593, -1), (key1926, -1), (key1911, -1), (key1354, 1), (key1326, 1), (key1683, 1), (key1556, 1), (key1920, 1), (key1899, 1)]

def rawRow3781 : Integer.Sparse Key := [(key1624, -2), (key1920, -2), (key1683, -2), (key1575, 1), (key1903, 1), (key1426, 1), (key1918, 1), (key1472, 1), (key1681, 1), (key1633, 2), (key1926, 2), (key1689, 2), (key1548, -1), (key1896, -1), (key1318, -1), (key1918, -1), (key1351, -1), (key1681, -1), (key1593, -1), (key1911, -1), (key1444, -1), (key1926, -1), (key1480, -1), (key1689, -1), (key1556, 1), (key1899, 1), (key1326, 1), (key1920, 1), (key1354, 1), (key1683, 1)]

def rawRow3782 : Integer.Sparse Key := [(key1920, -2), (key1624, -2), (key1683, -2), (key1903, 1), (key1575, 1), (key1918, 1), (key1426, 1), (key1681, 1), (key1472, 1), (key1926, 2), (key1633, 2), (key1689, 2), (key1896, -1), (key1548, -1), (key1918, -1), (key1318, -1), (key1681, -1), (key1351, -1), (key1911, -1), (key1593, -1), (key1926, -1), (key1444, -1), (key1689, -1), (key1480, -1), (key1899, 1), (key1556, 1), (key1920, 1), (key1326, 1), (key1683, 1), (key1354, 1)]

def rawRow3783 : Integer.Sparse Key := [(key1683, -2), (key1920, -2), (key1624, -2), (key1681, 1), (key1918, 1), (key1472, 1), (key1903, 1), (key1426, 1), (key1575, 1), (key1689, 2), (key1926, 2), (key1633, 2), (key1681, -1), (key1918, -1), (key1351, -1), (key1896, -1), (key1318, -1), (key1548, -1), (key1689, -1), (key1926, -1), (key1480, -1), (key1911, -1), (key1444, -1), (key1593, -1), (key1683, 1), (key1920, 1), (key1354, 1), (key1899, 1), (key1326, 1), (key1556, 1)]

def rawRow3784 : Integer.Sparse Key := [(key1920, -2), (key1683, -2), (key1624, -2), (key1918, 1), (key1681, 1), (key1903, 1), (key1472, 1), (key1575, 1), (key1426, 1), (key1926, 2), (key1689, 2), (key1633, 2), (key1918, -1), (key1681, -1), (key1896, -1), (key1351, -1), (key1548, -1), (key1318, -1), (key1926, -1), (key1689, -1), (key1911, -1), (key1480, -1), (key1593, -1), (key1444, -1), (key1920, 1), (key1683, 1), (key1899, 1), (key1354, 1), (key1556, 1), (key1326, 1)]

def rawRow3785 : Integer.Sparse Key := [(key1593, -2), (key1593, -2), (key1911, -2), (key1444, 1), (key1444, 1), (key1633, 1), (key1633, 1), (key1926, 1), (key1926, 1), (key1556, 2), (key1556, 2), (key1899, 2), (key1326, -1), (key1326, -1), (key1624, -1), (key1624, -1), (key1920, -1), (key1920, -1), (key1393, -1), (key1393, -1), (key1548, -1), (key1548, -1), (key1896, -1), (key1896, -1), (key1298, 1), (key1298, 1), (key1575, 1), (key1575, 1), (key1903, 1), (key1903, 1)]

def rawRow3786 : Integer.Sparse Key := [(key1593, -2), (key1911, -2), (key1593, -2), (key1633, 1), (key1926, 1), (key1444, 1), (key1926, 1), (key1444, 1), (key1633, 1), (key1556, 2), (key1899, 2), (key1556, 2), (key1624, -1), (key1920, -1), (key1326, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1548, -1), (key1896, -1), (key1393, -1), (key1896, -1), (key1393, -1), (key1548, -1), (key1575, 1), (key1903, 1), (key1298, 1), (key1903, 1), (key1298, 1), (key1575, 1)]

def rawRow3787 : Integer.Sparse Key := [(key1911, -2), (key1593, -2), (key1593, -2), (key1926, 1), (key1633, 1), (key1926, 1), (key1444, 1), (key1633, 1), (key1444, 1), (key1899, 2), (key1556, 2), (key1556, 2), (key1920, -1), (key1624, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1326, -1), (key1896, -1), (key1548, -1), (key1896, -1), (key1393, -1), (key1548, -1), (key1393, -1), (key1903, 1), (key1575, 1), (key1903, 1), (key1298, 1), (key1575, 1), (key1298, 1)]

def rawRow3788 : Integer.Sparse Key := [(key1633, -2), (key1689, -2), (key1926, -2), (key1444, 1), (key1480, 1), (key1593, 1), (key1689, 1), (key1911, 1), (key1926, 1), (key1624, 2), (key1683, 2), (key1920, 2), (key1326, -1), (key1354, -1), (key1556, -1), (key1683, -1), (key1899, -1), (key1920, -1), (key1426, -1), (key1472, -1), (key1575, -1), (key1681, -1), (key1903, -1), (key1918, -1), (key1318, 1), (key1351, 1), (key1548, 1), (key1681, 1), (key1896, 1), (key1918, 1)]

def rawRow3789 : Integer.Sparse Key := [(key1689, -2), (key1633, -2), (key1926, -2), (key1480, 1), (key1444, 1), (key1689, 1), (key1593, 1), (key1926, 1), (key1911, 1), (key1683, 2), (key1624, 2), (key1920, 2), (key1354, -1), (key1326, -1), (key1683, -1), (key1556, -1), (key1920, -1), (key1899, -1), (key1472, -1), (key1426, -1), (key1681, -1), (key1575, -1), (key1918, -1), (key1903, -1), (key1351, 1), (key1318, 1), (key1681, 1), (key1548, 1), (key1918, 1), (key1896, 1)]

def rawRow3790 : Integer.Sparse Key := [(key1633, -2), (key1926, -2), (key1689, -2), (key1593, 1), (key1911, 1), (key1444, 1), (key1926, 1), (key1480, 1), (key1689, 1), (key1624, 2), (key1920, 2), (key1683, 2), (key1556, -1), (key1899, -1), (key1326, -1), (key1920, -1), (key1354, -1), (key1683, -1), (key1575, -1), (key1903, -1), (key1426, -1), (key1918, -1), (key1472, -1), (key1681, -1), (key1548, 1), (key1896, 1), (key1318, 1), (key1918, 1), (key1351, 1), (key1681, 1)]

def rawRow3791 : Integer.Sparse Key := [(key1926, -2), (key1633, -2), (key1689, -2), (key1911, 1), (key1593, 1), (key1926, 1), (key1444, 1), (key1689, 1), (key1480, 1), (key1920, 2), (key1624, 2), (key1683, 2), (key1899, -1), (key1556, -1), (key1920, -1), (key1326, -1), (key1683, -1), (key1354, -1), (key1903, -1), (key1575, -1), (key1918, -1), (key1426, -1), (key1681, -1), (key1472, -1), (key1896, 1), (key1548, 1), (key1918, 1), (key1318, 1), (key1681, 1), (key1351, 1)]

def rawRow3792 : Integer.Sparse Key := [(key1689, -2), (key1926, -2), (key1633, -2), (key1689, 1), (key1926, 1), (key1480, 1), (key1911, 1), (key1444, 1), (key1593, 1), (key1683, 2), (key1920, 2), (key1624, 2), (key1683, -1), (key1920, -1), (key1354, -1), (key1899, -1), (key1326, -1), (key1556, -1), (key1681, -1), (key1918, -1), (key1472, -1), (key1903, -1), (key1426, -1), (key1575, -1), (key1681, 1), (key1918, 1), (key1351, 1), (key1896, 1), (key1318, 1), (key1548, 1)]

def rawRow3793 : Integer.Sparse Key := [(key1926, -2), (key1689, -2), (key1633, -2), (key1926, 1), (key1689, 1), (key1911, 1), (key1480, 1), (key1593, 1), (key1444, 1), (key1920, 2), (key1683, 2), (key1624, 2), (key1920, -1), (key1683, -1), (key1899, -1), (key1354, -1), (key1556, -1), (key1326, -1), (key1918, -1), (key1681, -1), (key1903, -1), (key1472, -1), (key1575, -1), (key1426, -1), (key1918, 1), (key1681, 1), (key1896, 1), (key1351, 1), (key1548, 1), (key1318, 1)]

def rawRow3794 : Integer.Sparse Key := [(key44, -2), (key47, -2), (key73, -2), (key47, 6), (key101, 2), (key104, 2), (key136, 2), (key22, -2), (key104, -2), (key172, -2), (key114, -6), (key34, 2), (key114, 2), (key176, 2)]

def rawRow3795 : Integer.Sparse Key := [(key47, -2), (key44, -2), (key73, -2), (key47, 6), (key104, 2), (key101, 2), (key136, 2), (key22, -2), (key172, -2), (key104, -2), (key114, -6), (key34, 2), (key176, 2), (key114, 2)]

def rawRow3796 : Integer.Sparse Key := [(key44, -2), (key73, -2), (key47, -2), (key47, 6), (key101, 2), (key136, 2), (key104, 2), (key104, -2), (key22, -2), (key172, -2), (key114, -6), (key114, 2), (key34, 2), (key176, 2)]

def rawRow3797 : Integer.Sparse Key := [(key73, -2), (key44, -2), (key47, -2), (key47, 6), (key136, 2), (key101, 2), (key104, 2), (key104, -2), (key172, -2), (key22, -2), (key114, -6), (key114, 2), (key176, 2), (key34, 2)]

def rawRow3798 : Integer.Sparse Key := [(key47, -2), (key73, -2), (key44, -2), (key47, 6), (key104, 2), (key136, 2), (key101, 2), (key172, -2), (key22, -2), (key104, -2), (key114, -6), (key176, 2), (key34, 2), (key114, 2)]

def rawRow3799 : Integer.Sparse Key := [(key73, -2), (key47, -2), (key44, -2), (key47, 6), (key136, 2), (key104, 2), (key101, 2), (key172, -2), (key104, -2), (key22, -2), (key114, -6), (key176, 2), (key114, 2), (key34, 2)]

def rawRow3800 : Integer.Sparse Key := [(key47, -2), (key47, -2), (key73, -2), (key44, 6), (key172, 2), (key172, 2), (key181, 2), (key19, -2), (key101, -2), (key101, -2), (key176, -6), (key34, 2), (key114, 2), (key114, 2)]

def rawRow3801 : Integer.Sparse Key := [(key47, -2), (key73, -2), (key47, -2), (key44, 6), (key172, 2), (key181, 2), (key172, 2), (key101, -2), (key19, -2), (key101, -2), (key176, -6), (key114, 2), (key34, 2), (key114, 2)]

def rawRow3802 : Integer.Sparse Key := [(key73, -2), (key47, -2), (key47, -2), (key44, 6), (key181, 2), (key172, 2), (key172, 2), (key101, -2), (key101, -2), (key19, -2), (key176, -6), (key114, 2), (key114, 2), (key34, 2)]

def rawRow3803 : Integer.Sparse Key := [(key101, -2), (key104, -2), (key136, -2), (key114, 6), (key44, 2), (key47, 2), (key73, 2), (key34, -2), (key114, -2), (key176, -2), (key47, -6), (key22, 2), (key104, 2), (key172, 2)]

def rawRow3804 : Integer.Sparse Key := [(key104, -2), (key101, -2), (key136, -2), (key114, 6), (key47, 2), (key44, 2), (key73, 2), (key34, -2), (key176, -2), (key114, -2), (key47, -6), (key22, 2), (key172, 2), (key104, 2)]

def rawRow3805 : Integer.Sparse Key := [(key101, -2), (key136, -2), (key104, -2), (key114, 6), (key44, 2), (key73, 2), (key47, 2), (key114, -2), (key34, -2), (key176, -2), (key47, -6), (key104, 2), (key22, 2), (key172, 2)]

def rawRow3806 : Integer.Sparse Key := [(key136, -2), (key101, -2), (key104, -2), (key114, 6), (key73, 2), (key44, 2), (key47, 2), (key114, -2), (key176, -2), (key34, -2), (key47, -6), (key104, 2), (key172, 2), (key22, 2)]

def rawRow3807 : Integer.Sparse Key := [(key104, -2), (key136, -2), (key101, -2), (key114, 6), (key47, 2), (key73, 2), (key44, 2), (key176, -2), (key34, -2), (key114, -2), (key47, -6), (key172, 2), (key22, 2), (key104, 2)]

def rawRow3808 : Integer.Sparse Key := [(key136, -2), (key104, -2), (key101, -2), (key114, 6), (key73, 2), (key47, 2), (key44, 2), (key176, -2), (key114, -2), (key34, -2), (key47, -6), (key172, 2), (key104, 2), (key22, 2)]

def rawRow3809 : Integer.Sparse Key := [(key104, -2), (key114, -2), (key136, -2), (key101, 6), (key172, 2), (key176, 2), (key181, 2), (key19, -2), (key44, -2), (key101, -2), (key172, -6), (key22, 2), (key47, 2), (key104, 2)]

def rawRow3810 : Integer.Sparse Key := [(key114, -2), (key104, -2), (key136, -2), (key101, 6), (key176, 2), (key172, 2), (key181, 2), (key19, -2), (key101, -2), (key44, -2), (key172, -6), (key22, 2), (key104, 2), (key47, 2)]

def rawRow3811 : Integer.Sparse Key := [(key104, -2), (key136, -2), (key114, -2), (key101, 6), (key172, 2), (key181, 2), (key176, 2), (key44, -2), (key19, -2), (key101, -2), (key172, -6), (key47, 2), (key22, 2), (key104, 2)]

def rawRow3812 : Integer.Sparse Key := [(key136, -2), (key104, -2), (key114, -2), (key101, 6), (key181, 2), (key172, 2), (key176, 2), (key44, -2), (key101, -2), (key19, -2), (key172, -6), (key47, 2), (key104, 2), (key22, 2)]

def rawRow3813 : Integer.Sparse Key := [(key114, -2), (key136, -2), (key104, -2), (key101, 6), (key176, 2), (key181, 2), (key172, 2), (key101, -2), (key19, -2), (key44, -2), (key172, -6), (key104, 2), (key22, 2), (key47, 2)]

def rawRow3814 : Integer.Sparse Key := [(key136, -2), (key114, -2), (key104, -2), (key101, 6), (key181, 2), (key176, 2), (key172, 2), (key101, -2), (key44, -2), (key19, -2), (key172, -6), (key104, 2), (key47, 2), (key22, 2)]

def rawRow3815 : Integer.Sparse Key := [(key172, -2), (key172, -2), (key181, -2), (key176, 6), (key47, 2), (key47, 2), (key73, 2), (key34, -2), (key114, -2), (key114, -2), (key44, -6), (key19, 2), (key101, 2), (key101, 2)]

def rawRow3816 : Integer.Sparse Key := [(key172, -2), (key181, -2), (key172, -2), (key176, 6), (key47, 2), (key73, 2), (key47, 2), (key114, -2), (key34, -2), (key114, -2), (key44, -6), (key101, 2), (key19, 2), (key101, 2)]

def rawRow3817 : Integer.Sparse Key := [(key181, -2), (key172, -2), (key172, -2), (key176, 6), (key73, 2), (key47, 2), (key47, 2), (key114, -2), (key114, -2), (key34, -2), (key44, -6), (key101, 2), (key101, 2), (key19, 2)]

def rawRow3818 : Integer.Sparse Key := [(key172, -2), (key176, -2), (key181, -2), (key172, 6), (key104, 2), (key114, 2), (key136, 2), (key22, -2), (key47, -2), (key104, -2), (key101, -6), (key19, 2), (key44, 2), (key101, 2)]

def rawRow3819 : Integer.Sparse Key := [(key176, -2), (key172, -2), (key181, -2), (key172, 6), (key114, 2), (key104, 2), (key136, 2), (key22, -2), (key104, -2), (key47, -2), (key101, -6), (key19, 2), (key101, 2), (key44, 2)]

def rawRow3820 : Integer.Sparse Key := [(key172, -2), (key181, -2), (key176, -2), (key172, 6), (key104, 2), (key136, 2), (key114, 2), (key47, -2), (key22, -2), (key104, -2), (key101, -6), (key44, 2), (key19, 2), (key101, 2)]

def rawRow3821 : Integer.Sparse Key := [(key181, -2), (key172, -2), (key176, -2), (key172, 6), (key136, 2), (key104, 2), (key114, 2), (key47, -2), (key104, -2), (key22, -2), (key101, -6), (key44, 2), (key101, 2), (key19, 2)]

def rawRow3822 : Integer.Sparse Key := [(key176, -2), (key181, -2), (key172, -2), (key172, 6), (key114, 2), (key136, 2), (key104, 2), (key104, -2), (key22, -2), (key47, -2), (key101, -6), (key101, 2), (key19, 2), (key44, 2)]

def rawRow3823 : Integer.Sparse Key := [(key181, -2), (key176, -2), (key172, -2), (key172, 6), (key136, 2), (key114, 2), (key104, 2), (key104, -2), (key47, -2), (key22, -2), (key101, -6), (key101, 2), (key44, 2), (key19, 2)]

def rawRow3824 : Integer.Sparse Key := [(key1540, -6), (key1385, 2), (key1540, 2), (key1552, 2), (key1567, 6), (key1290, -2), (key1567, -2), (key1589, -2), (key1418, -2), (key1616, -2), (key1620, -2), (key1310, 2), (key1616, 2), (key1629, 2)]

def rawRow3825 : Integer.Sparse Key := [(key1540, -6), (key1385, 2), (key1552, 2), (key1540, 2), (key1567, 6), (key1290, -2), (key1589, -2), (key1567, -2), (key1418, -2), (key1620, -2), (key1616, -2), (key1310, 2), (key1629, 2), (key1616, 2)]

def rawRow3826 : Integer.Sparse Key := [(key1540, -6), (key1540, 2), (key1385, 2), (key1552, 2), (key1567, 6), (key1567, -2), (key1290, -2), (key1589, -2), (key1616, -2), (key1418, -2), (key1620, -2), (key1616, 2), (key1310, 2), (key1629, 2)]

def rawRow3827 : Integer.Sparse Key := [(key1540, -6), (key1540, 2), (key1552, 2), (key1385, 2), (key1567, 6), (key1567, -2), (key1589, -2), (key1290, -2), (key1616, -2), (key1620, -2), (key1418, -2), (key1616, 2), (key1629, 2), (key1310, 2)]

def rawRow3828 : Integer.Sparse Key := [(key1540, -6), (key1552, 2), (key1385, 2), (key1540, 2), (key1567, 6), (key1589, -2), (key1290, -2), (key1567, -2), (key1620, -2), (key1418, -2), (key1616, -2), (key1629, 2), (key1310, 2), (key1616, 2)]

def rawRow3829 : Integer.Sparse Key := [(key1540, -6), (key1552, 2), (key1540, 2), (key1385, 2), (key1567, 6), (key1589, -2), (key1567, -2), (key1290, -2), (key1620, -2), (key1616, -2), (key1418, -2), (key1629, 2), (key1616, 2), (key1310, 2)]

def rawRow3830 : Integer.Sparse Key := [(key1552, -6), (key1385, 2), (key1540, 2), (key1540, 2), (key1589, 6), (key1290, -2), (key1567, -2), (key1567, -2), (key1440, -2), (key1629, -2), (key1629, -2), (key1322, 2), (key1620, 2), (key1620, 2)]

def rawRow3831 : Integer.Sparse Key := [(key1552, -6), (key1540, 2), (key1385, 2), (key1540, 2), (key1589, 6), (key1567, -2), (key1290, -2), (key1567, -2), (key1629, -2), (key1440, -2), (key1629, -2), (key1620, 2), (key1322, 2), (key1620, 2)]

def rawRow3832 : Integer.Sparse Key := [(key1552, -6), (key1540, 2), (key1540, 2), (key1385, 2), (key1589, 6), (key1567, -2), (key1567, -2), (key1290, -2), (key1629, -2), (key1629, -2), (key1440, -2), (key1620, 2), (key1620, 2), (key1322, 2)]

def rawRow3833 : Integer.Sparse Key := [(key1567, -6), (key1418, 2), (key1616, 2), (key1620, 2), (key1540, 6), (key1310, -2), (key1616, -2), (key1629, -2), (key1385, -2), (key1540, -2), (key1552, -2), (key1290, 2), (key1567, 2), (key1589, 2)]

def rawRow3834 : Integer.Sparse Key := [(key1567, -6), (key1418, 2), (key1620, 2), (key1616, 2), (key1540, 6), (key1310, -2), (key1629, -2), (key1616, -2), (key1385, -2), (key1552, -2), (key1540, -2), (key1290, 2), (key1589, 2), (key1567, 2)]

def rawRow3835 : Integer.Sparse Key := [(key1567, -6), (key1616, 2), (key1418, 2), (key1620, 2), (key1540, 6), (key1616, -2), (key1310, -2), (key1629, -2), (key1540, -2), (key1385, -2), (key1552, -2), (key1567, 2), (key1290, 2), (key1589, 2)]

def rawRow3836 : Integer.Sparse Key := [(key1567, -6), (key1616, 2), (key1620, 2), (key1418, 2), (key1540, 6), (key1616, -2), (key1629, -2), (key1310, -2), (key1540, -2), (key1552, -2), (key1385, -2), (key1567, 2), (key1589, 2), (key1290, 2)]

def rawRow3837 : Integer.Sparse Key := [(key1567, -6), (key1620, 2), (key1418, 2), (key1616, 2), (key1540, 6), (key1629, -2), (key1310, -2), (key1616, -2), (key1552, -2), (key1385, -2), (key1540, -2), (key1589, 2), (key1290, 2), (key1567, 2)]

def rawRow3838 : Integer.Sparse Key := [(key1567, -6), (key1620, 2), (key1616, 2), (key1418, 2), (key1540, 6), (key1629, -2), (key1616, -2), (key1310, -2), (key1552, -2), (key1540, -2), (key1385, -2), (key1589, 2), (key1567, 2), (key1290, 2)]

def rawRow3839 : Integer.Sparse Key := [(key1620, -6), (key1418, 2), (key1567, 2), (key1616, 2), (key1629, 6), (key1310, -2), (key1540, -2), (key1616, -2), (key1440, -2), (key1589, -2), (key1629, -2), (key1322, 2), (key1552, 2), (key1620, 2)]

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

def rawRow3840 : Integer.Sparse Key := [(key1620, -6), (key1418, 2), (key1616, 2), (key1567, 2), (key1629, 6), (key1310, -2), (key1616, -2), (key1540, -2), (key1440, -2), (key1629, -2), (key1589, -2), (key1322, 2), (key1620, 2), (key1552, 2)]

def rawRow3841 : Integer.Sparse Key := [(key1620, -6), (key1567, 2), (key1418, 2), (key1616, 2), (key1629, 6), (key1540, -2), (key1310, -2), (key1616, -2), (key1589, -2), (key1440, -2), (key1629, -2), (key1552, 2), (key1322, 2), (key1620, 2)]

def rawRow3842 : Integer.Sparse Key := [(key1620, -6), (key1567, 2), (key1616, 2), (key1418, 2), (key1629, 6), (key1540, -2), (key1616, -2), (key1310, -2), (key1589, -2), (key1629, -2), (key1440, -2), (key1552, 2), (key1620, 2), (key1322, 2)]

def rawRow3843 : Integer.Sparse Key := [(key1620, -6), (key1616, 2), (key1418, 2), (key1567, 2), (key1629, 6), (key1616, -2), (key1310, -2), (key1540, -2), (key1629, -2), (key1440, -2), (key1589, -2), (key1620, 2), (key1322, 2), (key1552, 2)]

def rawRow3844 : Integer.Sparse Key := [(key1620, -6), (key1616, 2), (key1567, 2), (key1418, 2), (key1629, 6), (key1616, -2), (key1540, -2), (key1310, -2), (key1629, -2), (key1589, -2), (key1440, -2), (key1620, 2), (key1552, 2), (key1322, 2)]

def rawRow3845 : Integer.Sparse Key := [(key1589, -6), (key1440, 2), (key1629, 2), (key1629, 2), (key1552, 6), (key1322, -2), (key1620, -2), (key1620, -2), (key1385, -2), (key1540, -2), (key1540, -2), (key1290, 2), (key1567, 2), (key1567, 2)]

def rawRow3846 : Integer.Sparse Key := [(key1589, -6), (key1629, 2), (key1440, 2), (key1629, 2), (key1552, 6), (key1620, -2), (key1322, -2), (key1620, -2), (key1540, -2), (key1385, -2), (key1540, -2), (key1567, 2), (key1290, 2), (key1567, 2)]

def rawRow3847 : Integer.Sparse Key := [(key1589, -6), (key1629, 2), (key1629, 2), (key1440, 2), (key1552, 6), (key1620, -2), (key1620, -2), (key1322, -2), (key1540, -2), (key1540, -2), (key1385, -2), (key1567, 2), (key1567, 2), (key1290, 2)]

def rawRow3848 : Integer.Sparse Key := [(key1629, -6), (key1440, 2), (key1589, 2), (key1629, 2), (key1620, 6), (key1322, -2), (key1552, -2), (key1620, -2), (key1418, -2), (key1567, -2), (key1616, -2), (key1310, 2), (key1540, 2), (key1616, 2)]

def rawRow3849 : Integer.Sparse Key := [(key1629, -6), (key1440, 2), (key1629, 2), (key1589, 2), (key1620, 6), (key1322, -2), (key1620, -2), (key1552, -2), (key1418, -2), (key1616, -2), (key1567, -2), (key1310, 2), (key1616, 2), (key1540, 2)]

def rawRow3850 : Integer.Sparse Key := [(key1629, -6), (key1589, 2), (key1440, 2), (key1629, 2), (key1620, 6), (key1552, -2), (key1322, -2), (key1620, -2), (key1567, -2), (key1418, -2), (key1616, -2), (key1540, 2), (key1310, 2), (key1616, 2)]

def rawRow3851 : Integer.Sparse Key := [(key1629, -6), (key1589, 2), (key1629, 2), (key1440, 2), (key1620, 6), (key1552, -2), (key1620, -2), (key1322, -2), (key1567, -2), (key1616, -2), (key1418, -2), (key1540, 2), (key1616, 2), (key1310, 2)]

def rawRow3852 : Integer.Sparse Key := [(key1629, -6), (key1629, 2), (key1440, 2), (key1589, 2), (key1620, 6), (key1620, -2), (key1322, -2), (key1552, -2), (key1616, -2), (key1418, -2), (key1567, -2), (key1616, 2), (key1310, 2), (key1540, 2)]

def rawRow3853 : Integer.Sparse Key := [(key1629, -6), (key1629, 2), (key1589, 2), (key1440, 2), (key1620, 6), (key1620, -2), (key1552, -2), (key1322, -2), (key1616, -2), (key1567, -2), (key1418, -2), (key1616, 2), (key1540, 2), (key1310, 2)]

def rawRow3854 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key407, -1), (key579, -1), (key420, -1), (key585, -1), (key240, 2), (key410, 2), (key579, 2), (key249, 1), (key252, 1), (key436, 1), (key594, 1), (key452, 1), (key603, 1), (key252, -1), (key268, -1), (key389, -1), (key569, -1), (key468, -1), (key594, -1), (key262, -2), (key444, -2), (key597, -2), (key262, 1), (key273, 1), (key399, 1), (key574, 1), (key471, 1), (key597, 1)]

def rawRow3855 : Integer.Sparse Key := [(key240, -1), (key237, -1), (key579, -1), (key407, -1), (key585, -1), (key420, -1), (key240, 2), (key579, 2), (key410, 2), (key252, 1), (key249, 1), (key594, 1), (key436, 1), (key603, 1), (key452, 1), (key268, -1), (key252, -1), (key569, -1), (key389, -1), (key594, -1), (key468, -1), (key262, -2), (key597, -2), (key444, -2), (key273, 1), (key262, 1), (key574, 1), (key399, 1), (key597, 1), (key471, 1)]

def rawRow3856 : Integer.Sparse Key := [(key407, -1), (key420, -1), (key237, -1), (key585, -1), (key240, -1), (key579, -1), (key410, 2), (key240, 2), (key579, 2), (key436, 1), (key452, 1), (key249, 1), (key603, 1), (key252, 1), (key594, 1), (key389, -1), (key468, -1), (key252, -1), (key594, -1), (key268, -1), (key569, -1), (key444, -2), (key262, -2), (key597, -2), (key399, 1), (key471, 1), (key262, 1), (key597, 1), (key273, 1), (key574, 1)]

def rawRow3857 : Integer.Sparse Key := [(key420, -1), (key407, -1), (key585, -1), (key237, -1), (key579, -1), (key240, -1), (key410, 2), (key579, 2), (key240, 2), (key452, 1), (key436, 1), (key603, 1), (key249, 1), (key594, 1), (key252, 1), (key468, -1), (key389, -1), (key594, -1), (key252, -1), (key569, -1), (key268, -1), (key444, -2), (key597, -2), (key262, -2), (key471, 1), (key399, 1), (key597, 1), (key262, 1), (key574, 1), (key273, 1)]

def rawRow3858 : Integer.Sparse Key := [(key579, -1), (key585, -1), (key240, -1), (key420, -1), (key237, -1), (key407, -1), (key579, 2), (key240, 2), (key410, 2), (key594, 1), (key603, 1), (key252, 1), (key452, 1), (key249, 1), (key436, 1), (key569, -1), (key594, -1), (key268, -1), (key468, -1), (key252, -1), (key389, -1), (key597, -2), (key262, -2), (key444, -2), (key574, 1), (key597, 1), (key273, 1), (key471, 1), (key262, 1), (key399, 1)]

def rawRow3859 : Integer.Sparse Key := [(key585, -1), (key579, -1), (key420, -1), (key240, -1), (key407, -1), (key237, -1), (key579, 2), (key410, 2), (key240, 2), (key603, 1), (key594, 1), (key452, 1), (key252, 1), (key436, 1), (key249, 1), (key594, -1), (key569, -1), (key468, -1), (key268, -1), (key389, -1), (key252, -1), (key597, -2), (key444, -2), (key262, -2), (key597, 1), (key574, 1), (key471, 1), (key273, 1), (key399, 1), (key262, 1)]

def rawRow3860 : Integer.Sparse Key := [(key240, -1), (key240, -1), (key410, -1), (key410, -1), (key420, -1), (key420, -1), (key237, 2), (key407, 2), (key407, 2), (key268, 1), (key268, 1), (key468, 1), (key468, 1), (key477, 1), (key477, 1), (key249, -1), (key249, -1), (key386, -1), (key386, -1), (key436, -1), (key436, -1), (key273, -2), (key471, -2), (key471, -2), (key262, 1), (key262, 1), (key399, 1), (key399, 1), (key444, 1), (key444, 1)]

def rawRow3861 : Integer.Sparse Key := [(key410, -1), (key420, -1), (key240, -1), (key420, -1), (key240, -1), (key410, -1), (key407, 2), (key237, 2), (key407, 2), (key468, 1), (key477, 1), (key268, 1), (key477, 1), (key268, 1), (key468, 1), (key386, -1), (key436, -1), (key249, -1), (key436, -1), (key249, -1), (key386, -1), (key471, -2), (key273, -2), (key471, -2), (key399, 1), (key444, 1), (key262, 1), (key444, 1), (key262, 1), (key399, 1)]

def rawRow3862 : Integer.Sparse Key := [(key420, -1), (key410, -1), (key420, -1), (key240, -1), (key410, -1), (key240, -1), (key407, 2), (key407, 2), (key237, 2), (key477, 1), (key468, 1), (key477, 1), (key268, 1), (key468, 1), (key268, 1), (key436, -1), (key386, -1), (key436, -1), (key249, -1), (key386, -1), (key249, -1), (key471, -2), (key471, -2), (key273, -2), (key444, 1), (key399, 1), (key444, 1), (key262, 1), (key399, 1), (key262, 1)]

def rawRow3863 : Integer.Sparse Key := [(key249, -1), (key252, -1), (key436, -1), (key594, -1), (key452, -1), (key603, -1), (key262, 2), (key444, 2), (key597, 2), (key237, 1), (key240, 1), (key407, 1), (key579, 1), (key420, 1), (key585, 1), (key262, -1), (key273, -1), (key399, -1), (key574, -1), (key471, -1), (key597, -1), (key240, -2), (key410, -2), (key579, -2), (key252, 1), (key268, 1), (key389, 1), (key569, 1), (key468, 1), (key594, 1)]

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

def rawRow3875 : Integer.Sparse Key := [(key268, -1), (key268, -1), (key468, -1), (key468, -1), (key477, -1), (key477, -1), (key273, 2), (key471, 2), (key471, 2), (key240, 1), (key240, 1), (key410, 1), (key410, 1), (key420, 1), (key420, 1), (key262, -1), (key262, -1), (key399, -1), (key399, -1), (key444, -1), (key444, -1), (key237, -2), (key407, -2), (key407, -2), (key249, 1), (key249, 1), (key386, 1), (key386, 1), (key436, 1), (key436, 1)]

def rawRow3876 : Integer.Sparse Key := [(key468, -1), (key477, -1), (key268, -1), (key477, -1), (key268, -1), (key468, -1), (key471, 2), (key273, 2), (key471, 2), (key410, 1), (key420, 1), (key240, 1), (key420, 1), (key240, 1), (key410, 1), (key399, -1), (key444, -1), (key262, -1), (key444, -1), (key262, -1), (key399, -1), (key407, -2), (key237, -2), (key407, -2), (key386, 1), (key436, 1), (key249, 1), (key436, 1), (key249, 1), (key386, 1)]

def rawRow3877 : Integer.Sparse Key := [(key477, -1), (key468, -1), (key477, -1), (key268, -1), (key468, -1), (key268, -1), (key471, 2), (key471, 2), (key273, 2), (key420, 1), (key410, 1), (key420, 1), (key240, 1), (key410, 1), (key240, 1), (key444, -1), (key399, -1), (key444, -1), (key262, -1), (key399, -1), (key262, -1), (key407, -2), (key407, -2), (key237, -2), (key436, 1), (key386, 1), (key436, 1), (key249, 1), (key386, 1), (key249, 1)]

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

def rawRow3920 : Integer.Sparse Key := [(key336, -2), (key336, -2), (key342, -2), (key306, 1), (key306, 1), (key320, 1), (key320, 1), (key330, 1), (key330, 1), (key579, 2), (key579, 2), (key585, 2), (key240, -1), (key240, -1), (key410, -1), (key410, -1), (key420, -1), (key420, -1), (key569, -1), (key569, -1), (key594, -1), (key594, -1), (key603, -1), (key603, -1), (key268, 1), (key268, 1), (key468, 1), (key468, 1), (key477, 1), (key477, 1)]

def rawRow3921 : Integer.Sparse Key := [(key336, -2), (key342, -2), (key336, -2), (key320, 1), (key330, 1), (key306, 1), (key330, 1), (key306, 1), (key320, 1), (key579, 2), (key585, 2), (key579, 2), (key410, -1), (key420, -1), (key240, -1), (key420, -1), (key240, -1), (key410, -1), (key594, -1), (key603, -1), (key569, -1), (key603, -1), (key569, -1), (key594, -1), (key468, 1), (key477, 1), (key268, 1), (key477, 1), (key268, 1), (key468, 1)]

def rawRow3922 : Integer.Sparse Key := [(key342, -2), (key336, -2), (key336, -2), (key330, 1), (key320, 1), (key330, 1), (key306, 1), (key320, 1), (key306, 1), (key585, 2), (key579, 2), (key579, 2), (key420, -1), (key410, -1), (key420, -1), (key240, -1), (key410, -1), (key240, -1), (key603, -1), (key594, -1), (key603, -1), (key569, -1), (key594, -1), (key569, -1), (key477, 1), (key468, 1), (key477, 1), (key268, 1), (key468, 1), (key268, 1)]

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

def rawRow3935 : Integer.Sparse Key := [(key579, -2), (key579, -2), (key585, -2), (key569, 1), (key569, 1), (key594, 1), (key594, 1), (key603, 1), (key603, 1), (key336, 2), (key336, 2), (key342, 2), (key268, -1), (key268, -1), (key468, -1), (key468, -1), (key477, -1), (key477, -1), (key306, -1), (key306, -1), (key320, -1), (key320, -1), (key330, -1), (key330, -1), (key240, 1), (key240, 1), (key410, 1), (key410, 1), (key420, 1), (key420, 1)]

def rawRow3936 : Integer.Sparse Key := [(key579, -2), (key585, -2), (key579, -2), (key594, 1), (key603, 1), (key569, 1), (key603, 1), (key569, 1), (key594, 1), (key336, 2), (key342, 2), (key336, 2), (key468, -1), (key477, -1), (key268, -1), (key477, -1), (key268, -1), (key468, -1), (key320, -1), (key330, -1), (key306, -1), (key330, -1), (key306, -1), (key320, -1), (key410, 1), (key420, 1), (key240, 1), (key420, 1), (key240, 1), (key410, 1)]

def rawRow3937 : Integer.Sparse Key := [(key585, -2), (key579, -2), (key579, -2), (key603, 1), (key594, 1), (key603, 1), (key569, 1), (key594, 1), (key569, 1), (key342, 2), (key336, 2), (key336, 2), (key477, -1), (key468, -1), (key477, -1), (key268, -1), (key468, -1), (key268, -1), (key330, -1), (key320, -1), (key330, -1), (key306, -1), (key320, -1), (key306, -1), (key420, 1), (key410, 1), (key420, 1), (key240, 1), (key410, 1), (key240, 1)]

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

def rawRow3968 : Integer.Sparse Key := [(key171, -2), (key174, -2), (key179, -2), (key171, 6), (key103, 2), (key112, 2), (key134, 2), (key21, -2), (key46, -2), (key103, -2), (key100, -6), (key18, 2), (key375, 2), (key426, 2)]

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

def rawRow3980 : Integer.Sparse Key := [(key1397, -2), (key1774, -2), (key1774, -2), (key1391, 1), (key1391, 1), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1447, 2), (key1825, 2), (key1825, 2), (key1316, -1), (key1316, -1), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1466, -1), (key1466, -1), (key1667, -1), (key1667, -1), (key1844, -1), (key1844, -1), (key1339, 1), (key1339, 1), (key1457, 1), (key1457, 1), (key1839, 1), (key1839, 1)]

def rawRow3981 : Integer.Sparse Key := [(key1774, -2), (key1397, -2), (key1774, -2), (key1546, 1), (key1772, 1), (key1391, 1), (key1772, 1), (key1391, 1), (key1546, 1), (key1825, 2), (key1447, 2), (key1825, 2), (key1424, -1), (key1813, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1667, -1), (key1844, -1), (key1466, -1), (key1844, -1), (key1466, -1), (key1667, -1), (key1457, 1), (key1839, 1), (key1339, 1), (key1839, 1), (key1339, 1), (key1457, 1)]

def rawRow3982 : Integer.Sparse Key := [(key1774, -2), (key1774, -2), (key1397, -2), (key1772, 1), (key1546, 1), (key1772, 1), (key1391, 1), (key1546, 1), (key1391, 1), (key1825, 2), (key1825, 2), (key1447, 2), (key1813, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1316, -1), (key1844, -1), (key1667, -1), (key1844, -1), (key1466, -1), (key1667, -1), (key1466, -1), (key1839, 1), (key1457, 1), (key1839, 1), (key1339, 1), (key1457, 1), (key1339, 1)]

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

def rawRow3995 : Integer.Sparse Key := [(key1447, -2), (key1825, -2), (key1825, -2), (key1466, 1), (key1466, 1), (key1667, 1), (key1667, 1), (key1844, 1), (key1844, 1), (key1397, 2), (key1774, 2), (key1774, 2), (key1339, -1), (key1339, -1), (key1457, -1), (key1457, -1), (key1839, -1), (key1839, -1), (key1391, -1), (key1391, -1), (key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1316, 1), (key1316, 1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1)]

def rawRow3996 : Integer.Sparse Key := [(key1825, -2), (key1447, -2), (key1825, -2), (key1667, 1), (key1844, 1), (key1466, 1), (key1844, 1), (key1466, 1), (key1667, 1), (key1774, 2), (key1397, 2), (key1774, 2), (key1457, -1), (key1839, -1), (key1339, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1546, -1), (key1772, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1546, -1), (key1424, 1), (key1813, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1424, 1)]

def rawRow3997 : Integer.Sparse Key := [(key1825, -2), (key1825, -2), (key1447, -2), (key1844, 1), (key1667, 1), (key1844, 1), (key1466, 1), (key1667, 1), (key1466, 1), (key1774, 2), (key1774, 2), (key1397, 2), (key1839, -1), (key1457, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1339, -1), (key1772, -1), (key1546, -1), (key1772, -1), (key1391, -1), (key1546, -1), (key1391, -1), (key1813, 1), (key1424, 1), (key1813, 1), (key1316, 1), (key1424, 1), (key1316, 1)]

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

def rawRow4070 : Integer.Sparse Key := [(key1554, -2), (key1554, -2), (key1778, -2), (key1390, 1), (key1390, 1), (key1545, 1), (key1545, 1), (key1771, 1), (key1771, 1), (key1591, 2), (key1591, 2), (key1796, 2), (key1295, -1), (key1295, -1), (key1572, -1), (key1572, -1), (key1787, -1), (key1787, -1), (key1442, -1), (key1442, -1), (key1631, -1), (key1631, -1), (key1823, -1), (key1823, -1), (key1324, 1), (key1324, 1), (key1622, 1), (key1622, 1), (key1815, 1), (key1815, 1)]

def rawRow4071 : Integer.Sparse Key := [(key1554, -2), (key1778, -2), (key1554, -2), (key1545, 1), (key1771, 1), (key1390, 1), (key1771, 1), (key1390, 1), (key1545, 1), (key1591, 2), (key1796, 2), (key1591, 2), (key1572, -1), (key1787, -1), (key1295, -1), (key1787, -1), (key1295, -1), (key1572, -1), (key1631, -1), (key1823, -1), (key1442, -1), (key1823, -1), (key1442, -1), (key1631, -1), (key1622, 1), (key1815, 1), (key1324, 1), (key1815, 1), (key1324, 1), (key1622, 1)]

def rawRow4072 : Integer.Sparse Key := [(key1778, -2), (key1554, -2), (key1554, -2), (key1771, 1), (key1545, 1), (key1771, 1), (key1390, 1), (key1545, 1), (key1390, 1), (key1796, 2), (key1591, 2), (key1591, 2), (key1787, -1), (key1572, -1), (key1787, -1), (key1295, -1), (key1572, -1), (key1295, -1), (key1823, -1), (key1631, -1), (key1823, -1), (key1442, -1), (key1631, -1), (key1442, -1), (key1815, 1), (key1622, 1), (key1815, 1), (key1324, 1), (key1622, 1), (key1324, 1)]

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

def rawRow4085 : Integer.Sparse Key := [(key1591, -2), (key1591, -2), (key1796, -2), (key1442, 1), (key1442, 1), (key1631, 1), (key1631, 1), (key1823, 1), (key1823, 1), (key1554, 2), (key1554, 2), (key1778, 2), (key1324, -1), (key1324, -1), (key1622, -1), (key1622, -1), (key1815, -1), (key1815, -1), (key1390, -1), (key1390, -1), (key1545, -1), (key1545, -1), (key1771, -1), (key1771, -1), (key1295, 1), (key1295, 1), (key1572, 1), (key1572, 1), (key1787, 1), (key1787, 1)]

def rawRow4086 : Integer.Sparse Key := [(key1591, -2), (key1796, -2), (key1591, -2), (key1631, 1), (key1823, 1), (key1442, 1), (key1823, 1), (key1442, 1), (key1631, 1), (key1554, 2), (key1778, 2), (key1554, 2), (key1622, -1), (key1815, -1), (key1324, -1), (key1815, -1), (key1324, -1), (key1622, -1), (key1545, -1), (key1771, -1), (key1390, -1), (key1771, -1), (key1390, -1), (key1545, -1), (key1572, 1), (key1787, 1), (key1295, 1), (key1787, 1), (key1295, 1), (key1572, 1)]

def rawRow4087 : Integer.Sparse Key := [(key1796, -2), (key1591, -2), (key1591, -2), (key1823, 1), (key1631, 1), (key1823, 1), (key1442, 1), (key1631, 1), (key1442, 1), (key1778, 2), (key1554, 2), (key1554, 2), (key1815, -1), (key1622, -1), (key1815, -1), (key1324, -1), (key1622, -1), (key1324, -1), (key1771, -1), (key1545, -1), (key1771, -1), (key1390, -1), (key1545, -1), (key1390, -1), (key1787, 1), (key1572, 1), (key1787, 1), (key1295, 1), (key1572, 1), (key1295, 1)]

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

def rawRow4160 : Integer.Sparse Key := [(key1298, -1), (key1298, -1), (key1575, -1), (key1575, -1), (key1903, -1), (key1903, -1), (key1292, 2), (key1569, 2), (key1569, 2), (key1326, 1), (key1326, 1), (key1624, 1), (key1624, 1), (key1920, 1), (key1920, 1), (key1312, -1), (key1312, -1), (key1420, -1), (key1420, -1), (key1618, -1), (key1618, -1), (key1354, -2), (key1683, -2), (key1683, -2), (key1351, 1), (key1351, 1), (key1472, 1), (key1472, 1), (key1681, 1), (key1681, 1)]

def rawRow4161 : Integer.Sparse Key := [(key1575, -1), (key1903, -1), (key1298, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1569, 2), (key1292, 2), (key1569, 2), (key1624, 1), (key1920, 1), (key1326, 1), (key1920, 1), (key1326, 1), (key1624, 1), (key1420, -1), (key1618, -1), (key1312, -1), (key1618, -1), (key1312, -1), (key1420, -1), (key1683, -2), (key1354, -2), (key1683, -2), (key1472, 1), (key1681, 1), (key1351, 1), (key1681, 1), (key1351, 1), (key1472, 1)]

def rawRow4162 : Integer.Sparse Key := [(key1903, -1), (key1575, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1298, -1), (key1569, 2), (key1569, 2), (key1292, 2), (key1920, 1), (key1624, 1), (key1920, 1), (key1326, 1), (key1624, 1), (key1326, 1), (key1618, -1), (key1420, -1), (key1618, -1), (key1312, -1), (key1420, -1), (key1312, -1), (key1683, -2), (key1683, -2), (key1354, -2), (key1681, 1), (key1472, 1), (key1681, 1), (key1351, 1), (key1472, 1), (key1351, 1)]

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

def rawRow4175 : Integer.Sparse Key := [(key1326, -1), (key1326, -1), (key1624, -1), (key1624, -1), (key1920, -1), (key1920, -1), (key1354, 2), (key1683, 2), (key1683, 2), (key1298, 1), (key1298, 1), (key1575, 1), (key1575, 1), (key1903, 1), (key1903, 1), (key1351, -1), (key1351, -1), (key1472, -1), (key1472, -1), (key1681, -1), (key1681, -1), (key1292, -2), (key1569, -2), (key1569, -2), (key1312, 1), (key1312, 1), (key1420, 1), (key1420, 1), (key1618, 1), (key1618, 1)]

def rawRow4176 : Integer.Sparse Key := [(key1624, -1), (key1920, -1), (key1326, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1683, 2), (key1354, 2), (key1683, 2), (key1575, 1), (key1903, 1), (key1298, 1), (key1903, 1), (key1298, 1), (key1575, 1), (key1472, -1), (key1681, -1), (key1351, -1), (key1681, -1), (key1351, -1), (key1472, -1), (key1569, -2), (key1292, -2), (key1569, -2), (key1420, 1), (key1618, 1), (key1312, 1), (key1618, 1), (key1312, 1), (key1420, 1)]

def rawRow4177 : Integer.Sparse Key := [(key1920, -1), (key1624, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1326, -1), (key1683, 2), (key1683, 2), (key1354, 2), (key1903, 1), (key1575, 1), (key1903, 1), (key1298, 1), (key1575, 1), (key1298, 1), (key1681, -1), (key1472, -1), (key1681, -1), (key1351, -1), (key1472, -1), (key1351, -1), (key1569, -2), (key1569, -2), (key1292, -2), (key1618, 1), (key1420, 1), (key1618, 1), (key1312, 1), (key1420, 1), (key1312, 1)]

def rawRow4178 : Integer.Sparse Key := [(key1326, -1), (key1354, -1), (key1556, -1), (key1683, -1), (key1899, -1), (key1920, -1), (key1326, 2), (key1556, 2), (key1624, 2), (key1318, 1), (key1351, 1), (key1548, 1), (key1681, 1), (key1896, 1), (key1918, 1), (key1298, -1), (key1318, -1), (key1393, -1), (key1426, -1), (key1548, -1), (key1575, -1), (key1312, -2), (key1542, -2), (key1618, -2), (key1292, 1), (key1312, 1), (key1387, 1), (key1420, 1), (key1542, 1), (key1569, 1)]

def rawRow4179 : Integer.Sparse Key := [(key1354, -1), (key1326, -1), (key1683, -1), (key1556, -1), (key1920, -1), (key1899, -1), (key1326, 2), (key1624, 2), (key1556, 2), (key1351, 1), (key1318, 1), (key1681, 1), (key1548, 1), (key1918, 1), (key1896, 1), (key1318, -1), (key1298, -1), (key1426, -1), (key1393, -1), (key1575, -1), (key1548, -1), (key1312, -2), (key1618, -2), (key1542, -2), (key1312, 1), (key1292, 1), (key1420, 1), (key1387, 1), (key1569, 1), (key1542, 1)]

def rawRow4180 : Integer.Sparse Key := [(key1556, -1), (key1899, -1), (key1326, -1), (key1920, -1), (key1354, -1), (key1683, -1), (key1556, 2), (key1326, 2), (key1624, 2), (key1548, 1), (key1896, 1), (key1318, 1), (key1918, 1), (key1351, 1), (key1681, 1), (key1393, -1), (key1548, -1), (key1298, -1), (key1575, -1), (key1318, -1), (key1426, -1), (key1542, -2), (key1312, -2), (key1618, -2), (key1387, 1), (key1542, 1), (key1292, 1), (key1569, 1), (key1312, 1), (key1420, 1)]

def rawRow4181 : Integer.Sparse Key := [(key1899, -1), (key1556, -1), (key1920, -1), (key1326, -1), (key1683, -1), (key1354, -1), (key1556, 2), (key1624, 2), (key1326, 2), (key1896, 1), (key1548, 1), (key1918, 1), (key1318, 1), (key1681, 1), (key1351, 1), (key1548, -1), (key1393, -1), (key1575, -1), (key1298, -1), (key1426, -1), (key1318, -1), (key1542, -2), (key1618, -2), (key1312, -2), (key1542, 1), (key1387, 1), (key1569, 1), (key1292, 1), (key1420, 1), (key1312, 1)]

def rawRow4182 : Integer.Sparse Key := [(key1683, -1), (key1920, -1), (key1354, -1), (key1899, -1), (key1326, -1), (key1556, -1), (key1624, 2), (key1326, 2), (key1556, 2), (key1681, 1), (key1918, 1), (key1351, 1), (key1896, 1), (key1318, 1), (key1548, 1), (key1426, -1), (key1575, -1), (key1318, -1), (key1548, -1), (key1298, -1), (key1393, -1), (key1618, -2), (key1312, -2), (key1542, -2), (key1420, 1), (key1569, 1), (key1312, 1), (key1542, 1), (key1292, 1), (key1387, 1)]

def rawRow4183 : Integer.Sparse Key := [(key1920, -1), (key1683, -1), (key1899, -1), (key1354, -1), (key1556, -1), (key1326, -1), (key1624, 2), (key1556, 2), (key1326, 2), (key1918, 1), (key1681, 1), (key1896, 1), (key1351, 1), (key1548, 1), (key1318, 1), (key1575, -1), (key1426, -1), (key1548, -1), (key1318, -1), (key1393, -1), (key1298, -1), (key1618, -2), (key1542, -2), (key1312, -2), (key1569, 1), (key1420, 1), (key1542, 1), (key1312, 1), (key1387, 1), (key1292, 1)]

def rawRow4184 : Integer.Sparse Key := [(key1541, -2), (key1545, -2), (key1771, -2), (key1390, 2), (key1545, 2), (key1554, 2), (key1568, 2), (key1572, 2), (key1787, 2), (key1295, -2), (key1572, -2), (key1591, -2), (key1454, -2), (key1654, -2), (key1657, -2), (key1336, 2), (key1654, 2), (key1665, 2)]

def rawRow4185 : Integer.Sparse Key := [(key1545, -2), (key1541, -2), (key1771, -2), (key1390, 2), (key1554, 2), (key1545, 2), (key1572, 2), (key1568, 2), (key1787, 2), (key1295, -2), (key1591, -2), (key1572, -2), (key1454, -2), (key1657, -2), (key1654, -2), (key1336, 2), (key1665, 2), (key1654, 2)]

def rawRow4186 : Integer.Sparse Key := [(key1541, -2), (key1771, -2), (key1545, -2), (key1545, 2), (key1390, 2), (key1554, 2), (key1568, 2), (key1787, 2), (key1572, 2), (key1572, -2), (key1295, -2), (key1591, -2), (key1654, -2), (key1454, -2), (key1657, -2), (key1654, 2), (key1336, 2), (key1665, 2)]

def rawRow4187 : Integer.Sparse Key := [(key1771, -2), (key1541, -2), (key1545, -2), (key1545, 2), (key1554, 2), (key1390, 2), (key1787, 2), (key1568, 2), (key1572, 2), (key1572, -2), (key1591, -2), (key1295, -2), (key1654, -2), (key1657, -2), (key1454, -2), (key1654, 2), (key1665, 2), (key1336, 2)]

def rawRow4188 : Integer.Sparse Key := [(key1545, -2), (key1771, -2), (key1541, -2), (key1554, 2), (key1390, 2), (key1545, 2), (key1572, 2), (key1787, 2), (key1568, 2), (key1591, -2), (key1295, -2), (key1572, -2), (key1657, -2), (key1454, -2), (key1654, -2), (key1665, 2), (key1336, 2), (key1654, 2)]

def rawRow4189 : Integer.Sparse Key := [(key1771, -2), (key1545, -2), (key1541, -2), (key1554, 2), (key1545, 2), (key1390, 2), (key1787, 2), (key1572, 2), (key1568, 2), (key1591, -2), (key1572, -2), (key1295, -2), (key1657, -2), (key1654, -2), (key1454, -2), (key1665, 2), (key1654, 2), (key1336, 2)]

def rawRow4190 : Integer.Sparse Key := [(key1554, -2), (key1554, -2), (key1778, -2), (key1386, 2), (key1541, 2), (key1541, 2), (key1591, 2), (key1591, 2), (key1796, 2), (key1291, -2), (key1568, -2), (key1568, -2), (key1464, -2), (key1665, -2), (key1665, -2), (key1343, 2), (key1657, 2), (key1657, 2)]

def rawRow4191 : Integer.Sparse Key := [(key1554, -2), (key1778, -2), (key1554, -2), (key1541, 2), (key1386, 2), (key1541, 2), (key1591, 2), (key1796, 2), (key1591, 2), (key1568, -2), (key1291, -2), (key1568, -2), (key1665, -2), (key1464, -2), (key1665, -2), (key1657, 2), (key1343, 2), (key1657, 2)]

def rawRow4192 : Integer.Sparse Key := [(key1778, -2), (key1554, -2), (key1554, -2), (key1541, 2), (key1541, 2), (key1386, 2), (key1796, 2), (key1591, 2), (key1591, 2), (key1568, -2), (key1568, -2), (key1291, -2), (key1665, -2), (key1665, -2), (key1464, -2), (key1657, 2), (key1657, 2), (key1343, 2)]

def rawRow4193 : Integer.Sparse Key := [(key1568, -2), (key1572, -2), (key1787, -2), (key1454, 2), (key1654, 2), (key1657, 2), (key1541, 2), (key1545, 2), (key1771, 2), (key1336, -2), (key1654, -2), (key1665, -2), (key1390, -2), (key1545, -2), (key1554, -2), (key1295, 2), (key1572, 2), (key1591, 2)]

def rawRow4194 : Integer.Sparse Key := [(key1572, -2), (key1568, -2), (key1787, -2), (key1454, 2), (key1657, 2), (key1654, 2), (key1545, 2), (key1541, 2), (key1771, 2), (key1336, -2), (key1665, -2), (key1654, -2), (key1390, -2), (key1554, -2), (key1545, -2), (key1295, 2), (key1591, 2), (key1572, 2)]

def rawRow4195 : Integer.Sparse Key := [(key1568, -2), (key1787, -2), (key1572, -2), (key1654, 2), (key1454, 2), (key1657, 2), (key1541, 2), (key1771, 2), (key1545, 2), (key1654, -2), (key1336, -2), (key1665, -2), (key1545, -2), (key1390, -2), (key1554, -2), (key1572, 2), (key1295, 2), (key1591, 2)]

def rawRow4196 : Integer.Sparse Key := [(key1787, -2), (key1568, -2), (key1572, -2), (key1654, 2), (key1657, 2), (key1454, 2), (key1771, 2), (key1541, 2), (key1545, 2), (key1654, -2), (key1665, -2), (key1336, -2), (key1545, -2), (key1554, -2), (key1390, -2), (key1572, 2), (key1591, 2), (key1295, 2)]

def rawRow4197 : Integer.Sparse Key := [(key1572, -2), (key1787, -2), (key1568, -2), (key1657, 2), (key1454, 2), (key1654, 2), (key1545, 2), (key1771, 2), (key1541, 2), (key1665, -2), (key1336, -2), (key1654, -2), (key1554, -2), (key1390, -2), (key1545, -2), (key1591, 2), (key1295, 2), (key1572, 2)]

def rawRow4198 : Integer.Sparse Key := [(key1787, -2), (key1572, -2), (key1568, -2), (key1657, 2), (key1654, 2), (key1454, 2), (key1771, 2), (key1545, 2), (key1541, 2), (key1665, -2), (key1654, -2), (key1336, -2), (key1554, -2), (key1545, -2), (key1390, -2), (key1591, 2), (key1572, 2), (key1295, 2)]

def rawRow4199 : Integer.Sparse Key := [(key1622, -2), (key1657, -2), (key1815, -2), (key1419, 2), (key1568, 2), (key1617, 2), (key1631, 2), (key1665, 2), (key1823, 2), (key1311, -2), (key1541, -2), (key1617, -2), (key1442, -2), (key1591, -2), (key1631, -2), (key1324, 2), (key1554, 2), (key1622, 2)]

def rawRow4200 : Integer.Sparse Key := [(key1657, -2), (key1622, -2), (key1815, -2), (key1419, 2), (key1617, 2), (key1568, 2), (key1665, 2), (key1631, 2), (key1823, 2), (key1311, -2), (key1617, -2), (key1541, -2), (key1442, -2), (key1631, -2), (key1591, -2), (key1324, 2), (key1622, 2), (key1554, 2)]

def rawRow4201 : Integer.Sparse Key := [(key1622, -2), (key1815, -2), (key1657, -2), (key1568, 2), (key1419, 2), (key1617, 2), (key1631, 2), (key1823, 2), (key1665, 2), (key1541, -2), (key1311, -2), (key1617, -2), (key1591, -2), (key1442, -2), (key1631, -2), (key1554, 2), (key1324, 2), (key1622, 2)]

def rawRow4202 : Integer.Sparse Key := [(key1815, -2), (key1622, -2), (key1657, -2), (key1568, 2), (key1617, 2), (key1419, 2), (key1823, 2), (key1631, 2), (key1665, 2), (key1541, -2), (key1617, -2), (key1311, -2), (key1591, -2), (key1631, -2), (key1442, -2), (key1554, 2), (key1622, 2), (key1324, 2)]

def rawRow4203 : Integer.Sparse Key := [(key1657, -2), (key1815, -2), (key1622, -2), (key1617, 2), (key1419, 2), (key1568, 2), (key1665, 2), (key1823, 2), (key1631, 2), (key1617, -2), (key1311, -2), (key1541, -2), (key1631, -2), (key1442, -2), (key1591, -2), (key1622, 2), (key1324, 2), (key1554, 2)]

def rawRow4204 : Integer.Sparse Key := [(key1815, -2), (key1657, -2), (key1622, -2), (key1617, 2), (key1568, 2), (key1419, 2), (key1823, 2), (key1665, 2), (key1631, 2), (key1617, -2), (key1541, -2), (key1311, -2), (key1631, -2), (key1591, -2), (key1442, -2), (key1622, 2), (key1554, 2), (key1324, 2)]

def rawRow4205 : Integer.Sparse Key := [(key1591, -2), (key1591, -2), (key1796, -2), (key1464, 2), (key1665, 2), (key1665, 2), (key1554, 2), (key1554, 2), (key1778, 2), (key1343, -2), (key1657, -2), (key1657, -2), (key1386, -2), (key1541, -2), (key1541, -2), (key1291, 2), (key1568, 2), (key1568, 2)]

def rawRow4206 : Integer.Sparse Key := [(key1591, -2), (key1796, -2), (key1591, -2), (key1665, 2), (key1464, 2), (key1665, 2), (key1554, 2), (key1778, 2), (key1554, 2), (key1657, -2), (key1343, -2), (key1657, -2), (key1541, -2), (key1386, -2), (key1541, -2), (key1568, 2), (key1291, 2), (key1568, 2)]

def rawRow4207 : Integer.Sparse Key := [(key1796, -2), (key1591, -2), (key1591, -2), (key1665, 2), (key1665, 2), (key1464, 2), (key1778, 2), (key1554, 2), (key1554, 2), (key1657, -2), (key1657, -2), (key1343, -2), (key1541, -2), (key1541, -2), (key1386, -2), (key1568, 2), (key1568, 2), (key1291, 2)]

def rawRow4208 : Integer.Sparse Key := [(key1631, -2), (key1665, -2), (key1823, -2), (key1442, 2), (key1591, 2), (key1631, 2), (key1622, 2), (key1657, 2), (key1815, 2), (key1324, -2), (key1554, -2), (key1622, -2), (key1419, -2), (key1568, -2), (key1617, -2), (key1311, 2), (key1541, 2), (key1617, 2)]

def rawRow4209 : Integer.Sparse Key := [(key1665, -2), (key1631, -2), (key1823, -2), (key1442, 2), (key1631, 2), (key1591, 2), (key1657, 2), (key1622, 2), (key1815, 2), (key1324, -2), (key1622, -2), (key1554, -2), (key1419, -2), (key1617, -2), (key1568, -2), (key1311, 2), (key1617, 2), (key1541, 2)]

def rawRow4210 : Integer.Sparse Key := [(key1631, -2), (key1823, -2), (key1665, -2), (key1591, 2), (key1442, 2), (key1631, 2), (key1622, 2), (key1815, 2), (key1657, 2), (key1554, -2), (key1324, -2), (key1622, -2), (key1568, -2), (key1419, -2), (key1617, -2), (key1541, 2), (key1311, 2), (key1617, 2)]

def rawRow4211 : Integer.Sparse Key := [(key1823, -2), (key1631, -2), (key1665, -2), (key1591, 2), (key1631, 2), (key1442, 2), (key1815, 2), (key1622, 2), (key1657, 2), (key1554, -2), (key1622, -2), (key1324, -2), (key1568, -2), (key1617, -2), (key1419, -2), (key1541, 2), (key1617, 2), (key1311, 2)]

def rawRow4212 : Integer.Sparse Key := [(key1665, -2), (key1823, -2), (key1631, -2), (key1631, 2), (key1442, 2), (key1591, 2), (key1657, 2), (key1815, 2), (key1622, 2), (key1622, -2), (key1324, -2), (key1554, -2), (key1617, -2), (key1419, -2), (key1568, -2), (key1617, 2), (key1311, 2), (key1541, 2)]

def rawRow4213 : Integer.Sparse Key := [(key1823, -2), (key1665, -2), (key1631, -2), (key1631, 2), (key1591, 2), (key1442, 2), (key1815, 2), (key1657, 2), (key1622, 2), (key1622, -2), (key1554, -2), (key1324, -2), (key1617, -2), (key1568, -2), (key1419, -2), (key1617, 2), (key1541, 2), (key1311, 2)]

def rawRow4214 : Integer.Sparse Key := [(key236, -1), (key239, -1), (key406, -1), (key418, -1), (key578, -1), (key583, -1), (key239, 2), (key409, 2), (key418, 2), (key248, 1), (key251, 1), (key435, 1), (key450, 1), (key593, 1), (key601, 1), (key251, -1), (key260, -1), (key319, -1), (key328, -1), (key442, -1), (key450, -1), (key267, -2), (key467, -2), (key475, -2), (key267, 1), (key271, 1), (key335, 1), (key340, 1), (key469, 1), (key475, 1)]

def rawRow4215 : Integer.Sparse Key := [(key239, -1), (key236, -1), (key418, -1), (key406, -1), (key583, -1), (key578, -1), (key239, 2), (key418, 2), (key409, 2), (key251, 1), (key248, 1), (key450, 1), (key435, 1), (key601, 1), (key593, 1), (key260, -1), (key251, -1), (key328, -1), (key319, -1), (key450, -1), (key442, -1), (key267, -2), (key475, -2), (key467, -2), (key271, 1), (key267, 1), (key340, 1), (key335, 1), (key475, 1), (key469, 1)]

def rawRow4216 : Integer.Sparse Key := [(key406, -1), (key418, -1), (key236, -1), (key583, -1), (key239, -1), (key418, -1), (key409, 2), (key239, 2), (key418, 2), (key435, 1), (key593, 1), (key248, 1), (key601, 1), (key251, 1), (key450, 1), (key319, -1), (key442, -1), (key251, -1), (key450, -1), (key260, -1), (key328, -1), (key467, -2), (key267, -2), (key475, -2), (key335, 1), (key469, 1), (key267, 1), (key475, 1), (key271, 1), (key340, 1)]

def rawRow4217 : Integer.Sparse Key := [(key418, -1), (key406, -1), (key583, -1), (key236, -1), (key418, -1), (key239, -1), (key409, 2), (key418, 2), (key239, 2), (key593, 1), (key435, 1), (key601, 1), (key248, 1), (key450, 1), (key251, 1), (key442, -1), (key319, -1), (key450, -1), (key251, -1), (key328, -1), (key260, -1), (key467, -2), (key475, -2), (key267, -2), (key469, 1), (key335, 1), (key475, 1), (key267, 1), (key340, 1), (key271, 1)]

def rawRow4218 : Integer.Sparse Key := [(key578, -1), (key583, -1), (key239, -1), (key418, -1), (key236, -1), (key406, -1), (key418, 2), (key239, 2), (key409, 2), (key450, 1), (key601, 1), (key251, 1), (key593, 1), (key248, 1), (key435, 1), (key328, -1), (key450, -1), (key260, -1), (key442, -1), (key251, -1), (key319, -1), (key475, -2), (key267, -2), (key467, -2), (key340, 1), (key475, 1), (key271, 1), (key469, 1), (key267, 1), (key335, 1)]

def rawRow4219 : Integer.Sparse Key := [(key583, -1), (key578, -1), (key418, -1), (key239, -1), (key406, -1), (key236, -1), (key418, 2), (key409, 2), (key239, 2), (key601, 1), (key450, 1), (key593, 1), (key251, 1), (key435, 1), (key248, 1), (key450, -1), (key328, -1), (key442, -1), (key260, -1), (key319, -1), (key251, -1), (key475, -2), (key467, -2), (key267, -2), (key475, 1), (key340, 1), (key469, 1), (key271, 1), (key335, 1), (key267, 1)]

def rawRow4220 : Integer.Sparse Key := [(key239, -1), (key239, -1), (key409, -1), (key409, -1), (key418, -1), (key418, -1), (key236, 2), (key406, 2), (key406, 2), (key260, 1), (key260, 1), (key442, 1), (key442, 1), (key595, 1), (key595, 1), (key248, -1), (key248, -1), (key316, -1), (key316, -1), (key435, -1), (key435, -1), (key271, -2), (key469, -2), (key469, -2), (key267, 1), (key267, 1), (key335, 1), (key335, 1), (key467, 1), (key467, 1)]

def rawRow4221 : Integer.Sparse Key := [(key409, -1), (key418, -1), (key239, -1), (key418, -1), (key239, -1), (key409, -1), (key406, 2), (key236, 2), (key406, 2), (key442, 1), (key595, 1), (key260, 1), (key595, 1), (key260, 1), (key442, 1), (key316, -1), (key435, -1), (key248, -1), (key435, -1), (key248, -1), (key316, -1), (key469, -2), (key271, -2), (key469, -2), (key335, 1), (key467, 1), (key267, 1), (key467, 1), (key267, 1), (key335, 1)]

def rawRow4222 : Integer.Sparse Key := [(key418, -1), (key409, -1), (key418, -1), (key239, -1), (key409, -1), (key239, -1), (key406, 2), (key406, 2), (key236, 2), (key595, 1), (key442, 1), (key595, 1), (key260, 1), (key442, 1), (key260, 1), (key435, -1), (key316, -1), (key435, -1), (key248, -1), (key316, -1), (key248, -1), (key469, -2), (key469, -2), (key271, -2), (key467, 1), (key335, 1), (key467, 1), (key267, 1), (key335, 1), (key267, 1)]

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

def rawRow4235 : Integer.Sparse Key := [(key267, -1), (key267, -1), (key467, -1), (key467, -1), (key475, -1), (key475, -1), (key271, 2), (key469, 2), (key469, 2), (key239, 1), (key239, 1), (key409, 1), (key409, 1), (key418, 1), (key418, 1), (key260, -1), (key260, -1), (key397, -1), (key397, -1), (key442, -1), (key442, -1), (key236, -2), (key406, -2), (key406, -2), (key248, 1), (key248, 1), (key316, 1), (key316, 1), (key435, 1), (key435, 1)]

def rawRow4236 : Integer.Sparse Key := [(key467, -1), (key475, -1), (key267, -1), (key475, -1), (key267, -1), (key467, -1), (key469, 2), (key271, 2), (key469, 2), (key409, 1), (key418, 1), (key239, 1), (key418, 1), (key239, 1), (key409, 1), (key397, -1), (key442, -1), (key260, -1), (key442, -1), (key260, -1), (key397, -1), (key406, -2), (key236, -2), (key406, -2), (key316, 1), (key435, 1), (key248, 1), (key435, 1), (key248, 1), (key316, 1)]

def rawRow4237 : Integer.Sparse Key := [(key475, -1), (key467, -1), (key475, -1), (key267, -1), (key467, -1), (key267, -1), (key469, 2), (key469, 2), (key271, 2), (key418, 1), (key409, 1), (key418, 1), (key239, 1), (key409, 1), (key239, 1), (key442, -1), (key397, -1), (key442, -1), (key260, -1), (key397, -1), (key260, -1), (key406, -2), (key406, -2), (key236, -2), (key435, 1), (key316, 1), (key435, 1), (key248, 1), (key316, 1), (key248, 1)]

def rawRow4238 : Integer.Sparse Key := [(key267, -1), (key271, -1), (key335, -1), (key469, -1), (key340, -1), (key475, -1), (key267, 2), (key335, 2), (key467, 2), (key251, 1), (key260, 1), (key319, 1), (key442, 1), (key328, 1), (key450, 1), (key239, -1), (key251, -1), (key305, -1), (key388, -1), (key319, -1), (key409, -1), (key248, -2), (key316, -2), (key435, -2), (key236, 1), (key248, 1), (key302, 1), (key316, 1), (key385, 1), (key406, 1)]

def rawRow4239 : Integer.Sparse Key := [(key271, -1), (key267, -1), (key469, -1), (key335, -1), (key475, -1), (key340, -1), (key267, 2), (key467, 2), (key335, 2), (key260, 1), (key251, 1), (key442, 1), (key319, 1), (key450, 1), (key328, 1), (key251, -1), (key239, -1), (key388, -1), (key305, -1), (key409, -1), (key319, -1), (key248, -2), (key435, -2), (key316, -2), (key248, 1), (key236, 1), (key316, 1), (key302, 1), (key406, 1), (key385, 1)]

def rawRow4240 : Integer.Sparse Key := [(key335, -1), (key340, -1), (key267, -1), (key475, -1), (key271, -1), (key469, -1), (key335, 2), (key267, 2), (key467, 2), (key319, 1), (key328, 1), (key251, 1), (key450, 1), (key260, 1), (key442, 1), (key305, -1), (key319, -1), (key239, -1), (key409, -1), (key251, -1), (key388, -1), (key316, -2), (key248, -2), (key435, -2), (key302, 1), (key316, 1), (key236, 1), (key406, 1), (key248, 1), (key316, 1)]

def rawRow4241 : Integer.Sparse Key := [(key340, -1), (key335, -1), (key475, -1), (key267, -1), (key469, -1), (key271, -1), (key335, 2), (key467, 2), (key267, 2), (key328, 1), (key319, 1), (key450, 1), (key251, 1), (key442, 1), (key260, 1), (key319, -1), (key305, -1), (key409, -1), (key239, -1), (key388, -1), (key251, -1), (key316, -2), (key435, -2), (key248, -2), (key316, 1), (key302, 1), (key406, 1), (key236, 1), (key316, 1), (key248, 1)]

def rawRow4242 : Integer.Sparse Key := [(key469, -1), (key475, -1), (key271, -1), (key340, -1), (key267, -1), (key335, -1), (key467, 2), (key267, 2), (key335, 2), (key442, 1), (key450, 1), (key260, 1), (key328, 1), (key251, 1), (key319, 1), (key388, -1), (key409, -1), (key251, -1), (key319, -1), (key239, -1), (key305, -1), (key435, -2), (key248, -2), (key316, -2), (key385, 1), (key406, 1), (key248, 1), (key316, 1), (key236, 1), (key302, 1)]

def rawRow4243 : Integer.Sparse Key := [(key475, -1), (key469, -1), (key340, -1), (key271, -1), (key335, -1), (key267, -1), (key467, 2), (key335, 2), (key267, 2), (key450, 1), (key442, 1), (key328, 1), (key260, 1), (key319, 1), (key251, 1), (key409, -1), (key388, -1), (key319, -1), (key251, -1), (key305, -1), (key239, -1), (key435, -2), (key316, -2), (key248, -2), (key406, 1), (key385, 1), (key316, 1), (key248, 1), (key302, 1), (key236, 1)]

def rawRow4244 : Integer.Sparse Key := [(key2642, -2), (key2729, -2), (key2883, -2), (key2632, 1), (key2640, 1), (key2706, 1), (key2860, 1), (key2726, 1), (key2870, 1), (key2654, 2), (key2748, 2), (key2913, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2649, -1), (key2654, -1), (key2738, -1), (key2898, -1), (key2748, -1), (key2905, -1), (key2619, 1), (key2642, 1), (key2674, 1), (key2796, 1), (key2729, 1), (key2832, 1)]

def rawRow4245 : Integer.Sparse Key := [(key2642, -2), (key2883, -2), (key2729, -2), (key2640, 1), (key2632, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2726, 1), (key2654, 2), (key2913, 2), (key2748, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2654, -1), (key2649, -1), (key2898, -1), (key2738, -1), (key2905, -1), (key2748, -1), (key2642, 1), (key2619, 1), (key2796, 1), (key2674, 1), (key2832, 1), (key2729, 1)]

def rawRow4246 : Integer.Sparse Key := [(key2729, -2), (key2642, -2), (key2883, -2), (key2706, 1), (key2726, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2748, 2), (key2654, 2), (key2913, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2738, -1), (key2748, -1), (key2649, -1), (key2905, -1), (key2654, -1), (key2898, -1), (key2674, 1), (key2729, 1), (key2619, 1), (key2832, 1), (key2642, 1), (key2796, 1)]

def rawRow4247 : Integer.Sparse Key := [(key2729, -2), (key2883, -2), (key2642, -2), (key2726, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2860, 1), (key2640, 1), (key2748, 2), (key2913, 2), (key2654, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2748, -1), (key2738, -1), (key2905, -1), (key2649, -1), (key2898, -1), (key2654, -1), (key2729, 1), (key2674, 1), (key2832, 1), (key2619, 1), (key2796, 1), (key2642, 1)]

def rawRow4248 : Integer.Sparse Key := [(key2883, -2), (key2642, -2), (key2729, -2), (key2860, 1), (key2870, 1), (key2640, 1), (key2726, 1), (key2632, 1), (key2706, 1), (key2913, 2), (key2654, 2), (key2748, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2898, -1), (key2905, -1), (key2654, -1), (key2748, -1), (key2649, -1), (key2738, -1), (key2796, 1), (key2832, 1), (key2642, 1), (key2729, 1), (key2619, 1), (key2674, 1)]

def rawRow4249 : Integer.Sparse Key := [(key2883, -2), (key2729, -2), (key2642, -2), (key2870, 1), (key2860, 1), (key2726, 1), (key2640, 1), (key2706, 1), (key2632, 1), (key2913, 2), (key2748, 2), (key2654, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2905, -1), (key2898, -1), (key2748, -1), (key2654, -1), (key2738, -1), (key2649, -1), (key2832, 1), (key2796, 1), (key2729, 1), (key2642, 1), (key2674, 1), (key2619, 1)]

def rawRow4250 : Integer.Sparse Key := [(key2654, -2), (key2748, -2), (key2913, -2), (key2649, 1), (key2654, 1), (key2738, 1), (key2898, 1), (key2748, 1), (key2905, 1), (key2642, 2), (key2729, 2), (key2883, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2796, -1), (key2729, -1), (key2832, -1), (key2632, -1), (key2640, -1), (key2706, -1), (key2860, -1), (key2726, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

def rawRow4251 : Integer.Sparse Key := [(key2654, -2), (key2913, -2), (key2748, -2), (key2654, 1), (key2649, 1), (key2898, 1), (key2738, 1), (key2905, 1), (key2748, 1), (key2642, 2), (key2883, 2), (key2729, 2), (key2642, -1), (key2619, -1), (key2796, -1), (key2674, -1), (key2832, -1), (key2729, -1), (key2640, -1), (key2632, -1), (key2860, -1), (key2706, -1), (key2870, -1), (key2726, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

def rawRow4252 : Integer.Sparse Key := [(key2748, -2), (key2654, -2), (key2913, -2), (key2738, 1), (key2748, 1), (key2649, 1), (key2905, 1), (key2654, 1), (key2898, 1), (key2729, 2), (key2642, 2), (key2883, 2), (key2674, -1), (key2729, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2706, -1), (key2726, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

def rawRow4253 : Integer.Sparse Key := [(key2748, -2), (key2913, -2), (key2654, -2), (key2748, 1), (key2738, 1), (key2905, 1), (key2649, 1), (key2898, 1), (key2654, 1), (key2729, 2), (key2883, 2), (key2642, 2), (key2729, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2796, -1), (key2642, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2860, -1), (key2640, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

def rawRow4254 : Integer.Sparse Key := [(key2913, -2), (key2654, -2), (key2748, -2), (key2898, 1), (key2905, 1), (key2654, 1), (key2748, 1), (key2649, 1), (key2738, 1), (key2883, 2), (key2642, 2), (key2729, 2), (key2796, -1), (key2832, -1), (key2642, -1), (key2729, -1), (key2619, -1), (key2674, -1), (key2860, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2632, -1), (key2706, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

def rawRow4255 : Integer.Sparse Key := [(key2913, -2), (key2748, -2), (key2654, -2), (key2905, 1), (key2898, 1), (key2748, 1), (key2654, 1), (key2738, 1), (key2649, 1), (key2883, 2), (key2729, 2), (key2642, 2), (key2832, -1), (key2796, -1), (key2729, -1), (key2642, -1), (key2674, -1), (key2619, -1), (key2870, -1), (key2860, -1), (key2726, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

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

def rawRow4268 : Integer.Sparse Key := [(key2894, -2), (key2896, -2), (key2903, -2), (key2783, 1), (key2791, 1), (key2806, 1), (key2857, 1), (key2826, 1), (key2867, 1), (key2973, 2), (key2975, 2), (key2982, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2975, -1), (key2959, -1), (key2982, -1), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1)]

def rawRow4269 : Integer.Sparse Key := [(key2896, -2), (key2894, -2), (key2903, -2), (key2791, 1), (key2783, 1), (key2857, 1), (key2806, 1), (key2867, 1), (key2826, 1), (key2975, 2), (key2973, 2), (key2982, 2), (key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2942, -1), (key2937, -1), (key2975, -1), (key2949, -1), (key2982, -1), (key2959, -1), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1)]

def rawRow4270 : Integer.Sparse Key := [(key2894, -2), (key2903, -2), (key2896, -2), (key2806, 1), (key2826, 1), (key2783, 1), (key2867, 1), (key2791, 1), (key2857, 1), (key2973, 2), (key2982, 2), (key2975, 2), (key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2949, -1), (key2959, -1), (key2937, -1), (key2982, -1), (key2942, -1), (key2975, -1), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1)]

def rawRow4271 : Integer.Sparse Key := [(key2903, -2), (key2894, -2), (key2896, -2), (key2826, 1), (key2806, 1), (key2867, 1), (key2783, 1), (key2857, 1), (key2791, 1), (key2982, 2), (key2973, 2), (key2975, 2), (key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2959, -1), (key2949, -1), (key2982, -1), (key2937, -1), (key2975, -1), (key2942, -1), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1)]

def rawRow4272 : Integer.Sparse Key := [(key2896, -2), (key2903, -2), (key2894, -2), (key2857, 1), (key2867, 1), (key2791, 1), (key2826, 1), (key2783, 1), (key2806, 1), (key2975, 2), (key2982, 2), (key2973, 2), (key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2975, -1), (key2982, -1), (key2942, -1), (key2959, -1), (key2937, -1), (key2949, -1), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1)]

def rawRow4273 : Integer.Sparse Key := [(key2903, -2), (key2896, -2), (key2894, -2), (key2867, 1), (key2857, 1), (key2826, 1), (key2791, 1), (key2806, 1), (key2783, 1), (key2982, 2), (key2975, 2), (key2973, 2), (key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2982, -1), (key2975, -1), (key2959, -1), (key2942, -1), (key2949, -1), (key2937, -1), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1)]

def rawRow4274 : Integer.Sparse Key := [(key2973, -2), (key2975, -2), (key2982, -2), (key2937, 1), (key2942, 1), (key2949, 1), (key2975, 1), (key2959, 1), (key2982, 1), (key2894, 2), (key2896, 2), (key2903, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2857, -1), (key2826, -1), (key2867, -1), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1)]

def rawRow4275 : Integer.Sparse Key := [(key2975, -2), (key2973, -2), (key2982, -2), (key2942, 1), (key2937, 1), (key2975, 1), (key2949, 1), (key2982, 1), (key2959, 1), (key2896, 2), (key2894, 2), (key2903, 2), (key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2791, -1), (key2783, -1), (key2857, -1), (key2806, -1), (key2867, -1), (key2826, -1), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1)]

def rawRow4276 : Integer.Sparse Key := [(key2973, -2), (key2982, -2), (key2975, -2), (key2949, 1), (key2959, 1), (key2937, 1), (key2982, 1), (key2942, 1), (key2975, 1), (key2894, 2), (key2903, 2), (key2896, 2), (key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2806, -1), (key2826, -1), (key2783, -1), (key2867, -1), (key2791, -1), (key2857, -1), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1)]

def rawRow4277 : Integer.Sparse Key := [(key2982, -2), (key2973, -2), (key2975, -2), (key2959, 1), (key2949, 1), (key2982, 1), (key2937, 1), (key2975, 1), (key2942, 1), (key2903, 2), (key2894, 2), (key2896, 2), (key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2826, -1), (key2806, -1), (key2867, -1), (key2783, -1), (key2857, -1), (key2791, -1), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1)]

def rawRow4278 : Integer.Sparse Key := [(key2975, -2), (key2982, -2), (key2973, -2), (key2975, 1), (key2982, 1), (key2942, 1), (key2959, 1), (key2937, 1), (key2949, 1), (key2896, 2), (key2903, 2), (key2894, 2), (key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2857, -1), (key2867, -1), (key2791, -1), (key2826, -1), (key2783, -1), (key2806, -1), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1)]

def rawRow4279 : Integer.Sparse Key := [(key2982, -2), (key2975, -2), (key2973, -2), (key2982, 1), (key2975, 1), (key2959, 1), (key2942, 1), (key2949, 1), (key2937, 1), (key2903, 2), (key2896, 2), (key2894, 2), (key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2867, -1), (key2857, -1), (key2826, -1), (key2791, -1), (key2806, -1), (key2783, -1), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1)]

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

def rawRow4304 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1425, -1), (key1623, -1), (key1443, -1), (key1632, -1), (key1312, 2), (key1420, 2), (key1618, 2), (key1338, 1), (key1344, 1), (key1456, 1), (key1658, 1), (key1465, 1), (key1666, 1), (key1292, -1), (key1312, -1), (key1387, -1), (key1542, -1), (key1420, -1), (key1569, -1), (key1338, -2), (key1456, -2), (key1656, -2), (key1297, 1), (key1317, 1), (key1392, 1), (key1547, 1), (key1425, 1), (key1574, 1)]

def rawRow4305 : Integer.Sparse Key := [(key1325, -1), (key1317, -1), (key1623, -1), (key1425, -1), (key1632, -1), (key1443, -1), (key1312, 2), (key1618, 2), (key1420, 2), (key1344, 1), (key1338, 1), (key1658, 1), (key1456, 1), (key1666, 1), (key1465, 1), (key1312, -1), (key1292, -1), (key1542, -1), (key1387, -1), (key1569, -1), (key1420, -1), (key1338, -2), (key1656, -2), (key1456, -2), (key1317, 1), (key1297, 1), (key1547, 1), (key1392, 1), (key1574, 1), (key1425, 1)]

def rawRow4306 : Integer.Sparse Key := [(key1425, -1), (key1443, -1), (key1317, -1), (key1632, -1), (key1325, -1), (key1623, -1), (key1420, 2), (key1312, 2), (key1618, 2), (key1456, 1), (key1465, 1), (key1338, 1), (key1666, 1), (key1344, 1), (key1658, 1), (key1387, -1), (key1420, -1), (key1292, -1), (key1569, -1), (key1312, -1), (key1542, -1), (key1456, -2), (key1338, -2), (key1656, -2), (key1392, 1), (key1425, 1), (key1297, 1), (key1574, 1), (key1317, 1), (key1547, 1)]

def rawRow4307 : Integer.Sparse Key := [(key1443, -1), (key1425, -1), (key1632, -1), (key1317, -1), (key1623, -1), (key1325, -1), (key1420, 2), (key1618, 2), (key1312, 2), (key1465, 1), (key1456, 1), (key1666, 1), (key1338, 1), (key1658, 1), (key1344, 1), (key1420, -1), (key1387, -1), (key1569, -1), (key1292, -1), (key1542, -1), (key1312, -1), (key1456, -2), (key1656, -2), (key1338, -2), (key1425, 1), (key1392, 1), (key1574, 1), (key1297, 1), (key1547, 1), (key1317, 1)]

def rawRow4308 : Integer.Sparse Key := [(key1623, -1), (key1632, -1), (key1325, -1), (key1443, -1), (key1317, -1), (key1425, -1), (key1618, 2), (key1312, 2), (key1420, 2), (key1658, 1), (key1666, 1), (key1344, 1), (key1465, 1), (key1338, 1), (key1456, 1), (key1542, -1), (key1569, -1), (key1312, -1), (key1420, -1), (key1292, -1), (key1387, -1), (key1656, -2), (key1338, -2), (key1456, -2), (key1547, 1), (key1574, 1), (key1317, 1), (key1425, 1), (key1297, 1), (key1392, 1)]

def rawRow4309 : Integer.Sparse Key := [(key1632, -1), (key1623, -1), (key1443, -1), (key1325, -1), (key1425, -1), (key1317, -1), (key1618, 2), (key1420, 2), (key1312, 2), (key1666, 1), (key1658, 1), (key1465, 1), (key1344, 1), (key1456, 1), (key1338, 1), (key1569, -1), (key1542, -1), (key1420, -1), (key1312, -1), (key1387, -1), (key1292, -1), (key1656, -2), (key1456, -2), (key1338, -2), (key1574, 1), (key1547, 1), (key1425, 1), (key1317, 1), (key1392, 1), (key1297, 1)]

def rawRow4310 : Integer.Sparse Key := [(key1338, -1), (key1344, -1), (key1456, -1), (key1658, -1), (key1465, -1), (key1666, -1), (key1338, 2), (key1456, 2), (key1656, 2), (key1317, 1), (key1325, 1), (key1425, 1), (key1623, 1), (key1443, 1), (key1632, 1), (key1297, -1), (key1317, -1), (key1392, -1), (key1547, -1), (key1425, -1), (key1574, -1), (key1312, -2), (key1420, -2), (key1618, -2), (key1292, 1), (key1312, 1), (key1387, 1), (key1542, 1), (key1420, 1), (key1569, 1)]

def rawRow4311 : Integer.Sparse Key := [(key1344, -1), (key1338, -1), (key1658, -1), (key1456, -1), (key1666, -1), (key1465, -1), (key1338, 2), (key1656, 2), (key1456, 2), (key1325, 1), (key1317, 1), (key1623, 1), (key1425, 1), (key1632, 1), (key1443, 1), (key1317, -1), (key1297, -1), (key1547, -1), (key1392, -1), (key1574, -1), (key1425, -1), (key1312, -2), (key1618, -2), (key1420, -2), (key1312, 1), (key1292, 1), (key1542, 1), (key1387, 1), (key1569, 1), (key1420, 1)]

def rawRow4312 : Integer.Sparse Key := [(key1456, -1), (key1465, -1), (key1338, -1), (key1666, -1), (key1344, -1), (key1658, -1), (key1456, 2), (key1338, 2), (key1656, 2), (key1425, 1), (key1443, 1), (key1317, 1), (key1632, 1), (key1325, 1), (key1623, 1), (key1392, -1), (key1425, -1), (key1297, -1), (key1574, -1), (key1317, -1), (key1547, -1), (key1420, -2), (key1312, -2), (key1618, -2), (key1387, 1), (key1420, 1), (key1292, 1), (key1569, 1), (key1312, 1), (key1542, 1)]

def rawRow4313 : Integer.Sparse Key := [(key1465, -1), (key1456, -1), (key1666, -1), (key1338, -1), (key1658, -1), (key1344, -1), (key1456, 2), (key1656, 2), (key1338, 2), (key1443, 1), (key1425, 1), (key1632, 1), (key1317, 1), (key1623, 1), (key1325, 1), (key1425, -1), (key1392, -1), (key1574, -1), (key1297, -1), (key1547, -1), (key1317, -1), (key1420, -2), (key1618, -2), (key1312, -2), (key1420, 1), (key1387, 1), (key1569, 1), (key1292, 1), (key1542, 1), (key1312, 1)]

def rawRow4314 : Integer.Sparse Key := [(key1658, -1), (key1666, -1), (key1344, -1), (key1465, -1), (key1338, -1), (key1456, -1), (key1656, 2), (key1338, 2), (key1456, 2), (key1623, 1), (key1632, 1), (key1325, 1), (key1443, 1), (key1317, 1), (key1425, 1), (key1547, -1), (key1574, -1), (key1317, -1), (key1425, -1), (key1297, -1), (key1392, -1), (key1618, -2), (key1312, -2), (key1420, -2), (key1542, 1), (key1569, 1), (key1312, 1), (key1420, 1), (key1292, 1), (key1387, 1)]

def rawRow4315 : Integer.Sparse Key := [(key1666, -1), (key1658, -1), (key1465, -1), (key1344, -1), (key1456, -1), (key1338, -1), (key1656, 2), (key1456, 2), (key1338, 2), (key1632, 1), (key1623, 1), (key1443, 1), (key1325, 1), (key1425, 1), (key1317, 1), (key1574, -1), (key1547, -1), (key1425, -1), (key1317, -1), (key1392, -1), (key1297, -1), (key1618, -2), (key1420, -2), (key1312, -2), (key1569, 1), (key1542, 1), (key1420, 1), (key1312, 1), (key1387, 1), (key1292, 1)]

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

def rawRow4328 : Integer.Sparse Key := [(key1656, -2), (key1658, -2), (key1666, -2), (key1547, 1), (key1555, 1), (key1574, 1), (key1623, 1), (key1592, 1), (key1632, 1), (key1814, 2), (key1816, 2), (key1824, 2), (key1317, -1), (key1325, -1), (key1425, -1), (key1623, -1), (key1443, -1), (key1632, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1816, -1), (key1797, -1), (key1824, -1), (key1338, 1), (key1344, 1), (key1456, 1), (key1658, 1), (key1465, 1), (key1666, 1)]

def rawRow4329 : Integer.Sparse Key := [(key1658, -2), (key1656, -2), (key1666, -2), (key1555, 1), (key1547, 1), (key1623, 1), (key1574, 1), (key1632, 1), (key1592, 1), (key1816, 2), (key1814, 2), (key1824, 2), (key1325, -1), (key1317, -1), (key1623, -1), (key1425, -1), (key1632, -1), (key1443, -1), (key1779, -1), (key1773, -1), (key1816, -1), (key1789, -1), (key1824, -1), (key1797, -1), (key1344, 1), (key1338, 1), (key1658, 1), (key1456, 1), (key1666, 1), (key1465, 1)]

def rawRow4330 : Integer.Sparse Key := [(key1656, -2), (key1666, -2), (key1658, -2), (key1574, 1), (key1592, 1), (key1547, 1), (key1632, 1), (key1555, 1), (key1623, 1), (key1814, 2), (key1824, 2), (key1816, 2), (key1425, -1), (key1443, -1), (key1317, -1), (key1632, -1), (key1325, -1), (key1623, -1), (key1789, -1), (key1797, -1), (key1773, -1), (key1824, -1), (key1779, -1), (key1816, -1), (key1456, 1), (key1465, 1), (key1338, 1), (key1666, 1), (key1344, 1), (key1658, 1)]

def rawRow4331 : Integer.Sparse Key := [(key1666, -2), (key1656, -2), (key1658, -2), (key1592, 1), (key1574, 1), (key1632, 1), (key1547, 1), (key1623, 1), (key1555, 1), (key1824, 2), (key1814, 2), (key1816, 2), (key1443, -1), (key1425, -1), (key1632, -1), (key1317, -1), (key1623, -1), (key1325, -1), (key1797, -1), (key1789, -1), (key1824, -1), (key1773, -1), (key1816, -1), (key1779, -1), (key1465, 1), (key1456, 1), (key1666, 1), (key1338, 1), (key1658, 1), (key1344, 1)]

def rawRow4332 : Integer.Sparse Key := [(key1658, -2), (key1666, -2), (key1656, -2), (key1623, 1), (key1632, 1), (key1555, 1), (key1592, 1), (key1547, 1), (key1574, 1), (key1816, 2), (key1824, 2), (key1814, 2), (key1623, -1), (key1632, -1), (key1325, -1), (key1443, -1), (key1317, -1), (key1425, -1), (key1816, -1), (key1824, -1), (key1779, -1), (key1797, -1), (key1773, -1), (key1789, -1), (key1658, 1), (key1666, 1), (key1344, 1), (key1465, 1), (key1338, 1), (key1456, 1)]

def rawRow4333 : Integer.Sparse Key := [(key1666, -2), (key1658, -2), (key1656, -2), (key1632, 1), (key1623, 1), (key1592, 1), (key1555, 1), (key1574, 1), (key1547, 1), (key1824, 2), (key1816, 2), (key1814, 2), (key1632, -1), (key1623, -1), (key1443, -1), (key1325, -1), (key1425, -1), (key1317, -1), (key1824, -1), (key1816, -1), (key1797, -1), (key1779, -1), (key1789, -1), (key1773, -1), (key1666, 1), (key1658, 1), (key1465, 1), (key1344, 1), (key1456, 1), (key1338, 1)]

def rawRow4334 : Integer.Sparse Key := [(key1814, -2), (key1816, -2), (key1824, -2), (key1773, 1), (key1779, 1), (key1789, 1), (key1816, 1), (key1797, 1), (key1824, 1), (key1656, 2), (key1658, 2), (key1666, 2), (key1338, -1), (key1344, -1), (key1456, -1), (key1658, -1), (key1465, -1), (key1666, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1623, -1), (key1592, -1), (key1632, -1), (key1317, 1), (key1325, 1), (key1425, 1), (key1623, 1), (key1443, 1), (key1632, 1)]

def rawRow4335 : Integer.Sparse Key := [(key1816, -2), (key1814, -2), (key1824, -2), (key1779, 1), (key1773, 1), (key1816, 1), (key1789, 1), (key1824, 1), (key1797, 1), (key1658, 2), (key1656, 2), (key1666, 2), (key1344, -1), (key1338, -1), (key1658, -1), (key1456, -1), (key1666, -1), (key1465, -1), (key1555, -1), (key1547, -1), (key1623, -1), (key1574, -1), (key1632, -1), (key1592, -1), (key1325, 1), (key1317, 1), (key1623, 1), (key1425, 1), (key1632, 1), (key1443, 1)]

def rawRow4336 : Integer.Sparse Key := [(key1814, -2), (key1824, -2), (key1816, -2), (key1789, 1), (key1797, 1), (key1773, 1), (key1824, 1), (key1779, 1), (key1816, 1), (key1656, 2), (key1666, 2), (key1658, 2), (key1456, -1), (key1465, -1), (key1338, -1), (key1666, -1), (key1344, -1), (key1658, -1), (key1574, -1), (key1592, -1), (key1547, -1), (key1632, -1), (key1555, -1), (key1623, -1), (key1425, 1), (key1443, 1), (key1317, 1), (key1632, 1), (key1325, 1), (key1623, 1)]

def rawRow4337 : Integer.Sparse Key := [(key1824, -2), (key1814, -2), (key1816, -2), (key1797, 1), (key1789, 1), (key1824, 1), (key1773, 1), (key1816, 1), (key1779, 1), (key1666, 2), (key1656, 2), (key1658, 2), (key1465, -1), (key1456, -1), (key1666, -1), (key1338, -1), (key1658, -1), (key1344, -1), (key1592, -1), (key1574, -1), (key1632, -1), (key1547, -1), (key1623, -1), (key1555, -1), (key1443, 1), (key1425, 1), (key1632, 1), (key1317, 1), (key1623, 1), (key1325, 1)]

def rawRow4338 : Integer.Sparse Key := [(key1816, -2), (key1824, -2), (key1814, -2), (key1816, 1), (key1824, 1), (key1779, 1), (key1797, 1), (key1773, 1), (key1789, 1), (key1658, 2), (key1666, 2), (key1656, 2), (key1658, -1), (key1666, -1), (key1344, -1), (key1465, -1), (key1338, -1), (key1456, -1), (key1623, -1), (key1632, -1), (key1555, -1), (key1592, -1), (key1547, -1), (key1574, -1), (key1623, 1), (key1632, 1), (key1325, 1), (key1443, 1), (key1317, 1), (key1425, 1)]

def rawRow4339 : Integer.Sparse Key := [(key1824, -2), (key1816, -2), (key1814, -2), (key1824, 1), (key1816, 1), (key1797, 1), (key1779, 1), (key1789, 1), (key1773, 1), (key1666, 2), (key1658, 2), (key1656, 2), (key1666, -1), (key1658, -1), (key1465, -1), (key1344, -1), (key1456, -1), (key1338, -1), (key1632, -1), (key1623, -1), (key1592, -1), (key1555, -1), (key1574, -1), (key1547, -1), (key1632, 1), (key1623, 1), (key1443, 1), (key1325, 1), (key1425, 1), (key1317, 1)]

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

def rawRow4352 : Integer.Sparse Key := [(key2796, -2), (key2832, -2), (key2883, -2), (key2786, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2829, 1), (key2870, 1), (key2944, 2), (key2961, 2), (key2992, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2939, -1), (key2944, -1), (key2951, -1), (key2977, -1), (key2961, -1), (key2984, -1), (key2619, 1), (key2642, 1), (key2674, 1), (key2796, 1), (key2729, 1), (key2832, 1)]

def rawRow4353 : Integer.Sparse Key := [(key2796, -2), (key2883, -2), (key2832, -2), (key2794, 1), (key2786, 1), (key2860, 1), (key2809, 1), (key2870, 1), (key2829, 1), (key2944, 2), (key2992, 2), (key2961, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2944, -1), (key2939, -1), (key2977, -1), (key2951, -1), (key2984, -1), (key2961, -1), (key2642, 1), (key2619, 1), (key2796, 1), (key2674, 1), (key2832, 1), (key2729, 1)]

def rawRow4354 : Integer.Sparse Key := [(key2832, -2), (key2796, -2), (key2883, -2), (key2809, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2794, 1), (key2860, 1), (key2961, 2), (key2944, 2), (key2992, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2951, -1), (key2961, -1), (key2939, -1), (key2984, -1), (key2944, -1), (key2977, -1), (key2674, 1), (key2729, 1), (key2619, 1), (key2832, 1), (key2642, 1), (key2796, 1)]

def rawRow4355 : Integer.Sparse Key := [(key2832, -2), (key2883, -2), (key2796, -2), (key2829, 1), (key2809, 1), (key2870, 1), (key2786, 1), (key2860, 1), (key2794, 1), (key2961, 2), (key2992, 2), (key2944, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2961, -1), (key2951, -1), (key2984, -1), (key2939, -1), (key2977, -1), (key2944, -1), (key2729, 1), (key2674, 1), (key2832, 1), (key2619, 1), (key2796, 1), (key2642, 1)]

def rawRow4356 : Integer.Sparse Key := [(key2883, -2), (key2796, -2), (key2832, -2), (key2860, 1), (key2870, 1), (key2794, 1), (key2829, 1), (key2786, 1), (key2809, 1), (key2992, 2), (key2944, 2), (key2961, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2977, -1), (key2984, -1), (key2944, -1), (key2961, -1), (key2939, -1), (key2951, -1), (key2796, 1), (key2832, 1), (key2642, 1), (key2729, 1), (key2619, 1), (key2674, 1)]

def rawRow4357 : Integer.Sparse Key := [(key2883, -2), (key2832, -2), (key2796, -2), (key2870, 1), (key2860, 1), (key2829, 1), (key2794, 1), (key2809, 1), (key2786, 1), (key2992, 2), (key2961, 2), (key2944, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2984, -1), (key2977, -1), (key2961, -1), (key2944, -1), (key2951, -1), (key2939, -1), (key2832, 1), (key2796, 1), (key2729, 1), (key2642, 1), (key2674, 1), (key2619, 1)]

def rawRow4358 : Integer.Sparse Key := [(key2944, -2), (key2961, -2), (key2992, -2), (key2939, 1), (key2944, 1), (key2951, 1), (key2977, 1), (key2961, 1), (key2984, 1), (key2796, 2), (key2832, 2), (key2883, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2796, -1), (key2729, -1), (key2832, -1), (key2786, -1), (key2794, -1), (key2809, -1), (key2860, -1), (key2829, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

def rawRow4359 : Integer.Sparse Key := [(key2944, -2), (key2992, -2), (key2961, -2), (key2944, 1), (key2939, 1), (key2977, 1), (key2951, 1), (key2984, 1), (key2961, 1), (key2796, 2), (key2883, 2), (key2832, 2), (key2642, -1), (key2619, -1), (key2796, -1), (key2674, -1), (key2832, -1), (key2729, -1), (key2794, -1), (key2786, -1), (key2860, -1), (key2809, -1), (key2870, -1), (key2829, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

def rawRow4360 : Integer.Sparse Key := [(key2961, -2), (key2944, -2), (key2992, -2), (key2951, 1), (key2961, 1), (key2939, 1), (key2984, 1), (key2944, 1), (key2977, 1), (key2832, 2), (key2796, 2), (key2883, 2), (key2674, -1), (key2729, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2809, -1), (key2829, -1), (key2786, -1), (key2870, -1), (key2794, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

def rawRow4361 : Integer.Sparse Key := [(key2961, -2), (key2992, -2), (key2944, -2), (key2961, 1), (key2951, 1), (key2984, 1), (key2939, 1), (key2977, 1), (key2944, 1), (key2832, 2), (key2883, 2), (key2796, 2), (key2729, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2796, -1), (key2642, -1), (key2829, -1), (key2809, -1), (key2870, -1), (key2786, -1), (key2860, -1), (key2794, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

def rawRow4362 : Integer.Sparse Key := [(key2992, -2), (key2944, -2), (key2961, -2), (key2977, 1), (key2984, 1), (key2944, 1), (key2961, 1), (key2939, 1), (key2951, 1), (key2883, 2), (key2796, 2), (key2832, 2), (key2796, -1), (key2832, -1), (key2642, -1), (key2729, -1), (key2619, -1), (key2674, -1), (key2860, -1), (key2870, -1), (key2794, -1), (key2829, -1), (key2786, -1), (key2809, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

def rawRow4363 : Integer.Sparse Key := [(key2992, -2), (key2961, -2), (key2944, -2), (key2984, 1), (key2977, 1), (key2961, 1), (key2944, 1), (key2951, 1), (key2939, 1), (key2883, 2), (key2832, 2), (key2796, 2), (key2832, -1), (key2796, -1), (key2729, -1), (key2642, -1), (key2674, -1), (key2619, -1), (key2870, -1), (key2860, -1), (key2829, -1), (key2794, -1), (key2809, -1), (key2786, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

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

def rawRow4388 : Integer.Sparse Key := [(key2892, -2), (key2895, -2), (key2902, -2), (key2781, 1), (key2790, 1), (key2804, 1), (key2856, 1), (key2825, 1), (key2866, 1), (key2971, 2), (key2974, 2), (key2981, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2974, -1), (key2958, -1), (key2981, -1), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1)]

def rawRow4389 : Integer.Sparse Key := [(key2895, -2), (key2892, -2), (key2902, -2), (key2790, 1), (key2781, 1), (key2856, 1), (key2804, 1), (key2866, 1), (key2825, 1), (key2974, 2), (key2971, 2), (key2981, 2), (key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2941, -1), (key2935, -1), (key2974, -1), (key2947, -1), (key2981, -1), (key2958, -1), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1)]

def rawRow4390 : Integer.Sparse Key := [(key2892, -2), (key2902, -2), (key2895, -2), (key2804, 1), (key2825, 1), (key2781, 1), (key2866, 1), (key2790, 1), (key2856, 1), (key2971, 2), (key2981, 2), (key2974, 2), (key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2947, -1), (key2958, -1), (key2935, -1), (key2981, -1), (key2941, -1), (key2974, -1), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1)]

def rawRow4391 : Integer.Sparse Key := [(key2902, -2), (key2892, -2), (key2895, -2), (key2825, 1), (key2804, 1), (key2866, 1), (key2781, 1), (key2856, 1), (key2790, 1), (key2981, 2), (key2971, 2), (key2974, 2), (key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2958, -1), (key2947, -1), (key2981, -1), (key2935, -1), (key2974, -1), (key2941, -1), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1)]

def rawRow4392 : Integer.Sparse Key := [(key2895, -2), (key2902, -2), (key2892, -2), (key2856, 1), (key2866, 1), (key2790, 1), (key2825, 1), (key2781, 1), (key2804, 1), (key2974, 2), (key2981, 2), (key2971, 2), (key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2974, -1), (key2981, -1), (key2941, -1), (key2958, -1), (key2935, -1), (key2947, -1), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1)]

def rawRow4393 : Integer.Sparse Key := [(key2902, -2), (key2895, -2), (key2892, -2), (key2866, 1), (key2856, 1), (key2825, 1), (key2790, 1), (key2804, 1), (key2781, 1), (key2981, 2), (key2974, 2), (key2971, 2), (key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2981, -1), (key2974, -1), (key2958, -1), (key2941, -1), (key2947, -1), (key2935, -1), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1)]

def rawRow4394 : Integer.Sparse Key := [(key2971, -2), (key2974, -2), (key2981, -2), (key2935, 1), (key2941, 1), (key2947, 1), (key2974, 1), (key2958, 1), (key2981, 1), (key2892, 2), (key2895, 2), (key2902, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2856, -1), (key2825, -1), (key2866, -1), (key2627, 1), (key2636, 1), (key2701, 1), (key2856, 1), (key2722, 1), (key2866, 1)]

def rawRow4395 : Integer.Sparse Key := [(key2974, -2), (key2971, -2), (key2981, -2), (key2941, 1), (key2935, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2958, 1), (key2895, 2), (key2892, 2), (key2902, 2), (key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2790, -1), (key2781, -1), (key2856, -1), (key2804, -1), (key2866, -1), (key2825, -1), (key2636, 1), (key2627, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2722, 1)]

def rawRow4396 : Integer.Sparse Key := [(key2971, -2), (key2981, -2), (key2974, -2), (key2947, 1), (key2958, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2892, 2), (key2902, 2), (key2895, 2), (key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2804, -1), (key2825, -1), (key2781, -1), (key2866, -1), (key2790, -1), (key2856, -1), (key2701, 1), (key2722, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2856, 1)]

def rawRow4397 : Integer.Sparse Key := [(key2981, -2), (key2971, -2), (key2974, -2), (key2958, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2974, 1), (key2941, 1), (key2902, 2), (key2892, 2), (key2895, 2), (key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2825, -1), (key2804, -1), (key2866, -1), (key2781, -1), (key2856, -1), (key2790, -1), (key2722, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2856, 1), (key2636, 1)]

def rawRow4398 : Integer.Sparse Key := [(key2974, -2), (key2981, -2), (key2971, -2), (key2974, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2935, 1), (key2947, 1), (key2895, 2), (key2902, 2), (key2892, 2), (key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2856, -1), (key2866, -1), (key2790, -1), (key2825, -1), (key2781, -1), (key2804, -1), (key2856, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2627, 1), (key2701, 1)]

def rawRow4399 : Integer.Sparse Key := [(key2981, -2), (key2974, -2), (key2971, -2), (key2981, 1), (key2974, 1), (key2958, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2902, 2), (key2895, 2), (key2892, 2), (key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2866, -1), (key2856, -1), (key2825, -1), (key2790, -1), (key2804, -1), (key2781, -1), (key2866, 1), (key2856, 1), (key2722, 1), (key2636, 1), (key2701, 1), (key2627, 1)]

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

def rawRow4424 : Integer.Sparse Key := [(key2406, -2), (key2437, -2), (key2440, -2), (key2406, 2), (key2409, 2), (key2440, 2), (key2472, 2), (key2503, 2), (key2506, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2538, -1), (key2506, -1), (key2554, -1), (key2480, -2), (key2482, -2), (key2522, -2), (key2390, 1), (key2392, 1), (key2480, 1), (key2543, 1), (key2522, 1), (key2563, 1)]

def rawRow4425 : Integer.Sparse Key := [(key2406, -2), (key2440, -2), (key2437, -2), (key2409, 2), (key2406, 2), (key2440, 2), (key2472, 2), (key2506, 2), (key2503, 2), (key2381, -1), (key2378, -1), (key2538, -1), (key2472, -1), (key2554, -1), (key2506, -1), (key2482, -2), (key2480, -2), (key2522, -2), (key2392, 1), (key2390, 1), (key2543, 1), (key2480, 1), (key2563, 1), (key2522, 1)]

def rawRow4426 : Integer.Sparse Key := [(key2437, -2), (key2406, -2), (key2440, -2), (key2406, 2), (key2440, 2), (key2409, 2), (key2503, 2), (key2472, 2), (key2506, 2), (key2472, -1), (key2506, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2480, -2), (key2522, -2), (key2482, -2), (key2480, 1), (key2522, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2543, 1)]

def rawRow4427 : Integer.Sparse Key := [(key2437, -2), (key2440, -2), (key2406, -2), (key2440, 2), (key2406, 2), (key2409, 2), (key2503, 2), (key2506, 2), (key2472, 2), (key2506, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2538, -1), (key2381, -1), (key2522, -2), (key2480, -2), (key2482, -2), (key2522, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2543, 1), (key2392, 1)]

def rawRow4428 : Integer.Sparse Key := [(key2440, -2), (key2406, -2), (key2437, -2), (key2409, 2), (key2440, 2), (key2406, 2), (key2506, 2), (key2472, 2), (key2503, 2), (key2538, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2378, -1), (key2472, -1), (key2482, -2), (key2522, -2), (key2480, -2), (key2543, 1), (key2563, 1), (key2392, 1), (key2522, 1), (key2390, 1), (key2480, 1)]

def rawRow4429 : Integer.Sparse Key := [(key2440, -2), (key2437, -2), (key2406, -2), (key2440, 2), (key2409, 2), (key2406, 2), (key2506, 2), (key2503, 2), (key2472, 2), (key2554, -1), (key2538, -1), (key2506, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2522, -2), (key2482, -2), (key2480, -2), (key2563, 1), (key2543, 1), (key2522, 1), (key2392, 1), (key2480, 1), (key2390, 1)]

def rawRow4430 : Integer.Sparse Key := [(key2472, -2), (key2503, -2), (key2506, -2), (key2480, 2), (key2482, 2), (key2522, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2543, -1), (key2522, -1), (key2563, -1), (key2406, -2), (key2409, -2), (key2440, -2), (key2378, 1), (key2381, 1), (key2472, 1), (key2538, 1), (key2506, 1), (key2554, 1)]

def rawRow4431 : Integer.Sparse Key := [(key2472, -2), (key2506, -2), (key2503, -2), (key2482, 2), (key2480, 2), (key2522, 2), (key2406, 2), (key2440, 2), (key2437, 2), (key2392, -1), (key2390, -1), (key2543, -1), (key2480, -1), (key2563, -1), (key2522, -1), (key2409, -2), (key2406, -2), (key2440, -2), (key2381, 1), (key2378, 1), (key2538, 1), (key2472, 1), (key2554, 1), (key2506, 1)]

def rawRow4432 : Integer.Sparse Key := [(key2503, -2), (key2472, -2), (key2506, -2), (key2480, 2), (key2522, 2), (key2482, 2), (key2437, 2), (key2406, 2), (key2440, 2), (key2480, -1), (key2522, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2406, -2), (key2440, -2), (key2409, -2), (key2472, 1), (key2506, 1), (key2378, 1), (key2554, 1), (key2381, 1), (key2538, 1)]

def rawRow4433 : Integer.Sparse Key := [(key2503, -2), (key2506, -2), (key2472, -2), (key2522, 2), (key2480, 2), (key2482, 2), (key2437, 2), (key2440, 2), (key2406, 2), (key2522, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2543, -1), (key2392, -1), (key2440, -2), (key2406, -2), (key2409, -2), (key2506, 1), (key2472, 1), (key2554, 1), (key2378, 1), (key2538, 1), (key2381, 1)]

def rawRow4434 : Integer.Sparse Key := [(key2506, -2), (key2472, -2), (key2503, -2), (key2482, 2), (key2522, 2), (key2480, 2), (key2440, 2), (key2406, 2), (key2437, 2), (key2543, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2390, -1), (key2480, -1), (key2409, -2), (key2440, -2), (key2406, -2), (key2538, 1), (key2554, 1), (key2381, 1), (key2506, 1), (key2378, 1), (key2472, 1)]

def rawRow4435 : Integer.Sparse Key := [(key2506, -2), (key2503, -2), (key2472, -2), (key2522, 2), (key2482, 2), (key2480, 2), (key2440, 2), (key2437, 2), (key2406, 2), (key2563, -1), (key2543, -1), (key2522, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2440, -2), (key2409, -2), (key2406, -2), (key2554, 1), (key2538, 1), (key2506, 1), (key2381, 1), (key2472, 1), (key2378, 1)]

def rawRow4436 : Integer.Sparse Key := [(key2482, -2), (key2506, -2), (key2522, -2), (key2472, 2), (key2480, 2), (key2503, 2), (key2543, 2), (key2554, 2), (key2563, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2480, -1), (key2437, -1), (key2503, -1), (key2538, -2), (key2543, -2), (key2554, -2), (key2381, 1), (key2392, 1), (key2409, 1), (key2482, 1), (key2440, 1), (key2506, 1)]

def rawRow4437 : Integer.Sparse Key := [(key2482, -2), (key2522, -2), (key2506, -2), (key2480, 2), (key2472, 2), (key2503, 2), (key2543, 2), (key2563, 2), (key2554, 2), (key2390, -1), (key2378, -1), (key2480, -1), (key2406, -1), (key2503, -1), (key2437, -1), (key2543, -2), (key2538, -2), (key2554, -2), (key2392, 1), (key2381, 1), (key2482, 1), (key2409, 1), (key2506, 1), (key2440, 1)]

def rawRow4438 : Integer.Sparse Key := [(key2506, -2), (key2482, -2), (key2522, -2), (key2472, 2), (key2503, 2), (key2480, 2), (key2554, 2), (key2543, 2), (key2563, 2), (key2406, -1), (key2437, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2538, -2), (key2554, -2), (key2543, -2), (key2409, 1), (key2440, 1), (key2381, 1), (key2506, 1), (key2392, 1), (key2482, 1)]

def rawRow4439 : Integer.Sparse Key := [(key2506, -2), (key2522, -2), (key2482, -2), (key2503, 2), (key2472, 2), (key2480, 2), (key2554, 2), (key2563, 2), (key2543, 2), (key2437, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2480, -1), (key2390, -1), (key2554, -2), (key2538, -2), (key2543, -2), (key2440, 1), (key2409, 1), (key2506, 1), (key2381, 1), (key2482, 1), (key2392, 1)]

def rawRow4440 : Integer.Sparse Key := [(key2522, -2), (key2482, -2), (key2506, -2), (key2480, 2), (key2503, 2), (key2472, 2), (key2563, 2), (key2543, 2), (key2554, 2), (key2480, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2378, -1), (key2406, -1), (key2543, -2), (key2554, -2), (key2538, -2), (key2482, 1), (key2506, 1), (key2392, 1), (key2440, 1), (key2381, 1), (key2409, 1)]

def rawRow4441 : Integer.Sparse Key := [(key2522, -2), (key2506, -2), (key2482, -2), (key2503, 2), (key2480, 2), (key2472, 2), (key2563, 2), (key2554, 2), (key2543, 2), (key2503, -1), (key2480, -1), (key2437, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2554, -2), (key2543, -2), (key2538, -2), (key2506, 1), (key2482, 1), (key2440, 1), (key2392, 1), (key2409, 1), (key2381, 1)]

def rawRow4442 : Integer.Sparse Key := [(key2543, -2), (key2554, -2), (key2563, -2), (key2538, 2), (key2543, 2), (key2554, 2), (key2482, 2), (key2506, 2), (key2522, 2), (key2381, -1), (key2392, -1), (key2409, -1), (key2482, -1), (key2440, -1), (key2506, -1), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, 1), (key2390, 1), (key2406, 1), (key2480, 1), (key2437, 1), (key2503, 1)]

def rawRow4443 : Integer.Sparse Key := [(key2543, -2), (key2563, -2), (key2554, -2), (key2543, 2), (key2538, 2), (key2554, 2), (key2482, 2), (key2522, 2), (key2506, 2), (key2392, -1), (key2381, -1), (key2482, -1), (key2409, -1), (key2506, -1), (key2440, -1), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, 1), (key2378, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2437, 1)]

def rawRow4444 : Integer.Sparse Key := [(key2554, -2), (key2543, -2), (key2563, -2), (key2538, 2), (key2554, 2), (key2543, 2), (key2506, 2), (key2482, 2), (key2522, 2), (key2409, -1), (key2440, -1), (key2381, -1), (key2506, -1), (key2392, -1), (key2482, -1), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, 1), (key2437, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2480, 1)]

def rawRow4445 : Integer.Sparse Key := [(key2554, -2), (key2563, -2), (key2543, -2), (key2554, 2), (key2538, 2), (key2543, 2), (key2506, 2), (key2522, 2), (key2482, 2), (key2440, -1), (key2409, -1), (key2506, -1), (key2381, -1), (key2482, -1), (key2392, -1), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2480, 1), (key2390, 1)]

def rawRow4446 : Integer.Sparse Key := [(key2563, -2), (key2543, -2), (key2554, -2), (key2543, 2), (key2554, 2), (key2538, 2), (key2522, 2), (key2482, 2), (key2506, 2), (key2482, -1), (key2506, -1), (key2392, -1), (key2440, -1), (key2381, -1), (key2409, -1), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2378, 1), (key2406, 1)]

def rawRow4447 : Integer.Sparse Key := [(key2563, -2), (key2554, -2), (key2543, -2), (key2554, 2), (key2543, 2), (key2538, 2), (key2522, 2), (key2506, 2), (key2482, 2), (key2506, -1), (key2482, -1), (key2440, -1), (key2392, -1), (key2409, -1), (key2381, -1), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, 1), (key2480, 1), (key2437, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

def rawRow4448 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2613, 2), (key2806, 2), (key2949, 2), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2629, -1), (key2647, -1), (key2783, -1), (key2937, -1), (key2894, -1), (key2973, -1), (key2637, -2), (key2857, -2), (key2975, -2), (key2637, 1), (key2652, 1), (key2791, 1), (key2942, 1), (key2896, 1), (key2975, 1)]

def rawRow4449 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2613, 2), (key2949, 2), (key2806, 2), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2647, -1), (key2629, -1), (key2937, -1), (key2783, -1), (key2973, -1), (key2894, -1), (key2637, -2), (key2975, -2), (key2857, -2), (key2652, 1), (key2637, 1), (key2942, 1), (key2791, 1), (key2975, 1), (key2896, 1)]

def rawRow4450 : Integer.Sparse Key := [(key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2806, 2), (key2613, 2), (key2949, 2), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2783, -1), (key2894, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2937, -1), (key2857, -2), (key2637, -2), (key2975, -2), (key2791, 1), (key2896, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2942, 1)]

def rawRow4451 : Integer.Sparse Key := [(key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2806, 2), (key2949, 2), (key2613, 2), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2894, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2937, -1), (key2647, -1), (key2857, -2), (key2975, -2), (key2637, -2), (key2896, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2942, 1), (key2652, 1)]

def rawRow4452 : Integer.Sparse Key := [(key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2949, 2), (key2613, 2), (key2806, 2), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2937, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2629, -1), (key2783, -1), (key2975, -2), (key2637, -2), (key2857, -2), (key2942, 1), (key2975, 1), (key2652, 1), (key2896, 1), (key2637, 1), (key2791, 1)]

def rawRow4453 : Integer.Sparse Key := [(key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2949, 2), (key2806, 2), (key2613, 2), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2973, -1), (key2937, -1), (key2894, -1), (key2647, -1), (key2783, -1), (key2629, -1), (key2975, -2), (key2857, -2), (key2637, -2), (key2975, 1), (key2942, 1), (key2896, 1), (key2652, 1), (key2791, 1), (key2637, 1)]

def rawRow4454 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2637, 2), (key2857, 2), (key2975, 2), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2637, -1), (key2652, -1), (key2791, -1), (key2942, -1), (key2896, -1), (key2975, -1), (key2613, -2), (key2806, -2), (key2949, -2), (key2629, 1), (key2647, 1), (key2783, 1), (key2937, 1), (key2894, 1), (key2973, 1)]

def rawRow4455 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2637, 2), (key2975, 2), (key2857, 2), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2652, -1), (key2637, -1), (key2942, -1), (key2791, -1), (key2975, -1), (key2896, -1), (key2613, -2), (key2949, -2), (key2806, -2), (key2647, 1), (key2629, 1), (key2937, 1), (key2783, 1), (key2973, 1), (key2894, 1)]

def rawRow4456 : Integer.Sparse Key := [(key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2857, 2), (key2637, 2), (key2975, 2), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2791, -1), (key2896, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2942, -1), (key2806, -2), (key2613, -2), (key2949, -2), (key2783, 1), (key2894, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2937, 1)]

def rawRow4457 : Integer.Sparse Key := [(key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2857, 2), (key2975, 2), (key2637, 2), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2896, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2942, -1), (key2652, -1), (key2806, -2), (key2949, -2), (key2613, -2), (key2894, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2937, 1), (key2647, 1)]

def rawRow4458 : Integer.Sparse Key := [(key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2975, 2), (key2637, 2), (key2857, 2), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2942, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2637, -1), (key2791, -1), (key2949, -2), (key2613, -2), (key2806, -2), (key2937, 1), (key2973, 1), (key2647, 1), (key2894, 1), (key2629, 1), (key2783, 1)]

def rawRow4459 : Integer.Sparse Key := [(key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2975, 2), (key2857, 2), (key2637, 2), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2975, -1), (key2942, -1), (key2896, -1), (key2652, -1), (key2791, -1), (key2637, -1), (key2949, -2), (key2806, -2), (key2613, -2), (key2973, 1), (key2937, 1), (key2894, 1), (key2647, 1), (key2783, 1), (key2629, 1)]

def rawRow4460 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2625, 2), (key2699, 2), (key2852, 2), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1), (key2609, -1), (key2625, -1), (key2664, -1), (key2779, -1), (key2699, -1), (key2802, -1), (key2647, -2), (key2736, -2), (key2894, -2), (key2613, 1), (key2629, 1), (key2668, 1), (key2783, 1), (key2703, 1), (key2806, 1)]

def rawRow4461 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2625, 2), (key2852, 2), (key2699, 2), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1), (key2625, -1), (key2609, -1), (key2779, -1), (key2664, -1), (key2802, -1), (key2699, -1), (key2647, -2), (key2894, -2), (key2736, -2), (key2629, 1), (key2613, 1), (key2783, 1), (key2668, 1), (key2806, 1), (key2703, 1)]

def rawRow4462 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2699, 2), (key2625, 2), (key2852, 2), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1), (key2664, -1), (key2699, -1), (key2609, -1), (key2802, -1), (key2625, -1), (key2779, -1), (key2736, -2), (key2647, -2), (key2894, -2), (key2668, 1), (key2703, 1), (key2613, 1), (key2806, 1), (key2629, 1), (key2783, 1)]

def rawRow4463 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2699, 2), (key2852, 2), (key2625, 2), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1), (key2699, -1), (key2664, -1), (key2802, -1), (key2609, -1), (key2779, -1), (key2625, -1), (key2736, -2), (key2894, -2), (key2647, -2), (key2703, 1), (key2668, 1), (key2806, 1), (key2613, 1), (key2783, 1), (key2629, 1)]

def rawRow4464 : Integer.Sparse Key := [(key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2852, 2), (key2625, 2), (key2699, 2), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1), (key2779, -1), (key2802, -1), (key2625, -1), (key2699, -1), (key2609, -1), (key2664, -1), (key2894, -2), (key2647, -2), (key2736, -2), (key2783, 1), (key2806, 1), (key2629, 1), (key2703, 1), (key2613, 1), (key2668, 1)]

def rawRow4465 : Integer.Sparse Key := [(key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2852, 2), (key2699, 2), (key2625, 2), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1), (key2802, -1), (key2779, -1), (key2699, -1), (key2625, -1), (key2664, -1), (key2609, -1), (key2894, -2), (key2736, -2), (key2647, -2), (key2806, 1), (key2783, 1), (key2703, 1), (key2629, 1), (key2668, 1), (key2613, 1)]

def rawRow4466 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2647, 2), (key2736, 2), (key2894, 2), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1), (key2613, -1), (key2629, -1), (key2668, -1), (key2783, -1), (key2703, -1), (key2806, -1), (key2625, -2), (key2699, -2), (key2852, -2), (key2609, 1), (key2625, 1), (key2664, 1), (key2779, 1), (key2699, 1), (key2802, 1)]

def rawRow4467 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2647, 2), (key2894, 2), (key2736, 2), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1), (key2629, -1), (key2613, -1), (key2783, -1), (key2668, -1), (key2806, -1), (key2703, -1), (key2625, -2), (key2852, -2), (key2699, -2), (key2625, 1), (key2609, 1), (key2779, 1), (key2664, 1), (key2802, 1), (key2699, 1)]

def rawRow4468 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2736, 2), (key2647, 2), (key2894, 2), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1), (key2668, -1), (key2703, -1), (key2613, -1), (key2806, -1), (key2629, -1), (key2783, -1), (key2699, -2), (key2625, -2), (key2852, -2), (key2664, 1), (key2699, 1), (key2609, 1), (key2802, 1), (key2625, 1), (key2779, 1)]

def rawRow4469 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2736, 2), (key2894, 2), (key2647, 2), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1), (key2703, -1), (key2668, -1), (key2806, -1), (key2613, -1), (key2783, -1), (key2629, -1), (key2699, -2), (key2852, -2), (key2625, -2), (key2699, 1), (key2664, 1), (key2802, 1), (key2609, 1), (key2779, 1), (key2625, 1)]

def rawRow4470 : Integer.Sparse Key := [(key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2894, 2), (key2647, 2), (key2736, 2), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1), (key2783, -1), (key2806, -1), (key2629, -1), (key2703, -1), (key2613, -1), (key2668, -1), (key2852, -2), (key2625, -2), (key2699, -2), (key2779, 1), (key2802, 1), (key2625, 1), (key2699, 1), (key2609, 1), (key2664, 1)]

def rawRow4471 : Integer.Sparse Key := [(key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2894, 2), (key2736, 2), (key2647, 2), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1), (key2806, -1), (key2783, -1), (key2703, -1), (key2629, -1), (key2668, -1), (key2613, -1), (key2852, -2), (key2699, -2), (key2625, -2), (key2802, 1), (key2779, 1), (key2699, 1), (key2625, 1), (key2664, 1), (key2609, 1)]

def rawRow4472 : Integer.Sparse Key := [(key2698, -2), (key2701, -2), (key2722, -2), (key2666, 2), (key2701, 2), (key2734, 2), (key2801, 2), (key2804, 2), (key2825, 2), (key2611, -2), (key2804, -2), (key2825, -2), (key2734, -2), (key2892, -2), (key2895, -2), (key2645, 2), (key2892, 2), (key2902, 2)]

def rawRow4473 : Integer.Sparse Key := [(key2701, -2), (key2698, -2), (key2722, -2), (key2666, 2), (key2734, 2), (key2701, 2), (key2804, 2), (key2801, 2), (key2825, 2), (key2611, -2), (key2825, -2), (key2804, -2), (key2734, -2), (key2895, -2), (key2892, -2), (key2645, 2), (key2902, 2), (key2892, 2)]

def rawRow4474 : Integer.Sparse Key := [(key2698, -2), (key2722, -2), (key2701, -2), (key2701, 2), (key2666, 2), (key2734, 2), (key2801, 2), (key2825, 2), (key2804, 2), (key2804, -2), (key2611, -2), (key2825, -2), (key2892, -2), (key2734, -2), (key2895, -2), (key2892, 2), (key2645, 2), (key2902, 2)]

def rawRow4475 : Integer.Sparse Key := [(key2722, -2), (key2698, -2), (key2701, -2), (key2701, 2), (key2734, 2), (key2666, 2), (key2825, 2), (key2801, 2), (key2804, 2), (key2804, -2), (key2825, -2), (key2611, -2), (key2892, -2), (key2895, -2), (key2734, -2), (key2892, 2), (key2902, 2), (key2645, 2)]

def rawRow4476 : Integer.Sparse Key := [(key2701, -2), (key2722, -2), (key2698, -2), (key2734, 2), (key2666, 2), (key2701, 2), (key2804, 2), (key2825, 2), (key2801, 2), (key2825, -2), (key2611, -2), (key2804, -2), (key2895, -2), (key2734, -2), (key2892, -2), (key2902, 2), (key2645, 2), (key2892, 2)]

def rawRow4477 : Integer.Sparse Key := [(key2722, -2), (key2701, -2), (key2698, -2), (key2734, 2), (key2701, 2), (key2666, 2), (key2825, 2), (key2804, 2), (key2801, 2), (key2825, -2), (key2804, -2), (key2611, -2), (key2895, -2), (key2892, -2), (key2734, -2), (key2902, 2), (key2892, 2), (key2645, 2)]

def rawRow4478 : Integer.Sparse Key := [(key2801, -2), (key2804, -2), (key2825, -2), (key2790, 2), (key2856, 2), (key2895, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2636, -2), (key2856, -2), (key2974, -2), (key2666, -2), (key2781, -2), (key2790, -2), (key2611, 2), (key2804, 2), (key2825, 2)]

def rawRow4479 : Integer.Sparse Key := [(key2804, -2), (key2801, -2), (key2825, -2), (key2790, 2), (key2895, 2), (key2856, 2), (key2701, 2), (key2698, 2), (key2722, 2), (key2636, -2), (key2974, -2), (key2856, -2), (key2666, -2), (key2790, -2), (key2781, -2), (key2611, 2), (key2825, 2), (key2804, 2)]

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

def rawRow4480 : Integer.Sparse Key := [(key2801, -2), (key2825, -2), (key2804, -2), (key2856, 2), (key2790, 2), (key2895, 2), (key2698, 2), (key2722, 2), (key2701, 2), (key2856, -2), (key2636, -2), (key2974, -2), (key2781, -2), (key2666, -2), (key2790, -2), (key2804, 2), (key2611, 2), (key2825, 2)]

def rawRow4481 : Integer.Sparse Key := [(key2825, -2), (key2801, -2), (key2804, -2), (key2856, 2), (key2895, 2), (key2790, 2), (key2722, 2), (key2698, 2), (key2701, 2), (key2856, -2), (key2974, -2), (key2636, -2), (key2781, -2), (key2790, -2), (key2666, -2), (key2804, 2), (key2825, 2), (key2611, 2)]

def rawRow4482 : Integer.Sparse Key := [(key2804, -2), (key2825, -2), (key2801, -2), (key2895, 2), (key2790, 2), (key2856, 2), (key2701, 2), (key2722, 2), (key2698, 2), (key2974, -2), (key2636, -2), (key2856, -2), (key2790, -2), (key2666, -2), (key2781, -2), (key2825, 2), (key2611, 2), (key2804, 2)]

def rawRow4483 : Integer.Sparse Key := [(key2825, -2), (key2804, -2), (key2801, -2), (key2895, 2), (key2856, 2), (key2790, 2), (key2722, 2), (key2701, 2), (key2698, 2), (key2974, -2), (key2856, -2), (key2636, -2), (key2790, -2), (key2781, -2), (key2666, -2), (key2825, 2), (key2804, 2), (key2611, 2)]

def rawRow4484 : Integer.Sparse Key := [(key2892, -2), (key2895, -2), (key2902, -2), (key2778, 2), (key2801, 2), (key2851, 2), (key2971, 2), (key2974, 2), (key2981, 2), (key2624, -2), (key2698, -2), (key2851, -2), (key2722, -2), (key2825, -2), (key2866, -2), (key2636, 2), (key2790, 2), (key2856, 2)]

def rawRow4485 : Integer.Sparse Key := [(key2895, -2), (key2892, -2), (key2902, -2), (key2778, 2), (key2851, 2), (key2801, 2), (key2974, 2), (key2971, 2), (key2981, 2), (key2624, -2), (key2851, -2), (key2698, -2), (key2722, -2), (key2866, -2), (key2825, -2), (key2636, 2), (key2856, 2), (key2790, 2)]

def rawRow4486 : Integer.Sparse Key := [(key2892, -2), (key2902, -2), (key2895, -2), (key2801, 2), (key2778, 2), (key2851, 2), (key2971, 2), (key2981, 2), (key2974, 2), (key2698, -2), (key2624, -2), (key2851, -2), (key2825, -2), (key2722, -2), (key2866, -2), (key2790, 2), (key2636, 2), (key2856, 2)]

def rawRow4487 : Integer.Sparse Key := [(key2902, -2), (key2892, -2), (key2895, -2), (key2801, 2), (key2851, 2), (key2778, 2), (key2981, 2), (key2971, 2), (key2974, 2), (key2698, -2), (key2851, -2), (key2624, -2), (key2825, -2), (key2866, -2), (key2722, -2), (key2790, 2), (key2856, 2), (key2636, 2)]

def rawRow4488 : Integer.Sparse Key := [(key2895, -2), (key2902, -2), (key2892, -2), (key2851, 2), (key2778, 2), (key2801, 2), (key2974, 2), (key2981, 2), (key2971, 2), (key2851, -2), (key2624, -2), (key2698, -2), (key2866, -2), (key2722, -2), (key2825, -2), (key2856, 2), (key2636, 2), (key2790, 2)]

def rawRow4489 : Integer.Sparse Key := [(key2902, -2), (key2895, -2), (key2892, -2), (key2851, 2), (key2801, 2), (key2778, 2), (key2981, 2), (key2974, 2), (key2971, 2), (key2851, -2), (key2698, -2), (key2624, -2), (key2866, -2), (key2825, -2), (key2722, -2), (key2856, 2), (key2790, 2), (key2636, 2)]

def rawRow4490 : Integer.Sparse Key := [(key2971, -2), (key2974, -2), (key2981, -2), (key2935, 2), (key2947, 2), (key2971, 2), (key2892, 2), (key2895, 2), (key2902, 2), (key2645, -2), (key2734, -2), (key2892, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, 2), (key2698, 2), (key2851, 2)]

def rawRow4491 : Integer.Sparse Key := [(key2974, -2), (key2971, -2), (key2981, -2), (key2935, 2), (key2971, 2), (key2947, 2), (key2895, 2), (key2892, 2), (key2902, 2), (key2645, -2), (key2892, -2), (key2734, -2), (key2778, -2), (key2851, -2), (key2801, -2), (key2624, 2), (key2851, 2), (key2698, 2)]

def rawRow4492 : Integer.Sparse Key := [(key2971, -2), (key2981, -2), (key2974, -2), (key2947, 2), (key2935, 2), (key2971, 2), (key2892, 2), (key2902, 2), (key2895, 2), (key2734, -2), (key2645, -2), (key2892, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, 2), (key2624, 2), (key2851, 2)]

def rawRow4493 : Integer.Sparse Key := [(key2981, -2), (key2971, -2), (key2974, -2), (key2947, 2), (key2971, 2), (key2935, 2), (key2902, 2), (key2892, 2), (key2895, 2), (key2734, -2), (key2892, -2), (key2645, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2698, 2), (key2851, 2), (key2624, 2)]

def rawRow4494 : Integer.Sparse Key := [(key2974, -2), (key2981, -2), (key2971, -2), (key2971, 2), (key2935, 2), (key2947, 2), (key2895, 2), (key2902, 2), (key2892, 2), (key2892, -2), (key2645, -2), (key2734, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key2851, 2), (key2624, 2), (key2698, 2)]

def rawRow4495 : Integer.Sparse Key := [(key2981, -2), (key2974, -2), (key2971, -2), (key2971, 2), (key2947, 2), (key2935, 2), (key2902, 2), (key2895, 2), (key2892, 2), (key2892, -2), (key2734, -2), (key2645, -2), (key2851, -2), (key2801, -2), (key2778, -2), (key2851, 2), (key2698, 2), (key2624, 2)]

def rawRow4496 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1568, -1), (key1787, -1), (key1591, -1), (key1796, -1), (key1295, 2), (key1572, 2), (key1787, 2), (key1311, 1), (key1315, 1), (key1617, 1), (key1812, 1), (key1631, 1), (key1823, 1), (key1315, -1), (key1336, -1), (key1545, -1), (key1771, -1), (key1654, -1), (key1812, -1), (key1324, -2), (key1622, -2), (key1815, -2), (key1324, 1), (key1343, 1), (key1554, 1), (key1778, 1), (key1657, 1), (key1815, 1)]

def rawRow4497 : Integer.Sparse Key := [(key1295, -1), (key1291, -1), (key1787, -1), (key1568, -1), (key1796, -1), (key1591, -1), (key1295, 2), (key1787, 2), (key1572, 2), (key1315, 1), (key1311, 1), (key1812, 1), (key1617, 1), (key1823, 1), (key1631, 1), (key1336, -1), (key1315, -1), (key1771, -1), (key1545, -1), (key1812, -1), (key1654, -1), (key1324, -2), (key1815, -2), (key1622, -2), (key1343, 1), (key1324, 1), (key1778, 1), (key1554, 1), (key1815, 1), (key1657, 1)]

def rawRow4498 : Integer.Sparse Key := [(key1568, -1), (key1591, -1), (key1291, -1), (key1796, -1), (key1295, -1), (key1787, -1), (key1572, 2), (key1295, 2), (key1787, 2), (key1617, 1), (key1631, 1), (key1311, 1), (key1823, 1), (key1315, 1), (key1812, 1), (key1545, -1), (key1654, -1), (key1315, -1), (key1812, -1), (key1336, -1), (key1771, -1), (key1622, -2), (key1324, -2), (key1815, -2), (key1554, 1), (key1657, 1), (key1324, 1), (key1815, 1), (key1343, 1), (key1778, 1)]

def rawRow4499 : Integer.Sparse Key := [(key1591, -1), (key1568, -1), (key1796, -1), (key1291, -1), (key1787, -1), (key1295, -1), (key1572, 2), (key1787, 2), (key1295, 2), (key1631, 1), (key1617, 1), (key1823, 1), (key1311, 1), (key1812, 1), (key1315, 1), (key1654, -1), (key1545, -1), (key1812, -1), (key1315, -1), (key1771, -1), (key1336, -1), (key1622, -2), (key1815, -2), (key1324, -2), (key1657, 1), (key1554, 1), (key1815, 1), (key1324, 1), (key1778, 1), (key1343, 1)]

def rawRow4500 : Integer.Sparse Key := [(key1787, -1), (key1796, -1), (key1295, -1), (key1591, -1), (key1291, -1), (key1568, -1), (key1787, 2), (key1295, 2), (key1572, 2), (key1812, 1), (key1823, 1), (key1315, 1), (key1631, 1), (key1311, 1), (key1617, 1), (key1771, -1), (key1812, -1), (key1336, -1), (key1654, -1), (key1315, -1), (key1545, -1), (key1815, -2), (key1324, -2), (key1622, -2), (key1778, 1), (key1815, 1), (key1343, 1), (key1657, 1), (key1324, 1), (key1554, 1)]

def rawRow4501 : Integer.Sparse Key := [(key1796, -1), (key1787, -1), (key1591, -1), (key1295, -1), (key1568, -1), (key1291, -1), (key1787, 2), (key1572, 2), (key1295, 2), (key1823, 1), (key1812, 1), (key1631, 1), (key1315, 1), (key1617, 1), (key1311, 1), (key1812, -1), (key1771, -1), (key1654, -1), (key1336, -1), (key1545, -1), (key1315, -1), (key1815, -2), (key1622, -2), (key1324, -2), (key1815, 1), (key1778, 1), (key1657, 1), (key1343, 1), (key1554, 1), (key1324, 1)]

def rawRow4502 : Integer.Sparse Key := [(key1295, -1), (key1295, -1), (key1572, -1), (key1572, -1), (key1591, -1), (key1591, -1), (key1291, 2), (key1568, 2), (key1568, 2), (key1336, 1), (key1336, 1), (key1654, 1), (key1654, 1), (key1665, 1), (key1665, 1), (key1311, -1), (key1311, -1), (key1541, -1), (key1541, -1), (key1617, -1), (key1617, -1), (key1343, -2), (key1657, -2), (key1657, -2), (key1324, 1), (key1324, 1), (key1554, 1), (key1554, 1), (key1622, 1), (key1622, 1)]

def rawRow4503 : Integer.Sparse Key := [(key1572, -1), (key1591, -1), (key1295, -1), (key1591, -1), (key1295, -1), (key1572, -1), (key1568, 2), (key1291, 2), (key1568, 2), (key1654, 1), (key1665, 1), (key1336, 1), (key1665, 1), (key1336, 1), (key1654, 1), (key1541, -1), (key1617, -1), (key1311, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1657, -2), (key1343, -2), (key1657, -2), (key1554, 1), (key1622, 1), (key1324, 1), (key1622, 1), (key1324, 1), (key1554, 1)]

def rawRow4504 : Integer.Sparse Key := [(key1591, -1), (key1572, -1), (key1591, -1), (key1295, -1), (key1572, -1), (key1295, -1), (key1568, 2), (key1568, 2), (key1291, 2), (key1665, 1), (key1654, 1), (key1665, 1), (key1336, 1), (key1654, 1), (key1336, 1), (key1617, -1), (key1541, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1311, -1), (key1657, -2), (key1657, -2), (key1343, -2), (key1622, 1), (key1554, 1), (key1622, 1), (key1324, 1), (key1554, 1), (key1324, 1)]

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

def rawRow4517 : Integer.Sparse Key := [(key1336, -1), (key1336, -1), (key1654, -1), (key1654, -1), (key1665, -1), (key1665, -1), (key1343, 2), (key1657, 2), (key1657, 2), (key1295, 1), (key1295, 1), (key1572, 1), (key1572, 1), (key1591, 1), (key1591, 1), (key1324, -1), (key1324, -1), (key1554, -1), (key1554, -1), (key1622, -1), (key1622, -1), (key1291, -2), (key1568, -2), (key1568, -2), (key1311, 1), (key1311, 1), (key1541, 1), (key1541, 1), (key1617, 1), (key1617, 1)]

def rawRow4518 : Integer.Sparse Key := [(key1654, -1), (key1665, -1), (key1336, -1), (key1665, -1), (key1336, -1), (key1654, -1), (key1657, 2), (key1343, 2), (key1657, 2), (key1572, 1), (key1591, 1), (key1295, 1), (key1591, 1), (key1295, 1), (key1572, 1), (key1554, -1), (key1622, -1), (key1324, -1), (key1622, -1), (key1324, -1), (key1554, -1), (key1568, -2), (key1291, -2), (key1568, -2), (key1541, 1), (key1617, 1), (key1311, 1), (key1617, 1), (key1311, 1), (key1541, 1)]

def rawRow4519 : Integer.Sparse Key := [(key1665, -1), (key1654, -1), (key1665, -1), (key1336, -1), (key1654, -1), (key1336, -1), (key1657, 2), (key1657, 2), (key1343, 2), (key1591, 1), (key1572, 1), (key1591, 1), (key1295, 1), (key1572, 1), (key1295, 1), (key1622, -1), (key1554, -1), (key1622, -1), (key1324, -1), (key1554, -1), (key1324, -1), (key1568, -2), (key1568, -2), (key1291, -2), (key1617, 1), (key1541, 1), (key1617, 1), (key1311, 1), (key1541, 1), (key1311, 1)]

def rawRow4520 : Integer.Sparse Key := [(key1336, -1), (key1343, -1), (key1454, -1), (key1657, -1), (key1464, -1), (key1665, -1), (key1336, 2), (key1454, 2), (key1654, 2), (key1315, 1), (key1324, 1), (key1423, 1), (key1622, 1), (key1442, 1), (key1631, 1), (key1295, -1), (key1315, -1), (key1390, -1), (key1545, -1), (key1423, -1), (key1572, -1), (key1311, -2), (key1419, -2), (key1617, -2), (key1291, 1), (key1311, 1), (key1386, 1), (key1541, 1), (key1419, 1), (key1568, 1)]

def rawRow4521 : Integer.Sparse Key := [(key1343, -1), (key1336, -1), (key1657, -1), (key1454, -1), (key1665, -1), (key1464, -1), (key1336, 2), (key1654, 2), (key1454, 2), (key1324, 1), (key1315, 1), (key1622, 1), (key1423, 1), (key1631, 1), (key1442, 1), (key1315, -1), (key1295, -1), (key1545, -1), (key1390, -1), (key1572, -1), (key1423, -1), (key1311, -2), (key1617, -2), (key1419, -2), (key1311, 1), (key1291, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1419, 1)]

def rawRow4522 : Integer.Sparse Key := [(key1454, -1), (key1464, -1), (key1336, -1), (key1665, -1), (key1343, -1), (key1657, -1), (key1454, 2), (key1336, 2), (key1654, 2), (key1423, 1), (key1442, 1), (key1315, 1), (key1631, 1), (key1324, 1), (key1622, 1), (key1390, -1), (key1423, -1), (key1295, -1), (key1572, -1), (key1315, -1), (key1545, -1), (key1419, -2), (key1311, -2), (key1617, -2), (key1386, 1), (key1419, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1541, 1)]

def rawRow4523 : Integer.Sparse Key := [(key1464, -1), (key1454, -1), (key1665, -1), (key1336, -1), (key1657, -1), (key1343, -1), (key1454, 2), (key1654, 2), (key1336, 2), (key1442, 1), (key1423, 1), (key1631, 1), (key1315, 1), (key1622, 1), (key1324, 1), (key1423, -1), (key1390, -1), (key1572, -1), (key1295, -1), (key1545, -1), (key1315, -1), (key1419, -2), (key1617, -2), (key1311, -2), (key1419, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1541, 1), (key1311, 1)]

def rawRow4524 : Integer.Sparse Key := [(key1657, -1), (key1665, -1), (key1343, -1), (key1464, -1), (key1336, -1), (key1454, -1), (key1654, 2), (key1336, 2), (key1454, 2), (key1622, 1), (key1631, 1), (key1324, 1), (key1442, 1), (key1315, 1), (key1423, 1), (key1545, -1), (key1572, -1), (key1315, -1), (key1423, -1), (key1295, -1), (key1390, -1), (key1617, -2), (key1311, -2), (key1419, -2), (key1541, 1), (key1568, 1), (key1311, 1), (key1419, 1), (key1291, 1), (key1386, 1)]

def rawRow4525 : Integer.Sparse Key := [(key1665, -1), (key1657, -1), (key1464, -1), (key1343, -1), (key1454, -1), (key1336, -1), (key1654, 2), (key1454, 2), (key1336, 2), (key1631, 1), (key1622, 1), (key1442, 1), (key1324, 1), (key1423, 1), (key1315, 1), (key1572, -1), (key1545, -1), (key1423, -1), (key1315, -1), (key1390, -1), (key1295, -1), (key1617, -2), (key1419, -2), (key1311, -2), (key1568, 1), (key1541, 1), (key1419, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

def rawRow4526 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2611, 2), (key2804, 2), (key2825, 2), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2627, -1), (key2636, -1), (key2701, -1), (key2722, -1), (key2856, -1), (key2866, -1), (key2645, -2), (key2892, -2), (key2902, -2), (key2645, 1), (key2651, 1), (key2734, 1), (key2745, 1), (key2895, 1), (key2902, 1)]

def rawRow4527 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2611, 2), (key2825, 2), (key2804, 2), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2636, -1), (key2627, -1), (key2722, -1), (key2701, -1), (key2866, -1), (key2856, -1), (key2645, -2), (key2902, -2), (key2892, -2), (key2651, 1), (key2645, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2895, 1)]

def rawRow4528 : Integer.Sparse Key := [(key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2804, 2), (key2611, 2), (key2825, 2), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2701, -1), (key2856, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2892, -2), (key2645, -2), (key2902, -2), (key2734, 1), (key2895, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2745, 1)]

def rawRow4529 : Integer.Sparse Key := [(key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2804, 2), (key2825, 2), (key2611, 2), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2856, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2722, -1), (key2636, -1), (key2892, -2), (key2902, -2), (key2645, -2), (key2895, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2745, 1), (key2651, 1)]

def rawRow4530 : Integer.Sparse Key := [(key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2825, 2), (key2611, 2), (key2804, 2), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2722, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2627, -1), (key2701, -1), (key2902, -2), (key2645, -2), (key2892, -2), (key2745, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2645, 1), (key2734, 1)]

def rawRow4531 : Integer.Sparse Key := [(key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2825, 2), (key2804, 2), (key2611, 2), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2866, -1), (key2722, -1), (key2856, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2902, -2), (key2892, -2), (key2645, -2), (key2902, 1), (key2745, 1), (key2895, 1), (key2651, 1), (key2734, 1), (key2645, 1)]

def rawRow4532 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2651, -2), (key2895, -2), (key2895, -2), (key2645, 1), (key2645, 1), (key2734, 1), (key2734, 1), (key2892, 1), (key2892, 1)]

def rawRow4533 : Integer.Sparse Key := [(key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2895, -2), (key2651, -2), (key2895, -2), (key2734, 1), (key2892, 1), (key2645, 1), (key2892, 1), (key2645, 1), (key2734, 1)]

def rawRow4534 : Integer.Sparse Key := [(key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2895, -2), (key2895, -2), (key2651, -2), (key2892, 1), (key2734, 1), (key2892, 1), (key2645, 1), (key2734, 1), (key2645, 1)]

def rawRow4535 : Integer.Sparse Key := [(key2624, -1), (key2627, -1), (key2851, -1), (key2971, -1), (key2866, -1), (key2981, -1), (key2636, 2), (key2856, 2), (key2974, 2), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2645, -1), (key2651, -1), (key2734, -1), (key2745, -1), (key2895, -1), (key2902, -1), (key2611, -2), (key2804, -2), (key2825, -2), (key2627, 1), (key2636, 1), (key2701, 1), (key2722, 1), (key2856, 1), (key2866, 1)]

def rawRow4536 : Integer.Sparse Key := [(key2627, -1), (key2624, -1), (key2971, -1), (key2851, -1), (key2981, -1), (key2866, -1), (key2636, 2), (key2974, 2), (key2856, 2), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2651, -1), (key2645, -1), (key2745, -1), (key2734, -1), (key2902, -1), (key2895, -1), (key2611, -2), (key2825, -2), (key2804, -2), (key2636, 1), (key2627, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2856, 1)]

def rawRow4537 : Integer.Sparse Key := [(key2851, -1), (key2866, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2856, 2), (key2636, 2), (key2974, 2), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2734, -1), (key2895, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2804, -2), (key2611, -2), (key2825, -2), (key2701, 1), (key2856, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2722, 1)]

def rawRow4538 : Integer.Sparse Key := [(key2866, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2971, -1), (key2627, -1), (key2856, 2), (key2974, 2), (key2636, 2), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2895, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2745, -1), (key2651, -1), (key2804, -2), (key2825, -2), (key2611, -2), (key2856, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2722, 1), (key2636, 1)]

def rawRow4539 : Integer.Sparse Key := [(key2971, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2624, -1), (key2851, -1), (key2974, 2), (key2636, 2), (key2856, 2), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2745, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2645, -1), (key2734, -1), (key2825, -2), (key2611, -2), (key2804, -2), (key2722, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2627, 1), (key2701, 1)]

def rawRow4540 : Integer.Sparse Key := [(key2981, -1), (key2971, -1), (key2866, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2974, 2), (key2856, 2), (key2636, 2), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2902, -1), (key2745, -1), (key2895, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2825, -2), (key2804, -2), (key2611, -2), (key2866, 1), (key2722, 1), (key2856, 1), (key2636, 1), (key2701, 1), (key2627, 1)]

def rawRow4541 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2636, -2), (key2790, -2), (key2856, -2), (key2611, 1), (key2627, 1), (key2666, 1), (key2701, 1), (key2781, 1), (key2804, 1)]

def rawRow4542 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2636, -2), (key2856, -2), (key2790, -2), (key2627, 1), (key2611, 1), (key2701, 1), (key2666, 1), (key2804, 1), (key2781, 1)]

def rawRow4543 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2790, -2), (key2636, -2), (key2856, -2), (key2666, 1), (key2781, 1), (key2611, 1), (key2804, 1), (key2627, 1), (key2701, 1)]

def rawRow4544 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2790, -2), (key2856, -2), (key2636, -2), (key2781, 1), (key2666, 1), (key2804, 1), (key2611, 1), (key2701, 1), (key2627, 1)]

def rawRow4545 : Integer.Sparse Key := [(key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2856, -2), (key2636, -2), (key2790, -2), (key2701, 1), (key2804, 1), (key2627, 1), (key2781, 1), (key2611, 1), (key2666, 1)]

def rawRow4546 : Integer.Sparse Key := [(key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2856, -2), (key2790, -2), (key2636, -2), (key2804, 1), (key2701, 1), (key2781, 1), (key2627, 1), (key2666, 1), (key2611, 1)]

def rawRow4547 : Integer.Sparse Key := [(key2645, -1), (key2645, -1), (key2892, -1), (key2892, -1), (key2902, -1), (key2902, -1), (key2651, 2), (key2895, 2), (key2895, 2), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2636, -1), (key2636, -1), (key2790, -1), (key2790, -1), (key2856, -1), (key2856, -1), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

def rawRow4548 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2645, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2895, 2), (key2651, 2), (key2895, 2), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2790, -1), (key2856, -1), (key2636, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

def rawRow4549 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2895, 2), (key2895, 2), (key2651, 2), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2856, -1), (key2790, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2636, -1), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

def rawRow4550 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2645, 2), (key2734, 2), (key2892, 2), (key2627, 1), (key2636, 1), (key2701, 1), (key2856, 1), (key2722, 1), (key2866, 1), (key2611, -1), (key2627, -1), (key2666, -1), (key2781, -1), (key2701, -1), (key2804, -1), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

def rawRow4551 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2645, 2), (key2892, 2), (key2734, 2), (key2636, 1), (key2627, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2722, 1), (key2627, -1), (key2611, -1), (key2781, -1), (key2666, -1), (key2804, -1), (key2701, -1), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

def rawRow4552 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2734, 2), (key2645, 2), (key2892, 2), (key2701, 1), (key2722, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2666, -1), (key2701, -1), (key2611, -1), (key2804, -1), (key2627, -1), (key2781, -1), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

def rawRow4553 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2734, 2), (key2892, 2), (key2645, 2), (key2722, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2856, 1), (key2636, 1), (key2701, -1), (key2666, -1), (key2804, -1), (key2611, -1), (key2781, -1), (key2627, -1), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

def rawRow4554 : Integer.Sparse Key := [(key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2892, 2), (key2645, 2), (key2734, 2), (key2856, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2627, 1), (key2701, 1), (key2781, -1), (key2804, -1), (key2627, -1), (key2701, -1), (key2611, -1), (key2666, -1), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

def rawRow4555 : Integer.Sparse Key := [(key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2892, 2), (key2734, 2), (key2645, 2), (key2866, 1), (key2856, 1), (key2722, 1), (key2636, 1), (key2701, 1), (key2627, 1), (key2804, -1), (key2781, -1), (key2701, -1), (key2627, -1), (key2666, -1), (key2611, -1), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

def rawRow4556 : Integer.Sparse Key := [(key1492, -2), (key1492, -2), (key1519, -2), (key1492, 1), (key1496, 1), (key1492, 1), (key1519, 1), (key1496, 1), (key1519, 1), (key1718, 2), (key1718, 2), (key1747, 2), (key1718, -1), (key1728, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1747, -1), (key1863, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1880, -1), (key1863, 1), (key1870, 1), (key1863, 1), (key1880, 1), (key1870, 1), (key1880, 1)]

def rawRow4557 : Integer.Sparse Key := [(key1492, -2), (key1519, -2), (key1492, -2), (key1496, 1), (key1492, 1), (key1519, 1), (key1492, 1), (key1519, 1), (key1496, 1), (key1718, 2), (key1747, 2), (key1718, 2), (key1728, -1), (key1718, -1), (key1747, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1870, 1), (key1863, 1), (key1880, 1), (key1863, 1), (key1880, 1), (key1870, 1)]

def rawRow4558 : Integer.Sparse Key := [(key1519, -2), (key1492, -2), (key1492, -2), (key1519, 1), (key1519, 1), (key1496, 1), (key1496, 1), (key1492, 1), (key1492, 1), (key1747, 2), (key1718, 2), (key1718, 2), (key1747, -1), (key1747, -1), (key1728, -1), (key1728, -1), (key1718, -1), (key1718, -1), (key1880, -1), (key1880, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1880, 1), (key1880, 1), (key1870, 1), (key1870, 1), (key1863, 1), (key1863, 1)]

def rawRow4559 : Integer.Sparse Key := [(key1496, -2), (key1496, -2), (key1496, -2), (key1492, 1), (key1492, 1), (key1492, 1), (key1492, 1), (key1492, 1), (key1492, 1), (key1728, 2), (key1728, 2), (key1728, 2), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1)]

def rawRow4560 : Integer.Sparse Key := [(key1718, -2), (key1718, -2), (key1747, -2), (key1863, 1), (key1865, 1), (key1863, 1), (key1880, 1), (key1865, 1), (key1880, 1), (key1492, 2), (key1492, 2), (key1519, 2), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1492, -1), (key1496, -1), (key1492, -1), (key1519, -1), (key1496, -1), (key1519, -1), (key1718, 1), (key1728, 1), (key1718, 1), (key1747, 1), (key1728, 1), (key1747, 1)]

def rawRow4561 : Integer.Sparse Key := [(key1718, -2), (key1747, -2), (key1718, -2), (key1865, 1), (key1863, 1), (key1880, 1), (key1863, 1), (key1880, 1), (key1865, 1), (key1492, 2), (key1519, 2), (key1492, 2), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1496, -1), (key1492, -1), (key1519, -1), (key1492, -1), (key1519, -1), (key1496, -1), (key1728, 1), (key1718, 1), (key1747, 1), (key1718, 1), (key1747, 1), (key1728, 1)]

def rawRow4562 : Integer.Sparse Key := [(key1747, -2), (key1718, -2), (key1718, -2), (key1880, 1), (key1880, 1), (key1865, 1), (key1865, 1), (key1863, 1), (key1863, 1), (key1519, 2), (key1492, 2), (key1492, 2), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1519, -1), (key1519, -1), (key1496, -1), (key1496, -1), (key1492, -1), (key1492, -1), (key1747, 1), (key1747, 1), (key1728, 1), (key1728, 1), (key1718, 1), (key1718, 1)]

def rawRow4563 : Integer.Sparse Key := [(key1370, -2), (key1865, -2), (key1865, -2), (key1366, 1), (key1366, 1), (key1718, 1), (key1718, 1), (key1863, 1), (key1863, 1), (key1379, 2), (key1870, 2), (key1870, 2), (key1366, -1), (key1366, -1), (key1492, -1), (key1492, -1), (key1863, -1), (key1863, -1), (key1379, -1), (key1379, -1), (key1728, -1), (key1728, -1), (key1870, -1), (key1870, -1), (key1370, 1), (key1370, 1), (key1496, 1), (key1496, 1), (key1865, 1), (key1865, 1)]

def rawRow4564 : Integer.Sparse Key := [(key1865, -2), (key1370, -2), (key1865, -2), (key1718, 1), (key1863, 1), (key1366, 1), (key1863, 1), (key1366, 1), (key1718, 1), (key1870, 2), (key1379, 2), (key1870, 2), (key1492, -1), (key1863, -1), (key1366, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1728, -1), (key1870, -1), (key1379, -1), (key1870, -1), (key1379, -1), (key1728, -1), (key1496, 1), (key1865, 1), (key1370, 1), (key1865, 1), (key1370, 1), (key1496, 1)]

def rawRow4565 : Integer.Sparse Key := [(key1865, -2), (key1865, -2), (key1370, -2), (key1863, 1), (key1718, 1), (key1863, 1), (key1366, 1), (key1718, 1), (key1366, 1), (key1870, 2), (key1870, 2), (key1379, 2), (key1863, -1), (key1492, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1366, -1), (key1870, -1), (key1728, -1), (key1870, -1), (key1379, -1), (key1728, -1), (key1379, -1), (key1865, 1), (key1496, 1), (key1865, 1), (key1370, 1), (key1496, 1), (key1370, 1)]

def rawRow4566 : Integer.Sparse Key := [(key1728, -2), (key1728, -2), (key1728, -2), (key1870, 1), (key1870, 1), (key1870, 1), (key1870, 1), (key1870, 1), (key1870, 1), (key1496, 2), (key1496, 2), (key1496, 2), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1)]

def rawRow4567 : Integer.Sparse Key := [(key1379, -2), (key1870, -2), (key1870, -2), (key1379, 1), (key1379, 1), (key1728, 1), (key1728, 1), (key1870, 1), (key1870, 1), (key1370, 2), (key1865, 2), (key1865, 2), (key1370, -1), (key1370, -1), (key1496, -1), (key1496, -1), (key1865, -1), (key1865, -1), (key1366, -1), (key1366, -1), (key1718, -1), (key1718, -1), (key1863, -1), (key1863, -1), (key1366, 1), (key1366, 1), (key1492, 1), (key1492, 1), (key1863, 1), (key1863, 1)]

def rawRow4568 : Integer.Sparse Key := [(key1870, -2), (key1379, -2), (key1870, -2), (key1728, 1), (key1870, 1), (key1379, 1), (key1870, 1), (key1379, 1), (key1728, 1), (key1865, 2), (key1370, 2), (key1865, 2), (key1496, -1), (key1865, -1), (key1370, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1718, -1), (key1863, -1), (key1366, -1), (key1863, -1), (key1366, -1), (key1718, -1), (key1492, 1), (key1863, 1), (key1366, 1), (key1863, 1), (key1366, 1), (key1492, 1)]

def rawRow4569 : Integer.Sparse Key := [(key1870, -2), (key1870, -2), (key1379, -2), (key1870, 1), (key1728, 1), (key1870, 1), (key1379, 1), (key1728, 1), (key1379, 1), (key1865, 2), (key1865, 2), (key1370, 2), (key1865, -1), (key1496, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1370, -1), (key1863, -1), (key1718, -1), (key1863, -1), (key1366, -1), (key1718, -1), (key1366, -1), (key1863, 1), (key1492, 1), (key1863, 1), (key1366, 1), (key1492, 1), (key1366, 1)]

def rawRow4570 : Integer.Sparse Key := [(key281, -6), (key281, 2), (key281, 2), (key290, 2), (key350, 6), (key350, -2), (key350, -2), (key367, -2), (key507, -2), (key507, -2), (key516, -2), (key507, 2), (key507, 2), (key538, 2)]

def rawRow4571 : Integer.Sparse Key := [(key281, -6), (key281, 2), (key290, 2), (key281, 2), (key350, 6), (key350, -2), (key367, -2), (key350, -2), (key507, -2), (key516, -2), (key507, -2), (key507, 2), (key538, 2), (key507, 2)]

def rawRow4572 : Integer.Sparse Key := [(key281, -6), (key290, 2), (key281, 2), (key281, 2), (key350, 6), (key367, -2), (key350, -2), (key350, -2), (key516, -2), (key507, -2), (key507, -2), (key538, 2), (key507, 2), (key507, 2)]

def rawRow4573 : Integer.Sparse Key := [(key290, -6), (key281, 2), (key281, 2), (key281, 2), (key367, 6), (key350, -2), (key350, -2), (key350, -2), (key538, -2), (key538, -2), (key538, -2), (key516, 2), (key516, 2), (key516, 2)]

def rawRow4574 : Integer.Sparse Key := [(key350, -6), (key507, 2), (key507, 2), (key516, 2), (key281, 6), (key507, -2), (key507, -2), (key538, -2), (key281, -2), (key281, -2), (key290, -2), (key350, 2), (key350, 2), (key367, 2)]

def rawRow4575 : Integer.Sparse Key := [(key350, -6), (key507, 2), (key516, 2), (key507, 2), (key281, 6), (key507, -2), (key538, -2), (key507, -2), (key281, -2), (key290, -2), (key281, -2), (key350, 2), (key367, 2), (key350, 2)]

def rawRow4576 : Integer.Sparse Key := [(key350, -6), (key516, 2), (key507, 2), (key507, 2), (key281, 6), (key538, -2), (key507, -2), (key507, -2), (key290, -2), (key281, -2), (key281, -2), (key367, 2), (key350, 2), (key350, 2)]

def rawRow4577 : Integer.Sparse Key := [(key516, -6), (key350, 2), (key507, 2), (key507, 2), (key538, 6), (key281, -2), (key507, -2), (key507, -2), (key367, -2), (key538, -2), (key538, -2), (key290, 2), (key516, 2), (key516, 2)]

def rawRow4578 : Integer.Sparse Key := [(key516, -6), (key507, 2), (key350, 2), (key507, 2), (key538, 6), (key507, -2), (key281, -2), (key507, -2), (key538, -2), (key367, -2), (key538, -2), (key516, 2), (key290, 2), (key516, 2)]

def rawRow4579 : Integer.Sparse Key := [(key516, -6), (key507, 2), (key507, 2), (key350, 2), (key538, 6), (key507, -2), (key507, -2), (key281, -2), (key538, -2), (key538, -2), (key367, -2), (key516, 2), (key516, 2), (key290, 2)]

def rawRow4580 : Integer.Sparse Key := [(key367, -6), (key538, 2), (key538, 2), (key538, 2), (key290, 6), (key516, -2), (key516, -2), (key516, -2), (key281, -2), (key281, -2), (key281, -2), (key350, 2), (key350, 2), (key350, 2)]

def rawRow4581 : Integer.Sparse Key := [(key538, -6), (key367, 2), (key538, 2), (key538, 2), (key516, 6), (key290, -2), (key516, -2), (key516, -2), (key350, -2), (key507, -2), (key507, -2), (key281, 2), (key507, 2), (key507, 2)]

def rawRow4582 : Integer.Sparse Key := [(key538, -6), (key538, 2), (key367, 2), (key538, 2), (key516, 6), (key516, -2), (key290, -2), (key516, -2), (key507, -2), (key350, -2), (key507, -2), (key507, 2), (key281, 2), (key507, 2)]

def rawRow4583 : Integer.Sparse Key := [(key538, -6), (key538, 2), (key538, 2), (key367, 2), (key516, 6), (key516, -2), (key516, -2), (key290, -2), (key507, -2), (key507, -2), (key350, -2), (key507, 2), (key507, 2), (key281, 2)]

def rawRow4584 : Integer.Sparse Key := [(key1362, -2), (key1367, -2), (key1367, -2), (key1362, 1), (key1367, 1), (key1362, 1), (key1376, 1), (key1367, 1), (key1376, 1), (key1488, 2), (key1493, 2), (key1493, 2), (key1488, -1), (key1493, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1515, -1), (key1714, -1), (key1719, -1), (key1714, -1), (key1725, -1), (key1719, -1), (key1725, -1), (key1714, 1), (key1719, 1), (key1714, 1), (key1743, 1), (key1719, 1), (key1743, 1)]

def rawRow4585 : Integer.Sparse Key := [(key1367, -2), (key1362, -2), (key1367, -2), (key1367, 1), (key1362, 1), (key1376, 1), (key1362, 1), (key1376, 1), (key1367, 1), (key1493, 2), (key1488, 2), (key1493, 2), (key1493, -1), (key1488, -1), (key1515, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1719, -1), (key1714, -1), (key1725, -1), (key1714, -1), (key1725, -1), (key1719, -1), (key1719, 1), (key1714, 1), (key1743, 1), (key1714, 1), (key1743, 1), (key1719, 1)]

def rawRow4586 : Integer.Sparse Key := [(key1367, -2), (key1367, -2), (key1362, -2), (key1376, 1), (key1376, 1), (key1367, 1), (key1367, 1), (key1362, 1), (key1362, 1), (key1493, 2), (key1493, 2), (key1488, 2), (key1515, -1), (key1515, -1), (key1493, -1), (key1493, -1), (key1488, -1), (key1488, -1), (key1725, -1), (key1725, -1), (key1719, -1), (key1719, -1), (key1714, -1), (key1714, -1), (key1743, 1), (key1743, 1), (key1719, 1), (key1719, 1), (key1714, 1), (key1714, 1)]

def rawRow4587 : Integer.Sparse Key := [(key1376, -2), (key1376, -2), (key1376, -2), (key1367, 1), (key1367, 1), (key1367, 1), (key1367, 1), (key1367, 1), (key1367, 1), (key1515, 2), (key1515, 2), (key1515, 2), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1)]

def rawRow4588 : Integer.Sparse Key := [(key1488, -2), (key1493, -2), (key1493, -2), (key1714, 1), (key1719, 1), (key1714, 1), (key1725, 1), (key1719, 1), (key1725, 1), (key1362, 2), (key1367, 2), (key1367, 2), (key1714, -1), (key1719, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1743, -1), (key1362, -1), (key1367, -1), (key1362, -1), (key1376, -1), (key1367, -1), (key1376, -1), (key1488, 1), (key1493, 1), (key1488, 1), (key1515, 1), (key1493, 1), (key1515, 1)]

def rawRow4589 : Integer.Sparse Key := [(key1493, -2), (key1488, -2), (key1493, -2), (key1719, 1), (key1714, 1), (key1725, 1), (key1714, 1), (key1725, 1), (key1719, 1), (key1367, 2), (key1362, 2), (key1367, 2), (key1719, -1), (key1714, -1), (key1743, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1367, -1), (key1362, -1), (key1376, -1), (key1362, -1), (key1376, -1), (key1367, -1), (key1493, 1), (key1488, 1), (key1515, 1), (key1488, 1), (key1515, 1), (key1493, 1)]

def rawRow4590 : Integer.Sparse Key := [(key1493, -2), (key1493, -2), (key1488, -2), (key1725, 1), (key1725, 1), (key1719, 1), (key1719, 1), (key1714, 1), (key1714, 1), (key1367, 2), (key1367, 2), (key1362, 2), (key1743, -1), (key1743, -1), (key1719, -1), (key1719, -1), (key1714, -1), (key1714, -1), (key1376, -1), (key1376, -1), (key1367, -1), (key1367, -1), (key1362, -1), (key1362, -1), (key1515, 1), (key1515, 1), (key1493, 1), (key1493, 1), (key1488, 1), (key1488, 1)]

def rawRow4591 : Integer.Sparse Key := [(key1725, -2), (key1725, -2), (key1941, -2), (key1493, 1), (key1493, 1), (key1719, 1), (key1719, 1), (key1938, 1), (key1938, 1), (key1743, 2), (key1743, 2), (key1950, 2), (key1367, -1), (key1367, -1), (key1719, -1), (key1719, -1), (key1938, -1), (key1938, -1), (key1515, -1), (key1515, -1), (key1743, -1), (key1743, -1), (key1950, -1), (key1950, -1), (key1376, 1), (key1376, 1), (key1725, 1), (key1725, 1), (key1941, 1), (key1941, 1)]

def rawRow4592 : Integer.Sparse Key := [(key1725, -2), (key1941, -2), (key1725, -2), (key1719, 1), (key1938, 1), (key1493, 1), (key1938, 1), (key1493, 1), (key1719, 1), (key1743, 2), (key1950, 2), (key1743, 2), (key1719, -1), (key1938, -1), (key1367, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1743, -1), (key1950, -1), (key1515, -1), (key1950, -1), (key1515, -1), (key1743, -1), (key1725, 1), (key1941, 1), (key1376, 1), (key1941, 1), (key1376, 1), (key1725, 1)]

def rawRow4593 : Integer.Sparse Key := [(key1941, -2), (key1725, -2), (key1725, -2), (key1938, 1), (key1719, 1), (key1938, 1), (key1493, 1), (key1719, 1), (key1493, 1), (key1950, 2), (key1743, 2), (key1743, 2), (key1938, -1), (key1719, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1367, -1), (key1950, -1), (key1743, -1), (key1950, -1), (key1515, -1), (key1743, -1), (key1515, -1), (key1941, 1), (key1725, 1), (key1941, 1), (key1376, 1), (key1725, 1), (key1376, 1)]

def rawRow4594 : Integer.Sparse Key := [(key1515, -2), (key1515, -2), (key1515, -2), (key1743, 1), (key1743, 1), (key1743, 1), (key1743, 1), (key1743, 1), (key1743, 1), (key1376, 2), (key1376, 2), (key1376, 2), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1)]

def rawRow4595 : Integer.Sparse Key := [(key1743, -2), (key1743, -2), (key1950, -2), (key1515, 1), (key1515, 1), (key1743, 1), (key1743, 1), (key1950, 1), (key1950, 1), (key1725, 2), (key1725, 2), (key1941, 2), (key1376, -1), (key1376, -1), (key1725, -1), (key1725, -1), (key1941, -1), (key1941, -1), (key1493, -1), (key1493, -1), (key1719, -1), (key1719, -1), (key1938, -1), (key1938, -1), (key1367, 1), (key1367, 1), (key1719, 1), (key1719, 1), (key1938, 1), (key1938, 1)]

def rawRow4596 : Integer.Sparse Key := [(key1743, -2), (key1950, -2), (key1743, -2), (key1743, 1), (key1950, 1), (key1515, 1), (key1950, 1), (key1515, 1), (key1743, 1), (key1725, 2), (key1941, 2), (key1725, 2), (key1725, -1), (key1941, -1), (key1376, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1719, -1), (key1938, -1), (key1493, -1), (key1938, -1), (key1493, -1), (key1719, -1), (key1719, 1), (key1938, 1), (key1367, 1), (key1938, 1), (key1367, 1), (key1719, 1)]

def rawRow4597 : Integer.Sparse Key := [(key1950, -2), (key1743, -2), (key1743, -2), (key1950, 1), (key1743, 1), (key1950, 1), (key1515, 1), (key1743, 1), (key1515, 1), (key1941, 2), (key1725, 2), (key1725, 2), (key1941, -1), (key1725, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1376, -1), (key1938, -1), (key1719, -1), (key1938, -1), (key1493, -1), (key1719, -1), (key1493, -1), (key1938, 1), (key1719, 1), (key1938, 1), (key1367, 1), (key1719, 1), (key1367, 1)]

def rawRow4598 : Integer.Sparse Key := [(key29, -2), (key33, -2), (key33, -2), (key33, 6), (key495, 2), (key500, 2), (key500, 2), (key500, -2), (key500, -2), (key554, -2), (key665, -6), (key665, 2), (key665, 2), (key682, 2)]

def rawRow4599 : Integer.Sparse Key := [(key33, -2), (key29, -2), (key33, -2), (key33, 6), (key500, 2), (key495, 2), (key500, 2), (key500, -2), (key554, -2), (key500, -2), (key665, -6), (key665, 2), (key682, 2), (key665, 2)]

def rawRow4600 : Integer.Sparse Key := [(key33, -2), (key33, -2), (key29, -2), (key33, 6), (key500, 2), (key500, 2), (key495, 2), (key554, -2), (key500, -2), (key500, -2), (key665, -6), (key682, 2), (key665, 2), (key665, 2)]

def rawRow4601 : Integer.Sparse Key := [(key33, -2), (key33, -2), (key33, -2), (key29, 6), (key554, 2), (key554, 2), (key554, 2), (key495, -2), (key495, -2), (key495, -2), (key682, -6), (key665, 2), (key665, 2), (key665, 2)]

def rawRow4602 : Integer.Sparse Key := [(key109, -2), (key113, -2), (key113, -2), (key149, 6), (key29, 2), (key33, 2), (key33, 2), (key665, -2), (key665, -2), (key682, -2), (key228, -6), (key500, 2), (key500, 2), (key554, 2)]

def rawRow4603 : Integer.Sparse Key := [(key113, -2), (key109, -2), (key113, -2), (key149, 6), (key33, 2), (key29, 2), (key33, 2), (key665, -2), (key682, -2), (key665, -2), (key228, -6), (key500, 2), (key554, 2), (key500, 2)]

def rawRow4604 : Integer.Sparse Key := [(key113, -2), (key113, -2), (key109, -2), (key149, 6), (key33, 2), (key33, 2), (key29, 2), (key682, -2), (key665, -2), (key665, -2), (key228, -6), (key554, 2), (key500, 2), (key500, 2)]

def rawRow4605 : Integer.Sparse Key := [(key113, -2), (key113, -2), (key149, -2), (key109, 6), (key175, 2), (key175, 2), (key185, 2), (key223, -2), (key495, -2), (key495, -2), (key554, -6), (key228, 2), (key500, 2), (key500, 2)]

def rawRow4606 : Integer.Sparse Key := [(key113, -2), (key149, -2), (key113, -2), (key109, 6), (key175, 2), (key185, 2), (key175, 2), (key495, -2), (key223, -2), (key495, -2), (key554, -6), (key500, 2), (key228, 2), (key500, 2)]

def rawRow4607 : Integer.Sparse Key := [(key149, -2), (key113, -2), (key113, -2), (key109, 6), (key185, 2), (key175, 2), (key175, 2), (key495, -2), (key495, -2), (key223, -2), (key554, -6), (key500, 2), (key500, 2), (key228, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4608 : Integer.Sparse Key := [(key175, -2), (key175, -2), (key175, -2), (key185, 6), (key33, 2), (key33, 2), (key33, 2), (key149, -2), (key149, -2), (key149, -2), (key223, -6), (key495, 2), (key495, 2), (key495, 2)]

def rawRow4609 : Integer.Sparse Key := [(key175, -2), (key175, -2), (key185, -2), (key175, 6), (key113, 2), (key113, 2), (key149, 2), (key33, -2), (key113, -2), (key113, -2), (key495, -6), (key223, 2), (key495, 2), (key495, 2)]

def rawRow4610 : Integer.Sparse Key := [(key175, -2), (key185, -2), (key175, -2), (key175, 6), (key113, 2), (key149, 2), (key113, 2), (key113, -2), (key33, -2), (key113, -2), (key495, -6), (key495, 2), (key223, 2), (key495, 2)]

def rawRow4611 : Integer.Sparse Key := [(key185, -2), (key175, -2), (key175, -2), (key175, 6), (key149, 2), (key113, 2), (key113, 2), (key113, -2), (key113, -2), (key33, -2), (key495, -6), (key495, 2), (key495, 2), (key223, 2)]

def rawRow4612 : Integer.Sparse Key := [(key1361, -6), (key1361, 2), (key1361, 2), (key1373, 2), (key1487, 6), (key1487, -2), (key1487, -2), (key1512, -2), (key1713, -2), (key1713, -2), (key1722, -2), (key1713, 2), (key1713, 2), (key1740, 2)]

def rawRow4613 : Integer.Sparse Key := [(key1361, -6), (key1361, 2), (key1373, 2), (key1361, 2), (key1487, 6), (key1487, -2), (key1512, -2), (key1487, -2), (key1713, -2), (key1722, -2), (key1713, -2), (key1713, 2), (key1740, 2), (key1713, 2)]

def rawRow4614 : Integer.Sparse Key := [(key1361, -6), (key1373, 2), (key1361, 2), (key1361, 2), (key1487, 6), (key1512, -2), (key1487, -2), (key1487, -2), (key1722, -2), (key1713, -2), (key1713, -2), (key1740, 2), (key1713, 2), (key1713, 2)]

def rawRow4615 : Integer.Sparse Key := [(key1373, -6), (key1361, 2), (key1361, 2), (key1361, 2), (key1512, 6), (key1487, -2), (key1487, -2), (key1487, -2), (key1740, -2), (key1740, -2), (key1740, -2), (key1722, 2), (key1722, 2), (key1722, 2)]

def rawRow4616 : Integer.Sparse Key := [(key1487, -6), (key1713, 2), (key1713, 2), (key1722, 2), (key1361, 6), (key1713, -2), (key1713, -2), (key1740, -2), (key1361, -2), (key1361, -2), (key1373, -2), (key1487, 2), (key1487, 2), (key1512, 2)]

def rawRow4617 : Integer.Sparse Key := [(key1487, -6), (key1713, 2), (key1722, 2), (key1713, 2), (key1361, 6), (key1713, -2), (key1740, -2), (key1713, -2), (key1361, -2), (key1373, -2), (key1361, -2), (key1487, 2), (key1512, 2), (key1487, 2)]

def rawRow4618 : Integer.Sparse Key := [(key1487, -6), (key1722, 2), (key1713, 2), (key1713, 2), (key1361, 6), (key1740, -2), (key1713, -2), (key1713, -2), (key1373, -2), (key1361, -2), (key1361, -2), (key1512, 2), (key1487, 2), (key1487, 2)]

def rawRow4619 : Integer.Sparse Key := [(key1722, -6), (key1487, 2), (key1713, 2), (key1713, 2), (key1740, 6), (key1361, -2), (key1713, -2), (key1713, -2), (key1512, -2), (key1740, -2), (key1740, -2), (key1373, 2), (key1722, 2), (key1722, 2)]

def rawRow4620 : Integer.Sparse Key := [(key1722, -6), (key1713, 2), (key1487, 2), (key1713, 2), (key1740, 6), (key1713, -2), (key1361, -2), (key1713, -2), (key1740, -2), (key1512, -2), (key1740, -2), (key1722, 2), (key1373, 2), (key1722, 2)]

def rawRow4621 : Integer.Sparse Key := [(key1722, -6), (key1713, 2), (key1713, 2), (key1487, 2), (key1740, 6), (key1713, -2), (key1713, -2), (key1361, -2), (key1740, -2), (key1740, -2), (key1512, -2), (key1722, 2), (key1722, 2), (key1373, 2)]

def rawRow4622 : Integer.Sparse Key := [(key1512, -6), (key1740, 2), (key1740, 2), (key1740, 2), (key1373, 6), (key1722, -2), (key1722, -2), (key1722, -2), (key1361, -2), (key1361, -2), (key1361, -2), (key1487, 2), (key1487, 2), (key1487, 2)]

def rawRow4623 : Integer.Sparse Key := [(key1740, -6), (key1512, 2), (key1740, 2), (key1740, 2), (key1722, 6), (key1373, -2), (key1722, -2), (key1722, -2), (key1487, -2), (key1713, -2), (key1713, -2), (key1361, 2), (key1713, 2), (key1713, 2)]

def rawRow4624 : Integer.Sparse Key := [(key1740, -6), (key1740, 2), (key1512, 2), (key1740, 2), (key1722, 6), (key1722, -2), (key1373, -2), (key1722, -2), (key1713, -2), (key1487, -2), (key1713, -2), (key1713, 2), (key1361, 2), (key1713, 2)]

def rawRow4625 : Integer.Sparse Key := [(key1740, -6), (key1740, 2), (key1740, 2), (key1512, 2), (key1722, 6), (key1722, -2), (key1722, -2), (key1373, -2), (key1713, -2), (key1713, -2), (key1487, -2), (key1713, 2), (key1713, 2), (key1361, 2)]

def rawRow4626 : Integer.Sparse Key := [(key351, -1), (key354, -1), (key351, -1), (key371, -1), (key354, -1), (key371, -1), (key354, 2), (key354, 2), (key371, 2), (key508, 1), (key511, 1), (key508, 1), (key543, 1), (key511, 1), (key543, 1), (key511, -1), (key523, -1), (key511, -1), (key543, -1), (key523, -1), (key543, -1), (key668, -2), (key668, -2), (key678, -2), (key668, 1), (key672, 1), (key668, 1), (key678, 1), (key672, 1), (key678, 1)]

def rawRow4627 : Integer.Sparse Key := [(key354, -1), (key351, -1), (key371, -1), (key351, -1), (key371, -1), (key354, -1), (key354, 2), (key371, 2), (key354, 2), (key511, 1), (key508, 1), (key543, 1), (key508, 1), (key543, 1), (key511, 1), (key523, -1), (key511, -1), (key543, -1), (key511, -1), (key543, -1), (key523, -1), (key668, -2), (key678, -2), (key668, -2), (key672, 1), (key668, 1), (key678, 1), (key668, 1), (key678, 1), (key672, 1)]

def rawRow4628 : Integer.Sparse Key := [(key371, -1), (key371, -1), (key354, -1), (key354, -1), (key351, -1), (key351, -1), (key371, 2), (key354, 2), (key354, 2), (key543, 1), (key543, 1), (key511, 1), (key511, 1), (key508, 1), (key508, 1), (key543, -1), (key543, -1), (key523, -1), (key523, -1), (key511, -1), (key511, -1), (key678, -2), (key668, -2), (key668, -2), (key678, 1), (key678, 1), (key672, 1), (key672, 1), (key668, 1), (key668, 1)]

def rawRow4629 : Integer.Sparse Key := [(key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key351, 2), (key351, 2), (key351, 2), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key672, -2), (key672, -2), (key672, -2), (key668, 1), (key668, 1), (key668, 1), (key668, 1), (key668, 1), (key668, 1)]

def rawRow4630 : Integer.Sparse Key := [(key439, -1), (key443, -1), (key439, -1), (key596, -1), (key443, -1), (key596, -1), (key458, 2), (key458, 2), (key607, 2), (key351, 1), (key354, 1), (key351, 1), (key371, 1), (key354, 1), (key371, 1), (key668, -1), (key672, -1), (key668, -1), (key678, -1), (key672, -1), (key678, -1), (key354, -2), (key354, -2), (key371, -2), (key511, 1), (key523, 1), (key511, 1), (key543, 1), (key523, 1), (key543, 1)]

def rawRow4631 : Integer.Sparse Key := [(key443, -1), (key439, -1), (key596, -1), (key439, -1), (key596, -1), (key443, -1), (key458, 2), (key607, 2), (key458, 2), (key354, 1), (key351, 1), (key371, 1), (key351, 1), (key371, 1), (key354, 1), (key672, -1), (key668, -1), (key678, -1), (key668, -1), (key678, -1), (key672, -1), (key354, -2), (key371, -2), (key354, -2), (key523, 1), (key511, 1), (key543, 1), (key511, 1), (key543, 1), (key523, 1)]

def rawRow4632 : Integer.Sparse Key := [(key596, -1), (key596, -1), (key443, -1), (key443, -1), (key439, -1), (key439, -1), (key607, 2), (key458, 2), (key458, 2), (key371, 1), (key371, 1), (key354, 1), (key354, 1), (key351, 1), (key351, 1), (key678, -1), (key678, -1), (key672, -1), (key672, -1), (key668, -1), (key668, -1), (key371, -2), (key354, -2), (key354, -2), (key543, 1), (key543, 1), (key523, 1), (key523, 1), (key511, 1), (key511, 1)]

def rawRow4633 : Integer.Sparse Key := [(key261, -1), (key261, -1), (key443, -1), (key443, -1), (key458, -1), (key458, -1), (key257, 2), (key439, 2), (key439, 2), (key272, 1), (key272, 1), (key470, 1), (key470, 1), (key481, 1), (key481, 1), (key282, -1), (key282, -1), (key351, -1), (key351, -1), (key508, -1), (key508, -1), (key295, -2), (key523, -2), (key523, -2), (key285, 1), (key285, 1), (key354, 1), (key354, 1), (key511, 1), (key511, 1)]

def rawRow4634 : Integer.Sparse Key := [(key443, -1), (key458, -1), (key261, -1), (key458, -1), (key261, -1), (key443, -1), (key439, 2), (key257, 2), (key439, 2), (key470, 1), (key481, 1), (key272, 1), (key481, 1), (key272, 1), (key470, 1), (key351, -1), (key508, -1), (key282, -1), (key508, -1), (key282, -1), (key351, -1), (key523, -2), (key295, -2), (key523, -2), (key354, 1), (key511, 1), (key285, 1), (key511, 1), (key285, 1), (key354, 1)]

def rawRow4635 : Integer.Sparse Key := [(key458, -1), (key443, -1), (key458, -1), (key261, -1), (key443, -1), (key261, -1), (key439, 2), (key439, 2), (key257, 2), (key481, 1), (key470, 1), (key481, 1), (key272, 1), (key470, 1), (key272, 1), (key508, -1), (key351, -1), (key508, -1), (key282, -1), (key351, -1), (key282, -1), (key523, -2), (key523, -2), (key295, -2), (key511, 1), (key354, 1), (key511, 1), (key285, 1), (key354, 1), (key285, 1)]

def rawRow4636 : Integer.Sparse Key := [(key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key481, 2), (key481, 2), (key481, 2), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key458, -1), (key458, -1), (key458, -1), (key458, -1), (key458, -1), (key458, -1), (key351, -2), (key351, -2), (key351, -2), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1)]

def rawRow4637 : Integer.Sparse Key := [(key272, -1), (key272, -1), (key470, -1), (key470, -1), (key481, -1), (key481, -1), (key272, 2), (key470, 2), (key470, 2), (key261, 1), (key261, 1), (key443, 1), (key443, 1), (key458, 1), (key458, 1), (key261, -1), (key261, -1), (key398, -1), (key398, -1), (key443, -1), (key443, -1), (key282, -2), (key508, -2), (key508, -2), (key282, 1), (key282, 1), (key351, 1), (key351, 1), (key508, 1), (key508, 1)]

def rawRow4638 : Integer.Sparse Key := [(key470, -1), (key481, -1), (key272, -1), (key481, -1), (key272, -1), (key470, -1), (key470, 2), (key272, 2), (key470, 2), (key443, 1), (key458, 1), (key261, 1), (key458, 1), (key261, 1), (key443, 1), (key398, -1), (key443, -1), (key261, -1), (key443, -1), (key261, -1), (key398, -1), (key508, -2), (key282, -2), (key508, -2), (key351, 1), (key508, 1), (key282, 1), (key508, 1), (key282, 1), (key351, 1)]

def rawRow4639 : Integer.Sparse Key := [(key481, -1), (key470, -1), (key481, -1), (key272, -1), (key470, -1), (key272, -1), (key470, 2), (key470, 2), (key272, 2), (key458, 1), (key443, 1), (key458, 1), (key261, 1), (key443, 1), (key261, 1), (key443, -1), (key398, -1), (key443, -1), (key261, -1), (key398, -1), (key261, -1), (key508, -2), (key508, -2), (key282, -2), (key508, 1), (key351, 1), (key508, 1), (key282, 1), (key351, 1), (key282, 1)]

def rawRow4640 : Integer.Sparse Key := [(key1502, -2), (key1508, -2), (key1508, -2), (key1504, 2), (key1508, 2), (key1508, 2), (key1734, 2), (key1737, 2), (key1737, 2), (key1737, -6), (key1945, -2), (key1947, -2), (key1947, -2), (key1947, 6)]

def rawRow4641 : Integer.Sparse Key := [(key1508, -2), (key1502, -2), (key1508, -2), (key1508, 2), (key1504, 2), (key1508, 2), (key1737, 2), (key1734, 2), (key1737, 2), (key1737, -6), (key1947, -2), (key1945, -2), (key1947, -2), (key1947, 6)]

def rawRow4642 : Integer.Sparse Key := [(key1508, -2), (key1508, -2), (key1502, -2), (key1508, 2), (key1508, 2), (key1504, 2), (key1737, 2), (key1737, 2), (key1734, 2), (key1737, -6), (key1947, -2), (key1947, -2), (key1945, -2), (key1947, 6)]

def rawRow4643 : Integer.Sparse Key := [(key1504, -2), (key1504, -2), (key1504, -2), (key1502, 2), (key1502, 2), (key1502, 2), (key1737, 2), (key1737, 2), (key1737, 2), (key1734, -6), (key1947, -2), (key1947, -2), (key1947, -2), (key1945, 6)]

def rawRow4644 : Integer.Sparse Key := [(key1734, -2), (key1737, -2), (key1737, -2), (key1945, 2), (key1947, 2), (key1947, 2), (key1502, 2), (key1508, 2), (key1508, 2), (key1947, -6), (key1504, -2), (key1508, -2), (key1508, -2), (key1737, 6)]

def rawRow4645 : Integer.Sparse Key := [(key1737, -2), (key1734, -2), (key1737, -2), (key1947, 2), (key1945, 2), (key1947, 2), (key1508, 2), (key1502, 2), (key1508, 2), (key1947, -6), (key1508, -2), (key1504, -2), (key1508, -2), (key1737, 6)]

def rawRow4646 : Integer.Sparse Key := [(key1737, -2), (key1737, -2), (key1734, -2), (key1947, 2), (key1947, 2), (key1945, 2), (key1508, 2), (key1508, 2), (key1502, 2), (key1947, -6), (key1508, -2), (key1508, -2), (key1504, -2), (key1737, 6)]

def rawRow4647 : Integer.Sparse Key := [(key1504, -2), (key1504, -2), (key1945, -2), (key1502, 2), (key1502, 2), (key1734, 2), (key1508, 2), (key1508, 2), (key1947, 2), (key1502, -6), (key1508, -2), (key1508, -2), (key1737, -2), (key1504, 6)]

def rawRow4648 : Integer.Sparse Key := [(key1504, -2), (key1945, -2), (key1504, -2), (key1502, 2), (key1734, 2), (key1502, 2), (key1508, 2), (key1947, 2), (key1508, 2), (key1502, -6), (key1508, -2), (key1737, -2), (key1508, -2), (key1504, 6)]

def rawRow4649 : Integer.Sparse Key := [(key1945, -2), (key1504, -2), (key1504, -2), (key1734, 2), (key1502, 2), (key1502, 2), (key1947, 2), (key1508, 2), (key1508, 2), (key1502, -6), (key1737, -2), (key1508, -2), (key1508, -2), (key1504, 6)]

def rawRow4650 : Integer.Sparse Key := [(key1737, -2), (key1737, -2), (key1737, -2), (key1947, 2), (key1947, 2), (key1947, 2), (key1504, 2), (key1504, 2), (key1504, 2), (key1945, -6), (key1502, -2), (key1502, -2), (key1502, -2), (key1734, 6)]

def rawRow4651 : Integer.Sparse Key := [(key1508, -2), (key1508, -2), (key1947, -2), (key1508, 2), (key1508, 2), (key1737, 2), (key1504, 2), (key1504, 2), (key1945, 2), (key1504, -6), (key1502, -2), (key1502, -2), (key1734, -2), (key1502, 6)]

def rawRow4652 : Integer.Sparse Key := [(key1508, -2), (key1947, -2), (key1508, -2), (key1508, 2), (key1737, 2), (key1508, 2), (key1504, 2), (key1945, 2), (key1504, 2), (key1504, -6), (key1502, -2), (key1734, -2), (key1502, -2), (key1502, 6)]

def rawRow4653 : Integer.Sparse Key := [(key1947, -2), (key1508, -2), (key1508, -2), (key1737, 2), (key1508, 2), (key1508, 2), (key1945, 2), (key1504, 2), (key1504, 2), (key1504, -6), (key1734, -2), (key1502, -2), (key1502, -2), (key1502, 6)]

def rawRow4654 : Integer.Sparse Key := [(key257, -2), (key261, -2), (key261, -2), (key257, 1), (key261, 1), (key257, 1), (key295, 1), (key285, 1), (key295, 1), (key351, 2), (key354, 2), (key354, 2), (key351, -1), (key354, -1), (key351, -1), (key371, -1), (key354, -1), (key371, -1), (key508, -1), (key511, -1), (key508, -1), (key523, -1), (key511, -1), (key523, -1), (key508, 1), (key511, 1), (key508, 1), (key543, 1), (key511, 1), (key543, 1)]

def rawRow4655 : Integer.Sparse Key := [(key261, -2), (key257, -2), (key261, -2), (key261, 1), (key257, 1), (key272, 1), (key282, 1), (key295, 1), (key285, 1), (key354, 2), (key351, 2), (key354, 2), (key354, -1), (key351, -1), (key371, -1), (key351, -1), (key371, -1), (key354, -1), (key511, -1), (key508, -1), (key523, -1), (key508, -1), (key523, -1), (key511, -1), (key511, 1), (key508, 1), (key543, 1), (key508, 1), (key543, 1), (key511, 1)]

def rawRow4656 : Integer.Sparse Key := [(key261, -2), (key261, -2), (key257, -2), (key272, 1), (key272, 1), (key261, 1), (key261, 1), (key282, 1), (key282, 1), (key354, 2), (key354, 2), (key351, 2), (key371, -1), (key371, -1), (key354, -1), (key354, -1), (key351, -1), (key351, -1), (key523, -1), (key523, -1), (key511, -1), (key511, -1), (key508, -1), (key508, -1), (key543, 1), (key543, 1), (key511, 1), (key511, 1), (key508, 1), (key508, 1)]

def rawRow4657 : Integer.Sparse Key := [(key272, -2), (key272, -2), (key272, -2), (key261, 1), (key261, 1), (key261, 1), (key261, 1), (key261, 1), (key261, 1), (key371, 2), (key371, 2), (key371, 2), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key543, -1), (key543, -1), (key543, -1), (key543, -1), (key543, -1), (key543, -1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1)]

def rawRow4658 : Integer.Sparse Key := [(key394, -2), (key398, -2), (key398, -2), (key439, 1), (key443, 1), (key439, 1), (key470, 1), (key443, 1), (key470, 1), (key257, 2), (key261, 2), (key261, 2), (key439, -1), (key443, -1), (key439, -1), (key596, -1), (key443, -1), (key596, -1), (key257, -1), (key261, -1), (key257, -1), (key295, -1), (key285, -1), (key295, -1), (key351, 1), (key354, 1), (key351, 1), (key371, 1), (key354, 1), (key371, 1)]

def rawRow4659 : Integer.Sparse Key := [(key398, -2), (key394, -2), (key398, -2), (key443, 1), (key439, 1), (key470, 1), (key439, 1), (key470, 1), (key443, 1), (key261, 2), (key257, 2), (key261, 2), (key443, -1), (key439, -1), (key596, -1), (key439, -1), (key596, -1), (key443, -1), (key261, -1), (key257, -1), (key272, -1), (key282, -1), (key295, -1), (key285, -1), (key354, 1), (key351, 1), (key371, 1), (key351, 1), (key371, 1), (key354, 1)]

def rawRow4660 : Integer.Sparse Key := [(key398, -2), (key398, -2), (key394, -2), (key470, 1), (key470, 1), (key443, 1), (key443, 1), (key439, 1), (key439, 1), (key261, 2), (key261, 2), (key257, 2), (key596, -1), (key596, -1), (key443, -1), (key443, -1), (key439, -1), (key439, -1), (key272, -1), (key272, -1), (key261, -1), (key261, -1), (key282, -1), (key282, -1), (key371, 1), (key371, 1), (key354, 1), (key354, 1), (key351, 1), (key351, 1)]

def rawRow4661 : Integer.Sparse Key := [(key470, -2), (key470, -2), (key481, -2), (key398, 1), (key398, 1), (key443, 1), (key443, 1), (key458, 1), (key458, 1), (key596, 2), (key596, 2), (key607, 2), (key261, -1), (key261, -1), (key443, -1), (key443, -1), (key458, -1), (key458, -1), (key573, -1), (key573, -1), (key596, -1), (key596, -1), (key607, -1), (key607, -1), (key272, 1), (key272, 1), (key470, 1), (key470, 1), (key481, 1), (key481, 1)]

def rawRow4662 : Integer.Sparse Key := [(key470, -2), (key481, -2), (key470, -2), (key443, 1), (key458, 1), (key398, 1), (key458, 1), (key398, 1), (key443, 1), (key596, 2), (key607, 2), (key596, 2), (key443, -1), (key458, -1), (key261, -1), (key458, -1), (key261, -1), (key443, -1), (key596, -1), (key607, -1), (key573, -1), (key607, -1), (key573, -1), (key596, -1), (key470, 1), (key481, 1), (key272, 1), (key481, 1), (key272, 1), (key470, 1)]

def rawRow4663 : Integer.Sparse Key := [(key481, -2), (key470, -2), (key470, -2), (key458, 1), (key443, 1), (key458, 1), (key398, 1), (key443, 1), (key398, 1), (key607, 2), (key596, 2), (key596, 2), (key458, -1), (key443, -1), (key458, -1), (key261, -1), (key443, -1), (key261, -1), (key607, -1), (key596, -1), (key607, -1), (key573, -1), (key596, -1), (key573, -1), (key481, 1), (key470, 1), (key481, 1), (key272, 1), (key470, 1), (key272, 1)]

def rawRow4664 : Integer.Sparse Key := [(key573, -2), (key573, -2), (key573, -2), (key596, 1), (key596, 1), (key596, 1), (key596, 1), (key596, 1), (key596, 1), (key272, 2), (key272, 2), (key272, 2), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key261, -1), (key261, -1), (key261, -1), (key261, -1), (key261, -1), (key261, -1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1)]

def rawRow4665 : Integer.Sparse Key := [(key596, -2), (key596, -2), (key607, -2), (key573, 1), (key573, 1), (key596, 1), (key596, 1), (key607, 1), (key607, 1), (key470, 2), (key470, 2), (key481, 2), (key272, -1), (key272, -1), (key470, -1), (key470, -1), (key481, -1), (key481, -1), (key398, -1), (key398, -1), (key443, -1), (key443, -1), (key458, -1), (key458, -1), (key261, 1), (key261, 1), (key443, 1), (key443, 1), (key458, 1), (key458, 1)]

def rawRow4666 : Integer.Sparse Key := [(key596, -2), (key607, -2), (key596, -2), (key596, 1), (key607, 1), (key573, 1), (key607, 1), (key573, 1), (key596, 1), (key470, 2), (key481, 2), (key470, 2), (key470, -1), (key481, -1), (key272, -1), (key481, -1), (key272, -1), (key470, -1), (key443, -1), (key458, -1), (key398, -1), (key458, -1), (key398, -1), (key443, -1), (key443, 1), (key458, 1), (key261, 1), (key458, 1), (key261, 1), (key443, 1)]

def rawRow4667 : Integer.Sparse Key := [(key607, -2), (key596, -2), (key596, -2), (key607, 1), (key596, 1), (key607, 1), (key573, 1), (key596, 1), (key573, 1), (key481, 2), (key470, 2), (key470, 2), (key481, -1), (key470, -1), (key481, -1), (key272, -1), (key470, -1), (key272, -1), (key458, -1), (key443, -1), (key458, -1), (key398, -1), (key443, -1), (key398, -1), (key458, 1), (key443, 1), (key458, 1), (key261, 1), (key443, 1), (key261, 1)]

def rawRow4668 : Integer.Sparse Key := [(key223, -2), (key226, -2), (key226, -2), (key226, 6), (key495, 2), (key498, 2), (key498, 2), (key498, -2), (key498, -2), (key552, -2), (key620, -6), (key620, 2), (key620, 2), (key646, 2)]

def rawRow4669 : Integer.Sparse Key := [(key226, -2), (key223, -2), (key226, -2), (key226, 6), (key498, 2), (key495, 2), (key498, 2), (key498, -2), (key552, -2), (key498, -2), (key620, -6), (key620, 2), (key646, 2), (key620, 2)]

def rawRow4670 : Integer.Sparse Key := [(key226, -2), (key226, -2), (key223, -2), (key226, 6), (key498, 2), (key498, 2), (key495, 2), (key552, -2), (key498, -2), (key498, -2), (key620, -6), (key646, 2), (key620, 2), (key620, 2)]

def rawRow4671 : Integer.Sparse Key := [(key226, -2), (key226, -2), (key226, -2), (key223, 6), (key552, 2), (key552, 2), (key552, 2), (key495, -2), (key495, -2), (key495, -2), (key646, -6), (key620, 2), (key620, 2), (key620, 2)]

def rawRow4672 : Integer.Sparse Key := [(key495, -2), (key498, -2), (key498, -2), (key620, 6), (key223, 2), (key226, 2), (key226, 2), (key620, -2), (key620, -2), (key646, -2), (key226, -6), (key498, 2), (key498, 2), (key552, 2)]

def rawRow4673 : Integer.Sparse Key := [(key498, -2), (key495, -2), (key498, -2), (key620, 6), (key226, 2), (key223, 2), (key226, 2), (key620, -2), (key646, -2), (key620, -2), (key226, -6), (key498, 2), (key552, 2), (key498, 2)]

def rawRow4674 : Integer.Sparse Key := [(key498, -2), (key498, -2), (key495, -2), (key620, 6), (key226, 2), (key226, 2), (key223, 2), (key646, -2), (key620, -2), (key620, -2), (key226, -6), (key552, 2), (key498, 2), (key498, 2)]

def rawRow4675 : Integer.Sparse Key := [(key498, -2), (key498, -2), (key620, -2), (key495, 6), (key552, 2), (key552, 2), (key646, 2), (key223, -2), (key495, -2), (key495, -2), (key552, -6), (key226, 2), (key498, 2), (key498, 2)]

def rawRow4676 : Integer.Sparse Key := [(key498, -2), (key620, -2), (key498, -2), (key495, 6), (key552, 2), (key646, 2), (key552, 2), (key495, -2), (key223, -2), (key495, -2), (key552, -6), (key498, 2), (key226, 2), (key498, 2)]

def rawRow4677 : Integer.Sparse Key := [(key620, -2), (key498, -2), (key498, -2), (key495, 6), (key646, 2), (key552, 2), (key552, 2), (key495, -2), (key495, -2), (key223, -2), (key552, -6), (key498, 2), (key498, 2), (key226, 2)]

def rawRow4678 : Integer.Sparse Key := [(key552, -2), (key552, -2), (key552, -2), (key646, 6), (key226, 2), (key226, 2), (key226, 2), (key620, -2), (key620, -2), (key620, -2), (key223, -6), (key495, 2), (key495, 2), (key495, 2)]

def rawRow4679 : Integer.Sparse Key := [(key552, -2), (key552, -2), (key646, -2), (key552, 6), (key498, 2), (key498, 2), (key620, 2), (key226, -2), (key498, -2), (key498, -2), (key495, -6), (key223, 2), (key495, 2), (key495, 2)]

def rawRow4680 : Integer.Sparse Key := [(key552, -2), (key646, -2), (key552, -2), (key552, 6), (key498, 2), (key620, 2), (key498, 2), (key498, -2), (key226, -2), (key498, -2), (key495, -6), (key495, 2), (key223, 2), (key495, 2)]

def rawRow4681 : Integer.Sparse Key := [(key646, -2), (key552, -2), (key552, -2), (key552, 6), (key620, 2), (key498, 2), (key498, 2), (key498, -2), (key498, -2), (key226, -2), (key495, -6), (key495, 2), (key495, 2), (key223, 2)]

def rawRow4682 : Integer.Sparse Key := [(key1366, -2), (key1366, -2), (key1379, -2), (key1366, 1), (key1370, 1), (key1366, 1), (key1379, 1), (key1370, 1), (key1379, 1), (key1718, 2), (key1718, 2), (key1728, 2), (key1718, -1), (key1728, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1747, -1), (key1863, -1), (key1865, -1), (key1863, -1), (key1870, -1), (key1865, -1), (key1870, -1), (key1863, 1), (key1870, 1), (key1863, 1), (key1880, 1), (key1870, 1), (key1880, 1)]

def rawRow4683 : Integer.Sparse Key := [(key1366, -2), (key1379, -2), (key1366, -2), (key1370, 1), (key1366, 1), (key1379, 1), (key1366, 1), (key1379, 1), (key1370, 1), (key1718, 2), (key1728, 2), (key1718, 2), (key1728, -1), (key1718, -1), (key1747, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1865, -1), (key1863, -1), (key1870, -1), (key1863, -1), (key1870, -1), (key1865, -1), (key1870, 1), (key1863, 1), (key1880, 1), (key1863, 1), (key1880, 1), (key1870, 1)]

def rawRow4684 : Integer.Sparse Key := [(key1379, -2), (key1366, -2), (key1366, -2), (key1379, 1), (key1379, 1), (key1370, 1), (key1370, 1), (key1366, 1), (key1366, 1), (key1728, 2), (key1718, 2), (key1718, 2), (key1747, -1), (key1747, -1), (key1728, -1), (key1728, -1), (key1718, -1), (key1718, -1), (key1870, -1), (key1870, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1880, 1), (key1880, 1), (key1870, 1), (key1870, 1), (key1863, 1), (key1863, 1)]

def rawRow4685 : Integer.Sparse Key := [(key1370, -2), (key1370, -2), (key1370, -2), (key1366, 1), (key1366, 1), (key1366, 1), (key1366, 1), (key1366, 1), (key1366, 1), (key1747, 2), (key1747, 2), (key1747, 2), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1)]

def rawRow4686 : Integer.Sparse Key := [(key1718, -2), (key1718, -2), (key1728, -2), (key1863, 1), (key1865, 1), (key1863, 1), (key1870, 1), (key1865, 1), (key1870, 1), (key1366, 2), (key1366, 2), (key1379, 2), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1366, -1), (key1370, -1), (key1366, -1), (key1379, -1), (key1370, -1), (key1379, -1), (key1718, 1), (key1728, 1), (key1718, 1), (key1747, 1), (key1728, 1), (key1747, 1)]

def rawRow4687 : Integer.Sparse Key := [(key1718, -2), (key1728, -2), (key1718, -2), (key1865, 1), (key1863, 1), (key1870, 1), (key1863, 1), (key1870, 1), (key1865, 1), (key1366, 2), (key1379, 2), (key1366, 2), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1370, -1), (key1366, -1), (key1379, -1), (key1366, -1), (key1379, -1), (key1370, -1), (key1728, 1), (key1718, 1), (key1747, 1), (key1718, 1), (key1747, 1), (key1728, 1)]

def rawRow4688 : Integer.Sparse Key := [(key1728, -2), (key1718, -2), (key1718, -2), (key1870, 1), (key1870, 1), (key1865, 1), (key1865, 1), (key1863, 1), (key1863, 1), (key1379, 2), (key1366, 2), (key1366, 2), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1379, -1), (key1379, -1), (key1370, -1), (key1370, -1), (key1366, -1), (key1366, -1), (key1747, 1), (key1747, 1), (key1728, 1), (key1728, 1), (key1718, 1), (key1718, 1)]

def rawRow4689 : Integer.Sparse Key := [(key1496, -2), (key1865, -2), (key1865, -2), (key1492, 1), (key1492, 1), (key1718, 1), (key1718, 1), (key1863, 1), (key1863, 1), (key1519, 2), (key1880, 2), (key1880, 2), (key1366, -1), (key1366, -1), (key1492, -1), (key1492, -1), (key1863, -1), (key1863, -1), (key1519, -1), (key1519, -1), (key1747, -1), (key1747, -1), (key1880, -1), (key1880, -1), (key1370, 1), (key1370, 1), (key1496, 1), (key1496, 1), (key1865, 1), (key1865, 1)]

def rawRow4690 : Integer.Sparse Key := [(key1865, -2), (key1496, -2), (key1865, -2), (key1718, 1), (key1863, 1), (key1492, 1), (key1863, 1), (key1492, 1), (key1718, 1), (key1880, 2), (key1519, 2), (key1880, 2), (key1492, -1), (key1863, -1), (key1366, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1747, -1), (key1880, -1), (key1519, -1), (key1880, -1), (key1519, -1), (key1747, -1), (key1496, 1), (key1865, 1), (key1370, 1), (key1865, 1), (key1370, 1), (key1496, 1)]

def rawRow4691 : Integer.Sparse Key := [(key1865, -2), (key1865, -2), (key1496, -2), (key1863, 1), (key1718, 1), (key1863, 1), (key1492, 1), (key1718, 1), (key1492, 1), (key1880, 2), (key1880, 2), (key1519, 2), (key1863, -1), (key1492, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1366, -1), (key1880, -1), (key1747, -1), (key1880, -1), (key1519, -1), (key1747, -1), (key1519, -1), (key1865, 1), (key1496, 1), (key1865, 1), (key1370, 1), (key1496, 1), (key1370, 1)]

def rawRow4692 : Integer.Sparse Key := [(key1747, -2), (key1747, -2), (key1747, -2), (key1880, 1), (key1880, 1), (key1880, 1), (key1880, 1), (key1880, 1), (key1880, 1), (key1370, 2), (key1370, 2), (key1370, 2), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1)]

def rawRow4693 : Integer.Sparse Key := [(key1519, -2), (key1880, -2), (key1880, -2), (key1519, 1), (key1519, 1), (key1747, 1), (key1747, 1), (key1880, 1), (key1880, 1), (key1496, 2), (key1865, 2), (key1865, 2), (key1370, -1), (key1370, -1), (key1496, -1), (key1496, -1), (key1865, -1), (key1865, -1), (key1492, -1), (key1492, -1), (key1718, -1), (key1718, -1), (key1863, -1), (key1863, -1), (key1366, 1), (key1366, 1), (key1492, 1), (key1492, 1), (key1863, 1), (key1863, 1)]

def rawRow4694 : Integer.Sparse Key := [(key1880, -2), (key1519, -2), (key1880, -2), (key1747, 1), (key1880, 1), (key1519, 1), (key1880, 1), (key1519, 1), (key1747, 1), (key1865, 2), (key1496, 2), (key1865, 2), (key1496, -1), (key1865, -1), (key1370, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1718, -1), (key1863, -1), (key1492, -1), (key1863, -1), (key1492, -1), (key1718, -1), (key1492, 1), (key1863, 1), (key1366, 1), (key1863, 1), (key1366, 1), (key1492, 1)]

def rawRow4695 : Integer.Sparse Key := [(key1880, -2), (key1880, -2), (key1519, -2), (key1880, 1), (key1747, 1), (key1880, 1), (key1519, 1), (key1747, 1), (key1519, 1), (key1865, 2), (key1865, 2), (key1496, 2), (key1865, -1), (key1496, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1370, -1), (key1863, -1), (key1718, -1), (key1863, -1), (key1492, -1), (key1718, -1), (key1492, -1), (key1863, 1), (key1492, 1), (key1863, 1), (key1366, 1), (key1492, 1), (key1366, 1)]

def rawRow4696 : Integer.Sparse Key := [(key1276, -2), (key1281, -2), (key1281, -2), (key1281, 6), (key1699, 2), (key1704, 2), (key1704, 2), (key1704, -2), (key1704, -2), (key1753, -2), (key1934, -6), (key1934, 2), (key1934, 2), (key1954, 2)]

def rawRow4697 : Integer.Sparse Key := [(key1281, -2), (key1276, -2), (key1281, -2), (key1281, 6), (key1704, 2), (key1699, 2), (key1704, 2), (key1704, -2), (key1753, -2), (key1704, -2), (key1934, -6), (key1934, 2), (key1954, 2), (key1934, 2)]

def rawRow4698 : Integer.Sparse Key := [(key1281, -2), (key1281, -2), (key1276, -2), (key1281, 6), (key1704, 2), (key1704, 2), (key1699, 2), (key1753, -2), (key1704, -2), (key1704, -2), (key1934, -6), (key1954, 2), (key1934, 2), (key1934, 2)]

def rawRow4699 : Integer.Sparse Key := [(key1281, -2), (key1281, -2), (key1281, -2), (key1276, 6), (key1753, 2), (key1753, 2), (key1753, 2), (key1699, -2), (key1699, -2), (key1699, -2), (key1954, -6), (key1934, 2), (key1934, 2), (key1934, 2)]

def rawRow4700 : Integer.Sparse Key := [(key1699, -2), (key1704, -2), (key1704, -2), (key1934, 6), (key1276, 2), (key1281, 2), (key1281, 2), (key1934, -2), (key1934, -2), (key1954, -2), (key1281, -6), (key1704, 2), (key1704, 2), (key1753, 2)]

def rawRow4701 : Integer.Sparse Key := [(key1704, -2), (key1699, -2), (key1704, -2), (key1934, 6), (key1281, 2), (key1276, 2), (key1281, 2), (key1934, -2), (key1954, -2), (key1934, -2), (key1281, -6), (key1704, 2), (key1753, 2), (key1704, 2)]

def rawRow4702 : Integer.Sparse Key := [(key1704, -2), (key1704, -2), (key1699, -2), (key1934, 6), (key1281, 2), (key1281, 2), (key1276, 2), (key1954, -2), (key1934, -2), (key1934, -2), (key1281, -6), (key1753, 2), (key1704, 2), (key1704, 2)]

def rawRow4703 : Integer.Sparse Key := [(key1704, -2), (key1704, -2), (key1934, -2), (key1699, 6), (key1753, 2), (key1753, 2), (key1954, 2), (key1276, -2), (key1699, -2), (key1699, -2), (key1753, -6), (key1281, 2), (key1704, 2), (key1704, 2)]

def rawRow4704 : Integer.Sparse Key := [(key1704, -2), (key1934, -2), (key1704, -2), (key1699, 6), (key1753, 2), (key1954, 2), (key1753, 2), (key1699, -2), (key1276, -2), (key1699, -2), (key1753, -6), (key1704, 2), (key1281, 2), (key1704, 2)]

def rawRow4705 : Integer.Sparse Key := [(key1934, -2), (key1704, -2), (key1704, -2), (key1699, 6), (key1954, 2), (key1753, 2), (key1753, 2), (key1699, -2), (key1699, -2), (key1276, -2), (key1753, -6), (key1704, 2), (key1704, 2), (key1281, 2)]

def rawRow4706 : Integer.Sparse Key := [(key1753, -2), (key1753, -2), (key1753, -2), (key1954, 6), (key1281, 2), (key1281, 2), (key1281, 2), (key1934, -2), (key1934, -2), (key1934, -2), (key1276, -6), (key1699, 2), (key1699, 2), (key1699, 2)]

def rawRow4707 : Integer.Sparse Key := [(key1753, -2), (key1753, -2), (key1954, -2), (key1753, 6), (key1704, 2), (key1704, 2), (key1934, 2), (key1281, -2), (key1704, -2), (key1704, -2), (key1699, -6), (key1276, 2), (key1699, 2), (key1699, 2)]

def rawRow4708 : Integer.Sparse Key := [(key1753, -2), (key1954, -2), (key1753, -2), (key1753, 6), (key1704, 2), (key1934, 2), (key1704, 2), (key1704, -2), (key1281, -2), (key1704, -2), (key1699, -6), (key1699, 2), (key1276, 2), (key1699, 2)]

def rawRow4709 : Integer.Sparse Key := [(key1954, -2), (key1753, -2), (key1753, -2), (key1753, 6), (key1934, 2), (key1704, 2), (key1704, 2), (key1704, -2), (key1704, -2), (key1281, -2), (key1699, -6), (key1699, 2), (key1699, 2), (key1276, 2)]

def rawRow4710 : Integer.Sparse Key := [(key1276, -2), (key1279, -2), (key1279, -2), (key1279, 6), (key1699, 2), (key1702, 2), (key1702, 2), (key1702, -2), (key1702, -2), (key1752, -2), (key1853, -6), (key1853, 2), (key1853, 2), (key1885, 2)]

def rawRow4711 : Integer.Sparse Key := [(key1279, -2), (key1276, -2), (key1279, -2), (key1279, 6), (key1702, 2), (key1699, 2), (key1702, 2), (key1702, -2), (key1752, -2), (key1702, -2), (key1853, -6), (key1853, 2), (key1885, 2), (key1853, 2)]

def rawRow4712 : Integer.Sparse Key := [(key1279, -2), (key1279, -2), (key1276, -2), (key1279, 6), (key1702, 2), (key1702, 2), (key1699, 2), (key1752, -2), (key1702, -2), (key1702, -2), (key1853, -6), (key1885, 2), (key1853, 2), (key1853, 2)]

def rawRow4713 : Integer.Sparse Key := [(key1279, -2), (key1279, -2), (key1279, -2), (key1276, 6), (key1752, 2), (key1752, 2), (key1752, 2), (key1699, -2), (key1699, -2), (key1699, -2), (key1885, -6), (key1853, 2), (key1853, 2), (key1853, 2)]

def rawRow4714 : Integer.Sparse Key := [(key1699, -2), (key1702, -2), (key1702, -2), (key1853, 6), (key1276, 2), (key1279, 2), (key1279, 2), (key1853, -2), (key1853, -2), (key1885, -2), (key1279, -6), (key1702, 2), (key1702, 2), (key1752, 2)]

def rawRow4715 : Integer.Sparse Key := [(key1702, -2), (key1699, -2), (key1702, -2), (key1853, 6), (key1279, 2), (key1276, 2), (key1279, 2), (key1853, -2), (key1885, -2), (key1853, -2), (key1279, -6), (key1702, 2), (key1752, 2), (key1702, 2)]

def rawRow4716 : Integer.Sparse Key := [(key1702, -2), (key1702, -2), (key1699, -2), (key1853, 6), (key1279, 2), (key1279, 2), (key1276, 2), (key1885, -2), (key1853, -2), (key1853, -2), (key1279, -6), (key1752, 2), (key1702, 2), (key1702, 2)]

def rawRow4717 : Integer.Sparse Key := [(key1702, -2), (key1702, -2), (key1853, -2), (key1699, 6), (key1752, 2), (key1752, 2), (key1885, 2), (key1276, -2), (key1699, -2), (key1699, -2), (key1752, -6), (key1279, 2), (key1702, 2), (key1702, 2)]

def rawRow4718 : Integer.Sparse Key := [(key1702, -2), (key1853, -2), (key1702, -2), (key1699, 6), (key1752, 2), (key1885, 2), (key1752, 2), (key1699, -2), (key1276, -2), (key1699, -2), (key1752, -6), (key1702, 2), (key1279, 2), (key1702, 2)]

def rawRow4719 : Integer.Sparse Key := [(key1853, -2), (key1702, -2), (key1702, -2), (key1699, 6), (key1885, 2), (key1752, 2), (key1752, 2), (key1699, -2), (key1699, -2), (key1276, -2), (key1752, -6), (key1702, 2), (key1702, 2), (key1279, 2)]

def rawRow4720 : Integer.Sparse Key := [(key1752, -2), (key1752, -2), (key1752, -2), (key1885, 6), (key1279, 2), (key1279, 2), (key1279, 2), (key1853, -2), (key1853, -2), (key1853, -2), (key1276, -6), (key1699, 2), (key1699, 2), (key1699, 2)]

def rawRow4721 : Integer.Sparse Key := [(key1752, -2), (key1752, -2), (key1885, -2), (key1752, 6), (key1702, 2), (key1702, 2), (key1853, 2), (key1279, -2), (key1702, -2), (key1702, -2), (key1699, -6), (key1276, 2), (key1699, 2), (key1699, 2)]

def rawRow4722 : Integer.Sparse Key := [(key1752, -2), (key1885, -2), (key1752, -2), (key1752, 6), (key1702, 2), (key1853, 2), (key1702, 2), (key1702, -2), (key1279, -2), (key1702, -2), (key1699, -6), (key1699, 2), (key1276, 2), (key1699, 2)]

def rawRow4723 : Integer.Sparse Key := [(key1885, -2), (key1752, -2), (key1752, -2), (key1752, 6), (key1853, 2), (key1702, 2), (key1702, 2), (key1702, -2), (key1702, -2), (key1279, -2), (key1699, -6), (key1699, 2), (key1699, 2), (key1276, 2)]

def rawRow4724 : Integer.Sparse Key := [(key1362, -2), (key1365, -2), (key1365, -2), (key1362, 1), (key1365, 1), (key1362, 1), (key1375, 1), (key1365, 1), (key1375, 1), (key1488, 2), (key1491, 2), (key1491, 2), (key1488, -1), (key1491, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1514, -1), (key1714, -1), (key1717, -1), (key1714, -1), (key1724, -1), (key1717, -1), (key1724, -1), (key1714, 1), (key1717, 1), (key1714, 1), (key1742, 1), (key1717, 1), (key1742, 1)]

def rawRow4725 : Integer.Sparse Key := [(key1365, -2), (key1362, -2), (key1365, -2), (key1365, 1), (key1362, 1), (key1375, 1), (key1362, 1), (key1375, 1), (key1365, 1), (key1491, 2), (key1488, 2), (key1491, 2), (key1491, -1), (key1488, -1), (key1514, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1717, -1), (key1714, -1), (key1724, -1), (key1714, -1), (key1724, -1), (key1717, -1), (key1717, 1), (key1714, 1), (key1742, 1), (key1714, 1), (key1742, 1), (key1717, 1)]

def rawRow4726 : Integer.Sparse Key := [(key1365, -2), (key1365, -2), (key1362, -2), (key1375, 1), (key1375, 1), (key1365, 1), (key1365, 1), (key1362, 1), (key1362, 1), (key1491, 2), (key1491, 2), (key1488, 2), (key1514, -1), (key1514, -1), (key1491, -1), (key1491, -1), (key1488, -1), (key1488, -1), (key1724, -1), (key1724, -1), (key1717, -1), (key1717, -1), (key1714, -1), (key1714, -1), (key1742, 1), (key1742, 1), (key1717, 1), (key1717, 1), (key1714, 1), (key1714, 1)]

def rawRow4727 : Integer.Sparse Key := [(key1375, -2), (key1375, -2), (key1375, -2), (key1365, 1), (key1365, 1), (key1365, 1), (key1365, 1), (key1365, 1), (key1365, 1), (key1514, 2), (key1514, 2), (key1514, 2), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1)]

def rawRow4728 : Integer.Sparse Key := [(key1488, -2), (key1491, -2), (key1491, -2), (key1714, 1), (key1717, 1), (key1714, 1), (key1724, 1), (key1717, 1), (key1724, 1), (key1362, 2), (key1365, 2), (key1365, 2), (key1714, -1), (key1717, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1742, -1), (key1362, -1), (key1365, -1), (key1362, -1), (key1375, -1), (key1365, -1), (key1375, -1), (key1488, 1), (key1491, 1), (key1488, 1), (key1514, 1), (key1491, 1), (key1514, 1)]

def rawRow4729 : Integer.Sparse Key := [(key1491, -2), (key1488, -2), (key1491, -2), (key1717, 1), (key1714, 1), (key1724, 1), (key1714, 1), (key1724, 1), (key1717, 1), (key1365, 2), (key1362, 2), (key1365, 2), (key1717, -1), (key1714, -1), (key1742, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1365, -1), (key1362, -1), (key1375, -1), (key1362, -1), (key1375, -1), (key1365, -1), (key1491, 1), (key1488, 1), (key1514, 1), (key1488, 1), (key1514, 1), (key1491, 1)]

def rawRow4730 : Integer.Sparse Key := [(key1491, -2), (key1491, -2), (key1488, -2), (key1724, 1), (key1724, 1), (key1717, 1), (key1717, 1), (key1714, 1), (key1714, 1), (key1365, 2), (key1365, 2), (key1362, 2), (key1742, -1), (key1742, -1), (key1717, -1), (key1717, -1), (key1714, -1), (key1714, -1), (key1375, -1), (key1375, -1), (key1365, -1), (key1365, -1), (key1362, -1), (key1362, -1), (key1514, 1), (key1514, 1), (key1491, 1), (key1491, 1), (key1488, 1), (key1488, 1)]

def rawRow4731 : Integer.Sparse Key := [(key1724, -2), (key1724, -2), (key1868, -2), (key1491, 1), (key1491, 1), (key1717, 1), (key1717, 1), (key1862, 1), (key1862, 1), (key1742, 2), (key1742, 2), (key1878, 2), (key1365, -1), (key1365, -1), (key1717, -1), (key1717, -1), (key1862, -1), (key1862, -1), (key1514, -1), (key1514, -1), (key1742, -1), (key1742, -1), (key1878, -1), (key1878, -1), (key1375, 1), (key1375, 1), (key1724, 1), (key1724, 1), (key1868, 1), (key1868, 1)]

def rawRow4732 : Integer.Sparse Key := [(key1724, -2), (key1868, -2), (key1724, -2), (key1717, 1), (key1862, 1), (key1491, 1), (key1862, 1), (key1491, 1), (key1717, 1), (key1742, 2), (key1878, 2), (key1742, 2), (key1717, -1), (key1862, -1), (key1365, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1742, -1), (key1878, -1), (key1514, -1), (key1878, -1), (key1514, -1), (key1742, -1), (key1724, 1), (key1868, 1), (key1375, 1), (key1868, 1), (key1375, 1), (key1724, 1)]

def rawRow4733 : Integer.Sparse Key := [(key1868, -2), (key1724, -2), (key1724, -2), (key1862, 1), (key1717, 1), (key1862, 1), (key1491, 1), (key1717, 1), (key1491, 1), (key1878, 2), (key1742, 2), (key1742, 2), (key1862, -1), (key1717, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1365, -1), (key1878, -1), (key1742, -1), (key1878, -1), (key1514, -1), (key1742, -1), (key1514, -1), (key1868, 1), (key1724, 1), (key1868, 1), (key1375, 1), (key1724, 1), (key1375, 1)]

def rawRow4734 : Integer.Sparse Key := [(key1514, -2), (key1514, -2), (key1514, -2), (key1742, 1), (key1742, 1), (key1742, 1), (key1742, 1), (key1742, 1), (key1742, 1), (key1375, 2), (key1375, 2), (key1375, 2), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1)]

def rawRow4735 : Integer.Sparse Key := [(key1742, -2), (key1742, -2), (key1878, -2), (key1514, 1), (key1514, 1), (key1742, 1), (key1742, 1), (key1878, 1), (key1878, 1), (key1724, 2), (key1724, 2), (key1868, 2), (key1375, -1), (key1375, -1), (key1724, -1), (key1724, -1), (key1868, -1), (key1868, -1), (key1491, -1), (key1491, -1), (key1717, -1), (key1717, -1), (key1862, -1), (key1862, -1), (key1365, 1), (key1365, 1), (key1717, 1), (key1717, 1), (key1862, 1), (key1862, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4736 : Integer.Sparse Key := [(key1742, -2), (key1878, -2), (key1742, -2), (key1742, 1), (key1878, 1), (key1514, 1), (key1878, 1), (key1514, 1), (key1742, 1), (key1724, 2), (key1868, 2), (key1724, 2), (key1724, -1), (key1868, -1), (key1375, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1717, -1), (key1862, -1), (key1491, -1), (key1862, -1), (key1491, -1), (key1717, -1), (key1717, 1), (key1862, 1), (key1365, 1), (key1862, 1), (key1365, 1), (key1717, 1)]

def rawRow4737 : Integer.Sparse Key := [(key1878, -2), (key1742, -2), (key1742, -2), (key1878, 1), (key1742, 1), (key1878, 1), (key1514, 1), (key1742, 1), (key1514, 1), (key1868, 2), (key1724, 2), (key1724, 2), (key1868, -1), (key1724, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1375, -1), (key1862, -1), (key1717, -1), (key1862, -1), (key1491, -1), (key1717, -1), (key1491, -1), (key1862, 1), (key1717, 1), (key1862, 1), (key1365, 1), (key1717, 1), (key1365, 1)]

def rawRow4738 : Integer.Sparse Key := [(key741, -2), (key742, -2), (key742, -2), (key742, 6), (key900, 2), (key901, 2), (key901, 2), (key901, -2), (key901, -2), (key951, -2), (key913, -6), (key913, 2), (key913, 2), (key954, 2)]

def rawRow4739 : Integer.Sparse Key := [(key742, -2), (key741, -2), (key742, -2), (key742, 6), (key901, 2), (key900, 2), (key901, 2), (key901, -2), (key951, -2), (key901, -2), (key913, -6), (key913, 2), (key954, 2), (key913, 2)]

def rawRow4740 : Integer.Sparse Key := [(key742, -2), (key742, -2), (key741, -2), (key742, 6), (key901, 2), (key901, 2), (key900, 2), (key951, -2), (key901, -2), (key901, -2), (key913, -6), (key954, 2), (key913, 2), (key913, 2)]

def rawRow4741 : Integer.Sparse Key := [(key742, -2), (key742, -2), (key742, -2), (key741, 6), (key951, 2), (key951, 2), (key951, 2), (key900, -2), (key900, -2), (key900, -2), (key954, -6), (key913, 2), (key913, 2), (key913, 2)]

def rawRow4742 : Integer.Sparse Key := [(key900, -2), (key901, -2), (key901, -2), (key913, 6), (key741, 2), (key742, 2), (key742, 2), (key913, -2), (key913, -2), (key954, -2), (key742, -6), (key901, 2), (key901, 2), (key951, 2)]

def rawRow4743 : Integer.Sparse Key := [(key901, -2), (key900, -2), (key901, -2), (key913, 6), (key742, 2), (key741, 2), (key742, 2), (key913, -2), (key954, -2), (key913, -2), (key742, -6), (key901, 2), (key951, 2), (key901, 2)]

def rawRow4744 : Integer.Sparse Key := [(key901, -2), (key901, -2), (key900, -2), (key913, 6), (key742, 2), (key742, 2), (key741, 2), (key954, -2), (key913, -2), (key913, -2), (key742, -6), (key951, 2), (key901, 2), (key901, 2)]

def rawRow4745 : Integer.Sparse Key := [(key901, -2), (key901, -2), (key913, -2), (key900, 6), (key951, 2), (key951, 2), (key954, 2), (key741, -2), (key900, -2), (key900, -2), (key951, -6), (key742, 2), (key901, 2), (key901, 2)]

def rawRow4746 : Integer.Sparse Key := [(key901, -2), (key913, -2), (key901, -2), (key900, 6), (key951, 2), (key954, 2), (key951, 2), (key900, -2), (key741, -2), (key900, -2), (key951, -6), (key901, 2), (key742, 2), (key901, 2)]

def rawRow4747 : Integer.Sparse Key := [(key913, -2), (key901, -2), (key901, -2), (key900, 6), (key954, 2), (key951, 2), (key951, 2), (key900, -2), (key900, -2), (key741, -2), (key951, -6), (key901, 2), (key901, 2), (key742, 2)]

def rawRow4748 : Integer.Sparse Key := [(key951, -2), (key951, -2), (key951, -2), (key954, 6), (key742, 2), (key742, 2), (key742, 2), (key913, -2), (key913, -2), (key913, -2), (key741, -6), (key900, 2), (key900, 2), (key900, 2)]

def rawRow4749 : Integer.Sparse Key := [(key951, -2), (key951, -2), (key954, -2), (key951, 6), (key901, 2), (key901, 2), (key913, 2), (key742, -2), (key901, -2), (key901, -2), (key900, -6), (key741, 2), (key900, 2), (key900, 2)]

def rawRow4750 : Integer.Sparse Key := [(key951, -2), (key954, -2), (key951, -2), (key951, 6), (key901, 2), (key913, 2), (key901, 2), (key901, -2), (key742, -2), (key901, -2), (key900, -6), (key900, 2), (key741, 2), (key900, 2)]

def rawRow4751 : Integer.Sparse Key := [(key954, -2), (key951, -2), (key951, -2), (key951, 6), (key913, 2), (key901, 2), (key901, 2), (key901, -2), (key901, -2), (key742, -2), (key900, -6), (key900, 2), (key900, 2), (key741, 2)]

def rawRow4752 : Integer.Sparse Key := [(key1280, -2), (key1280, -2), (key1284, -2), (key1280, 2), (key1284, 2), (key1284, 2), (key1703, 2), (key1703, 2), (key1707, 2), (key1703, -1), (key1707, -1), (key1703, -1), (key1757, -1), (key1707, -1), (key1757, -1), (key1854, -2), (key1856, -2), (key1856, -2), (key1854, 1), (key1856, 1), (key1854, 1), (key1887, 1), (key1856, 1), (key1887, 1)]

def rawRow4753 : Integer.Sparse Key := [(key1280, -2), (key1284, -2), (key1280, -2), (key1284, 2), (key1280, 2), (key1284, 2), (key1703, 2), (key1707, 2), (key1703, 2), (key1707, -1), (key1703, -1), (key1757, -1), (key1703, -1), (key1757, -1), (key1707, -1), (key1856, -2), (key1854, -2), (key1856, -2), (key1856, 1), (key1854, 1), (key1887, 1), (key1854, 1), (key1887, 1), (key1856, 1)]

def rawRow4754 : Integer.Sparse Key := [(key1284, -2), (key1280, -2), (key1280, -2), (key1284, 2), (key1284, 2), (key1280, 2), (key1707, 2), (key1703, 2), (key1703, 2), (key1757, -1), (key1757, -1), (key1707, -1), (key1707, -1), (key1703, -1), (key1703, -1), (key1856, -2), (key1856, -2), (key1854, -2), (key1887, 1), (key1887, 1), (key1856, 1), (key1856, 1), (key1854, 1), (key1854, 1)]

def rawRow4755 : Integer.Sparse Key := [(key1284, -2), (key1284, -2), (key1284, -2), (key1280, 2), (key1280, 2), (key1280, 2), (key1757, 2), (key1757, 2), (key1757, 2), (key1703, -1), (key1703, -1), (key1703, -1), (key1703, -1), (key1703, -1), (key1703, -1), (key1887, -2), (key1887, -2), (key1887, -2), (key1856, 1), (key1856, 1), (key1856, 1), (key1856, 1), (key1856, 1), (key1856, 1)]

def rawRow4756 : Integer.Sparse Key := [(key1703, -2), (key1703, -2), (key1707, -2), (key1854, 2), (key1856, 2), (key1856, 2), (key1280, 2), (key1280, 2), (key1284, 2), (key1854, -1), (key1856, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1887, -1), (key1280, -2), (key1284, -2), (key1284, -2), (key1703, 1), (key1707, 1), (key1703, 1), (key1757, 1), (key1707, 1), (key1757, 1)]

def rawRow4757 : Integer.Sparse Key := [(key1703, -2), (key1707, -2), (key1703, -2), (key1856, 2), (key1854, 2), (key1856, 2), (key1280, 2), (key1284, 2), (key1280, 2), (key1856, -1), (key1854, -1), (key1887, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1284, -2), (key1280, -2), (key1284, -2), (key1707, 1), (key1703, 1), (key1757, 1), (key1703, 1), (key1757, 1), (key1707, 1)]

def rawRow4758 : Integer.Sparse Key := [(key1707, -2), (key1703, -2), (key1703, -2), (key1856, 2), (key1856, 2), (key1854, 2), (key1284, 2), (key1280, 2), (key1280, 2), (key1887, -1), (key1887, -1), (key1856, -1), (key1856, -1), (key1854, -1), (key1854, -1), (key1284, -2), (key1284, -2), (key1280, -2), (key1757, 1), (key1757, 1), (key1707, 1), (key1707, 1), (key1703, 1), (key1703, 1)]

def rawRow4759 : Integer.Sparse Key := [(key1707, -2), (key1856, -2), (key1856, -2), (key1703, 2), (key1703, 2), (key1854, 2), (key1757, 2), (key1887, 2), (key1887, 2), (key1280, -1), (key1280, -1), (key1703, -1), (key1703, -1), (key1854, -1), (key1854, -1), (key1757, -2), (key1757, -2), (key1887, -2), (key1284, 1), (key1284, 1), (key1707, 1), (key1707, 1), (key1856, 1), (key1856, 1)]

def rawRow4760 : Integer.Sparse Key := [(key1856, -2), (key1707, -2), (key1856, -2), (key1703, 2), (key1854, 2), (key1703, 2), (key1887, 2), (key1757, 2), (key1887, 2), (key1703, -1), (key1854, -1), (key1280, -1), (key1854, -1), (key1280, -1), (key1703, -1), (key1757, -2), (key1887, -2), (key1757, -2), (key1707, 1), (key1856, 1), (key1284, 1), (key1856, 1), (key1284, 1), (key1707, 1)]

def rawRow4761 : Integer.Sparse Key := [(key1856, -2), (key1856, -2), (key1707, -2), (key1854, 2), (key1703, 2), (key1703, 2), (key1887, 2), (key1887, 2), (key1757, 2), (key1854, -1), (key1703, -1), (key1854, -1), (key1280, -1), (key1703, -1), (key1280, -1), (key1887, -2), (key1757, -2), (key1757, -2), (key1856, 1), (key1707, 1), (key1856, 1), (key1284, 1), (key1707, 1), (key1284, 1)]

def rawRow4762 : Integer.Sparse Key := [(key1757, -2), (key1757, -2), (key1757, -2), (key1887, 2), (key1887, 2), (key1887, 2), (key1284, 2), (key1284, 2), (key1284, 2), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1280, -2), (key1280, -2), (key1280, -2), (key1703, 1), (key1703, 1), (key1703, 1), (key1703, 1), (key1703, 1), (key1703, 1)]

def rawRow4763 : Integer.Sparse Key := [(key1757, -2), (key1887, -2), (key1887, -2), (key1757, 2), (key1757, 2), (key1887, 2), (key1707, 2), (key1856, 2), (key1856, 2), (key1284, -1), (key1284, -1), (key1707, -1), (key1707, -1), (key1856, -1), (key1856, -1), (key1703, -2), (key1703, -2), (key1854, -2), (key1280, 1), (key1280, 1), (key1703, 1), (key1703, 1), (key1854, 1), (key1854, 1)]

def rawRow4764 : Integer.Sparse Key := [(key1887, -2), (key1757, -2), (key1887, -2), (key1757, 2), (key1887, 2), (key1757, 2), (key1856, 2), (key1707, 2), (key1856, 2), (key1707, -1), (key1856, -1), (key1284, -1), (key1856, -1), (key1284, -1), (key1707, -1), (key1703, -2), (key1854, -2), (key1703, -2), (key1703, 1), (key1854, 1), (key1280, 1), (key1854, 1), (key1280, 1), (key1703, 1)]

def rawRow4765 : Integer.Sparse Key := [(key1887, -2), (key1887, -2), (key1757, -2), (key1887, 2), (key1757, 2), (key1757, 2), (key1856, 2), (key1856, 2), (key1707, 2), (key1856, -1), (key1707, -1), (key1856, -1), (key1284, -1), (key1707, -1), (key1284, -1), (key1854, -2), (key1703, -2), (key1703, -2), (key1854, 1), (key1703, 1), (key1854, 1), (key1280, 1), (key1703, 1), (key1280, 1)]

def rawRow4766 : Integer.Sparse Key := [(key1488, -1), (key1493, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1515, -1), (key1493, 2), (key1493, 2), (key1515, 2), (key1714, 1), (key1719, 1), (key1714, 1), (key1743, 1), (key1719, 1), (key1743, 1), (key1719, -1), (key1725, -1), (key1719, -1), (key1743, -1), (key1725, -1), (key1743, -1), (key1938, -2), (key1938, -2), (key1950, -2), (key1938, 1), (key1941, 1), (key1938, 1), (key1950, 1), (key1941, 1), (key1950, 1)]

def rawRow4767 : Integer.Sparse Key := [(key1493, -1), (key1488, -1), (key1515, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1493, 2), (key1515, 2), (key1493, 2), (key1719, 1), (key1714, 1), (key1743, 1), (key1714, 1), (key1743, 1), (key1719, 1), (key1725, -1), (key1719, -1), (key1743, -1), (key1719, -1), (key1743, -1), (key1725, -1), (key1938, -2), (key1950, -2), (key1938, -2), (key1941, 1), (key1938, 1), (key1950, 1), (key1938, 1), (key1950, 1), (key1941, 1)]

def rawRow4768 : Integer.Sparse Key := [(key1515, -1), (key1515, -1), (key1493, -1), (key1493, -1), (key1488, -1), (key1488, -1), (key1515, 2), (key1493, 2), (key1493, 2), (key1743, 1), (key1743, 1), (key1719, 1), (key1719, 1), (key1714, 1), (key1714, 1), (key1743, -1), (key1743, -1), (key1725, -1), (key1725, -1), (key1719, -1), (key1719, -1), (key1950, -2), (key1938, -2), (key1938, -2), (key1950, 1), (key1950, 1), (key1941, 1), (key1941, 1), (key1938, 1), (key1938, 1)]

def rawRow4769 : Integer.Sparse Key := [(key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1488, 2), (key1488, 2), (key1488, 2), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1941, -2), (key1941, -2), (key1941, -2), (key1938, 1), (key1938, 1), (key1938, 1), (key1938, 1), (key1938, 1), (key1938, 1)]

def rawRow4770 : Integer.Sparse Key := [(key1714, -1), (key1719, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1743, -1), (key1938, 2), (key1938, 2), (key1950, 2), (key1488, 1), (key1493, 1), (key1488, 1), (key1515, 1), (key1493, 1), (key1515, 1), (key1938, -1), (key1941, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1950, -1), (key1493, -2), (key1493, -2), (key1515, -2), (key1719, 1), (key1725, 1), (key1719, 1), (key1743, 1), (key1725, 1), (key1743, 1)]

def rawRow4771 : Integer.Sparse Key := [(key1719, -1), (key1714, -1), (key1743, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1938, 2), (key1950, 2), (key1938, 2), (key1493, 1), (key1488, 1), (key1515, 1), (key1488, 1), (key1515, 1), (key1493, 1), (key1941, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1493, -2), (key1515, -2), (key1493, -2), (key1725, 1), (key1719, 1), (key1743, 1), (key1719, 1), (key1743, 1), (key1725, 1)]

def rawRow4772 : Integer.Sparse Key := [(key1743, -1), (key1743, -1), (key1719, -1), (key1719, -1), (key1714, -1), (key1714, -1), (key1950, 2), (key1938, 2), (key1938, 2), (key1515, 1), (key1515, 1), (key1493, 1), (key1493, 1), (key1488, 1), (key1488, 1), (key1950, -1), (key1950, -1), (key1941, -1), (key1941, -1), (key1938, -1), (key1938, -1), (key1515, -2), (key1493, -2), (key1493, -2), (key1743, 1), (key1743, 1), (key1725, 1), (key1725, 1), (key1719, 1), (key1719, 1)]

def rawRow4773 : Integer.Sparse Key := [(key1367, -1), (key1367, -1), (key1719, -1), (key1719, -1), (key1938, -1), (key1938, -1), (key1362, 2), (key1714, 2), (key1714, 2), (key1376, 1), (key1376, 1), (key1725, 1), (key1725, 1), (key1941, 1), (key1941, 1), (key1362, -1), (key1362, -1), (key1488, -1), (key1488, -1), (key1714, -1), (key1714, -1), (key1376, -2), (key1725, -2), (key1725, -2), (key1367, 1), (key1367, 1), (key1493, 1), (key1493, 1), (key1719, 1), (key1719, 1)]

def rawRow4774 : Integer.Sparse Key := [(key1719, -1), (key1938, -1), (key1367, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1714, 2), (key1362, 2), (key1714, 2), (key1725, 1), (key1941, 1), (key1376, 1), (key1941, 1), (key1376, 1), (key1725, 1), (key1488, -1), (key1714, -1), (key1362, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1725, -2), (key1376, -2), (key1725, -2), (key1493, 1), (key1719, 1), (key1367, 1), (key1719, 1), (key1367, 1), (key1493, 1)]

def rawRow4775 : Integer.Sparse Key := [(key1938, -1), (key1719, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1367, -1), (key1714, 2), (key1714, 2), (key1362, 2), (key1941, 1), (key1725, 1), (key1941, 1), (key1376, 1), (key1725, 1), (key1376, 1), (key1714, -1), (key1488, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1362, -1), (key1725, -2), (key1725, -2), (key1376, -2), (key1719, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1493, 1), (key1367, 1)]

def rawRow4776 : Integer.Sparse Key := [(key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1941, 2), (key1941, 2), (key1941, 2), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1488, -2), (key1488, -2), (key1488, -2), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1)]

def rawRow4777 : Integer.Sparse Key := [(key1376, -1), (key1376, -1), (key1725, -1), (key1725, -1), (key1941, -1), (key1941, -1), (key1376, 2), (key1725, 2), (key1725, 2), (key1367, 1), (key1367, 1), (key1719, 1), (key1719, 1), (key1938, 1), (key1938, 1), (key1367, -1), (key1367, -1), (key1493, -1), (key1493, -1), (key1719, -1), (key1719, -1), (key1362, -2), (key1714, -2), (key1714, -2), (key1362, 1), (key1362, 1), (key1488, 1), (key1488, 1), (key1714, 1), (key1714, 1)]

def rawRow4778 : Integer.Sparse Key := [(key1725, -1), (key1941, -1), (key1376, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1725, 2), (key1376, 2), (key1725, 2), (key1719, 1), (key1938, 1), (key1367, 1), (key1938, 1), (key1367, 1), (key1719, 1), (key1493, -1), (key1719, -1), (key1367, -1), (key1719, -1), (key1367, -1), (key1493, -1), (key1714, -2), (key1362, -2), (key1714, -2), (key1488, 1), (key1714, 1), (key1362, 1), (key1714, 1), (key1362, 1), (key1488, 1)]

def rawRow4779 : Integer.Sparse Key := [(key1941, -1), (key1725, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1376, -1), (key1725, 2), (key1725, 2), (key1376, 2), (key1938, 1), (key1719, 1), (key1938, 1), (key1367, 1), (key1719, 1), (key1367, 1), (key1719, -1), (key1493, -1), (key1719, -1), (key1367, -1), (key1493, -1), (key1367, -1), (key1714, -2), (key1714, -2), (key1362, -2), (key1714, 1), (key1488, 1), (key1714, 1), (key1362, 1), (key1488, 1), (key1362, 1)]

def rawRow4780 : Integer.Sparse Key := [(key1362, -2), (key1365, -2), (key1365, -2), (key1365, 2), (key1365, 2), (key1375, 2), (key1488, 2), (key1491, 2), (key1491, 2), (key1491, -2), (key1491, -2), (key1514, -2), (key1862, -2), (key1862, -2), (key1868, -2), (key1862, 2), (key1862, 2), (key1878, 2)]

def rawRow4781 : Integer.Sparse Key := [(key1365, -2), (key1362, -2), (key1365, -2), (key1365, 2), (key1375, 2), (key1365, 2), (key1491, 2), (key1488, 2), (key1491, 2), (key1491, -2), (key1514, -2), (key1491, -2), (key1862, -2), (key1868, -2), (key1862, -2), (key1862, 2), (key1878, 2), (key1862, 2)]

def rawRow4782 : Integer.Sparse Key := [(key1365, -2), (key1365, -2), (key1362, -2), (key1375, 2), (key1365, 2), (key1365, 2), (key1491, 2), (key1491, 2), (key1488, 2), (key1514, -2), (key1491, -2), (key1491, -2), (key1868, -2), (key1862, -2), (key1862, -2), (key1878, 2), (key1862, 2), (key1862, 2)]

def rawRow4783 : Integer.Sparse Key := [(key1375, -2), (key1375, -2), (key1375, -2), (key1362, 2), (key1362, 2), (key1362, 2), (key1514, 2), (key1514, 2), (key1514, 2), (key1488, -2), (key1488, -2), (key1488, -2), (key1878, -2), (key1878, -2), (key1878, -2), (key1868, 2), (key1868, 2), (key1868, 2)]

def rawRow4784 : Integer.Sparse Key := [(key1488, -2), (key1491, -2), (key1491, -2), (key1862, 2), (key1862, 2), (key1868, 2), (key1362, 2), (key1365, 2), (key1365, 2), (key1862, -2), (key1862, -2), (key1878, -2), (key1365, -2), (key1365, -2), (key1375, -2), (key1491, 2), (key1491, 2), (key1514, 2)]

def rawRow4785 : Integer.Sparse Key := [(key1491, -2), (key1488, -2), (key1491, -2), (key1862, 2), (key1868, 2), (key1862, 2), (key1365, 2), (key1362, 2), (key1365, 2), (key1862, -2), (key1878, -2), (key1862, -2), (key1365, -2), (key1375, -2), (key1365, -2), (key1491, 2), (key1514, 2), (key1491, 2)]

def rawRow4786 : Integer.Sparse Key := [(key1491, -2), (key1491, -2), (key1488, -2), (key1868, 2), (key1862, 2), (key1862, 2), (key1365, 2), (key1365, 2), (key1362, 2), (key1878, -2), (key1862, -2), (key1862, -2), (key1375, -2), (key1365, -2), (key1365, -2), (key1514, 2), (key1491, 2), (key1491, 2)]

def rawRow4787 : Integer.Sparse Key := [(key1724, -2), (key1724, -2), (key1868, -2), (key1488, 2), (key1714, 2), (key1714, 2), (key1742, 2), (key1742, 2), (key1878, 2), (key1362, -2), (key1714, -2), (key1714, -2), (key1514, -2), (key1742, -2), (key1742, -2), (key1375, 2), (key1724, 2), (key1724, 2)]

def rawRow4788 : Integer.Sparse Key := [(key1724, -2), (key1868, -2), (key1724, -2), (key1714, 2), (key1488, 2), (key1714, 2), (key1742, 2), (key1878, 2), (key1742, 2), (key1714, -2), (key1362, -2), (key1714, -2), (key1742, -2), (key1514, -2), (key1742, -2), (key1724, 2), (key1375, 2), (key1724, 2)]

def rawRow4789 : Integer.Sparse Key := [(key1868, -2), (key1724, -2), (key1724, -2), (key1714, 2), (key1714, 2), (key1488, 2), (key1878, 2), (key1742, 2), (key1742, 2), (key1714, -2), (key1714, -2), (key1362, -2), (key1742, -2), (key1742, -2), (key1514, -2), (key1724, 2), (key1724, 2), (key1375, 2)]

def rawRow4790 : Integer.Sparse Key := [(key1514, -2), (key1514, -2), (key1514, -2), (key1878, 2), (key1878, 2), (key1878, 2), (key1375, 2), (key1375, 2), (key1375, 2), (key1868, -2), (key1868, -2), (key1868, -2), (key1362, -2), (key1362, -2), (key1362, -2), (key1488, 2), (key1488, 2), (key1488, 2)]

def rawRow4791 : Integer.Sparse Key := [(key1742, -2), (key1742, -2), (key1878, -2), (key1514, 2), (key1742, 2), (key1742, 2), (key1724, 2), (key1724, 2), (key1868, 2), (key1375, -2), (key1724, -2), (key1724, -2), (key1488, -2), (key1714, -2), (key1714, -2), (key1362, 2), (key1714, 2), (key1714, 2)]

def rawRow4792 : Integer.Sparse Key := [(key1742, -2), (key1878, -2), (key1742, -2), (key1742, 2), (key1514, 2), (key1742, 2), (key1724, 2), (key1868, 2), (key1724, 2), (key1724, -2), (key1375, -2), (key1724, -2), (key1714, -2), (key1488, -2), (key1714, -2), (key1714, 2), (key1362, 2), (key1714, 2)]

def rawRow4793 : Integer.Sparse Key := [(key1878, -2), (key1742, -2), (key1742, -2), (key1742, 2), (key1742, 2), (key1514, 2), (key1868, 2), (key1724, 2), (key1724, 2), (key1724, -2), (key1724, -2), (key1375, -2), (key1714, -2), (key1714, -2), (key1488, -2), (key1714, 2), (key1714, 2), (key1362, 2)]

def rawRow4794 : Integer.Sparse Key := [(key351, -1), (key353, -1), (key351, -1), (key370, -1), (key353, -1), (key370, -1), (key353, 2), (key353, 2), (key370, 2), (key508, 1), (key510, 1), (key508, 1), (key542, 1), (key510, 1), (key542, 1), (key510, -1), (key521, -1), (key510, -1), (key542, -1), (key521, -1), (key542, -1), (key628, -2), (key628, -2), (key641, -2), (key628, 1), (key630, 1), (key628, 1), (key641, 1), (key630, 1), (key641, 1)]

def rawRow4795 : Integer.Sparse Key := [(key353, -1), (key351, -1), (key370, -1), (key351, -1), (key370, -1), (key353, -1), (key353, 2), (key370, 2), (key353, 2), (key510, 1), (key508, 1), (key542, 1), (key508, 1), (key542, 1), (key510, 1), (key521, -1), (key510, -1), (key542, -1), (key510, -1), (key542, -1), (key521, -1), (key628, -2), (key641, -2), (key628, -2), (key630, 1), (key628, 1), (key641, 1), (key628, 1), (key641, 1), (key630, 1)]

def rawRow4796 : Integer.Sparse Key := [(key370, -1), (key370, -1), (key353, -1), (key353, -1), (key351, -1), (key351, -1), (key370, 2), (key353, 2), (key353, 2), (key542, 1), (key542, 1), (key510, 1), (key510, 1), (key508, 1), (key508, 1), (key542, -1), (key542, -1), (key521, -1), (key521, -1), (key510, -1), (key510, -1), (key641, -2), (key628, -2), (key628, -2), (key641, 1), (key641, 1), (key630, 1), (key630, 1), (key628, 1), (key628, 1)]

def rawRow4797 : Integer.Sparse Key := [(key353, -1), (key353, -1), (key353, -1), (key353, -1), (key353, -1), (key353, -1), (key351, 2), (key351, 2), (key351, 2), (key521, 1), (key521, 1), (key521, 1), (key521, 1), (key521, 1), (key521, 1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key630, -2), (key630, -2), (key630, -2), (key628, 1), (key628, 1), (key628, 1), (key628, 1), (key628, 1), (key628, 1)]

def rawRow4798 : Integer.Sparse Key := [(key508, -1), (key510, -1), (key508, -1), (key542, -1), (key510, -1), (key542, -1), (key628, 2), (key628, 2), (key641, 2), (key351, 1), (key353, 1), (key351, 1), (key370, 1), (key353, 1), (key370, 1), (key628, -1), (key630, -1), (key628, -1), (key641, -1), (key630, -1), (key641, -1), (key353, -2), (key353, -2), (key370, -2), (key510, 1), (key521, 1), (key510, 1), (key542, 1), (key521, 1), (key542, 1)]

def rawRow4799 : Integer.Sparse Key := [(key510, -1), (key508, -1), (key542, -1), (key508, -1), (key542, -1), (key510, -1), (key628, 2), (key641, 2), (key628, 2), (key353, 1), (key351, 1), (key370, 1), (key351, 1), (key370, 1), (key353, 1), (key630, -1), (key628, -1), (key641, -1), (key628, -1), (key641, -1), (key630, -1), (key353, -2), (key370, -2), (key353, -2), (key521, 1), (key510, 1), (key542, 1), (key510, 1), (key542, 1), (key521, 1)]

def rawRow4800 : Integer.Sparse Key := [(key542, -1), (key542, -1), (key510, -1), (key510, -1), (key508, -1), (key508, -1), (key641, 2), (key628, 2), (key628, 2), (key370, 1), (key370, 1), (key353, 1), (key353, 1), (key351, 1), (key351, 1), (key641, -1), (key641, -1), (key630, -1), (key630, -1), (key628, -1), (key628, -1), (key370, -2), (key353, -2), (key353, -2), (key542, 1), (key542, 1), (key521, 1), (key521, 1), (key510, 1), (key510, 1)]

def rawRow4801 : Integer.Sparse Key := [(key284, -1), (key284, -1), (key510, -1), (key510, -1), (key628, -1), (key628, -1), (key282, 2), (key508, 2), (key508, 2), (key293, 1), (key293, 1), (key521, 1), (key521, 1), (key630, 1), (key630, 1), (key282, -1), (key282, -1), (key351, -1), (key351, -1), (key508, -1), (key508, -1), (key293, -2), (key521, -2), (key521, -2), (key284, 1), (key284, 1), (key353, 1), (key353, 1), (key510, 1), (key510, 1)]

def rawRow4802 : Integer.Sparse Key := [(key510, -1), (key628, -1), (key284, -1), (key628, -1), (key284, -1), (key510, -1), (key508, 2), (key282, 2), (key508, 2), (key521, 1), (key630, 1), (key293, 1), (key630, 1), (key293, 1), (key521, 1), (key351, -1), (key508, -1), (key282, -1), (key508, -1), (key282, -1), (key351, -1), (key521, -2), (key293, -2), (key521, -2), (key353, 1), (key510, 1), (key284, 1), (key510, 1), (key284, 1), (key353, 1)]

def rawRow4803 : Integer.Sparse Key := [(key628, -1), (key510, -1), (key628, -1), (key284, -1), (key510, -1), (key284, -1), (key508, 2), (key508, 2), (key282, 2), (key630, 1), (key521, 1), (key630, 1), (key293, 1), (key521, 1), (key293, 1), (key508, -1), (key351, -1), (key508, -1), (key282, -1), (key351, -1), (key282, -1), (key521, -2), (key521, -2), (key293, -2), (key510, 1), (key353, 1), (key510, 1), (key284, 1), (key353, 1), (key284, 1)]

def rawRow4804 : Integer.Sparse Key := [(key521, -1), (key521, -1), (key521, -1), (key521, -1), (key521, -1), (key521, -1), (key630, 2), (key630, 2), (key630, 2), (key353, 1), (key353, 1), (key353, 1), (key353, 1), (key353, 1), (key353, 1), (key628, -1), (key628, -1), (key628, -1), (key628, -1), (key628, -1), (key628, -1), (key351, -2), (key351, -2), (key351, -2), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1)]

def rawRow4805 : Integer.Sparse Key := [(key293, -1), (key293, -1), (key521, -1), (key521, -1), (key630, -1), (key630, -1), (key293, 2), (key521, 2), (key521, 2), (key284, 1), (key284, 1), (key510, 1), (key510, 1), (key628, 1), (key628, 1), (key284, -1), (key284, -1), (key353, -1), (key353, -1), (key510, -1), (key510, -1), (key282, -2), (key508, -2), (key508, -2), (key282, 1), (key282, 1), (key351, 1), (key351, 1), (key508, 1), (key508, 1)]

def rawRow4806 : Integer.Sparse Key := [(key521, -1), (key630, -1), (key293, -1), (key630, -1), (key293, -1), (key521, -1), (key521, 2), (key293, 2), (key521, 2), (key510, 1), (key628, 1), (key284, 1), (key628, 1), (key284, 1), (key510, 1), (key353, -1), (key510, -1), (key284, -1), (key510, -1), (key284, -1), (key353, -1), (key508, -2), (key282, -2), (key508, -2), (key351, 1), (key508, 1), (key282, 1), (key508, 1), (key282, 1), (key351, 1)]

def rawRow4807 : Integer.Sparse Key := [(key630, -1), (key521, -1), (key630, -1), (key293, -1), (key521, -1), (key293, -1), (key521, 2), (key521, 2), (key293, 2), (key628, 1), (key510, 1), (key628, 1), (key284, 1), (key510, 1), (key284, 1), (key510, -1), (key353, -1), (key510, -1), (key284, -1), (key353, -1), (key284, -1), (key508, -2), (key508, -2), (key282, -2), (key508, 1), (key351, 1), (key508, 1), (key282, 1), (key351, 1), (key282, 1)]

def rawRow4808 : Integer.Sparse Key := [(key1488, -1), (key1491, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1514, -1), (key1491, 2), (key1491, 2), (key1514, 2), (key1714, 1), (key1717, 1), (key1714, 1), (key1742, 1), (key1717, 1), (key1742, 1), (key1717, -1), (key1724, -1), (key1717, -1), (key1742, -1), (key1724, -1), (key1742, -1), (key1862, -2), (key1862, -2), (key1878, -2), (key1862, 1), (key1868, 1), (key1862, 1), (key1878, 1), (key1868, 1), (key1878, 1)]

def rawRow4809 : Integer.Sparse Key := [(key1491, -1), (key1488, -1), (key1514, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1491, 2), (key1514, 2), (key1491, 2), (key1717, 1), (key1714, 1), (key1742, 1), (key1714, 1), (key1742, 1), (key1717, 1), (key1724, -1), (key1717, -1), (key1742, -1), (key1717, -1), (key1742, -1), (key1724, -1), (key1862, -2), (key1878, -2), (key1862, -2), (key1868, 1), (key1862, 1), (key1878, 1), (key1862, 1), (key1878, 1), (key1868, 1)]

def rawRow4810 : Integer.Sparse Key := [(key1514, -1), (key1514, -1), (key1491, -1), (key1491, -1), (key1488, -1), (key1488, -1), (key1514, 2), (key1491, 2), (key1491, 2), (key1742, 1), (key1742, 1), (key1717, 1), (key1717, 1), (key1714, 1), (key1714, 1), (key1742, -1), (key1742, -1), (key1724, -1), (key1724, -1), (key1717, -1), (key1717, -1), (key1878, -2), (key1862, -2), (key1862, -2), (key1878, 1), (key1878, 1), (key1868, 1), (key1868, 1), (key1862, 1), (key1862, 1)]

def rawRow4811 : Integer.Sparse Key := [(key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1488, 2), (key1488, 2), (key1488, 2), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1868, -2), (key1868, -2), (key1868, -2), (key1862, 1), (key1862, 1), (key1862, 1), (key1862, 1), (key1862, 1), (key1862, 1)]

def rawRow4812 : Integer.Sparse Key := [(key1714, -1), (key1717, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1742, -1), (key1862, 2), (key1862, 2), (key1878, 2), (key1488, 1), (key1491, 1), (key1488, 1), (key1514, 1), (key1491, 1), (key1514, 1), (key1862, -1), (key1868, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1878, -1), (key1491, -2), (key1491, -2), (key1514, -2), (key1717, 1), (key1724, 1), (key1717, 1), (key1742, 1), (key1724, 1), (key1742, 1)]

def rawRow4813 : Integer.Sparse Key := [(key1717, -1), (key1714, -1), (key1742, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1862, 2), (key1878, 2), (key1862, 2), (key1491, 1), (key1488, 1), (key1514, 1), (key1488, 1), (key1514, 1), (key1491, 1), (key1868, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1491, -2), (key1514, -2), (key1491, -2), (key1724, 1), (key1717, 1), (key1742, 1), (key1717, 1), (key1742, 1), (key1724, 1)]

def rawRow4814 : Integer.Sparse Key := [(key1742, -1), (key1742, -1), (key1717, -1), (key1717, -1), (key1714, -1), (key1714, -1), (key1878, 2), (key1862, 2), (key1862, 2), (key1514, 1), (key1514, 1), (key1491, 1), (key1491, 1), (key1488, 1), (key1488, 1), (key1878, -1), (key1878, -1), (key1868, -1), (key1868, -1), (key1862, -1), (key1862, -1), (key1514, -2), (key1491, -2), (key1491, -2), (key1742, 1), (key1742, 1), (key1724, 1), (key1724, 1), (key1717, 1), (key1717, 1)]

def rawRow4815 : Integer.Sparse Key := [(key1365, -1), (key1365, -1), (key1717, -1), (key1717, -1), (key1862, -1), (key1862, -1), (key1362, 2), (key1714, 2), (key1714, 2), (key1375, 1), (key1375, 1), (key1724, 1), (key1724, 1), (key1868, 1), (key1868, 1), (key1362, -1), (key1362, -1), (key1488, -1), (key1488, -1), (key1714, -1), (key1714, -1), (key1375, -2), (key1724, -2), (key1724, -2), (key1365, 1), (key1365, 1), (key1491, 1), (key1491, 1), (key1717, 1), (key1717, 1)]

def rawRow4816 : Integer.Sparse Key := [(key1717, -1), (key1862, -1), (key1365, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1714, 2), (key1362, 2), (key1714, 2), (key1724, 1), (key1868, 1), (key1375, 1), (key1868, 1), (key1375, 1), (key1724, 1), (key1488, -1), (key1714, -1), (key1362, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1724, -2), (key1375, -2), (key1724, -2), (key1491, 1), (key1717, 1), (key1365, 1), (key1717, 1), (key1365, 1), (key1491, 1)]

def rawRow4817 : Integer.Sparse Key := [(key1862, -1), (key1717, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1365, -1), (key1714, 2), (key1714, 2), (key1362, 2), (key1868, 1), (key1724, 1), (key1868, 1), (key1375, 1), (key1724, 1), (key1375, 1), (key1714, -1), (key1488, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1362, -1), (key1724, -2), (key1724, -2), (key1375, -2), (key1717, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1491, 1), (key1365, 1)]

def rawRow4818 : Integer.Sparse Key := [(key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1868, 2), (key1868, 2), (key1868, 2), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1488, -2), (key1488, -2), (key1488, -2), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1)]

def rawRow4819 : Integer.Sparse Key := [(key1375, -1), (key1375, -1), (key1724, -1), (key1724, -1), (key1868, -1), (key1868, -1), (key1375, 2), (key1724, 2), (key1724, 2), (key1365, 1), (key1365, 1), (key1717, 1), (key1717, 1), (key1862, 1), (key1862, 1), (key1365, -1), (key1365, -1), (key1491, -1), (key1491, -1), (key1717, -1), (key1717, -1), (key1362, -2), (key1714, -2), (key1714, -2), (key1362, 1), (key1362, 1), (key1488, 1), (key1488, 1), (key1714, 1), (key1714, 1)]

def rawRow4820 : Integer.Sparse Key := [(key1724, -1), (key1868, -1), (key1375, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1724, 2), (key1375, 2), (key1724, 2), (key1717, 1), (key1862, 1), (key1365, 1), (key1862, 1), (key1365, 1), (key1717, 1), (key1491, -1), (key1717, -1), (key1365, -1), (key1717, -1), (key1365, -1), (key1491, -1), (key1714, -2), (key1362, -2), (key1714, -2), (key1488, 1), (key1714, 1), (key1362, 1), (key1714, 1), (key1362, 1), (key1488, 1)]

def rawRow4821 : Integer.Sparse Key := [(key1868, -1), (key1724, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1375, -1), (key1724, 2), (key1724, 2), (key1375, 2), (key1862, 1), (key1717, 1), (key1862, 1), (key1365, 1), (key1717, 1), (key1365, 1), (key1717, -1), (key1491, -1), (key1717, -1), (key1365, -1), (key1491, -1), (key1365, -1), (key1714, -2), (key1714, -2), (key1362, -2), (key1714, 1), (key1488, 1), (key1714, 1), (key1362, 1), (key1488, 1), (key1362, 1)]

def rawRow4822 : Integer.Sparse Key := [(key291, -2), (key294, -2), (key294, -2), (key294, 6), (key518, 2), (key522, 2), (key522, 2), (key522, -2), (key522, -2), (key553, -2), (key631, -6), (key631, 2), (key631, 2), (key647, 2)]

def rawRow4823 : Integer.Sparse Key := [(key294, -2), (key291, -2), (key294, -2), (key294, 6), (key522, 2), (key518, 2), (key522, 2), (key522, -2), (key553, -2), (key522, -2), (key631, -6), (key631, 2), (key647, 2), (key631, 2)]

def rawRow4824 : Integer.Sparse Key := [(key294, -2), (key294, -2), (key291, -2), (key294, 6), (key522, 2), (key522, 2), (key518, 2), (key553, -2), (key522, -2), (key522, -2), (key631, -6), (key647, 2), (key631, 2), (key631, 2)]

def rawRow4825 : Integer.Sparse Key := [(key294, -2), (key294, -2), (key294, -2), (key291, 6), (key553, 2), (key553, 2), (key553, 2), (key518, -2), (key518, -2), (key518, -2), (key647, -6), (key631, 2), (key631, 2), (key631, 2)]

def rawRow4826 : Integer.Sparse Key := [(key518, -2), (key522, -2), (key522, -2), (key553, 6), (key291, 2), (key294, 2), (key294, 2), (key631, -2), (key631, -2), (key647, -2), (key294, -6), (key522, 2), (key522, 2), (key553, 2)]

def rawRow4827 : Integer.Sparse Key := [(key522, -2), (key518, -2), (key522, -2), (key553, 6), (key294, 2), (key291, 2), (key294, 2), (key631, -2), (key647, -2), (key631, -2), (key294, -6), (key522, 2), (key553, 2), (key522, 2)]

def rawRow4828 : Integer.Sparse Key := [(key522, -2), (key522, -2), (key518, -2), (key553, 6), (key294, 2), (key294, 2), (key291, 2), (key647, -2), (key631, -2), (key631, -2), (key294, -6), (key553, 2), (key522, 2), (key522, 2)]

def rawRow4829 : Integer.Sparse Key := [(key522, -2), (key522, -2), (key553, -2), (key518, 6), (key631, 2), (key631, 2), (key647, 2), (key291, -2), (key518, -2), (key518, -2), (key553, -6), (key294, 2), (key522, 2), (key522, 2)]

def rawRow4830 : Integer.Sparse Key := [(key522, -2), (key553, -2), (key522, -2), (key518, 6), (key631, 2), (key647, 2), (key631, 2), (key518, -2), (key291, -2), (key518, -2), (key553, -6), (key522, 2), (key294, 2), (key522, 2)]

def rawRow4831 : Integer.Sparse Key := [(key553, -2), (key522, -2), (key522, -2), (key518, 6), (key647, 2), (key631, 2), (key631, 2), (key518, -2), (key518, -2), (key291, -2), (key553, -6), (key522, 2), (key522, 2), (key294, 2)]

def rawRow4832 : Integer.Sparse Key := [(key631, -2), (key631, -2), (key631, -2), (key647, 6), (key294, 2), (key294, 2), (key294, 2), (key553, -2), (key553, -2), (key553, -2), (key291, -6), (key518, 2), (key518, 2), (key518, 2)]

def rawRow4833 : Integer.Sparse Key := [(key631, -2), (key631, -2), (key647, -2), (key631, 6), (key522, 2), (key522, 2), (key553, 2), (key294, -2), (key522, -2), (key522, -2), (key518, -6), (key291, 2), (key518, 2), (key518, 2)]

def rawRow4834 : Integer.Sparse Key := [(key631, -2), (key647, -2), (key631, -2), (key631, 6), (key522, 2), (key553, 2), (key522, 2), (key522, -2), (key294, -2), (key522, -2), (key518, -6), (key518, 2), (key291, 2), (key518, 2)]

def rawRow4835 : Integer.Sparse Key := [(key647, -2), (key631, -2), (key631, -2), (key631, 6), (key553, 2), (key522, 2), (key522, 2), (key522, -2), (key522, -2), (key294, -2), (key518, -6), (key518, 2), (key518, 2), (key291, 2)]

def rawRow4836 : Integer.Sparse Key := [(key2707, -2), (key2730, -2), (key2730, -2), (key2739, 1), (key2739, 1), (key2749, 1), (key2749, 1), (key2751, 1), (key2751, 1), (key2810, 2), (key2833, 2), (key2833, 2), (key2899, -1), (key2899, -1), (key2906, -1), (key2906, -1), (key2915, -1), (key2915, -1), (key2952, -1), (key2952, -1), (key2962, -1), (key2962, -1), (key2964, -1), (key2964, -1), (key2978, 1), (key2978, 1), (key2985, 1), (key2985, 1), (key2994, 1), (key2994, 1)]

def rawRow4837 : Integer.Sparse Key := [(key2730, -2), (key2707, -2), (key2730, -2), (key2749, 1), (key2751, 1), (key2739, 1), (key2751, 1), (key2739, 1), (key2749, 1), (key2833, 2), (key2810, 2), (key2833, 2), (key2906, -1), (key2915, -1), (key2899, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2962, -1), (key2964, -1), (key2952, -1), (key2964, -1), (key2952, -1), (key2962, -1), (key2985, 1), (key2994, 1), (key2978, 1), (key2994, 1), (key2978, 1), (key2985, 1)]

def rawRow4838 : Integer.Sparse Key := [(key2730, -2), (key2730, -2), (key2707, -2), (key2751, 1), (key2749, 1), (key2751, 1), (key2739, 1), (key2749, 1), (key2739, 1), (key2833, 2), (key2833, 2), (key2810, 2), (key2915, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2899, -1), (key2964, -1), (key2962, -1), (key2964, -1), (key2952, -1), (key2962, -1), (key2952, -1), (key2994, 1), (key2985, 1), (key2994, 1), (key2978, 1), (key2985, 1), (key2978, 1)]

def rawRow4839 : Integer.Sparse Key := [(key2810, -2), (key2833, -2), (key2833, -2), (key2952, 1), (key2952, 1), (key2962, 1), (key2962, 1), (key2964, 1), (key2964, 1), (key2707, 2), (key2730, 2), (key2730, 2), (key2978, -1), (key2978, -1), (key2985, -1), (key2985, -1), (key2994, -1), (key2994, -1), (key2739, -1), (key2739, -1), (key2749, -1), (key2749, -1), (key2751, -1), (key2751, -1), (key2899, 1), (key2899, 1), (key2906, 1), (key2906, 1), (key2915, 1), (key2915, 1)]

def rawRow4840 : Integer.Sparse Key := [(key2833, -2), (key2810, -2), (key2833, -2), (key2962, 1), (key2964, 1), (key2952, 1), (key2964, 1), (key2952, 1), (key2962, 1), (key2730, 2), (key2707, 2), (key2730, 2), (key2985, -1), (key2994, -1), (key2978, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2749, -1), (key2751, -1), (key2739, -1), (key2751, -1), (key2739, -1), (key2749, -1), (key2906, 1), (key2915, 1), (key2899, 1), (key2915, 1), (key2899, 1), (key2906, 1)]

def rawRow4841 : Integer.Sparse Key := [(key2833, -2), (key2833, -2), (key2810, -2), (key2964, 1), (key2962, 1), (key2964, 1), (key2952, 1), (key2962, 1), (key2952, 1), (key2730, 2), (key2730, 2), (key2707, 2), (key2994, -1), (key2985, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2978, -1), (key2751, -1), (key2749, -1), (key2751, -1), (key2739, -1), (key2749, -1), (key2739, -1), (key2915, 1), (key2906, 1), (key2915, 1), (key2899, 1), (key2906, 1), (key2899, 1)]

def rawRow4842 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 2), (key1335, 2), (key1389, 6), (key1544, -2), (key1770, -2), (key1770, -2), (key1422, -2), (key1453, -2), (key1453, -2), (key1571, 2), (key1786, 2), (key1786, 2)]

def rawRow4843 : Integer.Sparse Key := [(key1294, -6), (key1335, 2), (key1314, 2), (key1335, 2), (key1389, 6), (key1770, -2), (key1544, -2), (key1770, -2), (key1453, -2), (key1422, -2), (key1453, -2), (key1786, 2), (key1571, 2), (key1786, 2)]

def rawRow4844 : Integer.Sparse Key := [(key1294, -6), (key1335, 2), (key1335, 2), (key1314, 2), (key1389, 6), (key1770, -2), (key1770, -2), (key1544, -2), (key1453, -2), (key1453, -2), (key1422, -2), (key1786, 2), (key1786, 2), (key1571, 2)]

def rawRow4845 : Integer.Sparse Key := [(key1389, -6), (key1422, 2), (key1453, 2), (key1453, 2), (key1294, 6), (key1571, -2), (key1786, -2), (key1786, -2), (key1314, -2), (key1335, -2), (key1335, -2), (key1544, 2), (key1770, 2), (key1770, 2)]

def rawRow4846 : Integer.Sparse Key := [(key1389, -6), (key1453, 2), (key1422, 2), (key1453, 2), (key1294, 6), (key1786, -2), (key1571, -2), (key1786, -2), (key1335, -2), (key1314, -2), (key1335, -2), (key1770, 2), (key1544, 2), (key1770, 2)]

def rawRow4847 : Integer.Sparse Key := [(key1389, -6), (key1453, 2), (key1453, 2), (key1422, 2), (key1294, 6), (key1786, -2), (key1786, -2), (key1571, -2), (key1335, -2), (key1335, -2), (key1314, -2), (key1770, 2), (key1770, 2), (key1544, 2)]

def rawRow4848 : Integer.Sparse Key := [(key1422, -6), (key1389, 2), (key1453, 2), (key1453, 2), (key1571, 6), (key1294, -2), (key1786, -2), (key1786, -2), (key1544, -2), (key1653, -2), (key1653, -2), (key1314, 2), (key1811, 2), (key1811, 2)]

def rawRow4849 : Integer.Sparse Key := [(key1422, -6), (key1453, 2), (key1389, 2), (key1453, 2), (key1571, 6), (key1786, -2), (key1294, -2), (key1786, -2), (key1653, -2), (key1544, -2), (key1653, -2), (key1811, 2), (key1314, 2), (key1811, 2)]

def rawRow4850 : Integer.Sparse Key := [(key1422, -6), (key1453, 2), (key1453, 2), (key1389, 2), (key1571, 6), (key1786, -2), (key1786, -2), (key1294, -2), (key1653, -2), (key1653, -2), (key1544, -2), (key1811, 2), (key1811, 2), (key1314, 2)]

def rawRow4851 : Integer.Sparse Key := [(key1571, -6), (key1544, 2), (key1653, 2), (key1653, 2), (key1422, 6), (key1314, -2), (key1811, -2), (key1811, -2), (key1389, -2), (key1453, -2), (key1453, -2), (key1294, 2), (key1786, 2), (key1786, 2)]

def rawRow4852 : Integer.Sparse Key := [(key1571, -6), (key1653, 2), (key1544, 2), (key1653, 2), (key1422, 6), (key1811, -2), (key1314, -2), (key1811, -2), (key1453, -2), (key1389, -2), (key1453, -2), (key1786, 2), (key1294, 2), (key1786, 2)]

def rawRow4853 : Integer.Sparse Key := [(key1571, -6), (key1653, 2), (key1653, 2), (key1544, 2), (key1422, 6), (key1811, -2), (key1811, -2), (key1314, -2), (key1453, -2), (key1453, -2), (key1389, -2), (key1786, 2), (key1786, 2), (key1294, 2)]

def rawRow4854 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2644, 1), (key2644, 1), (key2671, 2), (key2671, 2), (key2676, 2), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2732, -1), (key2732, -1), (key2786, -1), (key2786, -1), (key2794, -1), (key2794, -1), (key2798, -1), (key2798, -1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2835, 1), (key2835, 1)]

def rawRow4855 : Integer.Sparse Key := [(key2612, -2), (key2618, -2), (key2616, -2), (key2640, 1), (key2644, 1), (key2632, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2671, 2), (key2676, 2), (key2671, 2), (key2726, -1), (key2732, -1), (key2706, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2794, -1), (key2798, -1), (key2786, -1), (key2798, -1), (key2786, -1), (key2794, -1), (key2829, 1), (key2835, 1), (key2809, 1), (key2835, 1), (key2809, 1), (key2829, 1)]

def rawRow4856 : Integer.Sparse Key := [(key2618, -2), (key2612, -2), (key2616, -2), (key2644, 1), (key2640, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2676, 2), (key2671, 2), (key2671, 2), (key2732, -1), (key2726, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2798, -1), (key2794, -1), (key2798, -1), (key2786, -1), (key2794, -1), (key2786, -1), (key2835, 1), (key2829, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2809, 1)]

def rawRow4857 : Integer.Sparse Key := [(key2667, -2), (key2667, -2), (key2673, -2), (key2702, 1), (key2702, 1), (key2735, 1), (key2735, 1), (key2737, 1), (key2737, 1), (key2612, 2), (key2616, 2), (key2621, 2), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2835, -1), (key2835, -1), (key2632, -1), (key2632, -1), (key2640, -1), (key2640, -1), (key2644, -1), (key2644, -1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1)]

def rawRow4858 : Integer.Sparse Key := [(key2667, -2), (key2673, -2), (key2667, -2), (key2735, 1), (key2737, 1), (key2702, 1), (key2737, 1), (key2702, 1), (key2735, 1), (key2612, 2), (key2618, 2), (key2616, 2), (key2829, -1), (key2835, -1), (key2809, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key2640, -1), (key2644, -1), (key2632, -1), (key2644, -1), (key2632, -1), (key2640, -1), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1)]

def rawRow4859 : Integer.Sparse Key := [(key2673, -2), (key2667, -2), (key2667, -2), (key2737, 1), (key2735, 1), (key2737, 1), (key2702, 1), (key2735, 1), (key2702, 1), (key2618, 2), (key2612, 2), (key2616, 2), (key2835, -1), (key2829, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key2644, -1), (key2640, -1), (key2644, -1), (key2632, -1), (key2640, -1), (key2632, -1), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1)]

def rawRow4860 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2667, 1), (key2667, 1), (key2735, 1), (key2735, 1), (key2747, 1), (key2747, 1), (key2805, 2), (key2805, 2), (key2831, 2), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key3023, -1), (key3023, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1)]

def rawRow4861 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2735, 1), (key2747, 1), (key2667, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2805, 2), (key2831, 2), (key2805, 2), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1)]

def rawRow4862 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2747, 1), (key2735, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2667, 1), (key2831, 2), (key2805, 2), (key2805, 2), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3023, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1)]

def rawRow4863 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2782, 1), (key2782, 1), (key2893, 1), (key2893, 1), (key2904, 1), (key2904, 1), (key2702, 2), (key2702, 2), (key2728, 2), (key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4864 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2893, 1), (key2904, 1), (key2782, 1), (key2904, 1), (key2782, 1), (key2893, 1), (key2702, 2), (key2728, 2), (key2702, 2), (key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1)]

def rawRow4865 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2904, 1), (key2893, 1), (key2904, 1), (key2782, 1), (key2893, 1), (key2782, 1), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1)]

def rawRow4866 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1006, -2), (key1019, 6), (key1033, 2), (key1033, 2), (key1041, 2), (key1127, -2), (key1199, -2), (key1199, -2), (key1076, -6), (key1155, 2), (key1212, 2), (key1212, 2)]

def rawRow4867 : Integer.Sparse Key := [(key998, -2), (key1006, -2), (key998, -2), (key1019, 6), (key1033, 2), (key1041, 2), (key1033, 2), (key1199, -2), (key1127, -2), (key1199, -2), (key1076, -6), (key1212, 2), (key1155, 2), (key1212, 2)]

def rawRow4868 : Integer.Sparse Key := [(key1006, -2), (key998, -2), (key998, -2), (key1019, 6), (key1041, 2), (key1033, 2), (key1033, 2), (key1199, -2), (key1199, -2), (key1127, -2), (key1076, -6), (key1212, 2), (key1212, 2), (key1155, 2)]

def rawRow4869 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1041, -2), (key1076, 6), (key998, 2), (key998, 2), (key1006, 2), (key1155, -2), (key1212, -2), (key1212, -2), (key1019, -6), (key1127, 2), (key1199, 2), (key1199, 2)]

def rawRow4870 : Integer.Sparse Key := [(key1033, -2), (key1041, -2), (key1033, -2), (key1076, 6), (key998, 2), (key1006, 2), (key998, 2), (key1212, -2), (key1155, -2), (key1212, -2), (key1019, -6), (key1199, 2), (key1127, 2), (key1199, 2)]

def rawRow4871 : Integer.Sparse Key := [(key1041, -2), (key1033, -2), (key1033, -2), (key1076, 6), (key1006, 2), (key998, 2), (key998, 2), (key1212, -2), (key1212, -2), (key1155, -2), (key1019, -6), (key1199, 2), (key1199, 2), (key1127, 2)]

def rawRow4872 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1076, -2), (key1041, 6), (key1111, 2), (key1111, 2), (key1155, 2), (key1006, -2), (key1193, -2), (key1193, -2), (key1127, -6), (key1019, 2), (key1199, 2), (key1199, 2)]

def rawRow4873 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1033, -2), (key1041, 6), (key1111, 2), (key1155, 2), (key1111, 2), (key1193, -2), (key1006, -2), (key1193, -2), (key1127, -6), (key1199, 2), (key1019, 2), (key1199, 2)]

def rawRow4874 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1033, -2), (key1041, 6), (key1155, 2), (key1111, 2), (key1111, 2), (key1193, -2), (key1193, -2), (key1006, -2), (key1127, -6), (key1199, 2), (key1199, 2), (key1019, 2)]

def rawRow4875 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1155, -2), (key1127, 6), (key1033, 2), (key1033, 2), (key1076, 2), (key1019, -2), (key1199, -2), (key1199, -2), (key1041, -6), (key1006, 2), (key1193, 2), (key1193, 2)]

def rawRow4876 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1111, -2), (key1127, 6), (key1033, 2), (key1076, 2), (key1033, 2), (key1199, -2), (key1019, -2), (key1199, -2), (key1041, -6), (key1193, 2), (key1006, 2), (key1193, 2)]

def rawRow4877 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1111, -2), (key1127, 6), (key1076, 2), (key1033, 2), (key1033, 2), (key1199, -2), (key1199, -2), (key1019, -2), (key1041, -6), (key1193, 2), (key1193, 2), (key1006, 2)]

def rawRow4878 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 2), (key2639, 2), (key2670, 6), (key2705, -2), (key2725, -2), (key2725, -2), (key2785, -2), (key2793, -2), (key2793, -2), (key2808, 2), (key2828, 2), (key2828, 2)]

def rawRow4879 : Integer.Sparse Key := [(key2615, -6), (key2639, 2), (key2631, 2), (key2639, 2), (key2670, 6), (key2725, -2), (key2705, -2), (key2725, -2), (key2793, -2), (key2785, -2), (key2793, -2), (key2828, 2), (key2808, 2), (key2828, 2)]

def rawRow4880 : Integer.Sparse Key := [(key2615, -6), (key2639, 2), (key2639, 2), (key2631, 2), (key2670, 6), (key2725, -2), (key2725, -2), (key2705, -2), (key2793, -2), (key2793, -2), (key2785, -2), (key2828, 2), (key2828, 2), (key2808, 2)]

def rawRow4881 : Integer.Sparse Key := [(key2670, -6), (key2785, 2), (key2793, 2), (key2793, 2), (key2615, 6), (key2808, -2), (key2828, -2), (key2828, -2), (key2631, -2), (key2639, -2), (key2639, -2), (key2705, 2), (key2725, 2), (key2725, 2)]

def rawRow4882 : Integer.Sparse Key := [(key2670, -6), (key2793, 2), (key2785, 2), (key2793, 2), (key2615, 6), (key2828, -2), (key2808, -2), (key2828, -2), (key2639, -2), (key2631, -2), (key2639, -2), (key2725, 2), (key2705, 2), (key2725, 2)]

def rawRow4883 : Integer.Sparse Key := [(key2670, -6), (key2793, 2), (key2793, 2), (key2785, 2), (key2615, 6), (key2828, -2), (key2828, -2), (key2808, -2), (key2639, -2), (key2639, -2), (key2631, -2), (key2725, 2), (key2725, 2), (key2705, 2)]

def rawRow4884 : Integer.Sparse Key := [(key2785, -6), (key2670, 2), (key2793, 2), (key2793, 2), (key2808, 6), (key2615, -2), (key2828, -2), (key2828, -2), (key2705, -2), (key2859, -2), (key2859, -2), (key2631, 2), (key2869, 2), (key2869, 2)]

def rawRow4885 : Integer.Sparse Key := [(key2785, -6), (key2793, 2), (key2670, 2), (key2793, 2), (key2808, 6), (key2828, -2), (key2615, -2), (key2828, -2), (key2859, -2), (key2705, -2), (key2859, -2), (key2869, 2), (key2631, 2), (key2869, 2)]

def rawRow4886 : Integer.Sparse Key := [(key2785, -6), (key2793, 2), (key2793, 2), (key2670, 2), (key2808, 6), (key2828, -2), (key2828, -2), (key2615, -2), (key2859, -2), (key2859, -2), (key2705, -2), (key2869, 2), (key2869, 2), (key2631, 2)]

def rawRow4887 : Integer.Sparse Key := [(key2808, -6), (key2705, 2), (key2859, 2), (key2859, 2), (key2785, 6), (key2631, -2), (key2869, -2), (key2869, -2), (key2670, -2), (key2793, -2), (key2793, -2), (key2615, 2), (key2828, 2), (key2828, 2)]

def rawRow4888 : Integer.Sparse Key := [(key2808, -6), (key2859, 2), (key2705, 2), (key2859, 2), (key2785, 6), (key2869, -2), (key2631, -2), (key2869, -2), (key2793, -2), (key2670, -2), (key2793, -2), (key2828, 2), (key2615, 2), (key2828, 2)]

def rawRow4889 : Integer.Sparse Key := [(key2808, -6), (key2859, 2), (key2859, 2), (key2705, 2), (key2785, 6), (key2869, -2), (key2869, -2), (key2631, -2), (key2793, -2), (key2793, -2), (key2670, -2), (key2828, 2), (key2828, 2), (key2615, 2)]

def rawRow4890 : Integer.Sparse Key := [(key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1775, -1), (key1775, -1), (key1560, 2), (key1781, 2), (key1781, 2), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1791, 1), (key1791, 1), (key1660, -1), (key1660, -1), (key1818, -1), (key1818, -1), (key1842, -1), (key1842, -1), (key1597, -2), (key1799, -2), (key1799, -2), (key1668, 1), (key1668, 1), (key1826, 1), (key1826, 1), (key1845, 1), (key1845, 1)]

def rawRow4891 : Integer.Sparse Key := [(key1772, -1), (key1775, -1), (key1546, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1781, 2), (key1560, 2), (key1781, 2), (key1788, 1), (key1791, 1), (key1573, 1), (key1791, 1), (key1573, 1), (key1788, 1), (key1818, -1), (key1842, -1), (key1660, -1), (key1842, -1), (key1660, -1), (key1818, -1), (key1799, -2), (key1597, -2), (key1799, -2), (key1826, 1), (key1845, 1), (key1668, 1), (key1845, 1), (key1668, 1), (key1826, 1)]

def rawRow4892 : Integer.Sparse Key := [(key1775, -1), (key1772, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1546, -1), (key1781, 2), (key1781, 2), (key1560, 2), (key1791, 1), (key1788, 1), (key1791, 1), (key1573, 1), (key1788, 1), (key1573, 1), (key1842, -1), (key1818, -1), (key1842, -1), (key1660, -1), (key1818, -1), (key1660, -1), (key1799, -2), (key1799, -2), (key1597, -2), (key1845, 1), (key1826, 1), (key1845, 1), (key1668, 1), (key1826, 1), (key1668, 1)]

def rawRow4893 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1791, -1), (key1791, -1), (key1597, 2), (key1799, 2), (key1799, 2), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1775, 1), (key1775, 1), (key1668, -1), (key1668, -1), (key1826, -1), (key1826, -1), (key1845, -1), (key1845, -1), (key1560, -2), (key1781, -2), (key1781, -2), (key1660, 1), (key1660, 1), (key1818, 1), (key1818, 1), (key1842, 1), (key1842, 1)]

def rawRow4894 : Integer.Sparse Key := [(key1788, -1), (key1791, -1), (key1573, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1799, 2), (key1597, 2), (key1799, 2), (key1772, 1), (key1775, 1), (key1546, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1826, -1), (key1845, -1), (key1668, -1), (key1845, -1), (key1668, -1), (key1826, -1), (key1781, -2), (key1560, -2), (key1781, -2), (key1818, 1), (key1842, 1), (key1660, 1), (key1842, 1), (key1660, 1), (key1818, 1)]

def rawRow4895 : Integer.Sparse Key := [(key1791, -1), (key1788, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1573, -1), (key1799, 2), (key1799, 2), (key1597, 2), (key1775, 1), (key1772, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1546, 1), (key1845, -1), (key1826, -1), (key1845, -1), (key1668, -1), (key1826, -1), (key1668, -1), (key1781, -2), (key1781, -2), (key1560, -2), (key1842, 1), (key1818, 1), (key1842, 1), (key1660, 1), (key1818, 1), (key1660, 1)]

def rawRow4896 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1788, -1), (key1788, -1), (key1799, -1), (key1799, -1), (key1303, 2), (key1791, 2), (key1791, 2), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1826, 1), (key1826, 1), (key1340, -1), (key1340, -1), (key1775, -1), (key1775, -1), (key1840, -1), (key1840, -1), (key1330, -2), (key1818, -2), (key1818, -2), (key1346, 1), (key1346, 1), (key1781, 1), (key1781, 1), (key1842, 1), (key1842, 1)]

def rawRow4897 : Integer.Sparse Key := [(key1788, -1), (key1799, -1), (key1296, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1791, 2), (key1303, 2), (key1791, 2), (key1813, 1), (key1826, 1), (key1316, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1775, -1), (key1840, -1), (key1340, -1), (key1840, -1), (key1340, -1), (key1775, -1), (key1818, -2), (key1330, -2), (key1818, -2), (key1781, 1), (key1842, 1), (key1346, 1), (key1842, 1), (key1346, 1), (key1781, 1)]

def rawRow4898 : Integer.Sparse Key := [(key1799, -1), (key1788, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1791, 2), (key1791, 2), (key1303, 2), (key1826, 1), (key1813, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1840, -1), (key1775, -1), (key1840, -1), (key1340, -1), (key1775, -1), (key1340, -1), (key1818, -2), (key1818, -2), (key1330, -2), (key1842, 1), (key1781, 1), (key1842, 1), (key1346, 1), (key1781, 1), (key1346, 1)]

def rawRow4899 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1813, -1), (key1813, -1), (key1826, -1), (key1826, -1), (key1330, 2), (key1818, 2), (key1818, 2), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1799, 1), (key1799, 1), (key1346, -1), (key1346, -1), (key1781, -1), (key1781, -1), (key1842, -1), (key1842, -1), (key1303, -2), (key1791, -2), (key1791, -2), (key1340, 1), (key1340, 1), (key1775, 1), (key1775, 1), (key1840, 1), (key1840, 1)]

def rawRow4900 : Integer.Sparse Key := [(key1813, -1), (key1826, -1), (key1316, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1818, 2), (key1330, 2), (key1818, 2), (key1788, 1), (key1799, 1), (key1296, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1781, -1), (key1842, -1), (key1346, -1), (key1842, -1), (key1346, -1), (key1781, -1), (key1791, -2), (key1303, -2), (key1791, -2), (key1775, 1), (key1840, 1), (key1340, 1), (key1840, 1), (key1340, 1), (key1775, 1)]

def rawRow4901 : Integer.Sparse Key := [(key1826, -1), (key1813, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1818, 2), (key1818, 2), (key1330, 2), (key1799, 1), (key1788, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1842, -1), (key1781, -1), (key1842, -1), (key1346, -1), (key1781, -1), (key1346, -1), (key1791, -2), (key1791, -2), (key1303, -2), (key1840, 1), (key1775, 1), (key1840, 1), (key1340, 1), (key1775, 1), (key1340, 1)]

def rawRow4902 : Integer.Sparse Key := [(key2719, -2), (key2719, -2), (key2733, -2), (key2756, 2), (key2756, 2), (key2759, 2), (key2822, 2), (key2822, 2), (key2836, 2), (key2924, -6), (key3015, -2), (key3015, -2), (key3018, -2), (key3027, 6)]

def rawRow4903 : Integer.Sparse Key := [(key2719, -2), (key2733, -2), (key2719, -2), (key2756, 2), (key2759, 2), (key2756, 2), (key2822, 2), (key2836, 2), (key2822, 2), (key2924, -6), (key3015, -2), (key3018, -2), (key3015, -2), (key3027, 6)]

def rawRow4904 : Integer.Sparse Key := [(key2733, -2), (key2719, -2), (key2719, -2), (key2759, 2), (key2756, 2), (key2756, 2), (key2836, 2), (key2822, 2), (key2822, 2), (key2924, -6), (key3018, -2), (key3015, -2), (key3015, -2), (key3027, 6)]

def rawRow4905 : Integer.Sparse Key := [(key2822, -2), (key2822, -2), (key2836, -2), (key3015, 2), (key3015, 2), (key3018, 2), (key2719, 2), (key2719, 2), (key2733, 2), (key3027, -6), (key2756, -2), (key2756, -2), (key2759, -2), (key2924, 6)]

def rawRow4906 : Integer.Sparse Key := [(key2822, -2), (key2836, -2), (key2822, -2), (key3015, 2), (key3018, 2), (key3015, 2), (key2719, 2), (key2733, 2), (key2719, 2), (key3027, -6), (key2756, -2), (key2759, -2), (key2756, -2), (key2924, 6)]

def rawRow4907 : Integer.Sparse Key := [(key2836, -2), (key2822, -2), (key2822, -2), (key3018, 2), (key3015, 2), (key3015, 2), (key2733, 2), (key2719, 2), (key2719, 2), (key3027, -6), (key2759, -2), (key2756, -2), (key2756, -2), (key2924, 6)]

def rawRow4908 : Integer.Sparse Key := [(key2693, -2), (key2693, -2), (key3018, -2), (key2695, 2), (key2695, 2), (key2836, 2), (key2719, 2), (key2719, 2), (key3027, 2), (key2733, -6), (key2756, -2), (key2756, -2), (key2924, -2), (key2759, 6)]

def rawRow4909 : Integer.Sparse Key := [(key3055, -2), (key3117, -2), (key2693, -2), (key2695, 2), (key2836, 2), (key2695, 2), (key2719, 2), (key3027, 2), (key2719, 2), (key2733, -6), (key2756, -2), (key2924, -2), (key2756, -2), (key2759, 6)]

def rawRow4910 : Integer.Sparse Key := [(key3117, -2), (key3055, -2), (key2693, -2), (key2836, 2), (key2695, 2), (key2695, 2), (key3027, 2), (key2719, 2), (key2719, 2), (key2733, -6), (key2924, -2), (key2756, -2), (key2756, -2), (key2759, 6)]

def rawRow4911 : Integer.Sparse Key := [(key3070, -2), (key3070, -2), (key3147, -2), (key3074, 2), (key3074, 2), (key3146, 2), (key2693, 2), (key2693, 2), (key3018, 2), (key2759, -6), (key2695, -2), (key2695, -2), (key2836, -2), (key2733, 6)]

def rawRow4912 : Integer.Sparse Key := [(key3070, -2), (key3147, -2), (key3070, -2), (key3074, 2), (key3146, 2), (key3074, 2), (key3055, 2), (key3117, 2), (key2693, 2), (key2759, -6), (key2695, -2), (key2836, -2), (key2695, -2), (key2733, 6)]

def rawRow4913 : Integer.Sparse Key := [(key3147, -2), (key3070, -2), (key3070, -2), (key3146, 2), (key3074, 2), (key3074, 2), (key3117, 2), (key3055, 2), (key2693, 2), (key2759, -6), (key2836, -2), (key2695, -2), (key2695, -2), (key2733, 6)]

def rawRow4914 : Integer.Sparse Key := [(key1296, -2), (key1296, -2), (key1303, -2), (key1316, 1), (key1316, 1), (key1337, 1), (key1337, 1), (key1340, 1), (key1340, 1), (key1391, 2), (key1391, 2), (key1398, 2), (key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1775, -1), (key1775, -1), (key1424, -1), (key1424, -1), (key1455, -1), (key1455, -1), (key1458, -1), (key1458, -1), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1791, 1), (key1791, 1)]

def rawRow4915 : Integer.Sparse Key := [(key1296, -2), (key1303, -2), (key1296, -2), (key1337, 1), (key1340, 1), (key1316, 1), (key1340, 1), (key1316, 1), (key1337, 1), (key1391, 2), (key1398, 2), (key1391, 2), (key1772, -1), (key1775, -1), (key1546, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1455, -1), (key1458, -1), (key1424, -1), (key1458, -1), (key1424, -1), (key1455, -1), (key1788, 1), (key1791, 1), (key1573, 1), (key1791, 1), (key1573, 1), (key1788, 1)]

def rawRow4916 : Integer.Sparse Key := [(key1303, -2), (key1296, -2), (key1296, -2), (key1340, 1), (key1337, 1), (key1340, 1), (key1316, 1), (key1337, 1), (key1316, 1), (key1398, 2), (key1391, 2), (key1391, 2), (key1775, -1), (key1772, -1), (key1775, -1), (key1546, -1), (key1772, -1), (key1546, -1), (key1458, -1), (key1455, -1), (key1458, -1), (key1424, -1), (key1455, -1), (key1424, -1), (key1791, 1), (key1788, 1), (key1791, 1), (key1573, 1), (key1788, 1), (key1573, 1)]

def rawRow4917 : Integer.Sparse Key := [(key1391, -2), (key1391, -2), (key1398, -2), (key1424, 1), (key1424, 1), (key1455, 1), (key1455, 1), (key1458, 1), (key1458, 1), (key1296, 2), (key1296, 2), (key1303, 2), (key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1791, -1), (key1791, -1), (key1316, -1), (key1316, -1), (key1337, -1), (key1337, -1), (key1340, -1), (key1340, -1), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1775, 1), (key1775, 1)]

def rawRow4918 : Integer.Sparse Key := [(key1391, -2), (key1398, -2), (key1391, -2), (key1455, 1), (key1458, 1), (key1424, 1), (key1458, 1), (key1424, 1), (key1455, 1), (key1296, 2), (key1303, 2), (key1296, 2), (key1788, -1), (key1791, -1), (key1573, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1337, -1), (key1340, -1), (key1316, -1), (key1340, -1), (key1316, -1), (key1337, -1), (key1772, 1), (key1775, 1), (key1546, 1), (key1775, 1), (key1546, 1), (key1772, 1)]

def rawRow4919 : Integer.Sparse Key := [(key1398, -2), (key1391, -2), (key1391, -2), (key1458, 1), (key1455, 1), (key1458, 1), (key1424, 1), (key1455, 1), (key1424, 1), (key1303, 2), (key1296, 2), (key1296, 2), (key1791, -1), (key1788, -1), (key1791, -1), (key1573, -1), (key1788, -1), (key1573, -1), (key1340, -1), (key1337, -1), (key1340, -1), (key1316, -1), (key1337, -1), (key1316, -1), (key1775, 1), (key1772, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1546, 1)]

def rawRow4920 : Integer.Sparse Key := [(key1424, -2), (key1424, -2), (key1448, -2), (key1391, 1), (key1391, 1), (key1455, 1), (key1455, 1), (key1467, 1), (key1467, 1), (key1573, 2), (key1573, 2), (key1597, 2), (key1296, -1), (key1296, -1), (key1788, -1), (key1788, -1), (key1799, -1), (key1799, -1), (key1546, -1), (key1546, -1), (key1655, -1), (key1655, -1), (key1668, -1), (key1668, -1), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1826, 1), (key1826, 1)]

def rawRow4921 : Integer.Sparse Key := [(key1424, -2), (key1448, -2), (key1424, -2), (key1455, 1), (key1467, 1), (key1391, 1), (key1467, 1), (key1391, 1), (key1455, 1), (key1573, 2), (key1597, 2), (key1573, 2), (key1788, -1), (key1799, -1), (key1296, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1655, -1), (key1668, -1), (key1546, -1), (key1668, -1), (key1546, -1), (key1655, -1), (key1813, 1), (key1826, 1), (key1316, 1), (key1826, 1), (key1316, 1), (key1813, 1)]

def rawRow4922 : Integer.Sparse Key := [(key1448, -2), (key1424, -2), (key1424, -2), (key1467, 1), (key1455, 1), (key1467, 1), (key1391, 1), (key1455, 1), (key1391, 1), (key1597, 2), (key1573, 2), (key1573, 2), (key1799, -1), (key1788, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1668, -1), (key1655, -1), (key1668, -1), (key1546, -1), (key1655, -1), (key1546, -1), (key1826, 1), (key1813, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1316, 1)]

def rawRow4923 : Integer.Sparse Key := [(key1573, -2), (key1573, -2), (key1597, -2), (key1546, 1), (key1546, 1), (key1655, 1), (key1655, 1), (key1668, 1), (key1668, 1), (key1424, 2), (key1424, 2), (key1448, 2), (key1316, -1), (key1316, -1), (key1813, -1), (key1813, -1), (key1826, -1), (key1826, -1), (key1391, -1), (key1391, -1), (key1455, -1), (key1455, -1), (key1467, -1), (key1467, -1), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1799, 1), (key1799, 1)]

def rawRow4924 : Integer.Sparse Key := [(key1573, -2), (key1597, -2), (key1573, -2), (key1655, 1), (key1668, 1), (key1546, 1), (key1668, 1), (key1546, 1), (key1655, 1), (key1424, 2), (key1448, 2), (key1424, 2), (key1813, -1), (key1826, -1), (key1316, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1455, -1), (key1467, -1), (key1391, -1), (key1467, -1), (key1391, -1), (key1455, -1), (key1788, 1), (key1799, 1), (key1296, 1), (key1799, 1), (key1296, 1), (key1788, 1)]

def rawRow4925 : Integer.Sparse Key := [(key1597, -2), (key1573, -2), (key1573, -2), (key1668, 1), (key1655, 1), (key1668, 1), (key1546, 1), (key1655, 1), (key1546, 1), (key1448, 2), (key1424, 2), (key1424, 2), (key1826, -1), (key1813, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1467, -1), (key1455, -1), (key1467, -1), (key1391, -1), (key1455, -1), (key1391, -1), (key1799, 1), (key1788, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1296, 1)]

def rawRow4926 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1005, -2), (key1018, 6), (key1033, 2), (key1033, 2), (key1040, 2), (key1126, -2), (key1198, -2), (key1198, -2), (key1075, -6), (key1154, 2), (key1211, 2), (key1211, 2)]

def rawRow4927 : Integer.Sparse Key := [(key998, -2), (key1005, -2), (key998, -2), (key1018, 6), (key1033, 2), (key1040, 2), (key1033, 2), (key1198, -2), (key1126, -2), (key1198, -2), (key1075, -6), (key1211, 2), (key1154, 2), (key1211, 2)]

def rawRow4928 : Integer.Sparse Key := [(key1005, -2), (key998, -2), (key998, -2), (key1018, 6), (key1040, 2), (key1033, 2), (key1033, 2), (key1198, -2), (key1198, -2), (key1126, -2), (key1075, -6), (key1211, 2), (key1211, 2), (key1154, 2)]

def rawRow4929 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1040, -2), (key1075, 6), (key998, 2), (key998, 2), (key1005, 2), (key1154, -2), (key1211, -2), (key1211, -2), (key1018, -6), (key1126, 2), (key1198, 2), (key1198, 2)]

def rawRow4930 : Integer.Sparse Key := [(key1033, -2), (key1040, -2), (key1033, -2), (key1075, 6), (key998, 2), (key1005, 2), (key998, 2), (key1211, -2), (key1154, -2), (key1211, -2), (key1018, -6), (key1198, 2), (key1126, 2), (key1198, 2)]

def rawRow4931 : Integer.Sparse Key := [(key1040, -2), (key1033, -2), (key1033, -2), (key1075, 6), (key1005, 2), (key998, 2), (key998, 2), (key1211, -2), (key1211, -2), (key1154, -2), (key1018, -6), (key1198, 2), (key1198, 2), (key1126, 2)]

def rawRow4932 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1075, -2), (key1040, 6), (key1111, 2), (key1111, 2), (key1154, 2), (key1005, -2), (key1192, -2), (key1192, -2), (key1126, -6), (key1018, 2), (key1198, 2), (key1198, 2)]

def rawRow4933 : Integer.Sparse Key := [(key1033, -2), (key1075, -2), (key1033, -2), (key1040, 6), (key1111, 2), (key1154, 2), (key1111, 2), (key1192, -2), (key1005, -2), (key1192, -2), (key1126, -6), (key1198, 2), (key1018, 2), (key1198, 2)]

def rawRow4934 : Integer.Sparse Key := [(key1075, -2), (key1033, -2), (key1033, -2), (key1040, 6), (key1154, 2), (key1111, 2), (key1111, 2), (key1192, -2), (key1192, -2), (key1005, -2), (key1126, -6), (key1198, 2), (key1198, 2), (key1018, 2)]

def rawRow4935 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1154, -2), (key1126, 6), (key1033, 2), (key1033, 2), (key1075, 2), (key1018, -2), (key1198, -2), (key1198, -2), (key1040, -6), (key1005, 2), (key1192, 2), (key1192, 2)]

def rawRow4936 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1111, -2), (key1126, 6), (key1033, 2), (key1075, 2), (key1033, 2), (key1198, -2), (key1018, -2), (key1198, -2), (key1040, -6), (key1192, 2), (key1005, 2), (key1192, 2)]

def rawRow4937 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1111, -2), (key1126, 6), (key1075, 2), (key1033, 2), (key1033, 2), (key1198, -2), (key1198, -2), (key1018, -2), (key1040, -6), (key1192, 2), (key1192, 2), (key1005, 2)]

def rawRow4938 : Integer.Sparse Key := [(key2633, -2), (key2643, -2), (key2643, -2), (key2650, 1), (key2650, 1), (key2655, 1), (key2655, 1), (key2656, 1), (key2656, 1), (key2787, 2), (key2797, 2), (key2797, 2), (key2899, -1), (key2899, -1), (key2906, -1), (key2906, -1), (key2915, -1), (key2915, -1), (key2940, -1), (key2940, -1), (key2945, -1), (key2945, -1), (key2946, -1), (key2946, -1), (key2978, 1), (key2978, 1), (key2985, 1), (key2985, 1), (key2994, 1), (key2994, 1)]

def rawRow4939 : Integer.Sparse Key := [(key2643, -2), (key2633, -2), (key2643, -2), (key2655, 1), (key2656, 1), (key2650, 1), (key2656, 1), (key2650, 1), (key2655, 1), (key2797, 2), (key2787, 2), (key2797, 2), (key2906, -1), (key2915, -1), (key2899, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2945, -1), (key2946, -1), (key2940, -1), (key2946, -1), (key2940, -1), (key2945, -1), (key2985, 1), (key2994, 1), (key2978, 1), (key2994, 1), (key2978, 1), (key2985, 1)]

def rawRow4940 : Integer.Sparse Key := [(key2643, -2), (key2643, -2), (key2633, -2), (key2656, 1), (key2655, 1), (key2656, 1), (key2650, 1), (key2655, 1), (key2650, 1), (key2797, 2), (key2797, 2), (key2787, 2), (key2915, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2899, -1), (key2946, -1), (key2945, -1), (key2946, -1), (key2940, -1), (key2945, -1), (key2940, -1), (key2994, 1), (key2985, 1), (key2994, 1), (key2978, 1), (key2985, 1), (key2978, 1)]

def rawRow4941 : Integer.Sparse Key := [(key2707, -2), (key2739, -2), (key2739, -2), (key2730, 1), (key2730, 1), (key2749, 1), (key2749, 1), (key2751, 1), (key2751, 1), (key2633, 2), (key2643, 2), (key2643, 2), (key2978, -1), (key2978, -1), (key2985, -1), (key2985, -1), (key2994, -1), (key2994, -1), (key2650, -1), (key2650, -1), (key2655, -1), (key2655, -1), (key2656, -1), (key2656, -1), (key2899, 1), (key2899, 1), (key2906, 1), (key2906, 1), (key2915, 1), (key2915, 1)]

def rawRow4942 : Integer.Sparse Key := [(key2739, -2), (key2707, -2), (key2739, -2), (key2749, 1), (key2751, 1), (key2730, 1), (key2751, 1), (key2730, 1), (key2749, 1), (key2643, 2), (key2633, 2), (key2643, 2), (key2985, -1), (key2994, -1), (key2978, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2655, -1), (key2656, -1), (key2650, -1), (key2656, -1), (key2650, -1), (key2655, -1), (key2906, 1), (key2915, 1), (key2899, 1), (key2915, 1), (key2899, 1), (key2906, 1)]

def rawRow4943 : Integer.Sparse Key := [(key2739, -2), (key2739, -2), (key2707, -2), (key2751, 1), (key2749, 1), (key2751, 1), (key2730, 1), (key2749, 1), (key2730, 1), (key2643, 2), (key2643, 2), (key2633, 2), (key2994, -1), (key2985, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2978, -1), (key2656, -1), (key2655, -1), (key2656, -1), (key2650, -1), (key2655, -1), (key2650, -1), (key2915, 1), (key2906, 1), (key2915, 1), (key2899, 1), (key2906, 1), (key2899, 1)]

def rawRow4944 : Integer.Sparse Key := [(key2672, -2), (key2749, -2), (key2749, -2), (key2675, 1), (key2675, 1), (key2739, 1), (key2739, 1), (key2751, 1), (key2751, 1), (key2707, 2), (key2978, 2), (key2978, 2), (key2643, -1), (key2643, -1), (key2730, -1), (key2730, -1), (key2994, -1), (key2994, -1), (key2739, -1), (key2739, -1), (key2899, -1), (key2899, -1), (key2999, -1), (key2999, -1), (key2655, 1), (key2655, 1), (key2749, 1), (key2749, 1), (key3004, 1), (key3004, 1)]

def rawRow4945 : Integer.Sparse Key := [(key2749, -2), (key2672, -2), (key2749, -2), (key2739, 1), (key2751, 1), (key2675, 1), (key2751, 1), (key2675, 1), (key2739, 1), (key2978, 2), (key2707, 2), (key2978, 2), (key2730, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2899, -1), (key2999, -1), (key2739, -1), (key2999, -1), (key2739, -1), (key2899, -1), (key2749, 1), (key3004, 1), (key2655, 1), (key3004, 1), (key2655, 1), (key2749, 1)]

def rawRow4946 : Integer.Sparse Key := [(key2749, -2), (key2749, -2), (key2672, -2), (key2751, 1), (key2739, 1), (key2751, 1), (key2675, 1), (key2739, 1), (key2675, 1), (key2978, 2), (key2978, 2), (key2707, 2), (key2994, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2643, -1), (key2999, -1), (key2899, -1), (key2999, -1), (key2739, -1), (key2899, -1), (key2739, -1), (key3004, 1), (key2749, 1), (key3004, 1), (key2655, 1), (key2749, 1), (key2655, 1)]

def rawRow4947 : Integer.Sparse Key := [(key2787, -2), (key2906, -2), (key2906, -2), (key2797, 1), (key2797, 1), (key2899, 1), (key2899, 1), (key2915, 1), (key2915, 1), (key2672, 2), (key2749, 2), (key2749, 2), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, -1), (key3004, -1), (key2675, -1), (key2675, -1), (key2797, -1), (key2797, -1), (key2946, -1), (key2946, -1), (key2643, 1), (key2643, 1), (key2730, 1), (key2730, 1), (key2994, 1), (key2994, 1)]

def rawRow4948 : Integer.Sparse Key := [(key2906, -2), (key2787, -2), (key2906, -2), (key2899, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, 1), (key2899, 1), (key2749, 2), (key2672, 2), (key2749, 2), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2797, -1), (key2946, -1), (key2675, -1), (key2946, -1), (key2675, -1), (key2797, -1), (key2730, 1), (key2994, 1), (key2643, 1), (key2994, 1), (key2643, 1), (key2730, 1)]

def rawRow4949 : Integer.Sparse Key := [(key2906, -2), (key2906, -2), (key2787, -2), (key2915, 1), (key2899, 1), (key2915, 1), (key2797, 1), (key2899, 1), (key2797, 1), (key2749, 2), (key2749, 2), (key2672, 2), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2655, -1), (key2946, -1), (key2797, -1), (key2946, -1), (key2675, -1), (key2797, -1), (key2675, -1), (key2994, 1), (key2730, 1), (key2994, 1), (key2643, 1), (key2730, 1), (key2643, 1)]

def rawRow4950 : Integer.Sparse Key := [(key2374, -2), (key2374, -2), (key2380, -2), (key2391, 6), (key2770, 2), (key2770, 2), (key2775, 2), (key2917, -2), (key2926, -2), (key2926, -2), (key3006, -6), (key3020, 2), (key3029, 2), (key3029, 2)]

def rawRow4951 : Integer.Sparse Key := [(key2374, -2), (key2380, -2), (key2374, -2), (key2391, 6), (key2770, 2), (key2775, 2), (key2770, 2), (key2926, -2), (key2917, -2), (key2926, -2), (key3006, -6), (key3029, 2), (key3020, 2), (key3029, 2)]

def rawRow4952 : Integer.Sparse Key := [(key2380, -2), (key2374, -2), (key2374, -2), (key2391, 6), (key2775, 2), (key2770, 2), (key2770, 2), (key2926, -2), (key2926, -2), (key2917, -2), (key3006, -6), (key3029, 2), (key3029, 2), (key3020, 2)]

def rawRow4953 : Integer.Sparse Key := [(key2374, -2), (key2374, -2), (key2391, -2), (key2380, 6), (key2847, 2), (key2847, 2), (key2917, 2), (key2775, -2), (key2884, -2), (key2884, -2), (key3020, -6), (key3006, 2), (key3029, 2), (key3029, 2)]

def rawRow4954 : Integer.Sparse Key := [(key2374, -2), (key2391, -2), (key2374, -2), (key2380, 6), (key2847, 2), (key2917, 2), (key2847, 2), (key2884, -2), (key2775, -2), (key2884, -2), (key3020, -6), (key3029, 2), (key3006, 2), (key3029, 2)]

def rawRow4955 : Integer.Sparse Key := [(key2391, -2), (key2374, -2), (key2374, -2), (key2380, 6), (key2917, 2), (key2847, 2), (key2847, 2), (key2884, -2), (key2884, -2), (key2775, -2), (key3020, -6), (key3029, 2), (key3029, 2), (key3006, 2)]

def rawRow4956 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2408, -2), (key2439, 6), (key2591, 2), (key2591, 2), (key2596, 2), (key3020, -2), (key3029, -2), (key3029, -2), (key2605, -6), (key2917, 2), (key2926, 2), (key2926, 2)]

def rawRow4957 : Integer.Sparse Key := [(key2402, -2), (key2408, -2), (key2402, -2), (key2439, 6), (key2591, 2), (key2596, 2), (key2591, 2), (key3029, -2), (key3020, -2), (key3029, -2), (key2605, -6), (key2926, 2), (key2917, 2), (key2926, 2)]

def rawRow4958 : Integer.Sparse Key := [(key2408, -2), (key2402, -2), (key2402, -2), (key2439, 6), (key2596, 2), (key2591, 2), (key2591, 2), (key3029, -2), (key3029, -2), (key3020, -2), (key2605, -6), (key2926, 2), (key2926, 2), (key2917, 2)]

def rawRow4959 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2439, -2), (key2408, 6), (key2847, 2), (key2847, 2), (key3020, 2), (key2596, -2), (key2884, -2), (key2884, -2), (key2917, -6), (key2605, 2), (key2926, 2), (key2926, 2)]

def rawRow4960 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2402, -2), (key2408, 6), (key2847, 2), (key3020, 2), (key2847, 2), (key2884, -2), (key2596, -2), (key2884, -2), (key2917, -6), (key2926, 2), (key2605, 2), (key2926, 2)]

def rawRow4961 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2402, -2), (key2408, 6), (key3020, 2), (key2847, 2), (key2847, 2), (key2884, -2), (key2884, -2), (key2596, -2), (key2917, -6), (key2926, 2), (key2926, 2), (key2605, 2)]

def rawRow4962 : Integer.Sparse Key := [(key2468, -2), (key2468, -2), (key2481, -2), (key2505, 6), (key2374, 2), (key2374, 2), (key2391, 2), (key3006, -2), (key3029, -2), (key3029, -2), (key2596, -6), (key2775, 2), (key2884, 2), (key2884, 2)]

def rawRow4963 : Integer.Sparse Key := [(key2468, -2), (key2481, -2), (key2468, -2), (key2505, 6), (key2374, 2), (key2391, 2), (key2374, 2), (key3029, -2), (key3006, -2), (key3029, -2), (key2596, -6), (key2884, 2), (key2775, 2), (key2884, 2)]

def rawRow4964 : Integer.Sparse Key := [(key2481, -2), (key2468, -2), (key2468, -2), (key2505, 6), (key2391, 2), (key2374, 2), (key2374, 2), (key3029, -2), (key3029, -2), (key3006, -2), (key2596, -6), (key2884, 2), (key2884, 2), (key2775, 2)]

def rawRow4965 : Integer.Sparse Key := [(key2468, -2), (key2468, -2), (key2505, -2), (key2481, 6), (key2402, 2), (key2402, 2), (key2439, 2), (key2605, -2), (key2926, -2), (key2926, -2), (key2775, -6), (key2596, 2), (key2884, 2), (key2884, 2)]

def rawRow4966 : Integer.Sparse Key := [(key2468, -2), (key2505, -2), (key2468, -2), (key2481, 6), (key2402, 2), (key2439, 2), (key2402, 2), (key2926, -2), (key2605, -2), (key2926, -2), (key2775, -6), (key2884, 2), (key2596, 2), (key2884, 2)]

def rawRow4967 : Integer.Sparse Key := [(key2505, -2), (key2468, -2), (key2468, -2), (key2481, 6), (key2439, 2), (key2402, 2), (key2402, 2), (key2926, -2), (key2926, -2), (key2605, -2), (key2775, -6), (key2884, 2), (key2884, 2), (key2596, 2)]

def rawRow4968 : Integer.Sparse Key := [(key2591, -2), (key2591, -2), (key2594, -2), (key2601, 6), (key2770, 2), (key2770, 2), (key2773, 2), (key2890, -2), (key2911, -2), (key2911, -2), (key2932, -6), (key2969, 2), (key2990, 2), (key2990, 2)]

def rawRow4969 : Integer.Sparse Key := [(key2591, -2), (key2594, -2), (key2591, -2), (key2601, 6), (key2770, 2), (key2773, 2), (key2770, 2), (key2911, -2), (key2890, -2), (key2911, -2), (key2932, -6), (key2990, 2), (key2969, 2), (key2990, 2)]

def rawRow4970 : Integer.Sparse Key := [(key2594, -2), (key2591, -2), (key2591, -2), (key2601, 6), (key2773, 2), (key2770, 2), (key2770, 2), (key2911, -2), (key2911, -2), (key2890, -2), (key2932, -6), (key2990, 2), (key2990, 2), (key2969, 2)]

def rawRow4971 : Integer.Sparse Key := [(key2591, -2), (key2591, -2), (key2601, -2), (key2594, 6), (key2847, 2), (key2847, 2), (key2890, 2), (key2773, -2), (key2881, -2), (key2881, -2), (key2969, -6), (key2932, 2), (key2990, 2), (key2990, 2)]

def rawRow4972 : Integer.Sparse Key := [(key2591, -2), (key2601, -2), (key2591, -2), (key2594, 6), (key2847, 2), (key2890, 2), (key2847, 2), (key2881, -2), (key2773, -2), (key2881, -2), (key2969, -6), (key2990, 2), (key2932, 2), (key2990, 2)]

def rawRow4973 : Integer.Sparse Key := [(key2601, -2), (key2591, -2), (key2591, -2), (key2594, 6), (key2890, 2), (key2847, 2), (key2847, 2), (key2881, -2), (key2881, -2), (key2773, -2), (key2969, -6), (key2990, 2), (key2990, 2), (key2932, 2)]

def rawRow4974 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2773, -2), (key2932, 6), (key2591, 2), (key2591, 2), (key2594, 2), (key2969, -2), (key2990, -2), (key2990, -2), (key2601, -6), (key2890, 2), (key2911, 2), (key2911, 2)]

def rawRow4975 : Integer.Sparse Key := [(key2770, -2), (key2773, -2), (key2770, -2), (key2932, 6), (key2591, 2), (key2594, 2), (key2591, 2), (key2990, -2), (key2969, -2), (key2990, -2), (key2601, -6), (key2911, 2), (key2890, 2), (key2911, 2)]

def rawRow4976 : Integer.Sparse Key := [(key2773, -2), (key2770, -2), (key2770, -2), (key2932, 6), (key2594, 2), (key2591, 2), (key2591, 2), (key2990, -2), (key2990, -2), (key2969, -2), (key2601, -6), (key2911, 2), (key2911, 2), (key2890, 2)]

def rawRow4977 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2932, -2), (key2773, 6), (key2847, 2), (key2847, 2), (key2969, 2), (key2594, -2), (key2881, -2), (key2881, -2), (key2890, -6), (key2601, 2), (key2911, 2), (key2911, 2)]

def rawRow4978 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2770, -2), (key2773, 6), (key2847, 2), (key2969, 2), (key2847, 2), (key2881, -2), (key2594, -2), (key2881, -2), (key2890, -6), (key2911, 2), (key2601, 2), (key2911, 2)]

def rawRow4979 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2770, -2), (key2773, 6), (key2969, 2), (key2847, 2), (key2847, 2), (key2881, -2), (key2881, -2), (key2594, -2), (key2890, -6), (key2911, 2), (key2911, 2), (key2601, 2)]

def rawRow4980 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2890, -2), (key2969, 6), (key2591, 2), (key2591, 2), (key2601, 2), (key2932, -2), (key2990, -2), (key2990, -2), (key2594, -6), (key2773, 2), (key2881, 2), (key2881, 2)]

def rawRow4981 : Integer.Sparse Key := [(key2847, -2), (key2890, -2), (key2847, -2), (key2969, 6), (key2591, 2), (key2601, 2), (key2591, 2), (key2990, -2), (key2932, -2), (key2990, -2), (key2594, -6), (key2881, 2), (key2773, 2), (key2881, 2)]

def rawRow4982 : Integer.Sparse Key := [(key2890, -2), (key2847, -2), (key2847, -2), (key2969, 6), (key2601, 2), (key2591, 2), (key2591, 2), (key2990, -2), (key2990, -2), (key2932, -2), (key2594, -6), (key2881, 2), (key2881, 2), (key2773, 2)]

def rawRow4983 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2969, -2), (key2890, 6), (key2770, 2), (key2770, 2), (key2932, 2), (key2601, -2), (key2911, -2), (key2911, -2), (key2773, -6), (key2594, 2), (key2881, 2), (key2881, 2)]

def rawRow4984 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2847, -2), (key2890, 6), (key2770, 2), (key2932, 2), (key2770, 2), (key2911, -2), (key2601, -2), (key2911, -2), (key2773, -6), (key2881, 2), (key2594, 2), (key2881, 2)]

def rawRow4985 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2847, -2), (key2890, 6), (key2932, 2), (key2770, 2), (key2770, 2), (key2911, -2), (key2911, -2), (key2601, -2), (key2773, -6), (key2881, 2), (key2881, 2), (key2594, 2)]

def rawRow4986 : Integer.Sparse Key := [(key2616, -2), (key2616, -2), (key2619, -2), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2642, 1), (key2642, 1), (key2671, 2), (key2671, 2), (key2674, 2), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2729, -1), (key2729, -1), (key2786, -1), (key2786, -1), (key2794, -1), (key2794, -1), (key2796, -1), (key2796, -1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2832, 1), (key2832, 1)]

def rawRow4987 : Integer.Sparse Key := [(key2616, -2), (key2619, -2), (key2616, -2), (key2640, 1), (key2642, 1), (key2632, 1), (key2642, 1), (key2632, 1), (key2640, 1), (key2671, 2), (key2674, 2), (key2671, 2), (key2726, -1), (key2729, -1), (key2706, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2794, -1), (key2796, -1), (key2786, -1), (key2796, -1), (key2786, -1), (key2794, -1), (key2829, 1), (key2832, 1), (key2809, 1), (key2832, 1), (key2809, 1), (key2829, 1)]

def rawRow4988 : Integer.Sparse Key := [(key2619, -2), (key2616, -2), (key2616, -2), (key2642, 1), (key2640, 1), (key2642, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2674, 2), (key2671, 2), (key2671, 2), (key2729, -1), (key2726, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2796, -1), (key2794, -1), (key2796, -1), (key2786, -1), (key2794, -1), (key2786, -1), (key2832, 1), (key2829, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2809, 1)]

def rawRow4989 : Integer.Sparse Key := [(key2632, -2), (key2632, -2), (key2649, -2), (key2616, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2654, 1), (key2654, 1), (key2706, 2), (key2706, 2), (key2738, 2), (key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2748, -1), (key2748, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2898, -1), (key2898, -1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2905, 1), (key2905, 1)]

def rawRow4990 : Integer.Sparse Key := [(key2632, -2), (key2649, -2), (key2632, -2), (key2640, 1), (key2654, 1), (key2616, 1), (key2654, 1), (key2616, 1), (key2640, 1), (key2706, 2), (key2738, 2), (key2706, 2), (key2726, -1), (key2748, -1), (key2671, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2860, -1), (key2898, -1), (key2809, -1), (key2898, -1), (key2809, -1), (key2860, -1), (key2870, 1), (key2905, 1), (key2786, 1), (key2905, 1), (key2786, 1), (key2870, 1)]

def rawRow4991 : Integer.Sparse Key := [(key2649, -2), (key2632, -2), (key2632, -2), (key2654, 1), (key2640, 1), (key2654, 1), (key2616, 1), (key2640, 1), (key2616, 1), (key2738, 2), (key2706, 2), (key2706, 2), (key2748, -1), (key2726, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2898, -1), (key2860, -1), (key2898, -1), (key2809, -1), (key2860, -1), (key2809, -1), (key2905, 1), (key2870, 1), (key2905, 1), (key2786, 1), (key2870, 1), (key2786, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4992 : Integer.Sparse Key := [(key2671, -2), (key2671, -2), (key2674, -2), (key2786, 1), (key2786, 1), (key2794, 1), (key2794, 1), (key2796, 1), (key2796, 1), (key2616, 2), (key2616, 2), (key2619, 2), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2832, -1), (key2832, -1), (key2632, -1), (key2632, -1), (key2640, -1), (key2640, -1), (key2642, -1), (key2642, -1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2729, 1), (key2729, 1)]

def rawRow4993 : Integer.Sparse Key := [(key2671, -2), (key2674, -2), (key2671, -2), (key2794, 1), (key2796, 1), (key2786, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2616, 2), (key2619, 2), (key2616, 2), (key2829, -1), (key2832, -1), (key2809, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2640, -1), (key2642, -1), (key2632, -1), (key2642, -1), (key2632, -1), (key2640, -1), (key2726, 1), (key2729, 1), (key2706, 1), (key2729, 1), (key2706, 1), (key2726, 1)]

def rawRow4994 : Integer.Sparse Key := [(key2674, -2), (key2671, -2), (key2671, -2), (key2796, 1), (key2794, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2786, 1), (key2619, 2), (key2616, 2), (key2616, 2), (key2832, -1), (key2829, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key2642, -1), (key2640, -1), (key2642, -1), (key2632, -1), (key2640, -1), (key2632, -1), (key2729, 1), (key2726, 1), (key2729, 1), (key2706, 1), (key2726, 1), (key2706, 1)]

def rawRow4995 : Integer.Sparse Key := [(key2786, -2), (key2786, -2), (key2939, -2), (key2671, 1), (key2671, 1), (key2794, 1), (key2794, 1), (key2944, 1), (key2944, 1), (key2809, 2), (key2809, 2), (key2951, 2), (key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key2977, -1), (key2977, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1)]

def rawRow4996 : Integer.Sparse Key := [(key2786, -2), (key2939, -2), (key2786, -2), (key2794, 1), (key2944, 1), (key2671, 1), (key2944, 1), (key2671, 1), (key2794, 1), (key2809, 2), (key2951, 2), (key2809, 2), (key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1)]

def rawRow4997 : Integer.Sparse Key := [(key2939, -2), (key2786, -2), (key2786, -2), (key2944, 1), (key2794, 1), (key2944, 1), (key2671, 1), (key2794, 1), (key2671, 1), (key2951, 2), (key2809, 2), (key2809, 2), (key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2977, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1)]

def rawRow4998 : Integer.Sparse Key := [(key2706, -2), (key2706, -2), (key2738, -2), (key2809, 1), (key2809, 1), (key2860, 1), (key2860, 1), (key2898, 1), (key2898, 1), (key2632, 2), (key2632, 2), (key2649, 2), (key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2905, -1), (key2905, -1), (key2616, -1), (key2616, -1), (key2640, -1), (key2640, -1), (key2654, -1), (key2654, -1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2748, 1), (key2748, 1)]

def rawRow4999 : Integer.Sparse Key := [(key2706, -2), (key2738, -2), (key2706, -2), (key2860, 1), (key2898, 1), (key2809, 1), (key2898, 1), (key2809, 1), (key2860, 1), (key2632, 2), (key2649, 2), (key2632, 2), (key2870, -1), (key2905, -1), (key2786, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2640, -1), (key2654, -1), (key2616, -1), (key2654, -1), (key2616, -1), (key2640, -1), (key2726, 1), (key2748, 1), (key2671, 1), (key2748, 1), (key2671, 1), (key2726, 1)]

def rawRow5000 : Integer.Sparse Key := [(key2738, -2), (key2706, -2), (key2706, -2), (key2898, 1), (key2860, 1), (key2898, 1), (key2809, 1), (key2860, 1), (key2809, 1), (key2649, 2), (key2632, 2), (key2632, 2), (key2905, -1), (key2870, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2786, -1), (key2654, -1), (key2640, -1), (key2654, -1), (key2616, -1), (key2640, -1), (key2616, -1), (key2748, 1), (key2726, 1), (key2748, 1), (key2671, 1), (key2726, 1), (key2671, 1)]

def rawRow5001 : Integer.Sparse Key := [(key2809, -2), (key2809, -2), (key2951, -2), (key2706, 1), (key2706, 1), (key2860, 1), (key2860, 1), (key2977, 1), (key2977, 1), (key2786, 2), (key2786, 2), (key2939, 2), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2671, -1), (key2671, -1), (key2794, -1), (key2794, -1), (key2944, -1), (key2944, -1), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1)]

def rawRow5002 : Integer.Sparse Key := [(key2809, -2), (key2951, -2), (key2809, -2), (key2860, 1), (key2977, 1), (key2706, 1), (key2977, 1), (key2706, 1), (key2860, 1), (key2786, 2), (key2939, 2), (key2786, 2), (key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1)]

def rawRow5003 : Integer.Sparse Key := [(key2951, -2), (key2809, -2), (key2809, -2), (key2977, 1), (key2860, 1), (key2977, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key2939, 2), (key2786, 2), (key2786, 2), (key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2944, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1)]

def rawRow5004 : Integer.Sparse Key := [(key2078, -2), (key2078, -2), (key2082, -2), (key2087, 6), (key2175, 2), (key2175, 2), (key2179, 2), (key2281, -2), (key2330, -2), (key2330, -2), (key2189, -6), (key2289, 2), (key2333, 2), (key2333, 2)]

def rawRow5005 : Integer.Sparse Key := [(key2078, -2), (key2082, -2), (key2078, -2), (key2087, 6), (key2175, 2), (key2179, 2), (key2175, 2), (key2330, -2), (key2281, -2), (key2330, -2), (key2189, -6), (key2333, 2), (key2289, 2), (key2333, 2)]

def rawRow5006 : Integer.Sparse Key := [(key2082, -2), (key2078, -2), (key2078, -2), (key2087, 6), (key2179, 2), (key2175, 2), (key2175, 2), (key2330, -2), (key2330, -2), (key2281, -2), (key2189, -6), (key2333, 2), (key2333, 2), (key2289, 2)]

def rawRow5007 : Integer.Sparse Key := [(key2078, -2), (key2078, -2), (key2087, -2), (key2082, 6), (key2275, 2), (key2275, 2), (key2281, 2), (key2179, -2), (key2328, -2), (key2328, -2), (key2289, -6), (key2189, 2), (key2333, 2), (key2333, 2)]

def rawRow5008 : Integer.Sparse Key := [(key2078, -2), (key2087, -2), (key2078, -2), (key2082, 6), (key2275, 2), (key2281, 2), (key2275, 2), (key2328, -2), (key2179, -2), (key2328, -2), (key2289, -6), (key2333, 2), (key2189, 2), (key2333, 2)]

def rawRow5009 : Integer.Sparse Key := [(key2087, -2), (key2078, -2), (key2078, -2), (key2082, 6), (key2281, 2), (key2275, 2), (key2275, 2), (key2328, -2), (key2328, -2), (key2179, -2), (key2289, -6), (key2333, 2), (key2333, 2), (key2189, 2)]

def rawRow5010 : Integer.Sparse Key := [(key2175, -2), (key2175, -2), (key2179, -2), (key2189, 6), (key2078, 2), (key2078, 2), (key2082, 2), (key2289, -2), (key2333, -2), (key2333, -2), (key2087, -6), (key2281, 2), (key2330, 2), (key2330, 2)]

def rawRow5011 : Integer.Sparse Key := [(key2175, -2), (key2179, -2), (key2175, -2), (key2189, 6), (key2078, 2), (key2082, 2), (key2078, 2), (key2333, -2), (key2289, -2), (key2333, -2), (key2087, -6), (key2330, 2), (key2281, 2), (key2330, 2)]

def rawRow5012 : Integer.Sparse Key := [(key2179, -2), (key2175, -2), (key2175, -2), (key2189, 6), (key2082, 2), (key2078, 2), (key2078, 2), (key2333, -2), (key2333, -2), (key2289, -2), (key2087, -6), (key2330, 2), (key2330, 2), (key2281, 2)]

def rawRow5013 : Integer.Sparse Key := [(key2175, -2), (key2175, -2), (key2189, -2), (key2179, 6), (key2275, 2), (key2275, 2), (key2289, 2), (key2082, -2), (key2328, -2), (key2328, -2), (key2281, -6), (key2087, 2), (key2330, 2), (key2330, 2)]

def rawRow5014 : Integer.Sparse Key := [(key2175, -2), (key2189, -2), (key2175, -2), (key2179, 6), (key2275, 2), (key2289, 2), (key2275, 2), (key2328, -2), (key2082, -2), (key2328, -2), (key2281, -6), (key2330, 2), (key2087, 2), (key2330, 2)]

def rawRow5015 : Integer.Sparse Key := [(key2189, -2), (key2175, -2), (key2175, -2), (key2179, 6), (key2289, 2), (key2275, 2), (key2275, 2), (key2328, -2), (key2328, -2), (key2082, -2), (key2281, -6), (key2330, 2), (key2330, 2), (key2087, 2)]

def rawRow5016 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2281, -2), (key2289, 6), (key2078, 2), (key2078, 2), (key2087, 2), (key2189, -2), (key2333, -2), (key2333, -2), (key2082, -6), (key2179, 2), (key2328, 2), (key2328, 2)]

def rawRow5017 : Integer.Sparse Key := [(key2275, -2), (key2281, -2), (key2275, -2), (key2289, 6), (key2078, 2), (key2087, 2), (key2078, 2), (key2333, -2), (key2189, -2), (key2333, -2), (key2082, -6), (key2328, 2), (key2179, 2), (key2328, 2)]

def rawRow5018 : Integer.Sparse Key := [(key2281, -2), (key2275, -2), (key2275, -2), (key2289, 6), (key2087, 2), (key2078, 2), (key2078, 2), (key2333, -2), (key2333, -2), (key2189, -2), (key2082, -6), (key2328, 2), (key2328, 2), (key2179, 2)]

def rawRow5019 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2289, -2), (key2281, 6), (key2175, 2), (key2175, 2), (key2189, 2), (key2087, -2), (key2330, -2), (key2330, -2), (key2179, -6), (key2082, 2), (key2328, 2), (key2328, 2)]

def rawRow5020 : Integer.Sparse Key := [(key2275, -2), (key2289, -2), (key2275, -2), (key2281, 6), (key2175, 2), (key2189, 2), (key2175, 2), (key2330, -2), (key2087, -2), (key2330, -2), (key2179, -6), (key2328, 2), (key2082, 2), (key2328, 2)]

def rawRow5021 : Integer.Sparse Key := [(key2289, -2), (key2275, -2), (key2275, -2), (key2281, 6), (key2189, 2), (key2175, 2), (key2175, 2), (key2330, -2), (key2330, -2), (key2087, -2), (key2179, -6), (key2328, 2), (key2328, 2), (key2082, 2)]

def rawRow5022 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2382, -2), (key2393, 2), (key2393, 2), (key2395, 2), (key2771, 2), (key2774, 2), (key2774, 2), (key2891, -1), (key2891, -1), (key2912, -1), (key2912, -1), (key2914, -1), (key2914, -1), (key2933, -2), (key2933, -2), (key2934, -2), (key2970, 1), (key2970, 1), (key2991, 1), (key2991, 1), (key2993, 1), (key2993, 1)]

def rawRow5023 : Integer.Sparse Key := [(key2382, -2), (key2379, -2), (key2382, -2), (key2393, 2), (key2395, 2), (key2393, 2), (key2774, 2), (key2771, 2), (key2774, 2), (key2912, -1), (key2914, -1), (key2891, -1), (key2914, -1), (key2891, -1), (key2912, -1), (key2933, -2), (key2934, -2), (key2933, -2), (key2991, 1), (key2993, 1), (key2970, 1), (key2993, 1), (key2970, 1), (key2991, 1)]

def rawRow5024 : Integer.Sparse Key := [(key2382, -2), (key2382, -2), (key2379, -2), (key2395, 2), (key2393, 2), (key2393, 2), (key2774, 2), (key2774, 2), (key2771, 2), (key2914, -1), (key2912, -1), (key2914, -1), (key2891, -1), (key2912, -1), (key2891, -1), (key2934, -2), (key2933, -2), (key2933, -2), (key2993, 1), (key2991, 1), (key2993, 1), (key2970, 1), (key2991, 1), (key2970, 1)]

def rawRow5025 : Integer.Sparse Key := [(key2379, -2), (key2393, -2), (key2393, -2), (key2382, 2), (key2382, 2), (key2395, 2), (key2848, 2), (key2891, 2), (key2891, 2), (key2774, -1), (key2774, -1), (key2882, -1), (key2882, -1), (key2914, -1), (key2914, -1), (key2970, -2), (key2970, -2), (key2996, -2), (key2933, 1), (key2933, 1), (key2991, 1), (key2991, 1), (key3003, 1), (key3003, 1)]

def rawRow5026 : Integer.Sparse Key := [(key2393, -2), (key2379, -2), (key2393, -2), (key2382, 2), (key2395, 2), (key2382, 2), (key2891, 2), (key2848, 2), (key2891, 2), (key2882, -1), (key2914, -1), (key2774, -1), (key2914, -1), (key2774, -1), (key2882, -1), (key2970, -2), (key2996, -2), (key2970, -2), (key2991, 1), (key3003, 1), (key2933, 1), (key3003, 1), (key2933, 1), (key2991, 1)]

def rawRow5027 : Integer.Sparse Key := [(key2393, -2), (key2393, -2), (key2379, -2), (key2395, 2), (key2382, 2), (key2382, 2), (key2891, 2), (key2891, 2), (key2848, 2), (key2914, -1), (key2882, -1), (key2914, -1), (key2774, -1), (key2882, -1), (key2774, -1), (key2996, -2), (key2970, -2), (key2970, -2), (key3003, 1), (key2991, 1), (key3003, 1), (key2933, 1), (key2991, 1), (key2933, 1)]

def rawRow5028 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2410, -2), (key2441, 2), (key2441, 2), (key2445, 2), (key2592, 2), (key2595, 2), (key2595, 2), (key2970, -1), (key2970, -1), (key2991, -1), (key2991, -1), (key2993, -1), (key2993, -1), (key2602, -2), (key2602, -2), (key2603, -2), (key2891, 1), (key2891, 1), (key2912, 1), (key2912, 1), (key2914, 1), (key2914, 1)]

def rawRow5029 : Integer.Sparse Key := [(key2410, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, 2), (key2441, 2), (key2595, 2), (key2592, 2), (key2595, 2), (key2991, -1), (key2993, -1), (key2970, -1), (key2993, -1), (key2970, -1), (key2991, -1), (key2602, -2), (key2603, -2), (key2602, -2), (key2912, 1), (key2914, 1), (key2891, 1), (key2914, 1), (key2891, 1), (key2912, 1)]

def rawRow5030 : Integer.Sparse Key := [(key2410, -2), (key2410, -2), (key2407, -2), (key2445, 2), (key2441, 2), (key2441, 2), (key2595, 2), (key2595, 2), (key2592, 2), (key2993, -1), (key2991, -1), (key2993, -1), (key2970, -1), (key2991, -1), (key2970, -1), (key2603, -2), (key2602, -2), (key2602, -2), (key2914, 1), (key2912, 1), (key2914, 1), (key2891, 1), (key2912, 1), (key2891, 1)]

def rawRow5031 : Integer.Sparse Key := [(key2407, -2), (key2441, -2), (key2441, -2), (key2410, 2), (key2410, 2), (key2445, 2), (key2848, 2), (key2970, 2), (key2970, 2), (key2595, -1), (key2595, -1), (key2882, -1), (key2882, -1), (key2993, -1), (key2993, -1), (key2891, -2), (key2891, -2), (key2996, -2), (key2602, 1), (key2602, 1), (key2912, 1), (key2912, 1), (key3003, 1), (key3003, 1)]

def rawRow5032 : Integer.Sparse Key := [(key2441, -2), (key2407, -2), (key2441, -2), (key2410, 2), (key2445, 2), (key2410, 2), (key2970, 2), (key2848, 2), (key2970, 2), (key2882, -1), (key2993, -1), (key2595, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2891, -2), (key2996, -2), (key2891, -2), (key2912, 1), (key3003, 1), (key2602, 1), (key3003, 1), (key2602, 1), (key2912, 1)]

def rawRow5033 : Integer.Sparse Key := [(key2441, -2), (key2441, -2), (key2407, -2), (key2445, 2), (key2410, 2), (key2410, 2), (key2970, 2), (key2970, 2), (key2848, 2), (key2993, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2595, -1), (key2996, -2), (key2891, -2), (key2891, -2), (key3003, 1), (key2912, 1), (key3003, 1), (key2602, 1), (key2912, 1), (key2602, 1)]

def rawRow5034 : Integer.Sparse Key := [(key2473, -2), (key2483, -2), (key2483, -2), (key2507, 2), (key2507, 2), (key2526, 2), (key2379, 2), (key2393, 2), (key2393, 2), (key2933, -1), (key2933, -1), (key2991, -1), (key2991, -1), (key3003, -1), (key3003, -1), (key2595, -2), (key2595, -2), (key2603, -2), (key2774, 1), (key2774, 1), (key2882, 1), (key2882, 1), (key2914, 1), (key2914, 1)]

def rawRow5035 : Integer.Sparse Key := [(key2483, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2507, 2), (key2393, 2), (key2379, 2), (key2393, 2), (key2991, -1), (key3003, -1), (key2933, -1), (key3003, -1), (key2933, -1), (key2991, -1), (key2595, -2), (key2603, -2), (key2595, -2), (key2882, 1), (key2914, 1), (key2774, 1), (key2914, 1), (key2774, 1), (key2882, 1)]

def rawRow5036 : Integer.Sparse Key := [(key2483, -2), (key2483, -2), (key2473, -2), (key2526, 2), (key2507, 2), (key2507, 2), (key2393, 2), (key2393, 2), (key2379, 2), (key3003, -1), (key2991, -1), (key3003, -1), (key2933, -1), (key2991, -1), (key2933, -1), (key2603, -2), (key2595, -2), (key2595, -2), (key2914, 1), (key2882, 1), (key2914, 1), (key2774, 1), (key2882, 1), (key2774, 1)]

def rawRow5037 : Integer.Sparse Key := [(key2473, -2), (key2507, -2), (key2507, -2), (key2483, 2), (key2483, 2), (key2526, 2), (key2407, 2), (key2441, 2), (key2441, 2), (key2602, -1), (key2602, -1), (key2912, -1), (key2912, -1), (key3003, -1), (key3003, -1), (key2774, -2), (key2774, -2), (key2934, -2), (key2595, 1), (key2595, 1), (key2882, 1), (key2882, 1), (key2993, 1), (key2993, 1)]

def rawRow5038 : Integer.Sparse Key := [(key2507, -2), (key2473, -2), (key2507, -2), (key2483, 2), (key2526, 2), (key2483, 2), (key2441, 2), (key2407, 2), (key2441, 2), (key2912, -1), (key3003, -1), (key2602, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2774, -2), (key2934, -2), (key2774, -2), (key2882, 1), (key2993, 1), (key2595, 1), (key2993, 1), (key2595, 1), (key2882, 1)]

def rawRow5039 : Integer.Sparse Key := [(key2507, -2), (key2507, -2), (key2473, -2), (key2526, 2), (key2483, 2), (key2483, 2), (key2441, 2), (key2441, 2), (key2407, 2), (key3003, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2602, -1), (key2934, -2), (key2774, -2), (key2774, -2), (key2993, 1), (key2882, 1), (key2993, 1), (key2595, 1), (key2882, 1), (key2595, 1)]

def rawRow5040 : Integer.Sparse Key := [(key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2732, -1), (key2732, -1), (key2753, 2), (key2758, 2), (key2758, 2), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2835, 1), (key2835, 1), (key2920, -1), (key2920, -1), (key2923, -1), (key2923, -1), (key2927, -1), (key2927, -1), (key3012, -2), (key3017, -2), (key3017, -2), (key3023, 1), (key3023, 1), (key3026, 1), (key3026, 1), (key3030, 1), (key3030, 1)]

def rawRow5041 : Integer.Sparse Key := [(key2726, -1), (key2732, -1), (key2706, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2758, 2), (key2753, 2), (key2758, 2), (key2829, 1), (key2835, 1), (key2809, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2923, -1), (key2927, -1), (key2920, -1), (key2927, -1), (key2920, -1), (key2923, -1), (key3017, -2), (key3012, -2), (key3017, -2), (key3026, 1), (key3030, 1), (key3023, 1), (key3030, 1), (key3023, 1), (key3026, 1)]

def rawRow5042 : Integer.Sparse Key := [(key2732, -1), (key2726, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2758, 2), (key2758, 2), (key2753, 2), (key2835, 1), (key2829, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2809, 1), (key2927, -1), (key2923, -1), (key2927, -1), (key2920, -1), (key2923, -1), (key2920, -1), (key3017, -2), (key3017, -2), (key3012, -2), (key3030, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key3023, 1)]

def rawRow5043 : Integer.Sparse Key := [(key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2758, -1), (key2758, -1), (key2676, 2), (key2732, 2), (key2732, 2), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2923, 1), (key2923, 1), (key2798, -1), (key2798, -1), (key2835, -1), (key2835, -1), (key2885, -1), (key2885, -1), (key3008, -2), (key3026, -2), (key3026, -2), (key3010, 1), (key3010, 1), (key3017, 1), (key3017, 1), (key3030, 1), (key3030, 1)]

def rawRow5044 : Integer.Sparse Key := [(key2726, -1), (key2758, -1), (key2671, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2732, 2), (key2676, 2), (key2732, 2), (key2870, 1), (key2923, 1), (key2786, 1), (key2923, 1), (key2786, 1), (key2870, 1), (key2835, -1), (key2885, -1), (key2798, -1), (key2885, -1), (key2798, -1), (key2835, -1), (key3026, -2), (key3008, -2), (key3026, -2), (key3017, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3017, 1)]

def rawRow5045 : Integer.Sparse Key := [(key2758, -1), (key2726, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2732, 2), (key2732, 2), (key2676, 2), (key2923, 1), (key2870, 1), (key2923, 1), (key2786, 1), (key2870, 1), (key2786, 1), (key2885, -1), (key2835, -1), (key2885, -1), (key2798, -1), (key2835, -1), (key2798, -1), (key3026, -2), (key3026, -2), (key3008, -2), (key3030, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key3010, 1)]

def rawRow5046 : Integer.Sparse Key := [(key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2835, -1), (key2835, -1), (key3012, 2), (key3017, 2), (key3017, 2), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1), (key3023, -1), (key3023, -1), (key3026, -1), (key3026, -1), (key3030, -1), (key3030, -1), (key2753, -2), (key2758, -2), (key2758, -2), (key2920, 1), (key2920, 1), (key2923, 1), (key2923, 1), (key2927, 1), (key2927, 1)]

def rawRow5047 : Integer.Sparse Key := [(key2829, -1), (key2835, -1), (key2809, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key3017, 2), (key3012, 2), (key3017, 2), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key3026, -1), (key3030, -1), (key3023, -1), (key3030, -1), (key3023, -1), (key3026, -1), (key2758, -2), (key2753, -2), (key2758, -2), (key2923, 1), (key2927, 1), (key2920, 1), (key2927, 1), (key2920, 1), (key2923, 1)]

def rawRow5048 : Integer.Sparse Key := [(key2835, -1), (key2829, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key3017, 2), (key3017, 2), (key3012, 2), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key3030, -1), (key3026, -1), (key3030, -1), (key3023, -1), (key3026, -1), (key3023, -1), (key2758, -2), (key2758, -2), (key2753, -2), (key2927, 1), (key2923, 1), (key2927, 1), (key2920, 1), (key2923, 1), (key2920, 1)]

def rawRow5049 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2621, 2), (key2835, 2), (key2835, 2), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, -1), (key2885, -1), (key2658, -2), (key2923, -2), (key2923, -2), (key2660, 1), (key2660, 1), (key2758, 1), (key2758, 1), (key2927, 1), (key2927, 1)]

def rawRow5050 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2835, 2), (key2621, 2), (key2835, 2), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2923, -2), (key2658, -2), (key2923, -2), (key2758, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2758, 1)]

def rawRow5051 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key2835, 2), (key2835, 2), (key2621, 2), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2644, -1), (key2923, -2), (key2923, -2), (key2658, -2), (key2927, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2660, 1)]

def rawRow5052 : Integer.Sparse Key := [(key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2976, -1), (key2976, -1), (key2728, 2), (key2983, 2), (key2983, 2), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1), (key3010, -1), (key3010, -1), (key3017, -1), (key3017, -1), (key3030, -1), (key3030, -1), (key2676, -2), (key2732, -2), (key2732, -2), (key2798, 1), (key2798, 1), (key2835, 1), (key2835, 1), (key2885, 1), (key2885, 1)]

def rawRow5053 : Integer.Sparse Key := [(key2972, -1), (key2976, -1), (key2702, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2983, 2), (key2728, 2), (key2983, 2), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key3017, -1), (key3030, -1), (key3010, -1), (key3030, -1), (key3010, -1), (key3017, -1), (key2732, -2), (key2676, -2), (key2732, -2), (key2835, 1), (key2885, 1), (key2798, 1), (key2885, 1), (key2798, 1), (key2835, 1)]

def rawRow5054 : Integer.Sparse Key := [(key2976, -1), (key2972, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2702, -1), (key2983, 2), (key2983, 2), (key2728, 2), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key3030, -1), (key3017, -1), (key3030, -1), (key3010, -1), (key3017, -1), (key3010, -1), (key2732, -2), (key2732, -2), (key2676, -2), (key2885, 1), (key2835, 1), (key2885, 1), (key2798, 1), (key2835, 1), (key2798, 1)]

def rawRow5055 : Integer.Sparse Key := [(key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2641, 2), (key2976, 2), (key2976, 2), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2660, -1), (key2660, -1), (key2758, -1), (key2758, -1), (key2927, -1), (key2927, -1), (key2621, -2), (key2835, -2), (key2835, -2), (key2644, 1), (key2644, 1), (key2732, 1), (key2732, 1), (key2885, 1), (key2885, 1)]

def rawRow5056 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2976, 2), (key2641, 2), (key2976, 2), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2758, -1), (key2927, -1), (key2660, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2835, -2), (key2621, -2), (key2835, -2), (key2732, 1), (key2885, 1), (key2644, 1), (key2885, 1), (key2644, 1), (key2732, 1)]

def rawRow5057 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2976, 2), (key2976, 2), (key2641, 2), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key2927, -1), (key2758, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2660, -1), (key2835, -2), (key2835, -2), (key2621, -2), (key2885, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2644, 1)]

def rawRow5058 : Integer.Sparse Key := [(key2616, -2), (key2616, -2), (key2619, -2), (key2649, 2), (key2654, 2), (key2654, 2), (key2671, 2), (key2671, 2), (key2674, 2), (key2738, -2), (key2748, -2), (key2748, -2), (key2939, -2), (key2944, -2), (key2944, -2), (key2951, 2), (key2961, 2), (key2961, 2)]

def rawRow5059 : Integer.Sparse Key := [(key2616, -2), (key2619, -2), (key2616, -2), (key2654, 2), (key2649, 2), (key2654, 2), (key2671, 2), (key2674, 2), (key2671, 2), (key2748, -2), (key2738, -2), (key2748, -2), (key2944, -2), (key2939, -2), (key2944, -2), (key2961, 2), (key2951, 2), (key2961, 2)]

def rawRow5060 : Integer.Sparse Key := [(key2619, -2), (key2616, -2), (key2616, -2), (key2654, 2), (key2654, 2), (key2649, 2), (key2674, 2), (key2671, 2), (key2671, 2), (key2748, -2), (key2748, -2), (key2738, -2), (key2944, -2), (key2944, -2), (key2939, -2), (key2961, 2), (key2961, 2), (key2951, 2)]

def rawRow5061 : Integer.Sparse Key := [(key2632, -2), (key2632, -2), (key2649, -2), (key2619, 2), (key2642, 2), (key2642, 2), (key2706, 2), (key2706, 2), (key2738, 2), (key2674, -2), (key2729, -2), (key2729, -2), (key2951, -2), (key2977, -2), (key2977, -2), (key2939, 2), (key2984, 2), (key2984, 2)]

def rawRow5062 : Integer.Sparse Key := [(key2632, -2), (key2649, -2), (key2632, -2), (key2642, 2), (key2619, 2), (key2642, 2), (key2706, 2), (key2738, 2), (key2706, 2), (key2729, -2), (key2674, -2), (key2729, -2), (key2977, -2), (key2951, -2), (key2977, -2), (key2984, 2), (key2939, 2), (key2984, 2)]

def rawRow5063 : Integer.Sparse Key := [(key2649, -2), (key2632, -2), (key2632, -2), (key2642, 2), (key2642, 2), (key2619, 2), (key2738, 2), (key2706, 2), (key2706, 2), (key2729, -2), (key2729, -2), (key2674, -2), (key2977, -2), (key2977, -2), (key2951, -2), (key2984, 2), (key2984, 2), (key2939, 2)]

def rawRow5064 : Integer.Sparse Key := [(key2671, -2), (key2671, -2), (key2674, -2), (key2939, 2), (key2944, 2), (key2944, 2), (key2616, 2), (key2616, 2), (key2619, 2), (key2951, -2), (key2961, -2), (key2961, -2), (key2649, -2), (key2654, -2), (key2654, -2), (key2738, 2), (key2748, 2), (key2748, 2)]

def rawRow5065 : Integer.Sparse Key := [(key2671, -2), (key2674, -2), (key2671, -2), (key2944, 2), (key2939, 2), (key2944, 2), (key2616, 2), (key2619, 2), (key2616, 2), (key2961, -2), (key2951, -2), (key2961, -2), (key2654, -2), (key2649, -2), (key2654, -2), (key2748, 2), (key2738, 2), (key2748, 2)]

def rawRow5066 : Integer.Sparse Key := [(key2674, -2), (key2671, -2), (key2671, -2), (key2944, 2), (key2944, 2), (key2939, 2), (key2619, 2), (key2616, 2), (key2616, 2), (key2961, -2), (key2961, -2), (key2951, -2), (key2654, -2), (key2654, -2), (key2649, -2), (key2748, 2), (key2748, 2), (key2738, 2)]

def rawRow5067 : Integer.Sparse Key := [(key2786, -2), (key2786, -2), (key2939, -2), (key2674, 2), (key2796, 2), (key2796, 2), (key2809, 2), (key2809, 2), (key2951, 2), (key2619, -2), (key2832, -2), (key2832, -2), (key2738, -2), (key2898, -2), (key2898, -2), (key2649, 2), (key2905, 2), (key2905, 2)]

def rawRow5068 : Integer.Sparse Key := [(key2786, -2), (key2939, -2), (key2786, -2), (key2796, 2), (key2674, 2), (key2796, 2), (key2809, 2), (key2951, 2), (key2809, 2), (key2832, -2), (key2619, -2), (key2832, -2), (key2898, -2), (key2738, -2), (key2898, -2), (key2905, 2), (key2649, 2), (key2905, 2)]

def rawRow5069 : Integer.Sparse Key := [(key2939, -2), (key2786, -2), (key2786, -2), (key2796, 2), (key2796, 2), (key2674, 2), (key2951, 2), (key2809, 2), (key2809, 2), (key2832, -2), (key2832, -2), (key2619, -2), (key2898, -2), (key2898, -2), (key2738, -2), (key2905, 2), (key2905, 2), (key2649, 2)]

def rawRow5070 : Integer.Sparse Key := [(key2706, -2), (key2706, -2), (key2738, -2), (key2951, 2), (key2977, 2), (key2977, 2), (key2632, 2), (key2632, 2), (key2649, 2), (key2939, -2), (key2984, -2), (key2984, -2), (key2619, -2), (key2642, -2), (key2642, -2), (key2674, 2), (key2729, 2), (key2729, 2)]

def rawRow5071 : Integer.Sparse Key := [(key2706, -2), (key2738, -2), (key2706, -2), (key2977, 2), (key2951, 2), (key2977, 2), (key2632, 2), (key2649, 2), (key2632, 2), (key2984, -2), (key2939, -2), (key2984, -2), (key2642, -2), (key2619, -2), (key2642, -2), (key2729, 2), (key2674, 2), (key2729, 2)]

def rawRow5072 : Integer.Sparse Key := [(key2738, -2), (key2706, -2), (key2706, -2), (key2977, 2), (key2977, 2), (key2951, 2), (key2649, 2), (key2632, 2), (key2632, 2), (key2984, -2), (key2984, -2), (key2939, -2), (key2642, -2), (key2642, -2), (key2619, -2), (key2729, 2), (key2729, 2), (key2674, 2)]

def rawRow5073 : Integer.Sparse Key := [(key2809, -2), (key2809, -2), (key2951, -2), (key2738, 2), (key2898, 2), (key2898, 2), (key2786, 2), (key2786, 2), (key2939, 2), (key2649, -2), (key2905, -2), (key2905, -2), (key2674, -2), (key2796, -2), (key2796, -2), (key2619, 2), (key2832, 2), (key2832, 2)]

def rawRow5074 : Integer.Sparse Key := [(key2809, -2), (key2951, -2), (key2809, -2), (key2898, 2), (key2738, 2), (key2898, 2), (key2786, 2), (key2939, 2), (key2786, 2), (key2905, -2), (key2649, -2), (key2905, -2), (key2796, -2), (key2674, -2), (key2796, -2), (key2832, 2), (key2619, 2), (key2832, 2)]

def rawRow5075 : Integer.Sparse Key := [(key2951, -2), (key2809, -2), (key2809, -2), (key2898, 2), (key2898, 2), (key2738, 2), (key2939, 2), (key2786, 2), (key2786, 2), (key2905, -2), (key2905, -2), (key2649, -2), (key2796, -2), (key2796, -2), (key2674, -2), (key2832, 2), (key2832, 2), (key2619, 2)]

def rawRow5076 : Integer.Sparse Key := [(key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1774, -1), (key1774, -1), (key1559, 2), (key1780, 2), (key1780, 2), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1790, 1), (key1790, 1), (key1659, -1), (key1659, -1), (key1817, -1), (key1817, -1), (key1841, -1), (key1841, -1), (key1596, -2), (key1798, -2), (key1798, -2), (key1667, 1), (key1667, 1), (key1825, 1), (key1825, 1), (key1844, 1), (key1844, 1)]

def rawRow5077 : Integer.Sparse Key := [(key1772, -1), (key1774, -1), (key1546, -1), (key1774, -1), (key1546, -1), (key1772, -1), (key1780, 2), (key1559, 2), (key1780, 2), (key1788, 1), (key1790, 1), (key1573, 1), (key1790, 1), (key1573, 1), (key1788, 1), (key1817, -1), (key1841, -1), (key1659, -1), (key1841, -1), (key1659, -1), (key1817, -1), (key1798, -2), (key1596, -2), (key1798, -2), (key1825, 1), (key1844, 1), (key1667, 1), (key1844, 1), (key1667, 1), (key1825, 1)]

def rawRow5078 : Integer.Sparse Key := [(key1774, -1), (key1772, -1), (key1774, -1), (key1546, -1), (key1772, -1), (key1546, -1), (key1780, 2), (key1780, 2), (key1559, 2), (key1790, 1), (key1788, 1), (key1790, 1), (key1573, 1), (key1788, 1), (key1573, 1), (key1841, -1), (key1817, -1), (key1841, -1), (key1659, -1), (key1817, -1), (key1659, -1), (key1798, -2), (key1798, -2), (key1596, -2), (key1844, 1), (key1825, 1), (key1844, 1), (key1667, 1), (key1825, 1), (key1667, 1)]

def rawRow5079 : Integer.Sparse Key := [(key1391, -1), (key1391, -1), (key1772, -1), (key1772, -1), (key1780, -1), (key1780, -1), (key1397, 2), (key1774, 2), (key1774, 2), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1), (key1817, 1), (key1817, 1), (key1457, -1), (key1457, -1), (key1790, -1), (key1790, -1), (key1839, -1), (key1839, -1), (key1447, -2), (key1825, -2), (key1825, -2), (key1466, 1), (key1466, 1), (key1798, 1), (key1798, 1), (key1844, 1), (key1844, 1)]

def rawRow5080 : Integer.Sparse Key := [(key1772, -1), (key1780, -1), (key1391, -1), (key1780, -1), (key1391, -1), (key1772, -1), (key1774, 2), (key1397, 2), (key1774, 2), (key1813, 1), (key1817, 1), (key1424, 1), (key1817, 1), (key1424, 1), (key1813, 1), (key1790, -1), (key1839, -1), (key1457, -1), (key1839, -1), (key1457, -1), (key1790, -1), (key1825, -2), (key1447, -2), (key1825, -2), (key1798, 1), (key1844, 1), (key1466, 1), (key1844, 1), (key1466, 1), (key1798, 1)]

def rawRow5081 : Integer.Sparse Key := [(key1780, -1), (key1772, -1), (key1780, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1774, 2), (key1774, 2), (key1397, 2), (key1817, 1), (key1813, 1), (key1817, 1), (key1424, 1), (key1813, 1), (key1424, 1), (key1839, -1), (key1790, -1), (key1839, -1), (key1457, -1), (key1790, -1), (key1457, -1), (key1825, -2), (key1825, -2), (key1447, -2), (key1844, 1), (key1798, 1), (key1844, 1), (key1466, 1), (key1798, 1), (key1466, 1)]

def rawRow5082 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1790, -1), (key1790, -1), (key1596, 2), (key1798, 2), (key1798, 2), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1774, 1), (key1774, 1), (key1667, -1), (key1667, -1), (key1825, -1), (key1825, -1), (key1844, -1), (key1844, -1), (key1559, -2), (key1780, -2), (key1780, -2), (key1659, 1), (key1659, 1), (key1817, 1), (key1817, 1), (key1841, 1), (key1841, 1)]

def rawRow5083 : Integer.Sparse Key := [(key1788, -1), (key1790, -1), (key1573, -1), (key1790, -1), (key1573, -1), (key1788, -1), (key1798, 2), (key1596, 2), (key1798, 2), (key1772, 1), (key1774, 1), (key1546, 1), (key1774, 1), (key1546, 1), (key1772, 1), (key1825, -1), (key1844, -1), (key1667, -1), (key1844, -1), (key1667, -1), (key1825, -1), (key1780, -2), (key1559, -2), (key1780, -2), (key1817, 1), (key1841, 1), (key1659, 1), (key1841, 1), (key1659, 1), (key1817, 1)]

def rawRow5084 : Integer.Sparse Key := [(key1790, -1), (key1788, -1), (key1790, -1), (key1573, -1), (key1788, -1), (key1573, -1), (key1798, 2), (key1798, 2), (key1596, 2), (key1774, 1), (key1772, 1), (key1774, 1), (key1546, 1), (key1772, 1), (key1546, 1), (key1844, -1), (key1825, -1), (key1844, -1), (key1667, -1), (key1825, -1), (key1667, -1), (key1780, -2), (key1780, -2), (key1559, -2), (key1841, 1), (key1817, 1), (key1841, 1), (key1659, 1), (key1817, 1), (key1659, 1)]

def rawRow5085 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1788, -1), (key1788, -1), (key1798, -1), (key1798, -1), (key1302, 2), (key1790, 2), (key1790, 2), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1825, 1), (key1825, 1), (key1339, -1), (key1339, -1), (key1774, -1), (key1774, -1), (key1839, -1), (key1839, -1), (key1329, -2), (key1817, -2), (key1817, -2), (key1345, 1), (key1345, 1), (key1780, 1), (key1780, 1), (key1841, 1), (key1841, 1)]

def rawRow5086 : Integer.Sparse Key := [(key1788, -1), (key1798, -1), (key1296, -1), (key1798, -1), (key1296, -1), (key1788, -1), (key1790, 2), (key1302, 2), (key1790, 2), (key1813, 1), (key1825, 1), (key1316, 1), (key1825, 1), (key1316, 1), (key1813, 1), (key1774, -1), (key1839, -1), (key1339, -1), (key1839, -1), (key1339, -1), (key1774, -1), (key1817, -2), (key1329, -2), (key1817, -2), (key1780, 1), (key1841, 1), (key1345, 1), (key1841, 1), (key1345, 1), (key1780, 1)]

def rawRow5087 : Integer.Sparse Key := [(key1798, -1), (key1788, -1), (key1798, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1790, 2), (key1790, 2), (key1302, 2), (key1825, 1), (key1813, 1), (key1825, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1839, -1), (key1774, -1), (key1839, -1), (key1339, -1), (key1774, -1), (key1339, -1), (key1817, -2), (key1817, -2), (key1329, -2), (key1841, 1), (key1780, 1), (key1841, 1), (key1345, 1), (key1780, 1), (key1345, 1)]

def rawRow5088 : Integer.Sparse Key := [(key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1817, -1), (key1817, -1), (key1447, 2), (key1825, 2), (key1825, 2), (key1391, 1), (key1391, 1), (key1772, 1), (key1772, 1), (key1780, 1), (key1780, 1), (key1466, -1), (key1466, -1), (key1798, -1), (key1798, -1), (key1844, -1), (key1844, -1), (key1397, -2), (key1774, -2), (key1774, -2), (key1457, 1), (key1457, 1), (key1790, 1), (key1790, 1), (key1839, 1), (key1839, 1)]

def rawRow5089 : Integer.Sparse Key := [(key1813, -1), (key1817, -1), (key1424, -1), (key1817, -1), (key1424, -1), (key1813, -1), (key1825, 2), (key1447, 2), (key1825, 2), (key1772, 1), (key1780, 1), (key1391, 1), (key1780, 1), (key1391, 1), (key1772, 1), (key1798, -1), (key1844, -1), (key1466, -1), (key1844, -1), (key1466, -1), (key1798, -1), (key1774, -2), (key1397, -2), (key1774, -2), (key1790, 1), (key1839, 1), (key1457, 1), (key1839, 1), (key1457, 1), (key1790, 1)]

def rawRow5090 : Integer.Sparse Key := [(key1817, -1), (key1813, -1), (key1817, -1), (key1424, -1), (key1813, -1), (key1424, -1), (key1825, 2), (key1825, 2), (key1447, 2), (key1780, 1), (key1772, 1), (key1780, 1), (key1391, 1), (key1772, 1), (key1391, 1), (key1844, -1), (key1798, -1), (key1844, -1), (key1466, -1), (key1798, -1), (key1466, -1), (key1774, -2), (key1774, -2), (key1397, -2), (key1839, 1), (key1790, 1), (key1839, 1), (key1457, 1), (key1790, 1), (key1457, 1)]

def rawRow5091 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1813, -1), (key1813, -1), (key1825, -1), (key1825, -1), (key1329, 2), (key1817, 2), (key1817, 2), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1798, 1), (key1798, 1), (key1345, -1), (key1345, -1), (key1780, -1), (key1780, -1), (key1841, -1), (key1841, -1), (key1302, -2), (key1790, -2), (key1790, -2), (key1339, 1), (key1339, 1), (key1774, 1), (key1774, 1), (key1839, 1), (key1839, 1)]

def rawRow5092 : Integer.Sparse Key := [(key1813, -1), (key1825, -1), (key1316, -1), (key1825, -1), (key1316, -1), (key1813, -1), (key1817, 2), (key1329, 2), (key1817, 2), (key1788, 1), (key1798, 1), (key1296, 1), (key1798, 1), (key1296, 1), (key1788, 1), (key1780, -1), (key1841, -1), (key1345, -1), (key1841, -1), (key1345, -1), (key1780, -1), (key1790, -2), (key1302, -2), (key1790, -2), (key1774, 1), (key1839, 1), (key1339, 1), (key1839, 1), (key1339, 1), (key1774, 1)]

def rawRow5093 : Integer.Sparse Key := [(key1825, -1), (key1813, -1), (key1825, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1817, 2), (key1817, 2), (key1329, 2), (key1798, 1), (key1788, 1), (key1798, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1841, -1), (key1780, -1), (key1841, -1), (key1345, -1), (key1780, -1), (key1345, -1), (key1790, -2), (key1790, -2), (key1302, -2), (key1839, 1), (key1774, 1), (key1839, 1), (key1339, 1), (key1774, 1), (key1339, 1)]

def rawRow5094 : Integer.Sparse Key := [(key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2729, -1), (key2729, -1), (key2738, 2), (key2748, 2), (key2748, 2), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2832, 1), (key2832, 1), (key2898, -1), (key2898, -1), (key2905, -1), (key2905, -1), (key2913, -1), (key2913, -1), (key2951, -2), (key2961, -2), (key2961, -2), (key2977, 1), (key2977, 1), (key2984, 1), (key2984, 1), (key2992, 1), (key2992, 1)]

def rawRow5095 : Integer.Sparse Key := [(key2726, -1), (key2729, -1), (key2706, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2748, 2), (key2738, 2), (key2748, 2), (key2829, 1), (key2832, 1), (key2809, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2905, -1), (key2913, -1), (key2898, -1), (key2913, -1), (key2898, -1), (key2905, -1), (key2961, -2), (key2951, -2), (key2961, -2), (key2984, 1), (key2992, 1), (key2977, 1), (key2992, 1), (key2977, 1), (key2984, 1)]

def rawRow5096 : Integer.Sparse Key := [(key2729, -1), (key2726, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2748, 2), (key2748, 2), (key2738, 2), (key2832, 1), (key2829, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2809, 1), (key2913, -1), (key2905, -1), (key2913, -1), (key2898, -1), (key2905, -1), (key2898, -1), (key2961, -2), (key2961, -2), (key2951, -2), (key2992, 1), (key2984, 1), (key2992, 1), (key2977, 1), (key2984, 1), (key2977, 1)]

def rawRow5097 : Integer.Sparse Key := [(key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2748, -1), (key2748, -1), (key2674, 2), (key2729, 2), (key2729, 2), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2905, 1), (key2905, 1), (key2796, -1), (key2796, -1), (key2832, -1), (key2832, -1), (key2883, -1), (key2883, -1), (key2939, -2), (key2984, -2), (key2984, -2), (key2944, 1), (key2944, 1), (key2961, 1), (key2961, 1), (key2992, 1), (key2992, 1)]

def rawRow5098 : Integer.Sparse Key := [(key2726, -1), (key2748, -1), (key2671, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2729, 2), (key2674, 2), (key2729, 2), (key2870, 1), (key2905, 1), (key2786, 1), (key2905, 1), (key2786, 1), (key2870, 1), (key2832, -1), (key2883, -1), (key2796, -1), (key2883, -1), (key2796, -1), (key2832, -1), (key2984, -2), (key2939, -2), (key2984, -2), (key2961, 1), (key2992, 1), (key2944, 1), (key2992, 1), (key2944, 1), (key2961, 1)]

def rawRow5099 : Integer.Sparse Key := [(key2748, -1), (key2726, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2729, 2), (key2729, 2), (key2674, 2), (key2905, 1), (key2870, 1), (key2905, 1), (key2786, 1), (key2870, 1), (key2786, 1), (key2883, -1), (key2832, -1), (key2883, -1), (key2796, -1), (key2832, -1), (key2796, -1), (key2984, -2), (key2984, -2), (key2939, -2), (key2992, 1), (key2961, 1), (key2992, 1), (key2944, 1), (key2961, 1), (key2944, 1)]

def rawRow5100 : Integer.Sparse Key := [(key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2832, -1), (key2832, -1), (key2951, 2), (key2961, 2), (key2961, 2), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2729, 1), (key2729, 1), (key2977, -1), (key2977, -1), (key2984, -1), (key2984, -1), (key2992, -1), (key2992, -1), (key2738, -2), (key2748, -2), (key2748, -2), (key2898, 1), (key2898, 1), (key2905, 1), (key2905, 1), (key2913, 1), (key2913, 1)]

def rawRow5101 : Integer.Sparse Key := [(key2829, -1), (key2832, -1), (key2809, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2961, 2), (key2951, 2), (key2961, 2), (key2726, 1), (key2729, 1), (key2706, 1), (key2729, 1), (key2706, 1), (key2726, 1), (key2984, -1), (key2992, -1), (key2977, -1), (key2992, -1), (key2977, -1), (key2984, -1), (key2748, -2), (key2738, -2), (key2748, -2), (key2905, 1), (key2913, 1), (key2898, 1), (key2913, 1), (key2898, 1), (key2905, 1)]

def rawRow5102 : Integer.Sparse Key := [(key2832, -1), (key2829, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key2961, 2), (key2961, 2), (key2951, 2), (key2729, 1), (key2726, 1), (key2729, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key2992, -1), (key2984, -1), (key2992, -1), (key2977, -1), (key2984, -1), (key2977, -1), (key2748, -2), (key2748, -2), (key2738, -2), (key2913, 1), (key2905, 1), (key2913, 1), (key2898, 1), (key2905, 1), (key2898, 1)]

def rawRow5103 : Integer.Sparse Key := [(key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2619, 2), (key2832, 2), (key2832, 2), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1), (key2642, -1), (key2642, -1), (key2729, -1), (key2729, -1), (key2883, -1), (key2883, -1), (key2649, -2), (key2905, -2), (key2905, -2), (key2654, 1), (key2654, 1), (key2748, 1), (key2748, 1), (key2913, 1), (key2913, 1)]

def rawRow5104 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2832, 2), (key2619, 2), (key2832, 2), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2729, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2905, -2), (key2649, -2), (key2905, -2), (key2748, 1), (key2913, 1), (key2654, 1), (key2913, 1), (key2654, 1), (key2748, 1)]

def rawRow5105 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2832, 2), (key2832, 2), (key2619, 2), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2883, -1), (key2729, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2642, -1), (key2905, -2), (key2905, -2), (key2649, -2), (key2913, 1), (key2748, 1), (key2913, 1), (key2654, 1), (key2748, 1), (key2654, 1)]

def rawRow5106 : Integer.Sparse Key := [(key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2905, -1), (key2905, -1), (key2939, 2), (key2984, 2), (key2984, 2), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2748, 1), (key2748, 1), (key2944, -1), (key2944, -1), (key2961, -1), (key2961, -1), (key2992, -1), (key2992, -1), (key2674, -2), (key2729, -2), (key2729, -2), (key2796, 1), (key2796, 1), (key2832, 1), (key2832, 1), (key2883, 1), (key2883, 1)]

def rawRow5107 : Integer.Sparse Key := [(key2870, -1), (key2905, -1), (key2786, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2984, 2), (key2939, 2), (key2984, 2), (key2726, 1), (key2748, 1), (key2671, 1), (key2748, 1), (key2671, 1), (key2726, 1), (key2961, -1), (key2992, -1), (key2944, -1), (key2992, -1), (key2944, -1), (key2961, -1), (key2729, -2), (key2674, -2), (key2729, -2), (key2832, 1), (key2883, 1), (key2796, 1), (key2883, 1), (key2796, 1), (key2832, 1)]

def rawRow5108 : Integer.Sparse Key := [(key2905, -1), (key2870, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2786, -1), (key2984, 2), (key2984, 2), (key2939, 2), (key2748, 1), (key2726, 1), (key2748, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2992, -1), (key2961, -1), (key2992, -1), (key2944, -1), (key2961, -1), (key2944, -1), (key2729, -2), (key2729, -2), (key2674, -2), (key2883, 1), (key2832, 1), (key2883, 1), (key2796, 1), (key2832, 1), (key2796, 1)]

def rawRow5109 : Integer.Sparse Key := [(key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2649, 2), (key2905, 2), (key2905, 2), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1), (key2654, -1), (key2654, -1), (key2748, -1), (key2748, -1), (key2913, -1), (key2913, -1), (key2619, -2), (key2832, -2), (key2832, -2), (key2642, 1), (key2642, 1), (key2729, 1), (key2729, 1), (key2883, 1), (key2883, 1)]

def rawRow5112 : Integer.Sparse Key := [(key1366, -2), (key1366, -2), (key1370, -2), (key1379, 6), (key1492, 2), (key1492, 2), (key1496, 2), (key1728, -2), (key1870, -2), (key1870, -2), (key1519, -6), (key1747, 2), (key1880, 2), (key1880, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow371 : Integer.Sparse Key := [(key1600, -1), (key1595, -1), (key1913, 2), (key1451, 1), (key1446, 1), (key1931, -1), (key1928, -1), (key1482, -2), (key1694, 1), (key1691, 1), (key1563, 1), (key1558, 1), (key1901, -2), (key1333, -1), (key1328, -1), (key1931, 1), (key1922, 1), (key1356, 2), (key1694, -1), (key1685, -1), (key1401, -1), (key1395, -1), (key1901, 1), (key1898, 1), (key1306, 1), (key1300, 1), (key1913, -1), (key1905, -1), (key1356, -1), (key1353, -1), (key1482, 1), (key1474, 1), (key1395, 2), (key1558, -1), (key1550, -1), (key1300, -2), (key1595, 1), (key1577, 1), (key1328, 1), (key1320, 1), (key1446, -1), (key1428, -1)]

def rawRow372 : Integer.Sparse Key := [(key1595, -1), (key1913, -1), (key1600, 2), (key1635, 1), (key1928, 1), (key1451, -1), (key1644, -1), (key1691, -2), (key1482, 1), (key1694, 1), (key1558, 1), (key1901, 1), (key1563, -2), (key1626, -1), (key1922, -1), (key1333, 1), (key1644, 1), (key1685, 2), (key1356, -1), (key1694, -1), (key1550, -1), (key1898, -1), (key1401, 1), (key1563, 1), (key1577, 1), (key1905, 1), (key1306, -1), (key1600, -1), (key1474, -1), (key1685, -1), (key1353, 1), (key1691, 1), (key1550, 2), (key1395, -1), (key1558, -1), (key1577, -2), (key1300, 1), (key1595, 1), (key1428, 1), (key1626, 1), (key1320, -1), (key1635, -1)]

def rawRow373 : Integer.Sparse Key := [(key1913, -1), (key1595, -1), (key1600, 2), (key1928, 1), (key1635, 1), (key1644, -1), (key1451, -1), (key1691, -2), (key1694, 1), (key1482, 1), (key1901, 1), (key1558, 1), (key1563, -2), (key1922, -1), (key1626, -1), (key1644, 1), (key1333, 1), (key1685, 2), (key1694, -1), (key1356, -1), (key1898, -1), (key1550, -1), (key1563, 1), (key1401, 1), (key1905, 1), (key1577, 1), (key1600, -1), (key1306, -1), (key1685, -1), (key1474, -1), (key1691, 1), (key1353, 1), (key1550, 2), (key1558, -1), (key1395, -1), (key1577, -2), (key1595, 1), (key1300, 1), (key1626, 1), (key1428, 1), (key1635, -1), (key1320, -1)]

def rawRow374 : Integer.Sparse Key := [(key1635, -1), (key1691, -1), (key1928, 2), (key1446, 1), (key1482, 1), (key1913, -1), (key1931, -1), (key1451, -2), (key1600, 1), (key1644, 1), (key1626, 1), (key1685, 1), (key1922, -2), (key1328, -1), (key1356, -1), (key1901, 1), (key1931, 1), (key1333, 2), (key1563, -1), (key1644, -1), (key1428, -1), (key1474, -1), (key1905, 1), (key1922, 1), (key1320, 1), (key1353, 1), (key1898, -1), (key1928, -1), (key1306, -1), (key1333, -1), (key1401, 1), (key1451, 1), (key1428, 2), (key1577, -1), (key1626, -1), (key1320, -2), (key1550, 1), (key1635, 1), (key1300, 1), (key1328, 1), (key1395, -1), (key1446, -1)]

def rawRow375 : Integer.Sparse Key := [(key1691, -1), (key1635, -1), (key1928, 2), (key1482, 1), (key1446, 1), (key1931, -1), (key1913, -1), (key1451, -2), (key1644, 1), (key1600, 1), (key1685, 1), (key1626, 1), (key1922, -2), (key1356, -1), (key1328, -1), (key1931, 1), (key1901, 1), (key1333, 2), (key1644, -1), (key1563, -1), (key1474, -1), (key1428, -1), (key1922, 1), (key1905, 1), (key1353, 1), (key1320, 1), (key1928, -1), (key1898, -1), (key1333, -1), (key1306, -1), (key1451, 1), (key1401, 1), (key1428, 2), (key1626, -1), (key1577, -1), (key1320, -2), (key1635, 1), (key1550, 1), (key1328, 1), (key1300, 1), (key1446, -1), (key1395, -1)]

def rawRow376 : Integer.Sparse Key := [(key1635, -1), (key1928, -1), (key1691, 2), (key1595, 1), (key1913, 1), (key1482, -1), (key1694, -1), (key1600, -2), (key1451, 1), (key1644, 1), (key1626, 1), (key1922, 1), (key1685, -2), (key1558, -1), (key1901, -1), (key1356, 1), (key1694, 1), (key1563, 2), (key1333, -1), (key1644, -1), (key1577, -1), (key1905, -1), (key1474, 1), (key1685, 1), (key1550, 1), (key1898, 1), (key1353, -1), (key1691, -1), (key1401, -1), (key1563, -1), (key1306, 1), (key1600, 1), (key1577, 2), (key1428, -1), (key1626, -1), (key1550, -2), (key1320, 1), (key1635, 1), (key1395, 1), (key1558, 1), (key1300, -1), (key1595, -1)]

def rawRow377 : Integer.Sparse Key := [(key1928, -1), (key1635, -1), (key1691, 2), (key1913, 1), (key1595, 1), (key1694, -1), (key1482, -1), (key1600, -2), (key1644, 1), (key1451, 1), (key1922, 1), (key1626, 1), (key1685, -2), (key1901, -1), (key1558, -1), (key1694, 1), (key1356, 1), (key1563, 2), (key1644, -1), (key1333, -1), (key1905, -1), (key1577, -1), (key1685, 1), (key1474, 1), (key1898, 1), (key1550, 1), (key1691, -1), (key1353, -1), (key1563, -1), (key1401, -1), (key1600, 1), (key1306, 1), (key1577, 2), (key1626, -1), (key1428, -1), (key1550, -2), (key1635, 1), (key1320, 1), (key1558, 1), (key1395, 1), (key1595, -1), (key1300, -1)]

def rawRow378 : Integer.Sparse Key := [(key243, -2), (key245, 1), (key245, 1), (key255, 2), (key266, -1), (key266, -1), (key270, -1), (key270, -1), (key275, 1), (key275, 1), (key309, 2), (key311, -1), (key311, -1), (key323, -2), (key334, 1), (key334, 1), (key338, 1), (key338, 1), (key344, -1), (key344, -1), (key392, -2), (key403, 1), (key403, 1), (key413, 2), (key424, -1), (key424, -1), (key473, -1), (key473, -1), (key479, 1), (key479, 1), (key571, 1), (key571, 1), (key576, -1), (key576, -1), (key581, -1), (key581, -1), (key587, 1), (key587, 1), (key599, 1), (key599, 1), (key605, -1), (key605, -1)]

def rawRow379 : Integer.Sparse Key := [(key245, -2), (key243, 1), (key245, 1), (key266, 2), (key255, -1), (key266, -1), (key275, -1), (key276, -1), (key270, 1), (key276, 1), (key311, 2), (key309, -1), (key311, -1), (key334, -2), (key323, 1), (key334, 1), (key344, 1), (key345, 1), (key338, -1), (key345, -1), (key403, -2), (key392, 1), (key403, 1), (key424, 2), (key413, -1), (key424, -1), (key479, -1), (key485, -1), (key473, 1), (key485, 1), (key576, 1), (key577, 1), (key571, -1), (key577, -1), (key587, -1), (key588, -1), (key581, 1), (key588, 1), (key605, 1), (key611, 1), (key599, -1), (key611, -1)]

def rawRow380 : Integer.Sparse Key := [(key245, -2), (key245, 1), (key243, 1), (key266, 2), (key266, -1), (key255, -1), (key276, -1), (key275, -1), (key276, 1), (key270, 1), (key311, 2), (key311, -1), (key309, -1), (key334, -2), (key334, 1), (key323, 1), (key345, 1), (key344, 1), (key345, -1), (key338, -1), (key403, -2), (key403, 1), (key392, 1), (key424, 2), (key424, -1), (key413, -1), (key485, -1), (key479, -1), (key485, 1), (key473, 1), (key577, 1), (key576, 1), (key577, -1), (key571, -1), (key588, -1), (key587, -1), (key588, 1), (key581, 1), (key611, 1), (key605, 1), (key611, -1), (key599, -1)]

def rawRow381 : Integer.Sparse Key := [(key255, -2), (key266, 1), (key266, 1), (key243, 2), (key275, -1), (key275, -1), (key245, -1), (key245, -1), (key266, 1), (key266, 1), (key323, 2), (key338, -1), (key338, -1), (key309, -2), (key344, 1), (key344, 1), (key311, 1), (key311, 1), (key334, -1), (key334, -1), (key413, -2), (key473, 1), (key473, 1), (key392, 2), (key479, -1), (key479, -1), (key403, -1), (key403, -1), (key424, 1), (key424, 1), (key581, 1), (key581, 1), (key599, -1), (key599, -1), (key571, -1), (key571, -1), (key605, 1), (key605, 1), (key576, 1), (key576, 1), (key587, -1), (key587, -1)]

def rawRow382 : Integer.Sparse Key := [(key266, -2), (key255, 1), (key266, 1), (key275, 2), (key243, -1), (key275, -1), (key266, -1), (key276, -1), (key245, 1), (key276, 1), (key338, 2), (key323, -1), (key338, -1), (key344, -2), (key309, 1), (key344, 1), (key334, 1), (key345, 1), (key311, -1), (key345, -1), (key473, -2), (key413, 1), (key473, 1), (key479, 2), (key392, -1), (key479, -1), (key424, -1), (key485, -1), (key403, 1), (key485, 1), (key599, 1), (key613, 1), (key581, -1), (key613, -1), (key605, -1), (key614, -1), (key571, 1), (key614, 1), (key587, 1), (key616, 1), (key576, -1), (key616, -1)]

def rawRow383 : Integer.Sparse Key := [(key266, -2), (key266, 1), (key255, 1), (key275, 2), (key275, -1), (key243, -1), (key276, -1), (key266, -1), (key276, 1), (key245, 1), (key338, 2), (key338, -1), (key323, -1), (key344, -2), (key344, 1), (key309, 1), (key345, 1), (key334, 1), (key345, -1), (key311, -1), (key473, -2), (key473, 1), (key413, 1), (key479, 2), (key479, -1), (key392, -1), (key485, -1), (key424, -1), (key485, 1), (key403, 1), (key613, 1), (key599, 1), (key613, -1), (key581, -1), (key614, -1), (key605, -1), (key614, 1), (key571, 1), (key616, 1), (key587, 1), (key616, -1), (key576, -1)]

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

def rawRow384 : Integer.Sparse Key := [(key270, -2), (key275, 1), (key276, 1), (key245, 2), (key266, -1), (key276, -1), (key243, -1), (key245, -1), (key255, 1), (key266, 1), (key334, 2), (key344, -1), (key345, -1), (key311, -2), (key338, 1), (key345, 1), (key309, 1), (key311, 1), (key323, -1), (key334, -1), (key424, -2), (key479, 1), (key485, 1), (key403, 2), (key473, -1), (key485, -1), (key392, -1), (key403, -1), (key413, 1), (key424, 1), (key587, 1), (key588, 1), (key605, -1), (key611, -1), (key576, -1), (key577, -1), (key599, 1), (key611, 1), (key571, 1), (key577, 1), (key581, -1), (key588, -1)]

def rawRow385 : Integer.Sparse Key := [(key270, -2), (key276, 1), (key275, 1), (key245, 2), (key276, -1), (key266, -1), (key245, -1), (key243, -1), (key266, 1), (key255, 1), (key334, 2), (key345, -1), (key344, -1), (key311, -2), (key345, 1), (key338, 1), (key311, 1), (key309, 1), (key334, -1), (key323, -1), (key424, -2), (key485, 1), (key479, 1), (key403, 2), (key485, -1), (key473, -1), (key403, -1), (key392, -1), (key424, 1), (key413, 1), (key588, 1), (key587, 1), (key611, -1), (key605, -1), (key577, -1), (key576, -1), (key611, 1), (key599, 1), (key577, 1), (key571, 1), (key588, -1), (key581, -1)]

def rawRow386 : Integer.Sparse Key := [(key275, -2), (key270, 1), (key276, 1), (key266, 2), (key245, -1), (key276, -1), (key255, -1), (key266, -1), (key243, 1), (key275, 1), (key344, 2), (key334, -1), (key345, -1), (key338, -2), (key311, 1), (key345, 1), (key323, 1), (key338, 1), (key309, -1), (key344, -1), (key479, -2), (key424, 1), (key485, 1), (key473, 2), (key403, -1), (key485, -1), (key413, -1), (key473, -1), (key392, 1), (key479, 1), (key605, 1), (key614, 1), (key587, -1), (key616, -1), (key599, -1), (key613, -1), (key576, 1), (key616, 1), (key581, 1), (key613, 1), (key571, -1), (key614, -1)]

def rawRow387 : Integer.Sparse Key := [(key275, -2), (key276, 1), (key270, 1), (key266, 2), (key276, -1), (key245, -1), (key266, -1), (key255, -1), (key275, 1), (key243, 1), (key344, 2), (key345, -1), (key334, -1), (key338, -2), (key345, 1), (key311, 1), (key338, 1), (key323, 1), (key344, -1), (key309, -1), (key479, -2), (key485, 1), (key424, 1), (key473, 2), (key485, -1), (key403, -1), (key473, -1), (key413, -1), (key479, 1), (key392, 1), (key614, 1), (key605, 1), (key616, -1), (key587, -1), (key613, -1), (key599, -1), (key616, 1), (key576, 1), (key613, 1), (key581, 1), (key614, -1), (key571, -1)]

def rawRow388 : Integer.Sparse Key := [(key309, -2), (key311, 1), (key311, 1), (key323, 2), (key338, -1), (key338, -1), (key334, -1), (key334, -1), (key344, 1), (key344, 1), (key243, 2), (key245, -1), (key245, -1), (key413, -2), (key424, 1), (key424, 1), (key581, 1), (key581, 1), (key587, -1), (key587, -1), (key255, -2), (key266, 1), (key266, 1), (key323, 2), (key334, -1), (key334, -1), (key599, -1), (key599, -1), (key605, 1), (key605, 1), (key270, 1), (key270, 1), (key275, -1), (key275, -1), (key338, -1), (key338, -1), (key344, 1), (key344, 1), (key473, 1), (key473, 1), (key479, -1), (key479, -1)]

def rawRow389 : Integer.Sparse Key := [(key311, -2), (key309, 1), (key311, 1), (key338, 2), (key323, -1), (key338, -1), (key344, -1), (key345, -1), (key334, 1), (key345, 1), (key245, 2), (key243, -1), (key245, -1), (key424, -2), (key413, 1), (key424, 1), (key587, 1), (key588, 1), (key581, -1), (key588, -1), (key266, -2), (key255, 1), (key266, 1), (key334, 2), (key323, -1), (key334, -1), (key605, -1), (key611, -1), (key599, 1), (key611, 1), (key275, 1), (key276, 1), (key270, -1), (key276, -1), (key344, -1), (key345, -1), (key338, 1), (key345, 1), (key479, 1), (key485, 1), (key473, -1), (key485, -1)]

def rawRow390 : Integer.Sparse Key := [(key311, -2), (key311, 1), (key309, 1), (key338, 2), (key338, -1), (key323, -1), (key345, -1), (key344, -1), (key345, 1), (key334, 1), (key245, 2), (key245, -1), (key243, -1), (key424, -2), (key424, 1), (key413, 1), (key588, 1), (key587, 1), (key588, -1), (key581, -1), (key266, -2), (key266, 1), (key255, 1), (key334, 2), (key334, -1), (key323, -1), (key611, -1), (key605, -1), (key611, 1), (key599, 1), (key276, 1), (key275, 1), (key276, -1), (key270, -1), (key345, -1), (key344, -1), (key345, 1), (key338, 1), (key485, 1), (key479, 1), (key485, -1), (key473, -1)]

def rawRow391 : Integer.Sparse Key := [(key323, -2), (key334, 1), (key334, 1), (key309, 2), (key344, -1), (key344, -1), (key311, -1), (key311, -1), (key338, 1), (key338, 1), (key413, 2), (key424, -1), (key424, -1), (key243, -2), (key587, 1), (key587, 1), (key245, 1), (key245, 1), (key424, -1), (key424, -1), (key323, -2), (key599, 1), (key599, 1), (key255, 2), (key605, -1), (key605, -1), (key266, -1), (key266, -1), (key334, 1), (key334, 1), (key338, 1), (key338, 1), (key473, -1), (key473, -1), (key270, -1), (key270, -1), (key479, 1), (key479, 1), (key275, 1), (key275, 1), (key344, -1), (key344, -1)]

def rawRow392 : Integer.Sparse Key := [(key334, -2), (key323, 1), (key334, 1), (key344, 2), (key309, -1), (key344, -1), (key338, -1), (key345, -1), (key311, 1), (key345, 1), (key424, 2), (key413, -1), (key424, -1), (key587, -2), (key243, 1), (key587, 1), (key424, 1), (key588, 1), (key245, -1), (key588, -1), (key599, -2), (key323, 1), (key599, 1), (key605, 2), (key255, -1), (key605, -1), (key334, -1), (key611, -1), (key266, 1), (key611, 1), (key473, 1), (key613, 1), (key338, -1), (key613, -1), (key479, -1), (key614, -1), (key270, 1), (key614, 1), (key344, 1), (key616, 1), (key275, -1), (key616, -1)]

def rawRow393 : Integer.Sparse Key := [(key334, -2), (key334, 1), (key323, 1), (key344, 2), (key344, -1), (key309, -1), (key345, -1), (key338, -1), (key345, 1), (key311, 1), (key424, 2), (key424, -1), (key413, -1), (key587, -2), (key587, 1), (key243, 1), (key588, 1), (key424, 1), (key588, -1), (key245, -1), (key599, -2), (key599, 1), (key323, 1), (key605, 2), (key605, -1), (key255, -1), (key611, -1), (key334, -1), (key611, 1), (key266, 1), (key613, 1), (key473, 1), (key613, -1), (key338, -1), (key614, -1), (key479, -1), (key614, 1), (key270, 1), (key616, 1), (key344, 1), (key616, -1), (key275, -1)]

def rawRow394 : Integer.Sparse Key := [(key338, -2), (key344, 1), (key345, 1), (key311, 2), (key334, -1), (key345, -1), (key309, -1), (key311, -1), (key323, 1), (key338, 1), (key581, 2), (key587, -1), (key588, -1), (key245, -2), (key424, 1), (key588, 1), (key243, 1), (key245, 1), (key413, -1), (key424, -1), (key334, -2), (key605, 1), (key611, 1), (key266, 2), (key599, -1), (key611, -1), (key255, -1), (key266, -1), (key323, 1), (key334, 1), (key344, 1), (key345, 1), (key479, -1), (key485, -1), (key275, -1), (key276, -1), (key473, 1), (key485, 1), (key270, 1), (key276, 1), (key338, -1), (key345, -1)]

def rawRow395 : Integer.Sparse Key := [(key338, -2), (key345, 1), (key344, 1), (key311, 2), (key345, -1), (key334, -1), (key311, -1), (key309, -1), (key338, 1), (key323, 1), (key581, 2), (key588, -1), (key587, -1), (key245, -2), (key588, 1), (key424, 1), (key245, 1), (key243, 1), (key424, -1), (key413, -1), (key334, -2), (key611, 1), (key605, 1), (key266, 2), (key611, -1), (key599, -1), (key266, -1), (key255, -1), (key334, 1), (key323, 1), (key345, 1), (key344, 1), (key485, -1), (key479, -1), (key276, -1), (key275, -1), (key485, 1), (key473, 1), (key276, 1), (key270, 1), (key345, -1), (key338, -1)]

def rawRow396 : Integer.Sparse Key := [(key344, -2), (key338, 1), (key345, 1), (key334, 2), (key311, -1), (key345, -1), (key323, -1), (key334, -1), (key309, 1), (key344, 1), (key587, 2), (key581, -1), (key588, -1), (key424, -2), (key245, 1), (key588, 1), (key413, 1), (key424, 1), (key243, -1), (key587, -1), (key605, -2), (key334, 1), (key611, 1), (key599, 2), (key266, -1), (key611, -1), (key323, -1), (key599, -1), (key255, 1), (key605, 1), (key479, 1), (key614, 1), (key344, -1), (key616, -1), (key473, -1), (key613, -1), (key275, 1), (key616, 1), (key338, 1), (key613, 1), (key270, -1), (key614, -1)]

def rawRow397 : Integer.Sparse Key := [(key344, -2), (key345, 1), (key338, 1), (key334, 2), (key345, -1), (key311, -1), (key334, -1), (key323, -1), (key344, 1), (key309, 1), (key587, 2), (key588, -1), (key581, -1), (key424, -2), (key588, 1), (key245, 1), (key424, 1), (key413, 1), (key587, -1), (key243, -1), (key605, -2), (key611, 1), (key334, 1), (key599, 2), (key611, -1), (key266, -1), (key599, -1), (key323, -1), (key605, 1), (key255, 1), (key614, 1), (key479, 1), (key616, -1), (key344, -1), (key613, -1), (key473, -1), (key616, 1), (key275, 1), (key613, 1), (key338, 1), (key614, -1), (key270, -1)]

def rawRow398 : Integer.Sparse Key := [(key392, -2), (key403, 1), (key403, 1), (key413, 2), (key473, -1), (key473, -1), (key424, -1), (key424, -1), (key479, 1), (key479, 1), (key255, 2), (key266, -1), (key266, -1), (key323, -2), (key599, 1), (key599, 1), (key334, 1), (key334, 1), (key605, -1), (key605, -1), (key243, -2), (key275, 1), (key275, 1), (key309, 2), (key344, -1), (key344, -1), (key576, -1), (key576, -1), (key587, 1), (key587, 1), (key245, 1), (key245, 1), (key266, -1), (key266, -1), (key311, -1), (key311, -1), (key334, 1), (key334, 1), (key403, 1), (key403, 1), (key424, -1), (key424, -1)]

def rawRow399 : Integer.Sparse Key := [(key403, -2), (key392, 1), (key403, 1), (key473, 2), (key413, -1), (key473, -1), (key479, -1), (key485, -1), (key424, 1), (key485, 1), (key266, 2), (key255, -1), (key266, -1), (key599, -2), (key323, 1), (key599, 1), (key605, 1), (key611, 1), (key334, -1), (key611, -1), (key275, -2), (key243, 1), (key275, 1), (key344, 2), (key309, -1), (key344, -1), (key587, -1), (key616, -1), (key576, 1), (key616, 1), (key266, 1), (key276, 1), (key245, -1), (key276, -1), (key334, -1), (key345, -1), (key311, 1), (key345, 1), (key424, 1), (key485, 1), (key403, -1), (key485, -1)]

def rawRow400 : Integer.Sparse Key := [(key403, -2), (key403, 1), (key392, 1), (key473, 2), (key473, -1), (key413, -1), (key485, -1), (key479, -1), (key485, 1), (key424, 1), (key266, 2), (key266, -1), (key255, -1), (key599, -2), (key599, 1), (key323, 1), (key611, 1), (key605, 1), (key611, -1), (key334, -1), (key275, -2), (key275, 1), (key243, 1), (key344, 2), (key344, -1), (key309, -1), (key616, -1), (key587, -1), (key616, 1), (key576, 1), (key276, 1), (key266, 1), (key276, -1), (key245, -1), (key345, -1), (key334, -1), (key345, 1), (key311, 1), (key485, 1), (key424, 1), (key485, -1), (key403, -1)]

def rawRow401 : Integer.Sparse Key := [(key413, -2), (key424, 1), (key424, 1), (key392, 2), (key479, -1), (key479, -1), (key403, -1), (key403, -1), (key473, 1), (key473, 1), (key323, 2), (key334, -1), (key334, -1), (key255, -2), (key605, 1), (key605, 1), (key266, 1), (key266, 1), (key599, -1), (key599, -1), (key309, -2), (key344, 1), (key344, 1), (key243, 2), (key587, -1), (key587, -1), (key275, -1), (key275, -1), (key344, 1), (key344, 1), (key311, 1), (key311, 1), (key403, -1), (key403, -1), (key245, -1), (key245, -1), (key424, 1), (key424, 1), (key266, 1), (key266, 1), (key334, -1), (key334, -1)]

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


