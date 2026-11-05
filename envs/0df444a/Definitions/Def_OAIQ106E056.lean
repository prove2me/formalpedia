-- Prove2me | Definitions.Def_OAIQ106E056
-- name    : OAIQ106E056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:08:06.881205+00:00
-- url     : https://prove2.me/theorems/0b6187a0-232c-428b-87ad-67ff0c6d77d7
-- title:
--   Definitions bundle OAIQ106E056 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1947 declarations of OpenAI's Lean: 1947 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow7260`, `OAI.MUB6.Certificate.GramRows.rawRow7261`, `OAI.MUB6.Certificate.GramRows.rawRow7262`, `OAI.MUB6.Certificate.GramRows.rawRow7263`, `OAI.MUB6.Certificate.GramRows.rawRow7264`, `OAI.MUB6.Certificate.GramRows.rawRow7265`, `OAI.MUB6.Certificate.GramRows.rawRow7266`, `OAI.MUB6.Certificate.GramRows.rawRow7267`, `OAI.MUB6.Certificate.GramRows.rawRow7268`, `OAI.MUB6.Certificate.GramRows.rawRow7269`, `OAI.MUB6.Certificate.GramRows.rawRow7270`, `OAI.MUB6.Certificate.GramRows.rawRow7271`, `OAI.MUB6.Certificate.GramRows.rawRow7272`, `OAI.MUB6.Certificate.GramRows.rawRow7273`, `OAI.MUB6.Certificate.GramRows.rawRow7274`, `OAI.MUB6.Certificate.GramRows.rawRow7275`, `OAI.MUB6.Certificate.GramRows.rawRow7276`, `OAI.MUB6.Certificate.GramRows.rawRow7277`, `OAI.MUB6.Certificate.GramRows.rawRow7278`, `OAI.MUB6.Certificate.GramRows.rawRow7279`, `OAI.MUB6.Certificate.GramRows.rawRow7280`, `OAI.MUB6.Certificate.GramRows.rawRow7281`, `OAI.MUB6.Certificate.GramRows.rawRow7282`, `OAI.MUB6.Certificate.GramRows.rawRow7283`, `OAI.MUB6.Certificate.GramRows.rawRow7284`, `OAI.MUB6.Certificate.GramRows.rawRow7285`, `OAI.MUB6.Certificate.GramRows.rawRow7286`, `OAI.MUB6.Certificate.GramRows.rawRow7287`, `OAI.MUB6.Certificate.GramRows.rawRow7288`, `OAI.MUB6.Certificate.GramRows.rawRow7289`, `OAI.MUB6.Certificate.GramRows.rawRow7290`, `OAI.MUB6.Certificate.GramRows.rawRow7291`, `OAI.MUB6.Certificate.GramRows.rawRow7292`, `OAI.MUB6.Certificate.GramRows.rawRow7293`, `OAI.MUB6.Certificate.GramRows.rawRow7294`, `OAI.MUB6.Certificate.GramRows.rawRow7295`, `OAI.MUB6.Certificate.GramRows.rawRow7296`, `OAI.MUB6.Certificate.GramRows.rawRow7297`, `OAI.MUB6.Certificate.GramRows.rawRow7298`, `OAI.MUB6.Certificate.GramRows.rawRow7299` and 1907 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block19`, `MutuallyUnbiased_GramRows_Block20`, `MutuallyUnbiased_GramRows_Block21`, `MutuallyUnbiased_GramRows_Block22`, `MutuallyUnbiased_GramRows_Block23`, `MutuallyUnbiased_GramRows_Block24`, `MutuallyUnbiased_GramRows_Block25`, `MutuallyUnbiased_GramRows_Block80`, `MutuallyUnbiased_GramRows_Block81`, `MutuallyUnbiased_GramRows_Block82`, `MutuallyUnbiased_GramRows_Block83`, `MutuallyUnbiased_GramRows_Block84`, `MutuallyUnbiased_GramRows_Block85`, `MutuallyUnbiased_GramRows_Block86`, `MutuallyUnbiased_GramRows_Block87`, `MutuallyUnbiased_GramRows_Block88`, `MutuallyUnbiased_GramRows_Block89`, `MutuallyUnbiased_GramRows_Block90`, `MutuallyUnbiased_GramRows_Block91`, `MutuallyUnbiased_GramRows_Block92`, `MutuallyUnbiased_GramRows_Block93`, `MutuallyUnbiased_GramRows_Block94`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_8_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval10_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval13_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e`.
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

def rawRow8 : Integer.Sparse Key := [(key267, -1), (key271, -1), (key267, 2), (key251, 1), (key260, 1), (key239, -1), (key251, -1), (key248, -2), (key236, 1), (key248, 1), (key328, 1), (key340, 1), (key328, -2), (key319, -1), (key335, -1), (key305, 1), (key319, 1), (key316, 2), (key302, -1), (key316, -1), (key450, -1), (key475, -1), (key418, 1), (key450, 1), (key442, 1), (key469, 1), (key397, -1), (key442, -1), (key406, -1), (key435, -1), (key385, 1), (key435, 1), (key601, 2), (key583, -1), (key601, -1), (key595, -2), (key572, 1), (key595, 1), (key578, 1), (key593, 1), (key568, -1), (key593, -1)]

def rawRow9 : Integer.Sparse Key := [(key271, -1), (key267, -1), (key267, 2), (key260, 1), (key251, 1), (key251, -1), (key239, -1), (key248, -2), (key248, 1), (key236, 1), (key340, 1), (key328, 1), (key328, -2), (key335, -1), (key319, -1), (key319, 1), (key305, 1), (key316, 2), (key316, -1), (key302, -1), (key475, -1), (key450, -1), (key450, 1), (key418, 1), (key469, 1), (key442, 1), (key442, -1), (key397, -1), (key435, -1), (key406, -1), (key435, 1), (key385, 1), (key601, 2), (key601, -1), (key583, -1), (key595, -2), (key595, 1), (key572, 1), (key593, 1), (key578, 1), (key593, -1), (key568, -1)]

def rawRow73 : Integer.Sparse Key := [(key1774, -1), (key1772, -1), (key1780, 2), (key1790, 1), (key1788, 1), (key1841, -1), (key1817, -1), (key1798, -2), (key1844, 1), (key1825, 1), (key1339, 1), (key1337, 1), (key1345, -2), (key1457, -1), (key1455, -1), (key1841, 1), (key1659, 1), (key1466, 2), (key1844, -1), (key1667, -1), (key1302, -1), (key1296, -1), (key1345, 1), (key1329, 1), (key1397, 1), (key1391, 1), (key1780, -1), (key1559, -1), (key1466, -1), (key1447, -1), (key1798, 1), (key1596, 1), (key1296, 2), (key1337, -1), (key1316, -1), (key1391, -2), (key1772, 1), (key1546, 1), (key1455, 1), (key1424, 1), (key1788, -1), (key1573, -1)]

def rawRow74 : Integer.Sparse Key := [(key1772, -1), (key1780, -1), (key1774, 2), (key1813, 1), (key1817, 1), (key1790, -1), (key1839, -1), (key1825, -2), (key1798, 1), (key1844, 1), (key1337, 1), (key1345, 1), (key1339, -2), (key1655, -1), (key1659, -1), (key1457, 1), (key1839, 1), (key1667, 2), (key1466, -1), (key1844, -1), (key1316, -1), (key1329, -1), (key1302, 1), (key1339, 1), (key1546, 1), (key1559, 1), (key1397, -1), (key1774, -1), (key1596, -1), (key1667, -1), (key1447, 1), (key1825, 1), (key1316, 2), (key1296, -1), (key1337, -1), (key1546, -2), (key1391, 1), (key1772, 1), (key1573, 1), (key1655, 1), (key1424, -1), (key1813, -1)]

def rawRow75 : Integer.Sparse Key := [(key1780, -1), (key1772, -1), (key1774, 2), (key1817, 1), (key1813, 1), (key1839, -1), (key1790, -1), (key1825, -2), (key1844, 1), (key1798, 1), (key1345, 1), (key1337, 1), (key1339, -2), (key1659, -1), (key1655, -1), (key1839, 1), (key1457, 1), (key1667, 2), (key1844, -1), (key1466, -1), (key1329, -1), (key1316, -1), (key1339, 1), (key1302, 1), (key1559, 1), (key1546, 1), (key1774, -1), (key1397, -1), (key1667, -1), (key1596, -1), (key1825, 1), (key1447, 1), (key1316, 2), (key1337, -1), (key1296, -1), (key1546, -2), (key1772, 1), (key1391, 1), (key1655, 1), (key1573, 1), (key1813, -1), (key1424, -1)]

def rawRow76 : Integer.Sparse Key := [(key1788, -1), (key1790, -1), (key1798, 2), (key1772, 1), (key1774, 1), (key1825, -1), (key1844, -1), (key1780, -2), (key1817, 1), (key1841, 1), (key1455, 1), (key1457, 1), (key1466, -2), (key1337, -1), (key1339, -1), (key1667, 1), (key1844, 1), (key1345, 2), (key1659, -1), (key1841, -1), (key1391, -1), (key1397, -1), (key1447, 1), (key1466, 1), (key1296, 1), (key1302, 1), (key1596, -1), (key1798, -1), (key1329, -1), (key1345, -1), (key1559, 1), (key1780, 1), (key1391, 2), (key1424, -1), (key1455, -1), (key1296, -2), (key1573, 1), (key1788, 1), (key1316, 1), (key1337, 1), (key1546, -1), (key1772, -1)]

def rawRow77 : Integer.Sparse Key := [(key1790, -1), (key1788, -1), (key1798, 2), (key1774, 1), (key1772, 1), (key1844, -1), (key1825, -1), (key1780, -2), (key1841, 1), (key1817, 1), (key1457, 1), (key1455, 1), (key1466, -2), (key1339, -1), (key1337, -1), (key1844, 1), (key1667, 1), (key1345, 2), (key1841, -1), (key1659, -1), (key1397, -1), (key1391, -1), (key1466, 1), (key1447, 1), (key1302, 1), (key1296, 1), (key1798, -1), (key1596, -1), (key1345, -1), (key1329, -1), (key1780, 1), (key1559, 1), (key1391, 2), (key1455, -1), (key1424, -1), (key1296, -2), (key1788, 1), (key1573, 1), (key1337, 1), (key1316, 1), (key1772, -1), (key1546, -1)]

def rawRow78 : Integer.Sparse Key := [(key1788, -1), (key1798, -1), (key1790, 2), (key1813, 1), (key1825, 1), (key1774, -1), (key1839, -1), (key1817, -2), (key1780, 1), (key1841, 1), (key1455, 1), (key1466, 1), (key1457, -2), (key1655, -1), (key1667, -1), (key1339, 1), (key1839, 1), (key1659, 2), (key1345, -1), (key1841, -1), (key1424, -1), (key1447, -1), (key1397, 1), (key1457, 1), (key1573, 1), (key1596, 1), (key1302, -1), (key1790, -1), (key1559, -1), (key1659, -1), (key1329, 1), (key1817, 1), (key1424, 2), (key1391, -1), (key1455, -1), (key1573, -2), (key1296, 1), (key1788, 1), (key1546, 1), (key1655, 1), (key1316, -1), (key1813, -1)]

def rawRow79 : Integer.Sparse Key := [(key1798, -1), (key1788, -1), (key1790, 2), (key1825, 1), (key1813, 1), (key1839, -1), (key1774, -1), (key1817, -2), (key1841, 1), (key1780, 1), (key1466, 1), (key1455, 1), (key1457, -2), (key1667, -1), (key1655, -1), (key1839, 1), (key1339, 1), (key1659, 2), (key1841, -1), (key1345, -1), (key1447, -1), (key1424, -1), (key1457, 1), (key1397, 1), (key1596, 1), (key1573, 1), (key1790, -1), (key1302, -1), (key1659, -1), (key1559, -1), (key1817, 1), (key1329, 1), (key1424, 2), (key1455, -1), (key1391, -1), (key1573, -2), (key1788, 1), (key1296, 1), (key1655, 1), (key1546, 1), (key1813, -1), (key1316, -1)]

def rawRow80 : Integer.Sparse Key := [(key1813, -1), (key1817, -1), (key1825, 2), (key1772, 1), (key1780, 1), (key1798, -1), (key1844, -1), (key1774, -2), (key1790, 1), (key1839, 1), (key1655, 1), (key1659, 1), (key1667, -2), (key1337, -1), (key1345, -1), (key1466, 1), (key1844, 1), (key1339, 2), (key1457, -1), (key1839, -1), (key1546, -1), (key1559, -1), (key1596, 1), (key1667, 1), (key1316, 1), (key1329, 1), (key1447, -1), (key1825, -1), (key1302, -1), (key1339, -1), (key1397, 1), (key1774, 1), (key1546, 2), (key1573, -1), (key1655, -1), (key1316, -2), (key1424, 1), (key1813, 1), (key1296, 1), (key1337, 1), (key1391, -1), (key1772, -1)]

def rawRow81 : Integer.Sparse Key := [(key1817, -1), (key1813, -1), (key1825, 2), (key1780, 1), (key1772, 1), (key1844, -1), (key1798, -1), (key1774, -2), (key1839, 1), (key1790, 1), (key1659, 1), (key1655, 1), (key1667, -2), (key1345, -1), (key1337, -1), (key1844, 1), (key1466, 1), (key1339, 2), (key1839, -1), (key1457, -1), (key1559, -1), (key1546, -1), (key1667, 1), (key1596, 1), (key1329, 1), (key1316, 1), (key1825, -1), (key1447, -1), (key1339, -1), (key1302, -1), (key1774, 1), (key1397, 1), (key1546, 2), (key1655, -1), (key1573, -1), (key1316, -2), (key1813, 1), (key1424, 1), (key1337, 1), (key1296, 1), (key1772, -1), (key1391, -1)]

def rawRow82 : Integer.Sparse Key := [(key1813, -1), (key1825, -1), (key1817, 2), (key1788, 1), (key1798, 1), (key1780, -1), (key1841, -1), (key1790, -2), (key1774, 1), (key1839, 1), (key1655, 1), (key1667, 1), (key1659, -2), (key1455, -1), (key1466, -1), (key1345, 1), (key1841, 1), (key1457, 2), (key1339, -1), (key1839, -1), (key1573, -1), (key1596, -1), (key1559, 1), (key1659, 1), (key1424, 1), (key1447, 1), (key1329, -1), (key1817, -1), (key1397, -1), (key1457, -1), (key1302, 1), (key1790, 1), (key1573, 2), (key1546, -1), (key1655, -1), (key1424, -2), (key1316, 1), (key1813, 1), (key1391, 1), (key1455, 1), (key1296, -1), (key1788, -1)]

def rawRow83 : Integer.Sparse Key := [(key1825, -1), (key1813, -1), (key1817, 2), (key1798, 1), (key1788, 1), (key1841, -1), (key1780, -1), (key1790, -2), (key1839, 1), (key1774, 1), (key1667, 1), (key1655, 1), (key1659, -2), (key1466, -1), (key1455, -1), (key1841, 1), (key1345, 1), (key1457, 2), (key1839, -1), (key1339, -1), (key1596, -1), (key1573, -1), (key1659, 1), (key1559, 1), (key1447, 1), (key1424, 1), (key1817, -1), (key1329, -1), (key1457, -1), (key1397, -1), (key1790, 1), (key1302, 1), (key1573, 2), (key1655, -1), (key1546, -1), (key1424, -2), (key1813, 1), (key1316, 1), (key1455, 1), (key1391, 1), (key1788, -1), (key1296, -1)]

def rawRow84 : Integer.Sparse Key := [(key2617, -2), (key2620, 1), (key2620, 1), (key2633, 2), (key2643, -1), (key2643, -1), (key2650, -1), (key2650, -1), (key2655, 1), (key2655, 1), (key2672, 2), (key2675, -1), (key2675, -1), (key2707, -2), (key2730, 1), (key2730, 1), (key2739, 1), (key2739, 1), (key2749, -1), (key2749, -1), (key2787, -2), (key2797, 1), (key2797, 1), (key2810, 2), (key2833, -1), (key2833, -1), (key2899, -1), (key2899, -1), (key2906, 1), (key2906, 1), (key2940, 1), (key2940, 1), (key2945, -1), (key2945, -1), (key2952, -1), (key2952, -1), (key2962, 1), (key2962, 1), (key2978, 1), (key2978, 1), (key2985, -1), (key2985, -1)]

def rawRow85 : Integer.Sparse Key := [(key2620, -2), (key2617, 1), (key2620, 1), (key2643, 2), (key2633, -1), (key2643, -1), (key2655, -1), (key2656, -1), (key2650, 1), (key2656, 1), (key2675, 2), (key2672, -1), (key2675, -1), (key2730, -2), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, 1), (key2739, -1), (key2751, -1), (key2797, -2), (key2787, 1), (key2797, 1), (key2833, 2), (key2810, -1), (key2833, -1), (key2906, -1), (key2915, -1), (key2899, 1), (key2915, 1), (key2945, 1), (key2946, 1), (key2940, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2952, 1), (key2964, 1), (key2985, 1), (key2994, 1), (key2978, -1), (key2994, -1)]

def rawRow86 : Integer.Sparse Key := [(key2620, -2), (key2620, 1), (key2617, 1), (key2643, 2), (key2643, -1), (key2633, -1), (key2656, -1), (key2655, -1), (key2656, 1), (key2650, 1), (key2675, 2), (key2675, -1), (key2672, -1), (key2730, -2), (key2730, 1), (key2707, 1), (key2751, 1), (key2749, 1), (key2751, -1), (key2739, -1), (key2797, -2), (key2797, 1), (key2787, 1), (key2833, 2), (key2833, -1), (key2810, -1), (key2915, -1), (key2906, -1), (key2915, 1), (key2899, 1), (key2946, 1), (key2945, 1), (key2946, -1), (key2940, -1), (key2964, -1), (key2962, -1), (key2964, 1), (key2952, 1), (key2994, 1), (key2985, 1), (key2994, -1), (key2978, -1)]

def rawRow87 : Integer.Sparse Key := [(key2633, -2), (key2643, 1), (key2643, 1), (key2617, 2), (key2655, -1), (key2655, -1), (key2620, -1), (key2620, -1), (key2643, 1), (key2643, 1), (key2707, 2), (key2739, -1), (key2739, -1), (key2672, -2), (key2749, 1), (key2749, 1), (key2675, 1), (key2675, 1), (key2730, -1), (key2730, -1), (key2810, -2), (key2899, 1), (key2899, 1), (key2787, 2), (key2906, -1), (key2906, -1), (key2797, -1), (key2797, -1), (key2833, 1), (key2833, 1), (key2952, 1), (key2952, 1), (key2978, -1), (key2978, -1), (key2940, -1), (key2940, -1), (key2985, 1), (key2985, 1), (key2945, 1), (key2945, 1), (key2962, -1), (key2962, -1)]

def rawRow88 : Integer.Sparse Key := [(key2643, -2), (key2633, 1), (key2643, 1), (key2655, 2), (key2617, -1), (key2655, -1), (key2643, -1), (key2656, -1), (key2620, 1), (key2656, 1), (key2739, 2), (key2707, -1), (key2739, -1), (key2749, -2), (key2672, 1), (key2749, 1), (key2730, 1), (key2751, 1), (key2675, -1), (key2751, -1), (key2899, -2), (key2810, 1), (key2899, 1), (key2906, 2), (key2787, -1), (key2906, -1), (key2833, -1), (key2915, -1), (key2797, 1), (key2915, 1), (key2978, 1), (key2999, 1), (key2952, -1), (key2999, -1), (key2985, -1), (key3001, -1), (key2940, 1), (key3001, 1), (key2962, 1), (key3004, 1), (key2945, -1), (key3004, -1)]

def rawRow89 : Integer.Sparse Key := [(key2643, -2), (key2643, 1), (key2633, 1), (key2655, 2), (key2655, -1), (key2617, -1), (key2656, -1), (key2643, -1), (key2656, 1), (key2620, 1), (key2739, 2), (key2739, -1), (key2707, -1), (key2749, -2), (key2749, 1), (key2672, 1), (key2751, 1), (key2730, 1), (key2751, -1), (key2675, -1), (key2899, -2), (key2899, 1), (key2810, 1), (key2906, 2), (key2906, -1), (key2787, -1), (key2915, -1), (key2833, -1), (key2915, 1), (key2797, 1), (key2999, 1), (key2978, 1), (key2999, -1), (key2952, -1), (key3001, -1), (key2985, -1), (key3001, 1), (key2940, 1), (key3004, 1), (key2962, 1), (key3004, -1), (key2945, -1)]

def rawRow90 : Integer.Sparse Key := [(key2650, -2), (key2655, 1), (key2656, 1), (key2620, 2), (key2643, -1), (key2656, -1), (key2617, -1), (key2620, -1), (key2633, 1), (key2643, 1), (key2730, 2), (key2749, -1), (key2751, -1), (key2675, -2), (key2739, 1), (key2751, 1), (key2672, 1), (key2675, 1), (key2707, -1), (key2730, -1), (key2833, -2), (key2906, 1), (key2915, 1), (key2797, 2), (key2899, -1), (key2915, -1), (key2787, -1), (key2797, -1), (key2810, 1), (key2833, 1), (key2962, 1), (key2964, 1), (key2985, -1), (key2994, -1), (key2945, -1), (key2946, -1), (key2978, 1), (key2994, 1), (key2940, 1), (key2946, 1), (key2952, -1), (key2964, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow730 : Integer.Sparse Key := [(key1417, -6), (key1384, 2), (key1417, 2), (key1471, 2), (key1566, 6), (key1289, -2), (key1566, -2), (key1902, -2), (key1539, -2), (key1615, -2), (key1680, -2), (key1309, 2), (key1615, 2), (key1917, 2)]

def rawRow731 : Integer.Sparse Key := [(key1417, -6), (key1384, 2), (key1471, 2), (key1417, 2), (key1566, 6), (key1289, -2), (key1902, -2), (key1566, -2), (key1539, -2), (key1680, -2), (key1615, -2), (key1309, 2), (key1917, 2), (key1615, 2)]

def rawRow732 : Integer.Sparse Key := [(key1417, -6), (key1417, 2), (key1384, 2), (key1471, 2), (key1566, 6), (key1566, -2), (key1289, -2), (key1902, -2), (key1615, -2), (key1539, -2), (key1680, -2), (key1615, 2), (key1309, 2), (key1917, 2)]

def rawRow733 : Integer.Sparse Key := [(key1417, -6), (key1417, 2), (key1471, 2), (key1384, 2), (key1566, 6), (key1566, -2), (key1902, -2), (key1289, -2), (key1615, -2), (key1680, -2), (key1539, -2), (key1615, 2), (key1917, 2), (key1309, 2)]

def rawRow734 : Integer.Sparse Key := [(key1417, -6), (key1471, 2), (key1384, 2), (key1417, 2), (key1566, 6), (key1902, -2), (key1289, -2), (key1566, -2), (key1680, -2), (key1539, -2), (key1615, -2), (key1917, 2), (key1309, 2), (key1615, 2)]

def rawRow735 : Integer.Sparse Key := [(key1417, -6), (key1471, 2), (key1417, 2), (key1384, 2), (key1566, 6), (key1902, -2), (key1566, -2), (key1289, -2), (key1680, -2), (key1615, -2), (key1539, -2), (key1917, 2), (key1615, 2), (key1309, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow736 : Integer.Sparse Key := [(key1539, -6), (key1566, 2), (key1615, 2), (key1680, 2), (key1309, 6), (key1417, -2), (key1615, -2), (key1917, -2), (key1289, -2), (key1309, -2), (key1350, -2), (key1384, 2), (key1539, 2), (key1895, 2)]

def rawRow737 : Integer.Sparse Key := [(key1539, -6), (key1566, 2), (key1680, 2), (key1615, 2), (key1309, 6), (key1417, -2), (key1917, -2), (key1615, -2), (key1289, -2), (key1350, -2), (key1309, -2), (key1384, 2), (key1895, 2), (key1539, 2)]

def rawRow738 : Integer.Sparse Key := [(key1539, -6), (key1615, 2), (key1566, 2), (key1680, 2), (key1309, 6), (key1615, -2), (key1417, -2), (key1917, -2), (key1309, -2), (key1289, -2), (key1350, -2), (key1539, 2), (key1384, 2), (key1895, 2)]

def rawRow739 : Integer.Sparse Key := [(key1539, -6), (key1615, 2), (key1680, 2), (key1566, 2), (key1309, 6), (key1615, -2), (key1917, -2), (key1417, -2), (key1309, -2), (key1350, -2), (key1289, -2), (key1539, 2), (key1895, 2), (key1384, 2)]

def rawRow740 : Integer.Sparse Key := [(key1539, -6), (key1680, 2), (key1566, 2), (key1615, 2), (key1309, 6), (key1917, -2), (key1417, -2), (key1615, -2), (key1350, -2), (key1289, -2), (key1309, -2), (key1895, 2), (key1384, 2), (key1539, 2)]

def rawRow741 : Integer.Sparse Key := [(key1539, -6), (key1680, 2), (key1615, 2), (key1566, 2), (key1309, 6), (key1917, -2), (key1615, -2), (key1417, -2), (key1350, -2), (key1309, -2), (key1289, -2), (key1895, 2), (key1539, 2), (key1384, 2)]

def rawRow742 : Integer.Sparse Key := [(key1566, -6), (key1539, 2), (key1615, 2), (key1680, 2), (key1417, 6), (key1309, -2), (key1615, -2), (key1917, -2), (key1384, -2), (key1417, -2), (key1471, -2), (key1289, 2), (key1566, 2), (key1902, 2)]

def rawRow743 : Integer.Sparse Key := [(key1566, -6), (key1539, 2), (key1680, 2), (key1615, 2), (key1417, 6), (key1309, -2), (key1917, -2), (key1615, -2), (key1384, -2), (key1471, -2), (key1417, -2), (key1289, 2), (key1902, 2), (key1566, 2)]

def rawRow744 : Integer.Sparse Key := [(key1566, -6), (key1615, 2), (key1539, 2), (key1680, 2), (key1417, 6), (key1615, -2), (key1309, -2), (key1917, -2), (key1417, -2), (key1384, -2), (key1471, -2), (key1566, 2), (key1289, 2), (key1902, 2)]

def rawRow745 : Integer.Sparse Key := [(key1566, -6), (key1615, 2), (key1680, 2), (key1539, 2), (key1417, 6), (key1615, -2), (key1917, -2), (key1309, -2), (key1417, -2), (key1471, -2), (key1384, -2), (key1566, 2), (key1902, 2), (key1289, 2)]

def rawRow746 : Integer.Sparse Key := [(key1566, -6), (key1680, 2), (key1539, 2), (key1615, 2), (key1417, 6), (key1917, -2), (key1309, -2), (key1615, -2), (key1471, -2), (key1384, -2), (key1417, -2), (key1902, 2), (key1289, 2), (key1566, 2)]

def rawRow747 : Integer.Sparse Key := [(key1566, -6), (key1680, 2), (key1615, 2), (key1539, 2), (key1417, 6), (key1917, -2), (key1615, -2), (key1309, -2), (key1471, -2), (key1417, -2), (key1384, -2), (key1902, 2), (key1566, 2), (key1289, 2)]

def rawRow748 : Integer.Sparse Key := [(key2608, -2), (key2614, -2), (key2614, -2), (key2624, 1), (key2630, 1), (key2624, 1), (key2638, 1), (key2630, 1), (key2638, 1), (key2663, 2), (key2669, 2), (key2669, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2778, -1), (key2784, -1), (key2778, -1), (key2792, -1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, 1), (key2801, 1), (key2827, 1), (key2807, 1), (key2827, 1)]

def rawRow749 : Integer.Sparse Key := [(key2614, -2), (key2608, -2), (key2614, -2), (key2630, 1), (key2624, 1), (key2638, 1), (key2624, 1), (key2638, 1), (key2630, 1), (key2669, 2), (key2663, 2), (key2669, 2), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2784, -1), (key2778, -1), (key2792, -1), (key2778, -1), (key2792, -1), (key2784, -1), (key2807, 1), (key2801, 1), (key2827, 1), (key2801, 1), (key2827, 1), (key2807, 1)]

def rawRow750 : Integer.Sparse Key := [(key2614, -2), (key2614, -2), (key2608, -2), (key2638, 1), (key2638, 1), (key2630, 1), (key2630, 1), (key2624, 1), (key2624, 1), (key2669, 2), (key2669, 2), (key2663, 2), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2792, -1), (key2792, -1), (key2784, -1), (key2784, -1), (key2778, -1), (key2778, -1), (key2827, 1), (key2827, 1), (key2807, 1), (key2807, 1), (key2801, 1), (key2801, 1)]

def rawRow751 : Integer.Sparse Key := [(key2624, -2), (key2630, -2), (key2638, -2), (key2608, 1), (key2614, 1), (key2624, 1), (key2638, 1), (key2657, 1), (key2659, 1), (key2698, 2), (key2704, 2), (key2752, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, -1), (key2851, -1), (key2858, -1), (key2918, -1), (key2919, -1), (key2778, 1), (key2784, 1), (key2851, 1), (key2868, 1), (key2918, 1), (key2922, 1)]

def rawRow752 : Integer.Sparse Key := [(key2630, -2), (key2624, -2), (key2638, -2), (key2614, 1), (key2608, 1), (key2638, 1), (key2624, 1), (key2659, 1), (key2657, 1), (key2704, 2), (key2698, 2), (key2752, 2), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2807, -1), (key2801, -1), (key2858, -1), (key2851, -1), (key2919, -1), (key2918, -1), (key2784, 1), (key2778, 1), (key2868, 1), (key2851, 1), (key2922, 1), (key2918, 1)]

def rawRow753 : Integer.Sparse Key := [(key2624, -2), (key2638, -2), (key2630, -2), (key2624, 1), (key2638, 1), (key2608, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2698, 2), (key2752, 2), (key2704, 2), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2851, -1), (key2918, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2851, 1), (key2918, 1), (key2778, 1), (key2922, 1), (key2784, 1), (key2868, 1)]

def rawRow754 : Integer.Sparse Key := [(key2638, -2), (key2624, -2), (key2630, -2), (key2638, 1), (key2624, 1), (key2659, 1), (key2608, 1), (key2638, 1), (key2614, 1), (key2752, 2), (key2698, 2), (key2704, 2), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2858, -1), (key2807, -1), (key2918, 1), (key2851, 1), (key2922, 1), (key2778, 1), (key2868, 1), (key2784, 1)]

def rawRow755 : Integer.Sparse Key := [(key2630, -2), (key2638, -2), (key2624, -2), (key2657, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2608, 1), (key2624, 1), (key2704, 2), (key2752, 2), (key2698, 2), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2858, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2801, -1), (key2851, -1), (key2868, 1), (key2922, 1), (key2784, 1), (key2918, 1), (key2778, 1), (key2851, 1)]

def rawRow756 : Integer.Sparse Key := [(key2638, -2), (key2630, -2), (key2624, -2), (key2659, 1), (key2657, 1), (key2638, 1), (key2614, 1), (key2624, 1), (key2608, 1), (key2752, 2), (key2704, 2), (key2698, 2), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2919, -1), (key2858, -1), (key2918, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, 1), (key2868, 1), (key2918, 1), (key2784, 1), (key2851, 1), (key2778, 1)]

def rawRow757 : Integer.Sparse Key := [(key2663, -2), (key2669, -2), (key2669, -2), (key2698, 1), (key2704, 1), (key2698, 1), (key2752, 1), (key2704, 1), (key2752, 1), (key2608, 2), (key2614, 2), (key2614, 2), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2624, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2698, 1), (key2704, 1), (key2698, 1), (key2724, 1), (key2704, 1), (key2724, 1)]

def rawRow758 : Integer.Sparse Key := [(key2669, -2), (key2663, -2), (key2669, -2), (key2704, 1), (key2698, 1), (key2752, 1), (key2698, 1), (key2752, 1), (key2704, 1), (key2614, 2), (key2608, 2), (key2614, 2), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2630, -1), (key2624, -1), (key2638, -1), (key2624, -1), (key2638, -1), (key2630, -1), (key2704, 1), (key2698, 1), (key2724, 1), (key2698, 1), (key2724, 1), (key2704, 1)]

def rawRow759 : Integer.Sparse Key := [(key2669, -2), (key2669, -2), (key2663, -2), (key2752, 1), (key2752, 1), (key2704, 1), (key2704, 1), (key2698, 1), (key2698, 1), (key2614, 2), (key2614, 2), (key2608, 2), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2638, -1), (key2638, -1), (key2630, -1), (key2630, -1), (key2624, -1), (key2624, -1), (key2724, 1), (key2724, 1), (key2704, 1), (key2704, 1), (key2698, 1), (key2698, 1)]

def rawRow760 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2663, 1), (key2669, 1), (key2698, 1), (key2752, 1), (key2724, 1), (key2757, 1), (key2801, 2), (key2807, 2), (key2827, 2), (key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2698, -1), (key2704, -1), (key2851, -1), (key2858, -1), (key3021, -1), (key3022, -1), (key2624, 1), (key2630, 1), (key2851, 1), (key2868, 1), (key3021, 1), (key3025, 1)]

def rawRow761 : Integer.Sparse Key := [(key2704, -2), (key2698, -2), (key2724, -2), (key2669, 1), (key2663, 1), (key2752, 1), (key2698, 1), (key2757, 1), (key2724, 1), (key2807, 2), (key2801, 2), (key2827, 2), (key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2704, -1), (key2698, -1), (key2858, -1), (key2851, -1), (key3022, -1), (key3021, -1), (key2630, 1), (key2624, 1), (key2868, 1), (key2851, 1), (key3025, 1), (key3021, 1)]

def rawRow762 : Integer.Sparse Key := [(key2698, -2), (key2724, -2), (key2704, -2), (key2698, 1), (key2724, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2801, 2), (key2827, 2), (key2807, 2), (key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2851, -1), (key3021, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2851, 1), (key3021, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key2868, 1)]

def rawRow763 : Integer.Sparse Key := [(key2724, -2), (key2698, -2), (key2704, -2), (key2724, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2752, 1), (key2669, 1), (key2827, 2), (key2801, 2), (key2807, 2), (key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key2858, -1), (key2704, -1), (key3021, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key2868, 1), (key2630, 1)]

def rawRow764 : Integer.Sparse Key := [(key2704, -2), (key2724, -2), (key2698, -2), (key2752, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2663, 1), (key2698, 1), (key2807, 2), (key2827, 2), (key2801, 2), (key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2858, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2698, -1), (key2851, -1), (key2868, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2624, 1), (key2851, 1)]

def rawRow765 : Integer.Sparse Key := [(key2724, -2), (key2704, -2), (key2698, -2), (key2757, 1), (key2752, 1), (key2724, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2827, 2), (key2807, 2), (key2801, 2), (key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key3022, -1), (key2858, -1), (key3021, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, 1), (key2868, 1), (key3021, 1), (key2630, 1), (key2851, 1), (key2624, 1)]

def rawRow766 : Integer.Sparse Key := [(key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2851, 1), (key2918, 1), (key2858, 1), (key2919, 1), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, -1), (key2704, -1), (key2851, -1), (key3021, -1), (key2858, -1), (key3022, -1), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1)]

def rawRow767 : Integer.Sparse Key := [(key2784, -2), (key2778, -2), (key2792, -2), (key2807, 1), (key2801, 1), (key2918, 1), (key2851, 1), (key2919, 1), (key2858, 1), (key2630, 2), (key2624, 2), (key2638, 2), (key2704, -1), (key2698, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2858, -1), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow768 : Integer.Sparse Key := [(key2778, -2), (key2792, -2), (key2784, -2), (key2851, 1), (key2858, 1), (key2801, 1), (key2919, 1), (key2807, 1), (key2918, 1), (key2624, 2), (key2638, 2), (key2630, 2), (key2851, -1), (key2858, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1)]

def rawRow769 : Integer.Sparse Key := [(key2792, -2), (key2778, -2), (key2784, -2), (key2858, 1), (key2851, 1), (key2919, 1), (key2801, 1), (key2918, 1), (key2807, 1), (key2638, 2), (key2624, 2), (key2630, 2), (key2858, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key3021, -1), (key2704, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1)]

def rawRow770 : Integer.Sparse Key := [(key2784, -2), (key2792, -2), (key2778, -2), (key2918, 1), (key2919, 1), (key2807, 1), (key2858, 1), (key2801, 1), (key2851, 1), (key2630, 2), (key2638, 2), (key2624, 2), (key3021, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1)]

def rawRow771 : Integer.Sparse Key := [(key2792, -2), (key2784, -2), (key2778, -2), (key2919, 1), (key2918, 1), (key2858, 1), (key2807, 1), (key2851, 1), (key2801, 1), (key2638, 2), (key2630, 2), (key2624, 2), (key3022, -1), (key3021, -1), (key2858, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1)]

def rawRow772 : Integer.Sparse Key := [(key2801, -2), (key2807, -2), (key2827, -2), (key2778, 1), (key2784, 1), (key2851, 1), (key2918, 1), (key2868, 1), (key2922, 1), (key2698, 2), (key2704, 2), (key2724, 2), (key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1)]

def rawRow773 : Integer.Sparse Key := [(key2807, -2), (key2801, -2), (key2827, -2), (key2784, 1), (key2778, 1), (key2918, 1), (key2851, 1), (key2922, 1), (key2868, 1), (key2704, 2), (key2698, 2), (key2724, 2), (key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1)]

def rawRow774 : Integer.Sparse Key := [(key2801, -2), (key2827, -2), (key2807, -2), (key2851, 1), (key2868, 1), (key2778, 1), (key2922, 1), (key2784, 1), (key2918, 1), (key2698, 2), (key2724, 2), (key2704, 2), (key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1)]

def rawRow775 : Integer.Sparse Key := [(key2827, -2), (key2801, -2), (key2807, -2), (key2868, 1), (key2851, 1), (key2922, 1), (key2778, 1), (key2918, 1), (key2784, 1), (key2724, 2), (key2698, 2), (key2704, 2), (key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1)]

def rawRow776 : Integer.Sparse Key := [(key2807, -2), (key2827, -2), (key2801, -2), (key2918, 1), (key2922, 1), (key2784, 1), (key2868, 1), (key2778, 1), (key2851, 1), (key2704, 2), (key2724, 2), (key2698, 2), (key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1)]

def rawRow777 : Integer.Sparse Key := [(key2827, -2), (key2807, -2), (key2801, -2), (key2922, 1), (key2918, 1), (key2868, 1), (key2784, 1), (key2851, 1), (key2778, 1), (key2724, 2), (key2704, 2), (key2698, 2), (key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1)]

def rawRow778 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1076, -2), (key1033, 1), (key1041, 1), (key1033, 1), (key1076, 1), (key1041, 1), (key1076, 1), (key1111, 2), (key1111, 2), (key1155, 2), (key1111, -1), (key1127, -1), (key1111, -1), (key1155, -1), (key1127, -1), (key1155, -1), (key1190, -1), (key1193, -1), (key1190, -1), (key1212, -1), (key1193, -1), (key1212, -1), (key1190, 1), (key1199, 1), (key1190, 1), (key1212, 1), (key1199, 1), (key1212, 1)]

def rawRow779 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1033, -2), (key1041, 1), (key1033, 1), (key1076, 1), (key1033, 1), (key1076, 1), (key1041, 1), (key1111, 2), (key1155, 2), (key1111, 2), (key1127, -1), (key1111, -1), (key1155, -1), (key1111, -1), (key1155, -1), (key1127, -1), (key1193, -1), (key1190, -1), (key1212, -1), (key1190, -1), (key1212, -1), (key1193, -1), (key1199, 1), (key1190, 1), (key1212, 1), (key1190, 1), (key1212, 1), (key1199, 1)]

def rawRow780 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1033, -2), (key1076, 1), (key1076, 1), (key1041, 1), (key1041, 1), (key1033, 1), (key1033, 1), (key1155, 2), (key1111, 2), (key1111, 2), (key1155, -1), (key1155, -1), (key1127, -1), (key1127, -1), (key1111, -1), (key1111, -1), (key1212, -1), (key1212, -1), (key1193, -1), (key1193, -1), (key1190, -1), (key1190, -1), (key1212, 1), (key1212, 1), (key1199, 1), (key1199, 1), (key1190, 1), (key1190, 1)]

def rawRow781 : Integer.Sparse Key := [(key1041, -2), (key1041, -2), (key1041, -2), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1127, 2), (key1127, 2), (key1127, 2), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1193, 1), (key1193, 1), (key1193, 1), (key1193, 1), (key1193, 1), (key1193, 1)]

def rawRow782 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1155, -2), (key1190, 1), (key1193, 1), (key1190, 1), (key1212, 1), (key1193, 1), (key1212, 1), (key1033, 2), (key1033, 2), (key1076, 2), (key1190, -1), (key1199, -1), (key1190, -1), (key1212, -1), (key1199, -1), (key1212, -1), (key1033, -1), (key1041, -1), (key1033, -1), (key1076, -1), (key1041, -1), (key1076, -1), (key1111, 1), (key1127, 1), (key1111, 1), (key1155, 1), (key1127, 1), (key1155, 1)]

def rawRow783 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1111, -2), (key1193, 1), (key1190, 1), (key1212, 1), (key1190, 1), (key1212, 1), (key1193, 1), (key1033, 2), (key1076, 2), (key1033, 2), (key1199, -1), (key1190, -1), (key1212, -1), (key1190, -1), (key1212, -1), (key1199, -1), (key1041, -1), (key1033, -1), (key1076, -1), (key1033, -1), (key1076, -1), (key1041, -1), (key1127, 1), (key1111, 1), (key1155, 1), (key1111, 1), (key1155, 1), (key1127, 1)]

def rawRow784 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1111, -2), (key1212, 1), (key1212, 1), (key1193, 1), (key1193, 1), (key1190, 1), (key1190, 1), (key1076, 2), (key1033, 2), (key1033, 2), (key1212, -1), (key1212, -1), (key1199, -1), (key1199, -1), (key1190, -1), (key1190, -1), (key1076, -1), (key1076, -1), (key1041, -1), (key1041, -1), (key1033, -1), (key1033, -1), (key1155, 1), (key1155, 1), (key1127, 1), (key1127, 1), (key1111, 1), (key1111, 1)]

def rawRow785 : Integer.Sparse Key := [(key1006, -2), (key1193, -2), (key1193, -2), (key998, 1), (key998, 1), (key1111, 1), (key1111, 1), (key1190, 1), (key1190, 1), (key1019, 2), (key1199, 2), (key1199, 2), (key998, -1), (key998, -1), (key1033, -1), (key1033, -1), (key1190, -1), (key1190, -1), (key1019, -1), (key1019, -1), (key1127, -1), (key1127, -1), (key1199, -1), (key1199, -1), (key1006, 1), (key1006, 1), (key1041, 1), (key1041, 1), (key1193, 1), (key1193, 1)]

def rawRow786 : Integer.Sparse Key := [(key1193, -2), (key1006, -2), (key1193, -2), (key1111, 1), (key1190, 1), (key998, 1), (key1190, 1), (key998, 1), (key1111, 1), (key1199, 2), (key1019, 2), (key1199, 2), (key1033, -1), (key1190, -1), (key998, -1), (key1190, -1), (key998, -1), (key1033, -1), (key1127, -1), (key1199, -1), (key1019, -1), (key1199, -1), (key1019, -1), (key1127, -1), (key1041, 1), (key1193, 1), (key1006, 1), (key1193, 1), (key1006, 1), (key1041, 1)]

def rawRow787 : Integer.Sparse Key := [(key1193, -2), (key1193, -2), (key1006, -2), (key1190, 1), (key1111, 1), (key1190, 1), (key998, 1), (key1111, 1), (key998, 1), (key1199, 2), (key1199, 2), (key1019, 2), (key1190, -1), (key1033, -1), (key1190, -1), (key998, -1), (key1033, -1), (key998, -1), (key1199, -1), (key1127, -1), (key1199, -1), (key1019, -1), (key1127, -1), (key1019, -1), (key1193, 1), (key1041, 1), (key1193, 1), (key1006, 1), (key1041, 1), (key1006, 1)]

def rawRow788 : Integer.Sparse Key := [(key1127, -2), (key1127, -2), (key1127, -2), (key1199, 1), (key1199, 1), (key1199, 1), (key1199, 1), (key1199, 1), (key1199, 1), (key1041, 2), (key1041, 2), (key1041, 2), (key1193, -1), (key1193, -1), (key1193, -1), (key1193, -1), (key1193, -1), (key1193, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1)]

def rawRow789 : Integer.Sparse Key := [(key1019, -2), (key1199, -2), (key1199, -2), (key1019, 1), (key1019, 1), (key1127, 1), (key1127, 1), (key1199, 1), (key1199, 1), (key1006, 2), (key1193, 2), (key1193, 2), (key1006, -1), (key1006, -1), (key1041, -1), (key1041, -1), (key1193, -1), (key1193, -1), (key998, -1), (key998, -1), (key1111, -1), (key1111, -1), (key1190, -1), (key1190, -1), (key998, 1), (key998, 1), (key1033, 1), (key1033, 1), (key1190, 1), (key1190, 1)]

def rawRow790 : Integer.Sparse Key := [(key1199, -2), (key1019, -2), (key1199, -2), (key1127, 1), (key1199, 1), (key1019, 1), (key1199, 1), (key1019, 1), (key1127, 1), (key1193, 2), (key1006, 2), (key1193, 2), (key1041, -1), (key1193, -1), (key1006, -1), (key1193, -1), (key1006, -1), (key1041, -1), (key1111, -1), (key1190, -1), (key998, -1), (key1190, -1), (key998, -1), (key1111, -1), (key1033, 1), (key1190, 1), (key998, 1), (key1190, 1), (key998, 1), (key1033, 1)]

def rawRow791 : Integer.Sparse Key := [(key1199, -2), (key1199, -2), (key1019, -2), (key1199, 1), (key1127, 1), (key1199, 1), (key1019, 1), (key1127, 1), (key1019, 1), (key1193, 2), (key1193, 2), (key1006, 2), (key1193, -1), (key1041, -1), (key1193, -1), (key1006, -1), (key1041, -1), (key1006, -1), (key1190, -1), (key1111, -1), (key1190, -1), (key998, -1), (key1111, -1), (key998, -1), (key1190, 1), (key1033, 1), (key1190, 1), (key998, 1), (key1033, 1), (key998, 1)]

def rawRow792 : Integer.Sparse Key := [(key20, -6), (key20, 2), (key20, 2), (key31, 2), (key45, 6), (key45, -2), (key45, -2), (key70, -2), (key102, -2), (key102, -2), (key111, -2), (key102, 2), (key102, 2), (key133, 2)]

def rawRow793 : Integer.Sparse Key := [(key20, -6), (key20, 2), (key31, 2), (key20, 2), (key45, 6), (key45, -2), (key70, -2), (key45, -2), (key102, -2), (key111, -2), (key102, -2), (key102, 2), (key133, 2), (key102, 2)]

def rawRow794 : Integer.Sparse Key := [(key20, -6), (key31, 2), (key20, 2), (key20, 2), (key45, 6), (key70, -2), (key45, -2), (key45, -2), (key111, -2), (key102, -2), (key102, -2), (key133, 2), (key102, 2), (key102, 2)]

def rawRow795 : Integer.Sparse Key := [(key31, -6), (key20, 2), (key20, 2), (key20, 2), (key70, 6), (key45, -2), (key45, -2), (key45, -2), (key133, -2), (key133, -2), (key133, -2), (key111, 2), (key111, 2), (key111, 2)]

def rawRow796 : Integer.Sparse Key := [(key45, -6), (key102, 2), (key102, 2), (key111, 2), (key20, 6), (key102, -2), (key102, -2), (key133, -2), (key20, -2), (key20, -2), (key31, -2), (key45, 2), (key45, 2), (key70, 2)]

def rawRow797 : Integer.Sparse Key := [(key45, -6), (key102, 2), (key111, 2), (key102, 2), (key20, 6), (key102, -2), (key133, -2), (key102, -2), (key20, -2), (key31, -2), (key20, -2), (key45, 2), (key70, 2), (key45, 2)]

def rawRow798 : Integer.Sparse Key := [(key45, -6), (key111, 2), (key102, 2), (key102, 2), (key20, 6), (key133, -2), (key102, -2), (key102, -2), (key31, -2), (key20, -2), (key20, -2), (key70, 2), (key45, 2), (key45, 2)]

def rawRow799 : Integer.Sparse Key := [(key111, -6), (key45, 2), (key102, 2), (key102, 2), (key133, 6), (key20, -2), (key102, -2), (key102, -2), (key70, -2), (key133, -2), (key133, -2), (key31, 2), (key111, 2), (key111, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow800 : Integer.Sparse Key := [(key111, -6), (key102, 2), (key45, 2), (key102, 2), (key133, 6), (key102, -2), (key20, -2), (key102, -2), (key133, -2), (key70, -2), (key133, -2), (key111, 2), (key31, 2), (key111, 2)]

def rawRow801 : Integer.Sparse Key := [(key111, -6), (key102, 2), (key102, 2), (key45, 2), (key133, 6), (key102, -2), (key102, -2), (key20, -2), (key133, -2), (key133, -2), (key70, -2), (key111, 2), (key111, 2), (key31, 2)]

def rawRow802 : Integer.Sparse Key := [(key70, -6), (key133, 2), (key133, 2), (key133, 2), (key31, 6), (key111, -2), (key111, -2), (key111, -2), (key20, -2), (key20, -2), (key20, -2), (key45, 2), (key45, 2), (key45, 2)]

def rawRow803 : Integer.Sparse Key := [(key133, -6), (key70, 2), (key133, 2), (key133, 2), (key111, 6), (key31, -2), (key111, -2), (key111, -2), (key45, -2), (key102, -2), (key102, -2), (key20, 2), (key102, 2), (key102, 2)]

def rawRow804 : Integer.Sparse Key := [(key133, -6), (key133, 2), (key70, 2), (key133, 2), (key111, 6), (key111, -2), (key31, -2), (key111, -2), (key102, -2), (key45, -2), (key102, -2), (key102, 2), (key20, 2), (key102, 2)]

def rawRow805 : Integer.Sparse Key := [(key133, -6), (key133, 2), (key133, 2), (key70, 2), (key111, 6), (key111, -2), (key111, -2), (key31, -2), (key102, -2), (key102, -2), (key45, -2), (key102, 2), (key102, 2), (key20, 2)]

def rawRow806 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1001, -2), (key993, 1), (key1001, 1), (key993, 1), (key1015, 1), (key1001, 1), (key1015, 1), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, -1), (key1036, -1), (key1028, -1), (key1071, -1), (key1036, -1), (key1071, -1), (key1106, -1), (key1114, -1), (key1106, -1), (key1123, -1), (key1114, -1), (key1123, -1), (key1106, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1150, 1)]

def rawRow807 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1001, -2), (key1001, 1), (key993, 1), (key1015, 1), (key993, 1), (key1015, 1), (key1001, 1), (key1036, 2), (key1028, 2), (key1036, 2), (key1036, -1), (key1028, -1), (key1071, -1), (key1028, -1), (key1071, -1), (key1036, -1), (key1114, -1), (key1106, -1), (key1123, -1), (key1106, -1), (key1123, -1), (key1114, -1), (key1114, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1114, 1)]

def rawRow808 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key993, -2), (key1015, 1), (key1015, 1), (key1001, 1), (key1001, 1), (key993, 1), (key993, 1), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, -1), (key1071, -1), (key1036, -1), (key1036, -1), (key1028, -1), (key1028, -1), (key1123, -1), (key1123, -1), (key1114, -1), (key1114, -1), (key1106, -1), (key1106, -1), (key1150, 1), (key1150, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1)]

def rawRow809 : Integer.Sparse Key := [(key1015, -2), (key1015, -2), (key1015, -2), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1071, 2), (key1071, 2), (key1071, 2), (key1036, -1), (key1036, -1), (key1036, -1), (key1036, -1), (key1036, -1), (key1036, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1)]

def rawRow810 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1036, -2), (key1106, 1), (key1114, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1123, 1), (key993, 2), (key1001, 2), (key1001, 2), (key1106, -1), (key1114, -1), (key1106, -1), (key1150, -1), (key1114, -1), (key1150, -1), (key993, -1), (key1001, -1), (key993, -1), (key1015, -1), (key1001, -1), (key1015, -1), (key1028, 1), (key1036, 1), (key1028, 1), (key1071, 1), (key1036, 1), (key1071, 1)]

def rawRow811 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1036, -2), (key1114, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1001, 2), (key993, 2), (key1001, 2), (key1114, -1), (key1106, -1), (key1150, -1), (key1106, -1), (key1150, -1), (key1114, -1), (key1001, -1), (key993, -1), (key1015, -1), (key993, -1), (key1015, -1), (key1001, -1), (key1036, 1), (key1028, 1), (key1071, 1), (key1028, 1), (key1071, 1), (key1036, 1)]

def rawRow812 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1028, -2), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1001, 2), (key1001, 2), (key993, 2), (key1150, -1), (key1150, -1), (key1114, -1), (key1114, -1), (key1106, -1), (key1106, -1), (key1015, -1), (key1015, -1), (key1001, -1), (key1001, -1), (key993, -1), (key993, -1), (key1071, 1), (key1071, 1), (key1036, 1), (key1036, 1), (key1028, 1), (key1028, 1)]

def rawRow813 : Integer.Sparse Key := [(key1123, -2), (key1123, -2), (key1235, -2), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1150, 2), (key1150, 2), (key1242, 2), (key1001, -1), (key1001, -1), (key1114, -1), (key1114, -1), (key1232, -1), (key1232, -1), (key1071, -1), (key1071, -1), (key1150, -1), (key1150, -1), (key1242, -1), (key1242, -1), (key1015, 1), (key1015, 1), (key1123, 1), (key1123, 1), (key1235, 1), (key1235, 1)]

def rawRow814 : Integer.Sparse Key := [(key1123, -2), (key1235, -2), (key1123, -2), (key1114, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1150, 2), (key1242, 2), (key1150, 2), (key1114, -1), (key1232, -1), (key1001, -1), (key1232, -1), (key1001, -1), (key1114, -1), (key1150, -1), (key1242, -1), (key1071, -1), (key1242, -1), (key1071, -1), (key1150, -1), (key1123, 1), (key1235, 1), (key1015, 1), (key1235, 1), (key1015, 1), (key1123, 1)]

def rawRow815 : Integer.Sparse Key := [(key1235, -2), (key1123, -2), (key1123, -2), (key1232, 1), (key1114, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1036, 1), (key1242, 2), (key1150, 2), (key1150, 2), (key1232, -1), (key1114, -1), (key1232, -1), (key1001, -1), (key1114, -1), (key1001, -1), (key1242, -1), (key1150, -1), (key1242, -1), (key1071, -1), (key1150, -1), (key1071, -1), (key1235, 1), (key1123, 1), (key1235, 1), (key1015, 1), (key1123, 1), (key1015, 1)]

def rawRow816 : Integer.Sparse Key := [(key1071, -2), (key1071, -2), (key1071, -2), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1015, 2), (key1015, 2), (key1015, 2), (key1123, -1), (key1123, -1), (key1123, -1), (key1123, -1), (key1123, -1), (key1123, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1)]

def rawRow817 : Integer.Sparse Key := [(key1150, -2), (key1150, -2), (key1242, -2), (key1071, 1), (key1071, 1), (key1150, 1), (key1150, 1), (key1242, 1), (key1242, 1), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, -1), (key1015, -1), (key1123, -1), (key1123, -1), (key1235, -1), (key1235, -1), (key1036, -1), (key1036, -1), (key1114, -1), (key1114, -1), (key1232, -1), (key1232, -1), (key1001, 1), (key1001, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1)]

def rawRow818 : Integer.Sparse Key := [(key1150, -2), (key1242, -2), (key1150, -2), (key1150, 1), (key1242, 1), (key1071, 1), (key1242, 1), (key1071, 1), (key1150, 1), (key1123, 2), (key1235, 2), (key1123, 2), (key1123, -1), (key1235, -1), (key1015, -1), (key1235, -1), (key1015, -1), (key1123, -1), (key1114, -1), (key1232, -1), (key1036, -1), (key1232, -1), (key1036, -1), (key1114, -1), (key1114, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1114, 1)]

def rawRow819 : Integer.Sparse Key := [(key1242, -2), (key1150, -2), (key1150, -2), (key1242, 1), (key1150, 1), (key1242, 1), (key1071, 1), (key1150, 1), (key1071, 1), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, -1), (key1123, -1), (key1235, -1), (key1015, -1), (key1123, -1), (key1015, -1), (key1232, -1), (key1114, -1), (key1232, -1), (key1036, -1), (key1114, -1), (key1036, -1), (key1232, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1001, 1)]

def rawRow820 : Integer.Sparse Key := [(key1, -2), (key7, -2), (key7, -2), (key7, 6), (key84, 2), (key90, 2), (key90, 2), (key90, -2), (key90, -2), (key151, -2), (key193, -6), (key193, 2), (key193, 2), (key202, 2)]

def rawRow821 : Integer.Sparse Key := [(key7, -2), (key1, -2), (key7, -2), (key7, 6), (key90, 2), (key84, 2), (key90, 2), (key90, -2), (key151, -2), (key90, -2), (key193, -6), (key193, 2), (key202, 2), (key193, 2)]

def rawRow822 : Integer.Sparse Key := [(key7, -2), (key7, -2), (key1, -2), (key7, 6), (key90, 2), (key90, 2), (key84, 2), (key151, -2), (key90, -2), (key90, -2), (key193, -6), (key202, 2), (key193, 2), (key193, 2)]

def rawRow823 : Integer.Sparse Key := [(key7, -2), (key7, -2), (key7, -2), (key1, 6), (key151, 2), (key151, 2), (key151, 2), (key84, -2), (key84, -2), (key84, -2), (key202, -6), (key193, 2), (key193, 2), (key193, 2)]

def rawRow824 : Integer.Sparse Key := [(key84, -2), (key90, -2), (key90, -2), (key151, 6), (key1, 2), (key7, 2), (key7, 2), (key193, -2), (key193, -2), (key202, -2), (key7, -6), (key90, 2), (key90, 2), (key151, 2)]

def rawRow825 : Integer.Sparse Key := [(key90, -2), (key84, -2), (key90, -2), (key151, 6), (key7, 2), (key1, 2), (key7, 2), (key193, -2), (key202, -2), (key193, -2), (key7, -6), (key90, 2), (key151, 2), (key90, 2)]

def rawRow826 : Integer.Sparse Key := [(key90, -2), (key90, -2), (key84, -2), (key151, 6), (key7, 2), (key7, 2), (key1, 2), (key202, -2), (key193, -2), (key193, -2), (key7, -6), (key151, 2), (key90, 2), (key90, 2)]

def rawRow827 : Integer.Sparse Key := [(key90, -2), (key90, -2), (key151, -2), (key84, 6), (key193, 2), (key193, 2), (key202, 2), (key1, -2), (key84, -2), (key84, -2), (key151, -6), (key7, 2), (key90, 2), (key90, 2)]

def rawRow828 : Integer.Sparse Key := [(key90, -2), (key151, -2), (key90, -2), (key84, 6), (key193, 2), (key202, 2), (key193, 2), (key84, -2), (key1, -2), (key84, -2), (key151, -6), (key90, 2), (key7, 2), (key90, 2)]

def rawRow829 : Integer.Sparse Key := [(key151, -2), (key90, -2), (key90, -2), (key84, 6), (key202, 2), (key193, 2), (key193, 2), (key84, -2), (key84, -2), (key1, -2), (key151, -6), (key90, 2), (key90, 2), (key7, 2)]

def rawRow830 : Integer.Sparse Key := [(key193, -2), (key193, -2), (key193, -2), (key202, 6), (key7, 2), (key7, 2), (key7, 2), (key151, -2), (key151, -2), (key151, -2), (key1, -6), (key84, 2), (key84, 2), (key84, 2)]

def rawRow831 : Integer.Sparse Key := [(key193, -2), (key193, -2), (key202, -2), (key193, 6), (key90, 2), (key90, 2), (key151, 2), (key7, -2), (key90, -2), (key90, -2), (key84, -6), (key1, 2), (key84, 2), (key84, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow832 : Integer.Sparse Key := [(key193, -2), (key202, -2), (key193, -2), (key193, 6), (key90, 2), (key151, 2), (key90, 2), (key90, -2), (key7, -2), (key90, -2), (key84, -6), (key84, 2), (key1, 2), (key84, 2)]

def rawRow833 : Integer.Sparse Key := [(key202, -2), (key193, -2), (key193, -2), (key193, 6), (key151, 2), (key90, 2), (key90, 2), (key90, -2), (key90, -2), (key7, -2), (key84, -6), (key84, 2), (key84, 2), (key1, 2)]

def rawRow834 : Integer.Sparse Key := [(key2785, -2), (key2785, -2), (key2785, -2), (key2793, 1), (key2793, 1), (key2793, 1), (key2793, 1), (key2793, 1), (key2793, 1), (key2808, 2), (key2808, 2), (key2808, 2), (key2859, -1), (key2859, -1), (key2859, -1), (key2859, -1), (key2859, -1), (key2859, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2869, 1), (key2869, 1), (key2869, 1), (key2869, 1), (key2869, 1), (key2869, 1)]

def rawRow835 : Integer.Sparse Key := [(key2670, -2), (key2793, -2), (key2793, -2), (key2670, 1), (key2670, 1), (key2785, 1), (key2785, 1), (key2793, 1), (key2793, 1), (key2705, 2), (key2859, 2), (key2859, 2), (key2705, -1), (key2705, -1), (key2808, -1), (key2808, -1), (key2859, -1), (key2859, -1), (key2725, -1), (key2725, -1), (key2869, -1), (key2869, -1), (key2879, -1), (key2879, -1), (key2725, 1), (key2725, 1), (key2828, 1), (key2828, 1), (key2879, 1), (key2879, 1)]

def rawRow836 : Integer.Sparse Key := [(key2793, -2), (key2670, -2), (key2793, -2), (key2785, 1), (key2793, 1), (key2670, 1), (key2793, 1), (key2670, 1), (key2785, 1), (key2859, 2), (key2705, 2), (key2859, 2), (key2808, -1), (key2859, -1), (key2705, -1), (key2859, -1), (key2705, -1), (key2808, -1), (key2869, -1), (key2879, -1), (key2725, -1), (key2879, -1), (key2725, -1), (key2869, -1), (key2828, 1), (key2879, 1), (key2725, 1), (key2879, 1), (key2725, 1), (key2828, 1)]

def rawRow837 : Integer.Sparse Key := [(key2793, -2), (key2793, -2), (key2670, -2), (key2793, 1), (key2785, 1), (key2793, 1), (key2670, 1), (key2785, 1), (key2670, 1), (key2859, 2), (key2859, 2), (key2705, 2), (key2859, -1), (key2808, -1), (key2859, -1), (key2705, -1), (key2808, -1), (key2705, -1), (key2879, -1), (key2869, -1), (key2879, -1), (key2725, -1), (key2869, -1), (key2725, -1), (key2879, 1), (key2828, 1), (key2879, 1), (key2725, 1), (key2828, 1), (key2725, 1)]

def rawRow838 : Integer.Sparse Key := [(key2808, -2), (key2808, -2), (key2808, -2), (key2828, 1), (key2828, 1), (key2828, 1), (key2828, 1), (key2828, 1), (key2828, 1), (key2785, 2), (key2785, 2), (key2785, 2), (key2869, -1), (key2869, -1), (key2869, -1), (key2869, -1), (key2869, -1), (key2869, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2859, 1), (key2859, 1), (key2859, 1), (key2859, 1), (key2859, 1), (key2859, 1)]

def rawRow839 : Integer.Sparse Key := [(key2615, -2), (key2828, -2), (key2828, -2), (key2615, 1), (key2615, 1), (key2808, 1), (key2808, 1), (key2828, 1), (key2828, 1), (key2631, 2), (key2869, 2), (key2869, 2), (key2631, -1), (key2631, -1), (key2785, -1), (key2785, -1), (key2869, -1), (key2869, -1), (key2639, -1), (key2639, -1), (key2859, -1), (key2859, -1), (key2879, -1), (key2879, -1), (key2639, 1), (key2639, 1), (key2793, 1), (key2793, 1), (key2879, 1), (key2879, 1)]

def rawRow840 : Integer.Sparse Key := [(key2828, -2), (key2615, -2), (key2828, -2), (key2808, 1), (key2828, 1), (key2615, 1), (key2828, 1), (key2615, 1), (key2808, 1), (key2869, 2), (key2631, 2), (key2869, 2), (key2785, -1), (key2869, -1), (key2631, -1), (key2869, -1), (key2631, -1), (key2785, -1), (key2859, -1), (key2879, -1), (key2639, -1), (key2879, -1), (key2639, -1), (key2859, -1), (key2793, 1), (key2879, 1), (key2639, 1), (key2879, 1), (key2639, 1), (key2793, 1)]

def rawRow841 : Integer.Sparse Key := [(key2828, -2), (key2828, -2), (key2615, -2), (key2828, 1), (key2808, 1), (key2828, 1), (key2615, 1), (key2808, 1), (key2615, 1), (key2869, 2), (key2869, 2), (key2631, 2), (key2869, -1), (key2785, -1), (key2869, -1), (key2631, -1), (key2785, -1), (key2631, -1), (key2879, -1), (key2859, -1), (key2879, -1), (key2639, -1), (key2859, -1), (key2639, -1), (key2879, 1), (key2793, 1), (key2879, 1), (key2639, 1), (key2793, 1), (key2639, 1)]

def rawRow842 : Integer.Sparse Key := [(key2705, -2), (key2859, -2), (key2859, -2), (key2725, 1), (key2725, 1), (key2869, 1), (key2869, 1), (key2879, 1), (key2879, 1), (key2670, 2), (key2793, 2), (key2793, 2), (key2725, -1), (key2725, -1), (key2828, -1), (key2828, -1), (key2879, -1), (key2879, -1), (key2670, -1), (key2670, -1), (key2785, -1), (key2785, -1), (key2793, -1), (key2793, -1), (key2705, 1), (key2705, 1), (key2808, 1), (key2808, 1), (key2859, 1), (key2859, 1)]

def rawRow843 : Integer.Sparse Key := [(key2859, -2), (key2705, -2), (key2859, -2), (key2869, 1), (key2879, 1), (key2725, 1), (key2879, 1), (key2725, 1), (key2869, 1), (key2793, 2), (key2670, 2), (key2793, 2), (key2828, -1), (key2879, -1), (key2725, -1), (key2879, -1), (key2725, -1), (key2828, -1), (key2785, -1), (key2793, -1), (key2670, -1), (key2793, -1), (key2670, -1), (key2785, -1), (key2808, 1), (key2859, 1), (key2705, 1), (key2859, 1), (key2705, 1), (key2808, 1)]

def rawRow844 : Integer.Sparse Key := [(key2859, -2), (key2859, -2), (key2705, -2), (key2879, 1), (key2869, 1), (key2879, 1), (key2725, 1), (key2869, 1), (key2725, 1), (key2793, 2), (key2793, 2), (key2670, 2), (key2879, -1), (key2828, -1), (key2879, -1), (key2725, -1), (key2828, -1), (key2725, -1), (key2793, -1), (key2785, -1), (key2793, -1), (key2670, -1), (key2785, -1), (key2670, -1), (key2859, 1), (key2808, 1), (key2859, 1), (key2705, 1), (key2808, 1), (key2705, 1)]

def rawRow845 : Integer.Sparse Key := [(key2631, -2), (key2869, -2), (key2869, -2), (key2639, 1), (key2639, 1), (key2859, 1), (key2859, 1), (key2879, 1), (key2879, 1), (key2615, 2), (key2828, 2), (key2828, 2), (key2639, -1), (key2639, -1), (key2793, -1), (key2793, -1), (key2879, -1), (key2879, -1), (key2615, -1), (key2615, -1), (key2808, -1), (key2808, -1), (key2828, -1), (key2828, -1), (key2631, 1), (key2631, 1), (key2785, 1), (key2785, 1), (key2869, 1), (key2869, 1)]

def rawRow846 : Integer.Sparse Key := [(key2869, -2), (key2631, -2), (key2869, -2), (key2859, 1), (key2879, 1), (key2639, 1), (key2879, 1), (key2639, 1), (key2859, 1), (key2828, 2), (key2615, 2), (key2828, 2), (key2793, -1), (key2879, -1), (key2639, -1), (key2879, -1), (key2639, -1), (key2793, -1), (key2808, -1), (key2828, -1), (key2615, -1), (key2828, -1), (key2615, -1), (key2808, -1), (key2785, 1), (key2869, 1), (key2631, 1), (key2869, 1), (key2631, 1), (key2785, 1)]

def rawRow847 : Integer.Sparse Key := [(key2869, -2), (key2869, -2), (key2631, -2), (key2879, 1), (key2859, 1), (key2879, 1), (key2639, 1), (key2859, 1), (key2639, 1), (key2828, 2), (key2828, 2), (key2615, 2), (key2879, -1), (key2793, -1), (key2879, -1), (key2639, -1), (key2793, -1), (key2639, -1), (key2828, -1), (key2808, -1), (key2828, -1), (key2615, -1), (key2808, -1), (key2615, -1), (key2869, 1), (key2785, 1), (key2869, 1), (key2631, 1), (key2785, 1), (key2631, 1)]

def rawRow848 : Integer.Sparse Key := [(key1287, -6), (key1307, 2), (key1307, 2), (key1307, 2), (key1382, 6), (key1537, -2), (key1537, -2), (key1537, -2), (key1415, -2), (key1415, -2), (key1415, -2), (key1564, 2), (key1564, 2), (key1564, 2)]

def rawRow849 : Integer.Sparse Key := [(key1307, -6), (key1287, 2), (key1307, 2), (key1307, 2), (key1537, 6), (key1382, -2), (key1537, -2), (key1537, -2), (key1564, -2), (key1613, -2), (key1613, -2), (key1415, 2), (key1613, 2), (key1613, 2)]

def rawRow850 : Integer.Sparse Key := [(key1307, -6), (key1307, 2), (key1287, 2), (key1307, 2), (key1537, 6), (key1537, -2), (key1382, -2), (key1537, -2), (key1613, -2), (key1564, -2), (key1613, -2), (key1613, 2), (key1415, 2), (key1613, 2)]

def rawRow851 : Integer.Sparse Key := [(key1307, -6), (key1307, 2), (key1307, 2), (key1287, 2), (key1537, 6), (key1537, -2), (key1537, -2), (key1382, -2), (key1613, -2), (key1613, -2), (key1564, -2), (key1613, 2), (key1613, 2), (key1415, 2)]

def rawRow852 : Integer.Sparse Key := [(key1382, -6), (key1415, 2), (key1415, 2), (key1415, 2), (key1287, 6), (key1564, -2), (key1564, -2), (key1564, -2), (key1307, -2), (key1307, -2), (key1307, -2), (key1537, 2), (key1537, 2), (key1537, 2)]

def rawRow853 : Integer.Sparse Key := [(key1415, -6), (key1382, 2), (key1415, 2), (key1415, 2), (key1564, 6), (key1287, -2), (key1564, -2), (key1564, -2), (key1537, -2), (key1613, -2), (key1613, -2), (key1307, 2), (key1613, 2), (key1613, 2)]

def rawRow854 : Integer.Sparse Key := [(key1415, -6), (key1415, 2), (key1382, 2), (key1415, 2), (key1564, 6), (key1564, -2), (key1287, -2), (key1564, -2), (key1613, -2), (key1537, -2), (key1613, -2), (key1613, 2), (key1307, 2), (key1613, 2)]

def rawRow855 : Integer.Sparse Key := [(key1415, -6), (key1415, 2), (key1415, 2), (key1382, 2), (key1564, 6), (key1564, -2), (key1564, -2), (key1287, -2), (key1613, -2), (key1613, -2), (key1537, -2), (key1613, 2), (key1613, 2), (key1307, 2)]

def rawRow856 : Integer.Sparse Key := [(key1537, -6), (key1564, 2), (key1613, 2), (key1613, 2), (key1307, 6), (key1415, -2), (key1613, -2), (key1613, -2), (key1287, -2), (key1307, -2), (key1307, -2), (key1382, 2), (key1537, 2), (key1537, 2)]

def rawRow857 : Integer.Sparse Key := [(key1537, -6), (key1613, 2), (key1564, 2), (key1613, 2), (key1307, 6), (key1613, -2), (key1415, -2), (key1613, -2), (key1307, -2), (key1287, -2), (key1307, -2), (key1537, 2), (key1382, 2), (key1537, 2)]

def rawRow858 : Integer.Sparse Key := [(key1537, -6), (key1613, 2), (key1613, 2), (key1564, 2), (key1307, 6), (key1613, -2), (key1613, -2), (key1415, -2), (key1307, -2), (key1307, -2), (key1287, -2), (key1537, 2), (key1537, 2), (key1382, 2)]

def rawRow859 : Integer.Sparse Key := [(key1564, -6), (key1537, 2), (key1613, 2), (key1613, 2), (key1415, 6), (key1307, -2), (key1613, -2), (key1613, -2), (key1382, -2), (key1415, -2), (key1415, -2), (key1287, 2), (key1564, 2), (key1564, 2)]

def rawRow860 : Integer.Sparse Key := [(key1564, -6), (key1613, 2), (key1537, 2), (key1613, 2), (key1415, 6), (key1613, -2), (key1307, -2), (key1613, -2), (key1415, -2), (key1382, -2), (key1415, -2), (key1564, 2), (key1287, 2), (key1564, 2)]

def rawRow861 : Integer.Sparse Key := [(key1564, -6), (key1613, 2), (key1613, 2), (key1537, 2), (key1415, 6), (key1613, -2), (key1613, -2), (key1307, -2), (key1415, -2), (key1415, -2), (key1382, -2), (key1564, 2), (key1564, 2), (key1287, 2)]

def rawRow862 : Integer.Sparse Key := [(key2610, -2), (key2610, -2), (key2610, -2), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2665, 2), (key2665, 2), (key2665, 2), (key2780, -1), (key2780, -1), (key2780, -1), (key2780, -1), (key2780, -1), (key2780, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1)]

def rawRow863 : Integer.Sparse Key := [(key2626, -2), (key2626, -2), (key2635, -2), (key2610, 1), (key2610, 1), (key2626, 1), (key2626, 1), (key2635, 1), (key2635, 1), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, -1), (key2665, -1), (key2780, -1), (key2780, -1), (key2789, -1), (key2789, -1), (key2803, -1), (key2803, -1), (key2853, -1), (key2853, -1), (key2855, -1), (key2855, -1), (key2700, 1), (key2700, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow864 : Integer.Sparse Key := [(key2626, -2), (key2635, -2), (key2626, -2), (key2626, 1), (key2635, 1), (key2610, 1), (key2635, 1), (key2610, 1), (key2626, 1), (key2780, 2), (key2789, 2), (key2780, 2), (key2780, -1), (key2789, -1), (key2665, -1), (key2789, -1), (key2665, -1), (key2780, -1), (key2853, -1), (key2855, -1), (key2803, -1), (key2855, -1), (key2803, -1), (key2853, -1), (key2853, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2853, 1)]

def rawRow865 : Integer.Sparse Key := [(key2635, -2), (key2626, -2), (key2626, -2), (key2635, 1), (key2626, 1), (key2635, 1), (key2610, 1), (key2626, 1), (key2610, 1), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, -1), (key2780, -1), (key2789, -1), (key2665, -1), (key2780, -1), (key2665, -1), (key2855, -1), (key2853, -1), (key2855, -1), (key2803, -1), (key2853, -1), (key2803, -1), (key2855, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2700, 1)]

def rawRow866 : Integer.Sparse Key := [(key2665, -2), (key2665, -2), (key2665, -2), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2610, 2), (key2610, 2), (key2610, 2), (key2803, -1), (key2803, -1), (key2803, -1), (key2803, -1), (key2803, -1), (key2803, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1)]

def rawRow867 : Integer.Sparse Key := [(key2700, -2), (key2700, -2), (key2721, -2), (key2665, 1), (key2665, 1), (key2700, 1), (key2700, 1), (key2721, 1), (key2721, 1), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, -1), (key2610, -1), (key2803, -1), (key2803, -1), (key2824, -1), (key2824, -1), (key2780, -1), (key2780, -1), (key2853, -1), (key2853, -1), (key2865, -1), (key2865, -1), (key2626, 1), (key2626, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1)]

def rawRow868 : Integer.Sparse Key := [(key2700, -2), (key2721, -2), (key2700, -2), (key2700, 1), (key2721, 1), (key2665, 1), (key2721, 1), (key2665, 1), (key2700, 1), (key2803, 2), (key2824, 2), (key2803, 2), (key2803, -1), (key2824, -1), (key2610, -1), (key2824, -1), (key2610, -1), (key2803, -1), (key2853, -1), (key2865, -1), (key2780, -1), (key2865, -1), (key2780, -1), (key2853, -1), (key2853, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2853, 1)]

def rawRow869 : Integer.Sparse Key := [(key2721, -2), (key2700, -2), (key2700, -2), (key2721, 1), (key2700, 1), (key2721, 1), (key2665, 1), (key2700, 1), (key2665, 1), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, -1), (key2803, -1), (key2824, -1), (key2610, -1), (key2803, -1), (key2610, -1), (key2865, -1), (key2853, -1), (key2865, -1), (key2780, -1), (key2853, -1), (key2780, -1), (key2865, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2626, 1)]

def rawRow870 : Integer.Sparse Key := [(key2780, -2), (key2780, -2), (key2789, -2), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2626, 2), (key2626, 2), (key2635, 2), (key2700, -1), (key2700, -1), (key2853, -1), (key2853, -1), (key2855, -1), (key2855, -1), (key2610, -1), (key2610, -1), (key2626, -1), (key2626, -1), (key2635, -1), (key2635, -1), (key2665, 1), (key2665, 1), (key2780, 1), (key2780, 1), (key2789, 1), (key2789, 1)]

def rawRow871 : Integer.Sparse Key := [(key2780, -2), (key2789, -2), (key2780, -2), (key2853, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2626, 2), (key2635, 2), (key2626, 2), (key2853, -1), (key2855, -1), (key2700, -1), (key2855, -1), (key2700, -1), (key2853, -1), (key2626, -1), (key2635, -1), (key2610, -1), (key2635, -1), (key2610, -1), (key2626, -1), (key2780, 1), (key2789, 1), (key2665, 1), (key2789, 1), (key2665, 1), (key2780, 1)]

def rawRow872 : Integer.Sparse Key := [(key2789, -2), (key2780, -2), (key2780, -2), (key2855, 1), (key2853, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2803, 1), (key2635, 2), (key2626, 2), (key2626, 2), (key2855, -1), (key2853, -1), (key2855, -1), (key2700, -1), (key2853, -1), (key2700, -1), (key2635, -1), (key2626, -1), (key2635, -1), (key2610, -1), (key2626, -1), (key2610, -1), (key2789, 1), (key2780, 1), (key2789, 1), (key2665, 1), (key2780, 1), (key2665, 1)]

def rawRow873 : Integer.Sparse Key := [(key2803, -2), (key2803, -2), (key2824, -2), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2700, 2), (key2700, 2), (key2721, 2), (key2626, -1), (key2626, -1), (key2853, -1), (key2853, -1), (key2865, -1), (key2865, -1), (key2665, -1), (key2665, -1), (key2700, -1), (key2700, -1), (key2721, -1), (key2721, -1), (key2610, 1), (key2610, 1), (key2803, 1), (key2803, 1), (key2824, 1), (key2824, 1)]

def rawRow874 : Integer.Sparse Key := [(key2803, -2), (key2824, -2), (key2803, -2), (key2853, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2700, 2), (key2721, 2), (key2700, 2), (key2853, -1), (key2865, -1), (key2626, -1), (key2865, -1), (key2626, -1), (key2853, -1), (key2700, -1), (key2721, -1), (key2665, -1), (key2721, -1), (key2665, -1), (key2700, -1), (key2803, 1), (key2824, 1), (key2610, 1), (key2824, 1), (key2610, 1), (key2803, 1)]

def rawRow875 : Integer.Sparse Key := [(key2824, -2), (key2803, -2), (key2803, -2), (key2865, 1), (key2853, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2780, 1), (key2721, 2), (key2700, 2), (key2700, 2), (key2865, -1), (key2853, -1), (key2865, -1), (key2626, -1), (key2853, -1), (key2626, -1), (key2721, -1), (key2700, -1), (key2721, -1), (key2665, -1), (key2700, -1), (key2665, -1), (key2824, 1), (key2803, 1), (key2824, 1), (key2610, 1), (key2803, 1), (key2610, 1)]

def rawRow876 : Integer.Sparse Key := [(key995, -2), (key995, -2), (key995, -2), (key1011, 6), (key1030, 2), (key1030, 2), (key1030, 2), (key1119, -2), (key1119, -2), (key1119, -2), (key1067, -6), (key1146, 2), (key1146, 2), (key1146, 2)]

def rawRow877 : Integer.Sparse Key := [(key995, -2), (key995, -2), (key1011, -2), (key995, 6), (key1108, 2), (key1108, 2), (key1119, 2), (key1030, -2), (key1108, -2), (key1108, -2), (key1146, -6), (key1067, 2), (key1146, 2), (key1146, 2)]

def rawRow878 : Integer.Sparse Key := [(key995, -2), (key1011, -2), (key995, -2), (key995, 6), (key1108, 2), (key1119, 2), (key1108, 2), (key1108, -2), (key1030, -2), (key1108, -2), (key1146, -6), (key1146, 2), (key1067, 2), (key1146, 2)]

def rawRow879 : Integer.Sparse Key := [(key1011, -2), (key995, -2), (key995, -2), (key995, 6), (key1119, 2), (key1108, 2), (key1108, 2), (key1108, -2), (key1108, -2), (key1030, -2), (key1146, -6), (key1146, 2), (key1146, 2), (key1067, 2)]

def rawRow880 : Integer.Sparse Key := [(key1030, -2), (key1030, -2), (key1030, -2), (key1067, 6), (key995, 2), (key995, 2), (key995, 2), (key1146, -2), (key1146, -2), (key1146, -2), (key1011, -6), (key1119, 2), (key1119, 2), (key1119, 2)]

def rawRow881 : Integer.Sparse Key := [(key1030, -2), (key1030, -2), (key1067, -2), (key1030, 6), (key1108, 2), (key1108, 2), (key1146, 2), (key995, -2), (key1108, -2), (key1108, -2), (key1119, -6), (key1011, 2), (key1119, 2), (key1119, 2)]

def rawRow882 : Integer.Sparse Key := [(key1030, -2), (key1067, -2), (key1030, -2), (key1030, 6), (key1108, 2), (key1146, 2), (key1108, 2), (key1108, -2), (key995, -2), (key1108, -2), (key1119, -6), (key1119, 2), (key1011, 2), (key1119, 2)]

def rawRow883 : Integer.Sparse Key := [(key1067, -2), (key1030, -2), (key1030, -2), (key1030, 6), (key1146, 2), (key1108, 2), (key1108, 2), (key1108, -2), (key1108, -2), (key995, -2), (key1119, -6), (key1119, 2), (key1119, 2), (key1011, 2)]

def rawRow884 : Integer.Sparse Key := [(key1108, -2), (key1108, -2), (key1119, -2), (key1146, 6), (key995, 2), (key995, 2), (key1011, 2), (key1067, -2), (key1146, -2), (key1146, -2), (key995, -6), (key1030, 2), (key1108, 2), (key1108, 2)]

def rawRow885 : Integer.Sparse Key := [(key1108, -2), (key1119, -2), (key1108, -2), (key1146, 6), (key995, 2), (key1011, 2), (key995, 2), (key1146, -2), (key1067, -2), (key1146, -2), (key995, -6), (key1108, 2), (key1030, 2), (key1108, 2)]

def rawRow886 : Integer.Sparse Key := [(key1119, -2), (key1108, -2), (key1108, -2), (key1146, 6), (key1011, 2), (key995, 2), (key995, 2), (key1146, -2), (key1146, -2), (key1067, -2), (key995, -6), (key1108, 2), (key1108, 2), (key1030, 2)]

def rawRow887 : Integer.Sparse Key := [(key1108, -2), (key1108, -2), (key1146, -2), (key1119, 6), (key1030, 2), (key1030, 2), (key1067, 2), (key1011, -2), (key1119, -2), (key1119, -2), (key1030, -6), (key995, 2), (key1108, 2), (key1108, 2)]

def rawRow888 : Integer.Sparse Key := [(key1108, -2), (key1146, -2), (key1108, -2), (key1119, 6), (key1030, 2), (key1067, 2), (key1030, 2), (key1119, -2), (key1011, -2), (key1119, -2), (key1030, -6), (key1108, 2), (key995, 2), (key1108, 2)]

def rawRow889 : Integer.Sparse Key := [(key1146, -2), (key1108, -2), (key1108, -2), (key1119, 6), (key1067, 2), (key1030, 2), (key1030, 2), (key1119, -2), (key1119, -2), (key1011, -2), (key1030, -6), (key1108, 2), (key1108, 2), (key995, 2)]

def rawRow890 : Integer.Sparse Key := [(key2606, -6), (key2622, 2), (key2622, 2), (key2622, 2), (key2661, 6), (key2696, -2), (key2696, -2), (key2696, -2), (key2776, -2), (key2776, -2), (key2776, -2), (key2799, 2), (key2799, 2), (key2799, 2)]

def rawRow891 : Integer.Sparse Key := [(key2622, -6), (key2606, 2), (key2622, 2), (key2622, 2), (key2696, 6), (key2661, -2), (key2696, -2), (key2696, -2), (key2799, -2), (key2849, -2), (key2849, -2), (key2776, 2), (key2849, 2), (key2849, 2)]

def rawRow892 : Integer.Sparse Key := [(key2622, -6), (key2622, 2), (key2606, 2), (key2622, 2), (key2696, 6), (key2696, -2), (key2661, -2), (key2696, -2), (key2849, -2), (key2799, -2), (key2849, -2), (key2849, 2), (key2776, 2), (key2849, 2)]

def rawRow893 : Integer.Sparse Key := [(key2622, -6), (key2622, 2), (key2622, 2), (key2606, 2), (key2696, 6), (key2696, -2), (key2696, -2), (key2661, -2), (key2849, -2), (key2849, -2), (key2799, -2), (key2849, 2), (key2849, 2), (key2776, 2)]

def rawRow894 : Integer.Sparse Key := [(key2661, -6), (key2696, 2), (key2696, 2), (key2696, 2), (key2606, 6), (key2799, -2), (key2799, -2), (key2799, -2), (key2622, -2), (key2622, -2), (key2622, -2), (key2696, 2), (key2696, 2), (key2696, 2)]

def rawRow895 : Integer.Sparse Key := [(key2696, -6), (key2661, 2), (key2696, 2), (key2696, 2), (key2799, 6), (key2606, -2), (key2799, -2), (key2799, -2), (key2696, -2), (key2849, -2), (key2849, -2), (key2622, 2), (key2849, 2), (key2849, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow896 : Integer.Sparse Key := [(key2696, -6), (key2696, 2), (key2661, 2), (key2696, 2), (key2799, 6), (key2799, -2), (key2606, -2), (key2799, -2), (key2849, -2), (key2696, -2), (key2849, -2), (key2849, 2), (key2622, 2), (key2849, 2)]

def rawRow897 : Integer.Sparse Key := [(key2696, -6), (key2696, 2), (key2696, 2), (key2661, 2), (key2799, 6), (key2799, -2), (key2799, -2), (key2606, -2), (key2849, -2), (key2849, -2), (key2696, -2), (key2849, 2), (key2849, 2), (key2622, 2)]

def rawRow898 : Integer.Sparse Key := [(key2776, -6), (key2799, 2), (key2849, 2), (key2849, 2), (key2622, 6), (key2696, -2), (key2849, -2), (key2849, -2), (key2606, -2), (key2622, -2), (key2622, -2), (key2661, 2), (key2696, 2), (key2696, 2)]

def rawRow899 : Integer.Sparse Key := [(key2776, -6), (key2849, 2), (key2799, 2), (key2849, 2), (key2622, 6), (key2849, -2), (key2696, -2), (key2849, -2), (key2622, -2), (key2606, -2), (key2622, -2), (key2696, 2), (key2661, 2), (key2696, 2)]

def rawRow900 : Integer.Sparse Key := [(key2776, -6), (key2849, 2), (key2849, 2), (key2799, 2), (key2622, 6), (key2849, -2), (key2849, -2), (key2696, -2), (key2622, -2), (key2622, -2), (key2606, -2), (key2696, 2), (key2696, 2), (key2661, 2)]

def rawRow901 : Integer.Sparse Key := [(key2799, -6), (key2776, 2), (key2849, 2), (key2849, 2), (key2696, 6), (key2622, -2), (key2849, -2), (key2849, -2), (key2661, -2), (key2696, -2), (key2696, -2), (key2606, 2), (key2799, 2), (key2799, 2)]

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

def rawRow7260 : Integer.Sparse Key := [(key2083, -2), (key2083, 1), (key2081, 1), (key2088, -2), (key2088, 1), (key2081, 1), (key2090, 1), (key2088, 1), (key2090, 1), (key2083, 1), (key2088, -2), (key2083, -2), (key2282, 2), (key2282, -1), (key2278, -1), (key2290, 2), (key2290, -1), (key2278, -1), (key2298, -1), (key2290, -1), (key2298, -1), (key2282, -1), (key2290, 2), (key2282, 2), (key2332, -1), (key2331, -1), (key2331, 1), (key2329, 1), (key2335, -1), (key2334, -1), (key2335, 1), (key2329, 1), (key2339, 1), (key2331, 1), (key2334, -1), (key2331, -1), (key2339, 1), (key2335, 1), (key2335, -1), (key2332, -1)]

def rawRow7261 : Integer.Sparse Key := [(key2088, -2), (key2088, 1), (key2090, 1), (key2083, -2), (key2083, 1), (key2090, 1), (key2081, 1), (key2083, 1), (key2081, 1), (key2088, 1), (key2083, -2), (key2088, -2), (key2290, 2), (key2290, -1), (key2298, -1), (key2282, 2), (key2282, -1), (key2298, -1), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, 2), (key2290, 2), (key2334, -1), (key2335, -1), (key2335, 1), (key2339, 1), (key2331, -1), (key2332, -1), (key2331, 1), (key2339, 1), (key2329, 1), (key2335, 1), (key2332, -1), (key2335, -1), (key2329, 1), (key2331, 1), (key2331, -1), (key2334, -1)]

def rawRow7262 : Integer.Sparse Key := [(key2088, -2), (key2090, 1), (key2088, 1), (key2083, -2), (key2090, 1), (key2083, 1), (key2083, 1), (key2081, 1), (key2088, 1), (key2081, 1), (key2088, -2), (key2083, -2), (key2290, 2), (key2298, -1), (key2290, -1), (key2282, 2), (key2298, -1), (key2282, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, 2), (key2282, 2), (key2335, -1), (key2334, -1), (key2339, 1), (key2335, 1), (key2332, -1), (key2331, -1), (key2339, 1), (key2331, 1), (key2335, 1), (key2329, 1), (key2335, -1), (key2332, -1), (key2331, 1), (key2329, 1), (key2334, -1), (key2331, -1)]

def rawRow7263 : Integer.Sparse Key := [(key2090, -2), (key2088, 1), (key2088, 1), (key2090, -2), (key2083, 1), (key2083, 1), (key2088, 1), (key2088, 1), (key2083, 1), (key2083, 1), (key2081, -2), (key2081, -2), (key2298, 2), (key2290, -1), (key2290, -1), (key2298, 2), (key2282, -1), (key2282, -1), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, 2), (key2278, 2), (key2339, -1), (key2339, -1), (key2334, 1), (key2334, 1), (key2339, -1), (key2339, -1), (key2332, 1), (key2332, 1), (key2332, 1), (key2332, 1), (key2329, -1), (key2329, -1), (key2334, 1), (key2334, 1), (key2329, -1), (key2329, -1)]

def rawRow7264 : Integer.Sparse Key := [(key2178, -2), (key2180, 1), (key2180, 1), (key2278, -2), (key2282, 1), (key2282, 1), (key2329, 1), (key2329, 1), (key2331, 1), (key2331, 1), (key2332, -2), (key2332, -2), (key2081, 2), (key2088, -1), (key2088, -1), (key2178, 2), (key2190, -1), (key2190, -1), (key2331, -1), (key2331, -1), (key2334, -1), (key2334, -1), (key2339, 2), (key2339, 2), (key2083, -1), (key2083, -1), (key2090, 1), (key2090, 1), (key2180, -1), (key2180, -1), (key2190, 1), (key2190, 1), (key2290, 1), (key2290, 1), (key2298, -1), (key2298, -1), (key2332, 1), (key2332, 1), (key2339, -1), (key2339, -1)]

def rawRow7265 : Integer.Sparse Key := [(key2180, -2), (key2178, 1), (key2180, 1), (key2282, -2), (key2278, 1), (key2282, 1), (key2331, 1), (key2332, 1), (key2329, 1), (key2332, 1), (key2329, -2), (key2331, -2), (key2088, 2), (key2081, -1), (key2088, -1), (key2190, 2), (key2178, -1), (key2190, -1), (key2334, -1), (key2339, -1), (key2331, -1), (key2339, -1), (key2331, 2), (key2334, 2), (key2088, -1), (key2090, -1), (key2083, 1), (key2088, 1), (key2190, -1), (key2192, -1), (key2180, 1), (key2192, 1), (key2282, 1), (key2298, 1), (key2282, -1), (key2290, -1), (key2335, 1), (key2339, 1), (key2332, -1), (key2335, -1)]

def rawRow7266 : Integer.Sparse Key := [(key2180, -2), (key2180, 1), (key2178, 1), (key2282, -2), (key2282, 1), (key2278, 1), (key2332, 1), (key2331, 1), (key2332, 1), (key2329, 1), (key2331, -2), (key2329, -2), (key2088, 2), (key2088, -1), (key2081, -1), (key2190, 2), (key2190, -1), (key2178, -1), (key2339, -1), (key2334, -1), (key2339, -1), (key2331, -1), (key2334, 2), (key2331, 2), (key2090, -1), (key2088, -1), (key2088, 1), (key2083, 1), (key2192, -1), (key2190, -1), (key2192, 1), (key2180, 1), (key2298, 1), (key2282, 1), (key2290, -1), (key2282, -1), (key2339, 1), (key2335, 1), (key2335, -1), (key2332, -1)]

def rawRow7267 : Integer.Sparse Key := [(key2278, -2), (key2329, 1), (key2329, 1), (key2178, -2), (key2331, 1), (key2331, 1), (key2180, 1), (key2180, 1), (key2282, 1), (key2282, 1), (key2332, -2), (key2332, -2), (key2178, 2), (key2331, -1), (key2331, -1), (key2081, 2), (key2334, -1), (key2334, -1), (key2088, -1), (key2088, -1), (key2190, -1), (key2190, -1), (key2339, 2), (key2339, 2), (key2180, -1), (key2180, -1), (key2332, 1), (key2332, 1), (key2083, -1), (key2083, -1), (key2290, 1), (key2290, 1), (key2190, 1), (key2190, 1), (key2339, -1), (key2339, -1), (key2090, 1), (key2090, 1), (key2298, -1), (key2298, -1)]

def rawRow7268 : Integer.Sparse Key := [(key2329, -2), (key2278, 1), (key2329, 1), (key2331, -2), (key2178, 1), (key2331, 1), (key2282, 1), (key2332, 1), (key2180, 1), (key2332, 1), (key2180, -2), (key2282, -2), (key2331, 2), (key2178, -1), (key2331, -1), (key2334, 2), (key2081, -1), (key2334, -1), (key2190, -1), (key2339, -1), (key2088, -1), (key2339, -1), (key2088, 2), (key2190, 2), (key2282, -1), (key2332, -1), (key2180, 1), (key2282, 1), (key2290, -1), (key2335, -1), (key2083, 1), (key2335, 1), (key2088, 1), (key2339, 1), (key2088, -1), (key2190, -1), (key2192, 1), (key2298, 1), (key2090, -1), (key2192, -1)]

def rawRow7269 : Integer.Sparse Key := [(key2329, -2), (key2329, 1), (key2278, 1), (key2331, -2), (key2331, 1), (key2178, 1), (key2332, 1), (key2282, 1), (key2332, 1), (key2180, 1), (key2282, -2), (key2180, -2), (key2331, 2), (key2331, -1), (key2178, -1), (key2334, 2), (key2334, -1), (key2081, -1), (key2339, -1), (key2190, -1), (key2339, -1), (key2088, -1), (key2190, 2), (key2088, 2), (key2332, -1), (key2282, -1), (key2282, 1), (key2180, 1), (key2335, -1), (key2290, -1), (key2335, 1), (key2083, 1), (key2339, 1), (key2088, 1), (key2190, -1), (key2088, -1), (key2298, 1), (key2192, 1), (key2192, -1), (key2090, -1)]

def rawRow7270 : Integer.Sparse Key := [(key2282, -2), (key2331, 1), (key2332, 1), (key2180, -2), (key2329, 1), (key2332, 1), (key2178, 1), (key2180, 1), (key2278, 1), (key2282, 1), (key2329, -2), (key2331, -2), (key2190, 2), (key2334, -1), (key2339, -1), (key2088, 2), (key2331, -1), (key2339, -1), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, 2), (key2334, 2), (key2190, -1), (key2192, -1), (key2335, 1), (key2339, 1), (key2088, -1), (key2090, -1), (key2282, 1), (key2298, 1), (key2180, 1), (key2192, 1), (key2332, -1), (key2335, -1), (key2083, 1), (key2088, 1), (key2282, -1), (key2290, -1)]

def rawRow7271 : Integer.Sparse Key := [(key2282, -2), (key2332, 1), (key2331, 1), (key2180, -2), (key2332, 1), (key2329, 1), (key2180, 1), (key2178, 1), (key2282, 1), (key2278, 1), (key2331, -2), (key2329, -2), (key2190, 2), (key2339, -1), (key2334, -1), (key2088, 2), (key2339, -1), (key2331, -1), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, 2), (key2331, 2), (key2192, -1), (key2190, -1), (key2339, 1), (key2335, 1), (key2090, -1), (key2088, -1), (key2298, 1), (key2282, 1), (key2192, 1), (key2180, 1), (key2335, -1), (key2332, -1), (key2088, 1), (key2083, 1), (key2290, -1), (key2282, -1)]

def rawRow7272 : Integer.Sparse Key := [(key2331, -2), (key2282, 1), (key2332, 1), (key2329, -2), (key2180, 1), (key2332, 1), (key2278, 1), (key2329, 1), (key2178, 1), (key2331, 1), (key2180, -2), (key2282, -2), (key2334, 2), (key2190, -1), (key2339, -1), (key2331, 2), (key2088, -1), (key2339, -1), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, 2), (key2190, 2), (key2290, -1), (key2335, -1), (key2192, 1), (key2298, 1), (key2282, -1), (key2332, -1), (key2088, 1), (key2339, 1), (key2083, 1), (key2335, 1), (key2090, -1), (key2192, -1), (key2180, 1), (key2282, 1), (key2088, -1), (key2190, -1)]

def rawRow7273 : Integer.Sparse Key := [(key2331, -2), (key2332, 1), (key2282, 1), (key2329, -2), (key2332, 1), (key2180, 1), (key2329, 1), (key2278, 1), (key2331, 1), (key2178, 1), (key2282, -2), (key2180, -2), (key2334, 2), (key2339, -1), (key2190, -1), (key2331, 2), (key2339, -1), (key2088, -1), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, 2), (key2088, 2), (key2335, -1), (key2290, -1), (key2298, 1), (key2192, 1), (key2332, -1), (key2282, -1), (key2339, 1), (key2088, 1), (key2335, 1), (key2083, 1), (key2192, -1), (key2090, -1), (key2282, 1), (key2180, 1), (key2190, -1), (key2088, -1)]

def rawRow7274 : Integer.Sparse Key := [(key2332, -2), (key2282, 1), (key2331, 1), (key2332, -2), (key2180, 1), (key2329, 1), (key2282, 1), (key2331, 1), (key2180, 1), (key2329, 1), (key2178, -2), (key2278, -2), (key2339, 2), (key2190, -1), (key2334, -1), (key2339, 2), (key2088, -1), (key2331, -1), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, 2), (key2178, 2), (key2298, -1), (key2339, -1), (key2190, 1), (key2290, 1), (key2298, -1), (key2339, -1), (key2090, 1), (key2332, 1), (key2090, 1), (key2332, 1), (key2083, -1), (key2180, -1), (key2190, 1), (key2290, 1), (key2083, -1), (key2180, -1)]

def rawRow7275 : Integer.Sparse Key := [(key2332, -2), (key2331, 1), (key2282, 1), (key2332, -2), (key2329, 1), (key2180, 1), (key2331, 1), (key2282, 1), (key2329, 1), (key2180, 1), (key2278, -2), (key2178, -2), (key2339, 2), (key2334, -1), (key2190, -1), (key2339, 2), (key2331, -1), (key2088, -1), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, 2), (key2081, 2), (key2339, -1), (key2298, -1), (key2290, 1), (key2190, 1), (key2339, -1), (key2298, -1), (key2332, 1), (key2090, 1), (key2332, 1), (key2090, 1), (key2180, -1), (key2083, -1), (key2290, 1), (key2190, 1), (key2180, -1), (key2083, -1)]

def rawRow7276 : Integer.Sparse Key := [(key2190, -2), (key2190, 1), (key2192, 1), (key2290, -2), (key2290, 1), (key2298, 1), (key2334, 1), (key2335, 1), (key2334, 1), (key2339, 1), (key2335, -2), (key2339, -2), (key2083, 2), (key2083, -1), (key2090, -1), (key2180, 2), (key2180, -1), (key2192, -1), (key2329, -1), (key2332, -1), (key2329, -1), (key2335, -1), (key2332, 2), (key2335, 2), (key2081, -1), (key2083, -1), (key2083, 1), (key2088, 1), (key2178, -1), (key2180, -1), (key2178, 1), (key2190, 1), (key2278, 1), (key2290, 1), (key2282, -1), (key2290, -1), (key2329, 1), (key2331, 1), (key2331, -1), (key2334, -1)]

def rawRow7277 : Integer.Sparse Key := [(key2190, -2), (key2192, 1), (key2190, 1), (key2290, -2), (key2298, 1), (key2290, 1), (key2335, 1), (key2334, 1), (key2339, 1), (key2334, 1), (key2339, -2), (key2335, -2), (key2083, 2), (key2090, -1), (key2083, -1), (key2180, 2), (key2192, -1), (key2180, -1), (key2332, -1), (key2329, -1), (key2335, -1), (key2329, -1), (key2335, 2), (key2332, 2), (key2083, -1), (key2081, -1), (key2088, 1), (key2083, 1), (key2180, -1), (key2178, -1), (key2190, 1), (key2178, 1), (key2290, 1), (key2278, 1), (key2290, -1), (key2282, -1), (key2331, 1), (key2329, 1), (key2334, -1), (key2331, -1)]

def rawRow7278 : Integer.Sparse Key := [(key2192, -2), (key2190, 1), (key2190, 1), (key2298, -2), (key2290, 1), (key2290, 1), (key2339, 1), (key2339, 1), (key2335, 1), (key2335, 1), (key2334, -2), (key2334, -2), (key2090, 2), (key2083, -1), (key2083, -1), (key2192, 2), (key2180, -1), (key2180, -1), (key2335, -1), (key2335, -1), (key2332, -1), (key2332, -1), (key2329, 2), (key2329, 2), (key2088, -1), (key2088, -1), (key2081, 1), (key2081, 1), (key2190, -1), (key2190, -1), (key2180, 1), (key2180, 1), (key2282, 1), (key2282, 1), (key2278, -1), (key2278, -1), (key2334, 1), (key2334, 1), (key2329, -1), (key2329, -1)]

def rawRow7279 : Integer.Sparse Key := [(key2290, -2), (key2334, 1), (key2335, 1), (key2190, -2), (key2334, 1), (key2339, 1), (key2190, 1), (key2192, 1), (key2290, 1), (key2298, 1), (key2335, -2), (key2339, -2), (key2180, 2), (key2329, -1), (key2332, -1), (key2083, 2), (key2329, -1), (key2335, -1), (key2083, -1), (key2090, -1), (key2180, -1), (key2192, -1), (key2332, 2), (key2335, 2), (key2178, -1), (key2180, -1), (key2329, 1), (key2331, 1), (key2081, -1), (key2083, -1), (key2278, 1), (key2290, 1), (key2178, 1), (key2190, 1), (key2331, -1), (key2334, -1), (key2083, 1), (key2088, 1), (key2282, -1), (key2290, -1)]

def rawRow7280 : Integer.Sparse Key := [(key2290, -2), (key2335, 1), (key2334, 1), (key2190, -2), (key2339, 1), (key2334, 1), (key2192, 1), (key2190, 1), (key2298, 1), (key2290, 1), (key2339, -2), (key2335, -2), (key2180, 2), (key2332, -1), (key2329, -1), (key2083, 2), (key2335, -1), (key2329, -1), (key2090, -1), (key2083, -1), (key2192, -1), (key2180, -1), (key2335, 2), (key2332, 2), (key2180, -1), (key2178, -1), (key2331, 1), (key2329, 1), (key2083, -1), (key2081, -1), (key2290, 1), (key2278, 1), (key2190, 1), (key2178, 1), (key2334, -1), (key2331, -1), (key2088, 1), (key2083, 1), (key2290, -1), (key2282, -1)]

def rawRow7281 : Integer.Sparse Key := [(key2334, -2), (key2290, 1), (key2335, 1), (key2334, -2), (key2190, 1), (key2339, 1), (key2290, 1), (key2335, 1), (key2190, 1), (key2339, 1), (key2192, -2), (key2298, -2), (key2329, 2), (key2180, -1), (key2332, -1), (key2329, 2), (key2083, -1), (key2335, -1), (key2180, -1), (key2332, -1), (key2083, -1), (key2335, -1), (key2090, 2), (key2192, 2), (key2278, -1), (key2329, -1), (key2180, 1), (key2282, 1), (key2278, -1), (key2329, -1), (key2081, 1), (key2334, 1), (key2081, 1), (key2334, 1), (key2088, -1), (key2190, -1), (key2180, 1), (key2282, 1), (key2088, -1), (key2190, -1)]

def rawRow7282 : Integer.Sparse Key := [(key2334, -2), (key2335, 1), (key2290, 1), (key2334, -2), (key2339, 1), (key2190, 1), (key2335, 1), (key2290, 1), (key2339, 1), (key2190, 1), (key2298, -2), (key2192, -2), (key2329, 2), (key2332, -1), (key2180, -1), (key2329, 2), (key2335, -1), (key2083, -1), (key2332, -1), (key2180, -1), (key2335, -1), (key2083, -1), (key2192, 2), (key2090, 2), (key2329, -1), (key2278, -1), (key2282, 1), (key2180, 1), (key2329, -1), (key2278, -1), (key2334, 1), (key2081, 1), (key2334, 1), (key2081, 1), (key2190, -1), (key2088, -1), (key2282, 1), (key2180, 1), (key2190, -1), (key2088, -1)]

def rawRow7283 : Integer.Sparse Key := [(key2335, -2), (key2290, 1), (key2334, 1), (key2339, -2), (key2190, 1), (key2334, 1), (key2298, 1), (key2339, 1), (key2192, 1), (key2335, 1), (key2190, -2), (key2290, -2), (key2332, 2), (key2180, -1), (key2329, -1), (key2335, 2), (key2083, -1), (key2329, -1), (key2192, -1), (key2335, -1), (key2090, -1), (key2332, -1), (key2083, 2), (key2180, 2), (key2282, -1), (key2331, -1), (key2178, 1), (key2278, 1), (key2290, -1), (key2334, -1), (key2083, 1), (key2329, 1), (key2088, 1), (key2331, 1), (key2081, -1), (key2178, -1), (key2190, 1), (key2290, 1), (key2083, -1), (key2180, -1)]

def rawRow7284 : Integer.Sparse Key := [(key2335, -2), (key2334, 1), (key2290, 1), (key2339, -2), (key2334, 1), (key2190, 1), (key2339, 1), (key2298, 1), (key2335, 1), (key2192, 1), (key2290, -2), (key2190, -2), (key2332, 2), (key2329, -1), (key2180, -1), (key2335, 2), (key2329, -1), (key2083, -1), (key2335, -1), (key2192, -1), (key2332, -1), (key2090, -1), (key2180, 2), (key2083, 2), (key2331, -1), (key2282, -1), (key2278, 1), (key2178, 1), (key2334, -1), (key2290, -1), (key2329, 1), (key2083, 1), (key2331, 1), (key2088, 1), (key2178, -1), (key2081, -1), (key2290, 1), (key2190, 1), (key2180, -1), (key2083, -1)]

def rawRow7285 : Integer.Sparse Key := [(key2298, -2), (key2339, 1), (key2339, 1), (key2192, -2), (key2335, 1), (key2335, 1), (key2190, 1), (key2190, 1), (key2290, 1), (key2290, 1), (key2334, -2), (key2334, -2), (key2192, 2), (key2335, -1), (key2335, -1), (key2090, 2), (key2332, -1), (key2332, -1), (key2083, -1), (key2083, -1), (key2180, -1), (key2180, -1), (key2329, 2), (key2329, 2), (key2190, -1), (key2190, -1), (key2334, 1), (key2334, 1), (key2088, -1), (key2088, -1), (key2282, 1), (key2282, 1), (key2180, 1), (key2180, 1), (key2329, -1), (key2329, -1), (key2081, 1), (key2081, 1), (key2278, -1), (key2278, -1)]

def rawRow7286 : Integer.Sparse Key := [(key2339, -2), (key2298, 1), (key2339, 1), (key2335, -2), (key2192, 1), (key2335, 1), (key2290, 1), (key2334, 1), (key2190, 1), (key2334, 1), (key2190, -2), (key2290, -2), (key2335, 2), (key2192, -1), (key2335, -1), (key2332, 2), (key2090, -1), (key2332, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2329, -1), (key2083, 2), (key2180, 2), (key2290, -1), (key2334, -1), (key2190, 1), (key2290, 1), (key2282, -1), (key2331, -1), (key2088, 1), (key2331, 1), (key2083, 1), (key2329, 1), (key2083, -1), (key2180, -1), (key2178, 1), (key2278, 1), (key2081, -1), (key2178, -1)]

def rawRow7287 : Integer.Sparse Key := [(key2339, -2), (key2339, 1), (key2298, 1), (key2335, -2), (key2335, 1), (key2192, 1), (key2334, 1), (key2290, 1), (key2334, 1), (key2190, 1), (key2290, -2), (key2190, -2), (key2335, 2), (key2335, -1), (key2192, -1), (key2332, 2), (key2332, -1), (key2090, -1), (key2329, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2180, 2), (key2083, 2), (key2334, -1), (key2290, -1), (key2290, 1), (key2190, 1), (key2331, -1), (key2282, -1), (key2331, 1), (key2088, 1), (key2329, 1), (key2083, 1), (key2180, -1), (key2083, -1), (key2278, 1), (key2178, 1), (key2178, -1), (key2081, -1)]

def rawRow7288 : Integer.Sparse Key := [(key822, 1), (key822, 1), (key823, -2), (key822, 1), (key822, 1), (key827, -2), (key827, -2), (key828, 1), (key828, 1), (key823, -2), (key828, 1), (key828, 1), (key906, -2), (key906, -2), (key910, 1), (key910, 1), (key911, 1), (key911, 1), (key910, 1), (key910, 1), (key918, -2), (key911, 1), (key911, 1), (key918, -2), (key952, 4), (key953, -2), (key953, -2), (key953, -2), (key953, -2), (key957, 4)]

def rawRow7289 : Integer.Sparse Key := [(key822, 1), (key823, 1), (key822, -2), (key827, 1), (key828, 1), (key822, -2), (key828, -2), (key822, 1), (key827, 1), (key828, -2), (key823, 1), (key828, 1), (key910, -2), (key911, -2), (key906, 1), (key911, 1), (key906, 1), (key910, 1), (key910, 1), (key918, 1), (key910, -2), (key911, 1), (key918, 1), (key911, -2), (key953, 4), (key952, -2), (key953, -2), (key953, -2), (key957, -2), (key953, 4)]

def rawRow7290 : Integer.Sparse Key := [(key823, 1), (key822, 1), (key822, -2), (key828, 1), (key827, 1), (key828, -2), (key822, -2), (key827, 1), (key822, 1), (key828, -2), (key828, 1), (key823, 1), (key911, -2), (key910, -2), (key911, 1), (key906, 1), (key910, 1), (key906, 1), (key918, 1), (key910, 1), (key910, -2), (key918, 1), (key911, 1), (key911, -2), (key953, 4), (key953, -2), (key952, -2), (key957, -2), (key953, -2), (key953, 4)]

def rawRow7291 : Integer.Sparse Key := [(key827, 1), (key828, 1), (key828, -2), (key822, 1), (key823, 1), (key822, -2), (key828, -2), (key823, 1), (key828, 1), (key822, -2), (key822, 1), (key827, 1), (key910, -2), (key911, -2), (key910, 1), (key918, 1), (key911, 1), (key918, 1), (key906, 1), (key911, 1), (key911, -2), (key906, 1), (key910, 1), (key910, -2), (key953, 4), (key953, -2), (key957, -2), (key952, -2), (key953, -2), (key953, 4)]

def rawRow7292 : Integer.Sparse Key := [(key828, 1), (key827, 1), (key828, -2), (key823, 1), (key822, 1), (key828, -2), (key822, -2), (key828, 1), (key823, 1), (key822, -2), (key827, 1), (key822, 1), (key911, -2), (key910, -2), (key918, 1), (key910, 1), (key918, 1), (key911, 1), (key911, 1), (key906, 1), (key911, -2), (key910, 1), (key906, 1), (key910, -2), (key953, 4), (key957, -2), (key953, -2), (key953, -2), (key952, -2), (key953, 4)]

def rawRow7293 : Integer.Sparse Key := [(key828, 1), (key828, 1), (key827, -2), (key828, 1), (key828, 1), (key823, -2), (key823, -2), (key822, 1), (key822, 1), (key827, -2), (key822, 1), (key822, 1), (key918, -2), (key918, -2), (key911, 1), (key911, 1), (key910, 1), (key910, 1), (key911, 1), (key911, 1), (key906, -2), (key910, 1), (key910, 1), (key906, -2), (key957, 4), (key953, -2), (key953, -2), (key953, -2), (key953, -2), (key952, 4)]

def rawRow7294 : Integer.Sparse Key := [(key822, 1), (key822, 1), (key823, -2), (key906, 1), (key906, 1), (key910, -2), (key910, -2), (key911, 1), (key911, 1), (key952, -2), (key953, 1), (key953, 1), (key822, -2), (key822, -2), (key827, 1), (key827, 1), (key828, 1), (key828, 1), (key910, 1), (key910, 1), (key918, -2), (key953, 1), (key953, 1), (key957, -2), (key823, 4), (key828, -2), (key828, -2), (key911, -2), (key911, -2), (key918, 4)]

def rawRow7295 : Integer.Sparse Key := [(key822, 1), (key823, 1), (key822, -2), (key910, 1), (key911, 1), (key906, -2), (key911, -2), (key906, 1), (key910, 1), (key953, -2), (key952, 1), (key953, 1), (key827, -2), (key828, -2), (key822, 1), (key828, 1), (key822, 1), (key827, 1), (key910, 1), (key918, 1), (key910, -2), (key953, 1), (key957, 1), (key953, -2), (key828, 4), (key823, -2), (key828, -2), (key911, -2), (key918, -2), (key911, 4)]

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

def rawRow7296 : Integer.Sparse Key := [(key823, 1), (key822, 1), (key822, -2), (key911, 1), (key910, 1), (key911, -2), (key906, -2), (key910, 1), (key906, 1), (key953, -2), (key953, 1), (key952, 1), (key828, -2), (key827, -2), (key828, 1), (key822, 1), (key827, 1), (key822, 1), (key918, 1), (key910, 1), (key910, -2), (key957, 1), (key953, 1), (key953, -2), (key828, 4), (key828, -2), (key823, -2), (key918, -2), (key911, -2), (key911, 4)]

def rawRow7297 : Integer.Sparse Key := [(key906, 1), (key906, 1), (key952, -2), (key822, 1), (key822, 1), (key910, -2), (key910, -2), (key953, 1), (key953, 1), (key823, -2), (key911, 1), (key911, 1), (key822, -2), (key822, -2), (key910, 1), (key910, 1), (key953, 1), (key953, 1), (key827, 1), (key827, 1), (key957, -2), (key828, 1), (key828, 1), (key918, -2), (key823, 4), (key911, -2), (key911, -2), (key828, -2), (key828, -2), (key918, 4)]

def rawRow7298 : Integer.Sparse Key := [(key906, 1), (key952, 1), (key906, -2), (key910, 1), (key953, 1), (key822, -2), (key953, -2), (key822, 1), (key910, 1), (key911, -2), (key823, 1), (key911, 1), (key910, -2), (key953, -2), (key822, 1), (key953, 1), (key822, 1), (key910, 1), (key827, 1), (key957, 1), (key827, -2), (key828, 1), (key918, 1), (key828, -2), (key911, 4), (key823, -2), (key911, -2), (key828, -2), (key918, -2), (key828, 4)]

def rawRow7299 : Integer.Sparse Key := [(key952, 1), (key906, 1), (key906, -2), (key953, 1), (key910, 1), (key953, -2), (key822, -2), (key910, 1), (key822, 1), (key911, -2), (key911, 1), (key823, 1), (key953, -2), (key910, -2), (key953, 1), (key822, 1), (key910, 1), (key822, 1), (key957, 1), (key827, 1), (key827, -2), (key918, 1), (key828, 1), (key828, -2), (key911, 4), (key911, -2), (key823, -2), (key918, -2), (key828, -2), (key828, 4)]

def rawRow7300 : Integer.Sparse Key := [(key910, 1), (key911, 1), (key953, -2), (key822, 1), (key823, 1), (key906, -2), (key911, -2), (key952, 1), (key953, 1), (key822, -2), (key906, 1), (key910, 1), (key827, -2), (key828, -2), (key910, 1), (key918, 1), (key953, 1), (key957, 1), (key822, 1), (key828, 1), (key953, -2), (key822, 1), (key827, 1), (key910, -2), (key828, 4), (key911, -2), (key918, -2), (key823, -2), (key828, -2), (key911, 4)]

def rawRow7301 : Integer.Sparse Key := [(key911, 1), (key910, 1), (key953, -2), (key823, 1), (key822, 1), (key911, -2), (key906, -2), (key953, 1), (key952, 1), (key822, -2), (key910, 1), (key906, 1), (key828, -2), (key827, -2), (key918, 1), (key910, 1), (key957, 1), (key953, 1), (key828, 1), (key822, 1), (key953, -2), (key827, 1), (key822, 1), (key910, -2), (key828, 4), (key918, -2), (key911, -2), (key828, -2), (key823, -2), (key911, 4)]

def rawRow7302 : Integer.Sparse Key := [(key910, 1), (key953, 1), (key911, -2), (key906, 1), (key952, 1), (key822, -2), (key953, -2), (key823, 1), (key911, 1), (key906, -2), (key822, 1), (key910, 1), (key910, -2), (key953, -2), (key827, 1), (key957, 1), (key828, 1), (key918, 1), (key822, 1), (key953, 1), (key828, -2), (key822, 1), (key910, 1), (key827, -2), (key911, 4), (key828, -2), (key918, -2), (key823, -2), (key911, -2), (key828, 4)]

def rawRow7303 : Integer.Sparse Key := [(key953, 1), (key910, 1), (key911, -2), (key952, 1), (key906, 1), (key953, -2), (key822, -2), (key911, 1), (key823, 1), (key906, -2), (key910, 1), (key822, 1), (key953, -2), (key910, -2), (key957, 1), (key827, 1), (key918, 1), (key828, 1), (key953, 1), (key822, 1), (key828, -2), (key910, 1), (key822, 1), (key827, -2), (key911, 4), (key918, -2), (key828, -2), (key911, -2), (key823, -2), (key828, 4)]

def rawRow7304 : Integer.Sparse Key := [(key911, 1), (key953, 1), (key910, -2), (key911, 1), (key953, 1), (key823, -2), (key952, -2), (key822, 1), (key906, 1), (key910, -2), (key822, 1), (key906, 1), (key918, -2), (key957, -2), (key828, 1), (key953, 1), (key827, 1), (key910, 1), (key828, 1), (key953, 1), (key822, -2), (key827, 1), (key910, 1), (key822, -2), (key918, 4), (key828, -2), (key911, -2), (key828, -2), (key911, -2), (key823, 4)]

def rawRow7305 : Integer.Sparse Key := [(key953, 1), (key911, 1), (key910, -2), (key953, 1), (key911, 1), (key952, -2), (key823, -2), (key906, 1), (key822, 1), (key910, -2), (key906, 1), (key822, 1), (key957, -2), (key918, -2), (key953, 1), (key828, 1), (key910, 1), (key827, 1), (key953, 1), (key828, 1), (key822, -2), (key910, 1), (key827, 1), (key822, -2), (key918, 4), (key911, -2), (key828, -2), (key911, -2), (key828, -2), (key823, 4)]

def rawRow7306 : Integer.Sparse Key := [(key827, 1), (key828, 1), (key828, -2), (key910, 1), (key911, 1), (key910, -2), (key918, -2), (key911, 1), (key918, 1), (key953, -2), (key953, 1), (key957, 1), (key822, -2), (key823, -2), (key822, 1), (key828, 1), (key823, 1), (key828, 1), (key906, 1), (key911, 1), (key911, -2), (key952, 1), (key953, 1), (key953, -2), (key822, 4), (key822, -2), (key827, -2), (key906, -2), (key910, -2), (key910, 4)]

def rawRow7307 : Integer.Sparse Key := [(key828, 1), (key827, 1), (key828, -2), (key911, 1), (key910, 1), (key918, -2), (key910, -2), (key918, 1), (key911, 1), (key953, -2), (key957, 1), (key953, 1), (key823, -2), (key822, -2), (key828, 1), (key822, 1), (key828, 1), (key823, 1), (key911, 1), (key906, 1), (key911, -2), (key953, 1), (key952, 1), (key953, -2), (key822, 4), (key827, -2), (key822, -2), (key910, -2), (key906, -2), (key910, 4)]

def rawRow7308 : Integer.Sparse Key := [(key828, 1), (key828, 1), (key827, -2), (key918, 1), (key918, 1), (key911, -2), (key911, -2), (key910, 1), (key910, 1), (key957, -2), (key953, 1), (key953, 1), (key828, -2), (key828, -2), (key823, 1), (key823, 1), (key822, 1), (key822, 1), (key911, 1), (key911, 1), (key906, -2), (key953, 1), (key953, 1), (key952, -2), (key827, 4), (key822, -2), (key822, -2), (key910, -2), (key910, -2), (key906, 4)]

def rawRow7309 : Integer.Sparse Key := [(key910, 1), (key911, 1), (key953, -2), (key827, 1), (key828, 1), (key910, -2), (key918, -2), (key953, 1), (key957, 1), (key828, -2), (key911, 1), (key918, 1), (key822, -2), (key823, -2), (key906, 1), (key911, 1), (key952, 1), (key953, 1), (key822, 1), (key828, 1), (key953, -2), (key823, 1), (key828, 1), (key911, -2), (key822, 4), (key906, -2), (key910, -2), (key822, -2), (key827, -2), (key910, 4)]

def rawRow7310 : Integer.Sparse Key := [(key911, 1), (key910, 1), (key953, -2), (key828, 1), (key827, 1), (key918, -2), (key910, -2), (key957, 1), (key953, 1), (key828, -2), (key918, 1), (key911, 1), (key823, -2), (key822, -2), (key911, 1), (key906, 1), (key953, 1), (key952, 1), (key828, 1), (key822, 1), (key953, -2), (key828, 1), (key823, 1), (key911, -2), (key822, 4), (key910, -2), (key906, -2), (key827, -2), (key822, -2), (key910, 4)]

def rawRow7311 : Integer.Sparse Key := [(key910, 1), (key953, 1), (key911, -2), (key910, 1), (key953, 1), (key827, -2), (key957, -2), (key828, 1), (key918, 1), (key911, -2), (key828, 1), (key918, 1), (key906, -2), (key952, -2), (key822, 1), (key953, 1), (key823, 1), (key911, 1), (key822, 1), (key953, 1), (key828, -2), (key823, 1), (key911, 1), (key828, -2), (key906, 4), (key822, -2), (key910, -2), (key822, -2), (key910, -2), (key827, 4)]

def rawRow7312 : Integer.Sparse Key := [(key953, 1), (key910, 1), (key911, -2), (key953, 1), (key910, 1), (key957, -2), (key827, -2), (key918, 1), (key828, 1), (key911, -2), (key918, 1), (key828, 1), (key952, -2), (key906, -2), (key953, 1), (key822, 1), (key911, 1), (key823, 1), (key953, 1), (key822, 1), (key828, -2), (key911, 1), (key823, 1), (key828, -2), (key906, 4), (key910, -2), (key822, -2), (key910, -2), (key822, -2), (key827, 4)]

def rawRow7313 : Integer.Sparse Key := [(key911, 1), (key953, 1), (key910, -2), (key918, 1), (key957, 1), (key828, -2), (key953, -2), (key827, 1), (key910, 1), (key918, -2), (key828, 1), (key911, 1), (key911, -2), (key953, -2), (key823, 1), (key952, 1), (key822, 1), (key906, 1), (key828, 1), (key953, 1), (key822, -2), (key828, 1), (key911, 1), (key823, -2), (key910, 4), (key822, -2), (key906, -2), (key827, -2), (key910, -2), (key822, 4)]

def rawRow7314 : Integer.Sparse Key := [(key953, 1), (key911, 1), (key910, -2), (key957, 1), (key918, 1), (key953, -2), (key828, -2), (key910, 1), (key827, 1), (key918, -2), (key911, 1), (key828, 1), (key953, -2), (key911, -2), (key952, 1), (key823, 1), (key906, 1), (key822, 1), (key953, 1), (key828, 1), (key822, -2), (key911, 1), (key828, 1), (key823, -2), (key910, 4), (key906, -2), (key822, -2), (key910, -2), (key827, -2), (key822, 4)]

def rawRow7315 : Integer.Sparse Key := [(key918, 1), (key918, 1), (key957, -2), (key828, 1), (key828, 1), (key911, -2), (key911, -2), (key953, 1), (key953, 1), (key827, -2), (key910, 1), (key910, 1), (key828, -2), (key828, -2), (key911, 1), (key911, 1), (key953, 1), (key953, 1), (key823, 1), (key823, 1), (key952, -2), (key822, 1), (key822, 1), (key906, -2), (key827, 4), (key910, -2), (key910, -2), (key822, -2), (key822, -2), (key906, 4)]

def rawRow7316 : Integer.Sparse Key := [(key918, 1), (key957, 1), (key918, -2), (key911, 1), (key953, 1), (key828, -2), (key953, -2), (key828, 1), (key911, 1), (key910, -2), (key827, 1), (key910, 1), (key911, -2), (key953, -2), (key828, 1), (key953, 1), (key828, 1), (key911, 1), (key823, 1), (key952, 1), (key823, -2), (key822, 1), (key906, 1), (key822, -2), (key910, 4), (key827, -2), (key910, -2), (key822, -2), (key906, -2), (key822, 4)]

def rawRow7317 : Integer.Sparse Key := [(key957, 1), (key918, 1), (key918, -2), (key953, 1), (key911, 1), (key953, -2), (key828, -2), (key911, 1), (key828, 1), (key910, -2), (key910, 1), (key827, 1), (key953, -2), (key911, -2), (key953, 1), (key828, 1), (key911, 1), (key828, 1), (key952, 1), (key823, 1), (key823, -2), (key906, 1), (key822, 1), (key822, -2), (key910, 4), (key910, -2), (key827, -2), (key906, -2), (key822, -2), (key822, 4)]

def rawRow7318 : Integer.Sparse Key := [(key781, -4), (key784, 2), (key784, 2), (key784, 2), (key784, 2), (key786, -4), (key806, 2), (key809, -1), (key809, -1), (key806, 2), (key814, -1), (key814, -1), (key809, -1), (key809, -1), (key814, -1), (key814, -1), (key816, 2), (key816, 2), (key822, -1), (key822, -1), (key823, 2), (key822, -1), (key822, -1), (key827, 2), (key827, 2), (key828, -1), (key828, -1), (key823, 2), (key828, -1), (key828, -1)]

def rawRow7319 : Integer.Sparse Key := [(key784, -4), (key781, 2), (key784, 2), (key784, 2), (key786, 2), (key784, -4), (key809, 2), (key806, -1), (key809, -1), (key814, 2), (key806, -1), (key814, -1), (key814, -1), (key816, -1), (key809, -1), (key816, -1), (key809, 2), (key814, 2), (key822, -1), (key823, -1), (key822, 2), (key827, -1), (key828, -1), (key822, 2), (key828, 2), (key822, -1), (key827, -1), (key828, 2), (key823, -1), (key828, -1)]

def rawRow7320 : Integer.Sparse Key := [(key784, -4), (key784, 2), (key781, 2), (key786, 2), (key784, 2), (key784, -4), (key809, 2), (key809, -1), (key806, -1), (key814, 2), (key814, -1), (key806, -1), (key816, -1), (key814, -1), (key816, -1), (key809, -1), (key814, 2), (key809, 2), (key823, -1), (key822, -1), (key822, 2), (key828, -1), (key827, -1), (key828, 2), (key822, 2), (key827, -1), (key822, -1), (key828, 2), (key828, -1), (key823, -1)]

def rawRow7321 : Integer.Sparse Key := [(key784, -4), (key784, 2), (key786, 2), (key781, 2), (key784, 2), (key784, -4), (key814, 2), (key814, -1), (key816, -1), (key809, 2), (key809, -1), (key816, -1), (key806, -1), (key809, -1), (key806, -1), (key814, -1), (key809, 2), (key814, 2), (key827, -1), (key828, -1), (key828, 2), (key822, -1), (key823, -1), (key822, 2), (key828, 2), (key823, -1), (key828, -1), (key822, 2), (key822, -1), (key827, -1)]

def rawRow7322 : Integer.Sparse Key := [(key784, -4), (key786, 2), (key784, 2), (key784, 2), (key781, 2), (key784, -4), (key814, 2), (key816, -1), (key814, -1), (key809, 2), (key816, -1), (key809, -1), (key809, -1), (key806, -1), (key814, -1), (key806, -1), (key814, 2), (key809, 2), (key828, -1), (key827, -1), (key828, 2), (key823, -1), (key822, -1), (key828, 2), (key822, 2), (key828, -1), (key823, -1), (key822, 2), (key827, -1), (key822, -1)]

def rawRow7323 : Integer.Sparse Key := [(key786, -4), (key784, 2), (key784, 2), (key784, 2), (key784, 2), (key781, -4), (key816, 2), (key814, -1), (key814, -1), (key816, 2), (key809, -1), (key809, -1), (key814, -1), (key814, -1), (key809, -1), (key809, -1), (key806, 2), (key806, 2), (key828, -1), (key828, -1), (key827, 2), (key828, -1), (key828, -1), (key823, 2), (key823, 2), (key822, -1), (key822, -1), (key827, 2), (key822, -1), (key822, -1)]

def rawRow7324 : Integer.Sparse Key := [(key806, -4), (key809, 2), (key809, 2), (key814, 2), (key814, 2), (key816, -4), (key781, 2), (key784, -1), (key784, -1), (key806, 2), (key814, -1), (key814, -1), (key822, -1), (key822, -1), (key827, -1), (key827, -1), (key828, 2), (key828, 2), (key784, -1), (key784, -1), (key786, 2), (key809, -1), (key809, -1), (key814, 2), (key814, 2), (key816, -1), (key816, -1), (key823, 2), (key828, -1), (key828, -1)]

def rawRow7325 : Integer.Sparse Key := [(key809, -4), (key806, 2), (key809, 2), (key814, 2), (key816, 2), (key814, -4), (key784, 2), (key781, -1), (key784, -1), (key814, 2), (key806, -1), (key814, -1), (key827, -1), (key828, -1), (key822, -1), (key828, -1), (key822, 2), (key827, 2), (key784, -1), (key786, -1), (key784, 2), (key814, -1), (key816, -1), (key809, 2), (key816, 2), (key809, -1), (key814, -1), (key828, 2), (key823, -1), (key828, -1)]

def rawRow7326 : Integer.Sparse Key := [(key809, -4), (key809, 2), (key806, 2), (key816, 2), (key814, 2), (key814, -4), (key784, 2), (key784, -1), (key781, -1), (key814, 2), (key814, -1), (key806, -1), (key828, -1), (key827, -1), (key828, -1), (key822, -1), (key827, 2), (key822, 2), (key786, -1), (key784, -1), (key784, 2), (key816, -1), (key814, -1), (key816, 2), (key809, 2), (key814, -1), (key809, -1), (key828, 2), (key828, -1), (key823, -1)]

def rawRow7327 : Integer.Sparse Key := [(key806, -4), (key814, 2), (key814, 2), (key809, 2), (key809, 2), (key816, -4), (key806, 2), (key814, -1), (key814, -1), (key781, 2), (key827, -1), (key827, -1), (key784, -1), (key784, -1), (key814, -1), (key814, -1), (key828, 2), (key828, 2), (key809, -1), (key809, -1), (key823, 2), (key784, -1), (key784, -1), (key814, 2), (key814, 2), (key828, -1), (key828, -1), (key786, 2), (key816, -1), (key816, -1)]

def rawRow7328 : Integer.Sparse Key := [(key814, -4), (key806, 2), (key814, 2), (key809, 2), (key816, 2), (key809, -4), (key814, 2), (key806, -1), (key814, -1), (key827, 2), (key781, -1), (key827, -1), (key814, -1), (key828, -1), (key784, -1), (key828, -1), (key784, 2), (key814, 2), (key809, -1), (key823, -1), (key809, 2), (key814, -1), (key828, -1), (key784, 2), (key828, 2), (key784, -1), (key814, -1), (key816, 2), (key786, -1), (key816, -1)]

def rawRow7329 : Integer.Sparse Key := [(key814, -4), (key814, 2), (key806, 2), (key816, 2), (key809, 2), (key809, -4), (key814, 2), (key814, -1), (key806, -1), (key827, 2), (key827, -1), (key781, -1), (key828, -1), (key814, -1), (key828, -1), (key784, -1), (key814, 2), (key784, 2), (key823, -1), (key809, -1), (key809, 2), (key828, -1), (key814, -1), (key828, 2), (key784, 2), (key814, -1), (key784, -1), (key816, 2), (key816, -1), (key786, -1)]

def rawRow7330 : Integer.Sparse Key := [(key809, -4), (key814, 2), (key816, 2), (key806, 2), (key809, 2), (key814, -4), (key822, 2), (key827, -1), (key828, -1), (key784, 2), (key814, -1), (key828, -1), (key781, -1), (key784, -1), (key806, -1), (key814, -1), (key822, 2), (key827, 2), (key814, -1), (key816, -1), (key828, 2), (key784, -1), (key786, -1), (key809, 2), (key816, 2), (key823, -1), (key828, -1), (key784, 2), (key809, -1), (key814, -1)]

def rawRow7331 : Integer.Sparse Key := [(key809, -4), (key816, 2), (key814, 2), (key809, 2), (key806, 2), (key814, -4), (key822, 2), (key828, -1), (key827, -1), (key784, 2), (key828, -1), (key814, -1), (key784, -1), (key781, -1), (key814, -1), (key806, -1), (key827, 2), (key822, 2), (key816, -1), (key814, -1), (key828, 2), (key786, -1), (key784, -1), (key816, 2), (key809, 2), (key828, -1), (key823, -1), (key784, 2), (key814, -1), (key809, -1)]

def rawRow7332 : Integer.Sparse Key := [(key814, -4), (key809, 2), (key816, 2), (key806, 2), (key814, 2), (key809, -4), (key827, 2), (key822, -1), (key828, -1), (key814, 2), (key784, -1), (key828, -1), (key806, -1), (key814, -1), (key781, -1), (key827, -1), (key784, 2), (key814, 2), (key814, -1), (key828, -1), (key816, 2), (key809, -1), (key823, -1), (key784, 2), (key828, 2), (key786, -1), (key816, -1), (key809, 2), (key784, -1), (key814, -1)]

def rawRow7333 : Integer.Sparse Key := [(key814, -4), (key816, 2), (key809, 2), (key814, 2), (key806, 2), (key809, -4), (key827, 2), (key828, -1), (key822, -1), (key814, 2), (key828, -1), (key784, -1), (key814, -1), (key806, -1), (key827, -1), (key781, -1), (key814, 2), (key784, 2), (key828, -1), (key814, -1), (key816, 2), (key823, -1), (key809, -1), (key828, 2), (key784, 2), (key816, -1), (key786, -1), (key809, 2), (key814, -1), (key784, -1)]

def rawRow7334 : Integer.Sparse Key := [(key816, -4), (key809, 2), (key814, 2), (key809, 2), (key814, 2), (key806, -4), (key828, 2), (key822, -1), (key827, -1), (key828, 2), (key784, -1), (key814, -1), (key822, -1), (key827, -1), (key784, -1), (key814, -1), (key781, 2), (key806, 2), (key816, -1), (key828, -1), (key814, 2), (key816, -1), (key828, -1), (key786, 2), (key823, 2), (key784, -1), (key809, -1), (key814, 2), (key784, -1), (key809, -1)]

def rawRow7335 : Integer.Sparse Key := [(key816, -4), (key814, 2), (key809, 2), (key814, 2), (key809, 2), (key806, -4), (key828, 2), (key827, -1), (key822, -1), (key828, 2), (key814, -1), (key784, -1), (key827, -1), (key822, -1), (key814, -1), (key784, -1), (key806, 2), (key781, 2), (key828, -1), (key816, -1), (key814, 2), (key828, -1), (key816, -1), (key823, 2), (key786, 2), (key809, -1), (key784, -1), (key814, 2), (key809, -1), (key784, -1)]

def rawRow7336 : Integer.Sparse Key := [(key822, -4), (key822, 2), (key823, 2), (key827, 2), (key828, 2), (key828, -4), (key784, 2), (key784, -1), (key786, -1), (key809, 2), (key809, -1), (key823, -1), (key814, -1), (key816, -1), (key814, -1), (key828, -1), (key816, 2), (key828, 2), (key781, -1), (key784, -1), (key784, 2), (key806, -1), (key809, -1), (key806, 2), (key814, 2), (key809, -1), (key814, -1), (key822, 2), (key822, -1), (key827, -1)]

def rawRow7337 : Integer.Sparse Key := [(key822, -4), (key823, 2), (key822, 2), (key828, 2), (key827, 2), (key828, -4), (key784, 2), (key786, -1), (key784, -1), (key809, 2), (key823, -1), (key809, -1), (key816, -1), (key814, -1), (key828, -1), (key814, -1), (key828, 2), (key816, 2), (key784, -1), (key781, -1), (key784, 2), (key809, -1), (key806, -1), (key814, 2), (key806, 2), (key814, -1), (key809, -1), (key822, 2), (key827, -1), (key822, -1)]

def rawRow7338 : Integer.Sparse Key := [(key823, -4), (key822, 2), (key822, 2), (key828, 2), (key828, 2), (key827, -4), (key786, 2), (key784, -1), (key784, -1), (key823, 2), (key809, -1), (key809, -1), (key828, -1), (key828, -1), (key816, -1), (key816, -1), (key814, 2), (key814, 2), (key784, -1), (key784, -1), (key781, 2), (key814, -1), (key814, -1), (key809, 2), (key809, 2), (key806, -1), (key806, -1), (key827, 2), (key822, -1), (key822, -1)]

def rawRow7339 : Integer.Sparse Key := [(key822, -4), (key827, 2), (key828, 2), (key822, 2), (key823, 2), (key828, -4), (key809, 2), (key814, -1), (key816, -1), (key784, 2), (key814, -1), (key828, -1), (key784, -1), (key786, -1), (key809, -1), (key823, -1), (key816, 2), (key828, 2), (key806, -1), (key809, -1), (key814, 2), (key781, -1), (key784, -1), (key806, 2), (key814, 2), (key822, -1), (key827, -1), (key784, 2), (key809, -1), (key814, -1)]

def rawRow7340 : Integer.Sparse Key := [(key822, -4), (key828, 2), (key827, 2), (key823, 2), (key822, 2), (key828, -4), (key809, 2), (key816, -1), (key814, -1), (key784, 2), (key828, -1), (key814, -1), (key786, -1), (key784, -1), (key823, -1), (key809, -1), (key828, 2), (key816, 2), (key809, -1), (key806, -1), (key814, 2), (key784, -1), (key781, -1), (key814, 2), (key806, 2), (key827, -1), (key822, -1), (key784, 2), (key814, -1), (key809, -1)]

def rawRow7341 : Integer.Sparse Key := [(key827, -4), (key822, 2), (key828, 2), (key822, 2), (key828, 2), (key823, -4), (key814, 2), (key809, -1), (key816, -1), (key814, 2), (key784, -1), (key828, -1), (key809, -1), (key816, -1), (key784, -1), (key828, -1), (key786, 2), (key823, 2), (key806, -1), (key814, -1), (key809, 2), (key806, -1), (key814, -1), (key781, 2), (key827, 2), (key784, -1), (key814, -1), (key809, 2), (key784, -1), (key814, -1)]

def rawRow7342 : Integer.Sparse Key := [(key827, -4), (key828, 2), (key822, 2), (key828, 2), (key822, 2), (key823, -4), (key814, 2), (key816, -1), (key809, -1), (key814, 2), (key828, -1), (key784, -1), (key816, -1), (key809, -1), (key828, -1), (key784, -1), (key823, 2), (key786, 2), (key814, -1), (key806, -1), (key809, 2), (key814, -1), (key806, -1), (key827, 2), (key781, 2), (key814, -1), (key784, -1), (key809, 2), (key814, -1), (key784, -1)]

def rawRow7343 : Integer.Sparse Key := [(key828, -4), (key822, 2), (key827, 2), (key823, 2), (key828, 2), (key822, -4), (key816, 2), (key809, -1), (key814, -1), (key828, 2), (key784, -1), (key814, -1), (key823, -1), (key828, -1), (key786, -1), (key816, -1), (key784, 2), (key809, 2), (key809, -1), (key814, -1), (key806, 2), (key822, -1), (key827, -1), (key784, 2), (key814, 2), (key781, -1), (key806, -1), (key814, 2), (key784, -1), (key809, -1)]

def rawRow7344 : Integer.Sparse Key := [(key828, -4), (key827, 2), (key822, 2), (key828, 2), (key823, 2), (key822, -4), (key816, 2), (key814, -1), (key809, -1), (key828, 2), (key814, -1), (key784, -1), (key828, -1), (key823, -1), (key816, -1), (key786, -1), (key809, 2), (key784, 2), (key814, -1), (key809, -1), (key806, 2), (key827, -1), (key822, -1), (key814, 2), (key784, 2), (key806, -1), (key781, -1), (key814, 2), (key809, -1), (key784, -1)]

def rawRow7345 : Integer.Sparse Key := [(key823, -4), (key828, 2), (key828, 2), (key822, 2), (key822, 2), (key827, -4), (key823, 2), (key828, -1), (key828, -1), (key786, 2), (key816, -1), (key816, -1), (key784, -1), (key784, -1), (key809, -1), (key809, -1), (key814, 2), (key814, 2), (key822, -1), (key822, -1), (key827, 2), (key784, -1), (key784, -1), (key809, 2), (key809, 2), (key814, -1), (key814, -1), (key781, 2), (key806, -1), (key806, -1)]

def rawRow7346 : Integer.Sparse Key := [(key828, -4), (key823, 2), (key828, 2), (key822, 2), (key827, 2), (key822, -4), (key828, 2), (key823, -1), (key828, -1), (key816, 2), (key786, -1), (key816, -1), (key809, -1), (key814, -1), (key784, -1), (key814, -1), (key784, 2), (key809, 2), (key822, -1), (key827, -1), (key822, 2), (key809, -1), (key814, -1), (key784, 2), (key814, 2), (key784, -1), (key809, -1), (key806, 2), (key781, -1), (key806, -1)]

def rawRow7347 : Integer.Sparse Key := [(key828, -4), (key828, 2), (key823, 2), (key827, 2), (key822, 2), (key822, -4), (key828, 2), (key828, -1), (key823, -1), (key816, 2), (key816, -1), (key786, -1), (key814, -1), (key809, -1), (key814, -1), (key784, -1), (key809, 2), (key784, 2), (key827, -1), (key822, -1), (key822, 2), (key814, -1), (key809, -1), (key814, 2), (key784, 2), (key809, -1), (key784, -1), (key806, 2), (key806, -1), (key781, -1)]

def rawRow7348 : Integer.Sparse Key := [(key2362, 2), (key2365, 2), (key2365, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2532, 2), (key2532, 2), (key2562, 2), (key2562, 2), (key2564, 2), (key2564, 2), (key2365, -2), (key2365, -2), (key2367, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2525, -2), (key2525, -2), (key2533, -2), (key2564, -2), (key2564, -2)]

def rawRow7349 : Integer.Sparse Key := [(key2365, 2), (key2362, 2), (key2365, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2365, -2), (key2367, -2), (key2365, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2564, -2), (key2533, -2), (key2564, -2)]

def rawRow7350 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2362, 2), (key2521, 2), (key2521, 2), (key2457, 2), (key2564, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, 2), (key2367, -2), (key2365, -2), (key2365, -2), (key2525, -2), (key2521, -2), (key2525, -2), (key2460, -2), (key2521, -2), (key2460, -2), (key2564, -2), (key2564, -2), (key2533, -2)]

def rawRow7351 : Integer.Sparse Key := [(key2457, 2), (key2521, 2), (key2521, 2), (key2362, 2), (key2562, 2), (key2562, 2), (key2365, 2), (key2365, 2), (key2521, 2), (key2521, 2), (key2564, 2), (key2564, 2), (key2460, -2), (key2460, -2), (key2533, -2), (key2365, -2), (key2365, -2), (key2521, -2), (key2521, -2), (key2564, -2), (key2564, -2), (key2367, -2), (key2525, -2), (key2525, -2)]

def rawRow7352 : Integer.Sparse Key := [(key2521, 2), (key2457, 2), (key2521, 2), (key2562, 2), (key2362, 2), (key2562, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2460, -2), (key2533, -2), (key2460, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2525, -2), (key2367, -2), (key2525, -2)]

def rawRow7353 : Integer.Sparse Key := [(key2521, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2562, 2), (key2362, 2), (key2564, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2365, 2), (key2533, -2), (key2460, -2), (key2460, -2), (key2564, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2525, -2), (key2525, -2), (key2367, -2)]

def rawRow7354 : Integer.Sparse Key := [(key2532, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2564, 2), (key2362, 2), (key2365, 2), (key2457, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2521, -2), (key2525, -2), (key2564, -2), (key2365, -2), (key2367, -2), (key2460, -2), (key2525, -2), (key2533, -2), (key2564, -2), (key2365, -2), (key2460, -2), (key2521, -2)]

def rawRow7355 : Integer.Sparse Key := [(key2532, 2), (key2564, 2), (key2562, 2), (key2365, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2362, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2532, 2), (key2525, -2), (key2521, -2), (key2564, -2), (key2367, -2), (key2365, -2), (key2525, -2), (key2460, -2), (key2564, -2), (key2533, -2), (key2365, -2), (key2521, -2), (key2460, -2)]

def rawRow7356 : Integer.Sparse Key := [(key2562, 2), (key2532, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2457, 2), (key2521, 2), (key2362, 2), (key2562, 2), (key2365, 2), (key2521, 2), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, -2), (key2533, -2), (key2365, -2), (key2564, -2), (key2367, -2), (key2525, -2), (key2460, -2), (key2365, -2), (key2521, -2)]

def rawRow7357 : Integer.Sparse Key := [(key2562, 2), (key2564, 2), (key2532, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2457, 2), (key2562, 2), (key2362, 2), (key2521, 2), (key2365, 2), (key2564, -2), (key2521, -2), (key2525, -2), (key2533, -2), (key2460, -2), (key2564, -2), (key2365, -2), (key2525, -2), (key2367, -2), (key2460, -2), (key2521, -2), (key2365, -2)]

def rawRow7358 : Integer.Sparse Key := [(key2564, 2), (key2532, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2365, 2), (key2521, 2), (key2362, 2), (key2457, 2), (key2525, -2), (key2564, -2), (key2521, -2), (key2525, -2), (key2564, -2), (key2367, -2), (key2533, -2), (key2365, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2460, -2)]

def rawRow7359 : Integer.Sparse Key := [(key2564, 2), (key2562, 2), (key2532, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2562, 2), (key2532, 2), (key2521, 2), (key2365, 2), (key2457, 2), (key2362, 2), (key2564, -2), (key2525, -2), (key2521, -2), (key2564, -2), (key2525, -2), (key2533, -2), (key2367, -2), (key2460, -2), (key2365, -2), (key2521, -2), (key2460, -2), (key2365, -2)]

def rawRow7360 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2367, 2), (key2460, 2), (key2460, 2), (key2533, 2), (key2521, 2), (key2525, 2), (key2521, 2), (key2564, 2), (key2525, 2), (key2564, 2), (key2362, -2), (key2365, -2), (key2365, -2), (key2457, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2532, -2), (key2532, -2), (key2562, -2)]

def rawRow7361 : Integer.Sparse Key := [(key2365, 2), (key2367, 2), (key2365, 2), (key2460, 2), (key2533, 2), (key2460, 2), (key2525, 2), (key2521, 2), (key2564, 2), (key2521, 2), (key2564, 2), (key2525, 2), (key2365, -2), (key2362, -2), (key2365, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2457, -2), (key2521, -2), (key2460, -2), (key2532, -2), (key2562, -2), (key2532, -2)]

def rawRow7362 : Integer.Sparse Key := [(key2367, 2), (key2365, 2), (key2365, 2), (key2533, 2), (key2460, 2), (key2460, 2), (key2564, 2), (key2564, 2), (key2525, 2), (key2525, 2), (key2521, 2), (key2521, 2), (key2365, -2), (key2365, -2), (key2362, -2), (key2521, -2), (key2521, -2), (key2460, -2), (key2460, -2), (key2457, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2532, -2)]

def rawRow7363 : Integer.Sparse Key := [(key2460, 2), (key2521, 2), (key2525, 2), (key2365, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2367, 2), (key2460, 2), (key2533, 2), (key2525, 2), (key2564, 2), (key2457, -2), (key2460, -2), (key2521, -2), (key2362, -2), (key2365, -2), (key2457, -2), (key2521, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2460, -2), (key2521, -2)]

def rawRow7364 : Integer.Sparse Key := [(key2460, 2), (key2525, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2521, 2), (key2367, 2), (key2365, 2), (key2533, 2), (key2460, 2), (key2564, 2), (key2525, 2), (key2460, -2), (key2457, -2), (key2521, -2), (key2365, -2), (key2362, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2365, -2), (key2521, -2), (key2460, -2)]

def rawRow7365 : Integer.Sparse Key := [(key2521, 2), (key2460, 2), (key2525, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2460, 2), (key2525, 2), (key2365, 2), (key2564, 2), (key2367, 2), (key2533, 2), (key2457, -2), (key2521, -2), (key2460, -2), (key2457, -2), (key2521, -2), (key2362, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2460, -2), (key2365, -2), (key2521, -2)]

def rawRow7366 : Integer.Sparse Key := [(key2521, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2525, 2), (key2460, 2), (key2564, 2), (key2365, 2), (key2533, 2), (key2367, 2), (key2521, -2), (key2457, -2), (key2460, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2362, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2521, -2), (key2365, -2)]

def rawRow7367 : Integer.Sparse Key := [(key2525, 2), (key2460, 2), (key2521, 2), (key2564, 2), (key2365, 2), (key2521, 2), (key2533, 2), (key2564, 2), (key2367, 2), (key2525, 2), (key2365, 2), (key2460, 2), (key2460, -2), (key2521, -2), (key2457, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2362, -2), (key2457, -2), (key2521, -2), (key2365, -2), (key2460, -2)]

def rawRow7368 : Integer.Sparse Key := [(key2525, 2), (key2521, 2), (key2460, 2), (key2564, 2), (key2521, 2), (key2365, 2), (key2564, 2), (key2533, 2), (key2525, 2), (key2367, 2), (key2460, 2), (key2365, 2), (key2521, -2), (key2460, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2521, -2), (key2365, -2), (key2457, -2), (key2362, -2), (key2521, -2), (key2460, -2), (key2365, -2)]

def rawRow7369 : Integer.Sparse Key := [(key2533, 2), (key2564, 2), (key2564, 2), (key2367, 2), (key2525, 2), (key2525, 2), (key2365, 2), (key2365, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2532, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2365, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2362, -2), (key2457, -2), (key2457, -2)]

def rawRow7370 : Integer.Sparse Key := [(key2564, 2), (key2533, 2), (key2564, 2), (key2525, 2), (key2367, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2365, 2), (key2521, 2), (key2365, 2), (key2460, 2), (key2532, -2), (key2562, -2), (key2532, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2457, -2), (key2362, -2), (key2457, -2)]

def rawRow7371 : Integer.Sparse Key := [(key2564, 2), (key2564, 2), (key2533, 2), (key2525, 2), (key2525, 2), (key2367, 2), (key2521, 2), (key2460, 2), (key2521, 2), (key2365, 2), (key2460, 2), (key2365, 2), (key2562, -2), (key2532, -2), (key2532, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2365, -2), (key2457, -2), (key2457, -2), (key2362, -2)]

def rawRow7372 : Integer.Sparse Key := [(key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2), (key1178, -2)]

def rawRow7373 : Integer.Sparse Key := [(key974, 2), (key974, 2), (key974, 2), (key1088, 2), (key1088, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key1178, 2), (key974, -2), (key974, -2), (key974, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key1178, -2), (key1178, -2)]

def rawRow7374 : Integer.Sparse Key := [(key1088, 2), (key1178, 2), (key1178, 2), (key974, 2), (key1178, 2), (key1178, 2), (key974, 2), (key974, 2), (key1088, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key1088, -2), (key1088, -2), (key1178, -2), (key974, -2), (key974, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key1178, -2), (key974, -2), (key1088, -2), (key1088, -2)]

def rawRow7375 : Integer.Sparse Key := [(key1178, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key974, 2), (key1178, 2), (key1088, 2), (key1178, 2), (key974, 2), (key1178, 2), (key974, 2), (key1088, 2), (key1088, -2), (key1178, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key974, -2), (key1178, -2), (key974, -2), (key1088, -2), (key1088, -2), (key974, -2), (key1088, -2)]

def rawRow7376 : Integer.Sparse Key := [(key1178, 2), (key1178, 2), (key1088, 2), (key1178, 2), (key1178, 2), (key974, 2), (key1178, 2), (key1088, 2), (key1178, 2), (key974, 2), (key1088, 2), (key974, 2), (key1178, -2), (key1088, -2), (key1088, -2), (key1178, -2), (key1088, -2), (key1178, -2), (key974, -2), (key1088, -2), (key974, -2), (key1088, -2), (key1088, -2), (key974, -2)]

def rawRow7381 : Integer.Sparse Key := [(key83, -24), (key83, 6), (key83, 6), (key83, 6), (key0, 6)]

def rawRow7382 : Integer.Sparse Key := [(key1090, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1169, 2), (key1098, 2), (key1169, 2), (key1180, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1220, -2)]

def rawRow7383 : Integer.Sparse Key := [(key1090, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1169, 2), (key1098, 2), (key1183, -2), (key1180, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1220, -2), (key1183, -2)]

def rawRow7384 : Integer.Sparse Key := [(key1098, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1169, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1183, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1183, -2)]

def rawRow7385 : Integer.Sparse Key := [(key1169, 2), (key1169, 2), (key1169, 2), (key1098, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1090, 2), (key1220, -2), (key1220, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1180, -2), (key1180, -2)]

def rawRow7386 : Integer.Sparse Key := [(key976, 2), (key976, 2), (key984, 2), (key1090, 2), (key1090, 2), (key1169, 2), (key1180, 2), (key1183, 2), (key1180, 2), (key1220, 2), (key1183, 2), (key1220, 2), (key976, -2), (key984, -2), (key984, -2), (key1090, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1169, -2), (key1183, -2), (key1183, -2), (key1220, -2)]

def rawRow7387 : Integer.Sparse Key := [(key976, 2), (key984, 2), (key976, 2), (key1090, 2), (key1169, 2), (key1090, 2), (key1183, 2), (key1180, 2), (key1220, 2), (key1180, 2), (key1220, 2), (key1183, 2), (key984, -2), (key976, -2), (key984, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1183, -2), (key1220, -2), (key1183, -2)]

def rawRow7388 : Integer.Sparse Key := [(key984, 2), (key976, 2), (key976, 2), (key1169, 2), (key1090, 2), (key1090, 2), (key1220, 2), (key1220, 2), (key1183, 2), (key1183, 2), (key1180, 2), (key1180, 2), (key984, -2), (key984, -2), (key976, -2), (key1169, -2), (key1169, -2), (key1098, -2), (key1098, -2), (key1090, -2), (key1090, -2), (key1220, -2), (key1183, -2), (key1183, -2)]

def rawRow7389 : Integer.Sparse Key := [(key1090, 2), (key1180, 2), (key1183, 2), (key976, 2), (key1180, 2), (key1220, 2), (key976, 2), (key984, 2), (key1090, 2), (key1169, 2), (key1183, 2), (key1220, 2), (key1090, -2), (key1098, -2), (key1183, -2), (key976, -2), (key984, -2), (key1090, -2), (key1169, -2), (key1183, -2), (key1220, -2), (key984, -2), (key1098, -2), (key1169, -2)]

def rawRow7390 : Integer.Sparse Key := [(key1090, 2), (key1183, 2), (key1180, 2), (key976, 2), (key1220, 2), (key1180, 2), (key984, 2), (key976, 2), (key1169, 2), (key1090, 2), (key1220, 2), (key1183, 2), (key1098, -2), (key1090, -2), (key1183, -2), (key984, -2), (key976, -2), (key1169, -2), (key1090, -2), (key1220, -2), (key1183, -2), (key984, -2), (key1169, -2), (key1098, -2)]

def rawRow7391 : Integer.Sparse Key := [(key1180, 2), (key1090, 2), (key1183, 2), (key1180, 2), (key976, 2), (key1220, 2), (key1090, 2), (key1183, 2), (key976, 2), (key1220, 2), (key984, 2), (key1169, 2), (key1090, -2), (key1183, -2), (key1098, -2), (key1090, -2), (key1183, -2), (key976, -2), (key1220, -2), (key984, -2), (key1169, -2), (key1098, -2), (key984, -2), (key1169, -2)]

def rawRow7392 : Integer.Sparse Key := [(key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1220, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1169, 2), (key984, 2), (key1183, -2), (key1090, -2), (key1098, -2), (key1183, -2), (key1090, -2), (key1220, -2), (key976, -2), (key1169, -2), (key984, -2), (key1098, -2), (key1169, -2), (key984, -2)]

def rawRow7393 : Integer.Sparse Key := [(key1183, 2), (key1090, 2), (key1180, 2), (key1220, 2), (key976, 2), (key1180, 2), (key1169, 2), (key1220, 2), (key984, 2), (key1183, 2), (key976, 2), (key1090, 2), (key1098, -2), (key1183, -2), (key1090, -2), (key1169, -2), (key1220, -2), (key984, -2), (key1183, -2), (key976, -2), (key1090, -2), (key1169, -2), (key984, -2), (key1098, -2)]

def rawRow7394 : Integer.Sparse Key := [(key1183, 2), (key1180, 2), (key1090, 2), (key1220, 2), (key1180, 2), (key976, 2), (key1220, 2), (key1169, 2), (key1183, 2), (key984, 2), (key1090, 2), (key976, 2), (key1183, -2), (key1098, -2), (key1090, -2), (key1220, -2), (key1169, -2), (key1183, -2), (key984, -2), (key1090, -2), (key976, -2), (key1169, -2), (key1098, -2), (key984, -2)]

def rawRow7395 : Integer.Sparse Key := [(key1169, 2), (key1220, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1183, 2), (key976, 2), (key976, 2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1169, -2), (key1169, -2), (key1220, -2), (key984, -2), (key984, -2), (key1098, -2), (key1098, -2), (key1183, -2), (key1183, -2), (key976, -2), (key1090, -2), (key1090, -2)]

def rawRow7396 : Integer.Sparse Key := [(key1220, 2), (key1169, 2), (key1220, 2), (key1183, 2), (key984, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key976, 2), (key1180, 2), (key976, 2), (key1090, 2), (key1169, -2), (key1220, -2), (key1169, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, -2), (key976, -2), (key1090, -2)]

def rawRow7397 : Integer.Sparse Key := [(key1220, 2), (key1220, 2), (key1169, 2), (key1183, 2), (key1183, 2), (key984, 2), (key1180, 2), (key1090, 2), (key1180, 2), (key976, 2), (key1090, 2), (key976, 2), (key1220, -2), (key1169, -2), (key1169, -2), (key1183, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1098, -2), (key984, -2), (key1090, -2), (key1090, -2), (key976, -2)]

def rawRow7398 : Integer.Sparse Key := [(key3, -24), (key86, 6), (key86, 6), (key86, 6), (key147, 6)]

def rawRow7399 : Integer.Sparse Key := [(key3, -24), (key86, 6), (key86, 6), (key147, 6), (key86, 6)]

def rawRow7400 : Integer.Sparse Key := [(key3, -24), (key86, 6), (key147, 6), (key86, 6), (key86, 6)]

def rawRow7401 : Integer.Sparse Key := [(key3, -24), (key147, 6), (key86, 6), (key86, 6), (key86, 6)]

def rawRow7402 : Integer.Sparse Key := [(key86, -24), (key3, 6), (key86, 6), (key86, 6), (key147, 6)]

def rawRow7403 : Integer.Sparse Key := [(key86, -24), (key3, 6), (key86, 6), (key147, 6), (key86, 6)]

def rawRow7404 : Integer.Sparse Key := [(key86, -24), (key3, 6), (key147, 6), (key86, 6), (key86, 6)]

def rawRow7405 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key3, 6), (key86, 6), (key147, 6)]

def rawRow7406 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key3, 6), (key147, 6), (key86, 6)]

def rawRow7407 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key86, 6), (key3, 6), (key147, 6)]

def rawRow7408 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key86, 6), (key147, 6), (key3, 6)]

def rawRow7409 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key147, 6), (key3, 6), (key86, 6)]

def rawRow7410 : Integer.Sparse Key := [(key86, -24), (key86, 6), (key147, 6), (key86, 6), (key3, 6)]

def rawRow7411 : Integer.Sparse Key := [(key86, -24), (key147, 6), (key3, 6), (key86, 6), (key86, 6)]

def rawRow7412 : Integer.Sparse Key := [(key86, -24), (key147, 6), (key86, 6), (key3, 6), (key86, 6)]

def rawRow7413 : Integer.Sparse Key := [(key86, -24), (key147, 6), (key86, 6), (key86, 6), (key3, 6)]

def rawRow7414 : Integer.Sparse Key := [(key1, -6), (key7, -6), (key7, -6), (key7, -6), (key84, 2), (key90, 2), (key90, 2), (key84, 2), (key90, 2), (key84, 2), (key151, 2), (key90, 2), (key151, 2), (key90, 2), (key90, 2), (key151, 2)]

def rawRow7415 : Integer.Sparse Key := [(key7, -6), (key1, -6), (key7, -6), (key7, -6), (key90, 2), (key84, 2), (key90, 2), (key90, 2), (key84, 2), (key151, 2), (key84, 2), (key151, 2), (key90, 2), (key90, 2), (key151, 2), (key90, 2)]

def rawRow7416 : Integer.Sparse Key := [(key7, -6), (key7, -6), (key1, -6), (key7, -6), (key90, 2), (key90, 2), (key84, 2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key151, 2), (key90, 2), (key90, 2)]

def rawRow7417 : Integer.Sparse Key := [(key7, -6), (key7, -6), (key7, -6), (key1, -6), (key151, 2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key84, 2)]

def rawRow7418 : Integer.Sparse Key := [(key84, -6), (key90, -6), (key90, -6), (key151, -6), (key1, 2), (key7, 2), (key7, 2), (key84, 2), (key90, 2), (key84, 2), (key151, 2), (key90, 2), (key151, 2), (key193, 2), (key193, 2), (key202, 2)]

def rawRow7419 : Integer.Sparse Key := [(key90, -6), (key84, -6), (key90, -6), (key151, -6), (key7, 2), (key1, 2), (key7, 2), (key90, 2), (key84, 2), (key151, 2), (key84, 2), (key151, 2), (key90, 2), (key193, 2), (key202, 2), (key193, 2)]

def rawRow7420 : Integer.Sparse Key := [(key90, -6), (key90, -6), (key84, -6), (key151, -6), (key7, 2), (key7, 2), (key1, 2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key202, 2), (key193, 2), (key193, 2)]

def rawRow7421 : Integer.Sparse Key := [(key84, -6), (key90, -6), (key151, -6), (key90, -6), (key84, 2), (key90, 2), (key151, 2), (key1, 2), (key7, 2), (key84, 2), (key151, 2), (key193, 2), (key202, 2), (key7, 2), (key90, 2), (key151, 2)]

def rawRow7422 : Integer.Sparse Key := [(key90, -6), (key84, -6), (key151, -6), (key90, -6), (key90, 2), (key84, 2), (key151, 2), (key7, 2), (key1, 2), (key151, 2), (key84, 2), (key202, 2), (key193, 2), (key7, 2), (key151, 2), (key90, 2)]

def rawRow7423 : Integer.Sparse Key := [(key84, -6), (key151, -6), (key90, -6), (key90, -6), (key84, 2), (key151, 2), (key90, 2), (key84, 2), (key151, 2), (key1, 2), (key202, 2), (key7, 2), (key151, 2), (key90, 2), (key7, 2), (key151, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7424 : Integer.Sparse Key := [(key151, -6), (key84, -6), (key90, -6), (key90, -6), (key151, 2), (key84, 2), (key90, 2), (key151, 2), (key84, 2), (key202, 2), (key1, 2), (key151, 2), (key7, 2), (key90, 2), (key151, 2), (key7, 2)]

def rawRow7425 : Integer.Sparse Key := [(key90, -6), (key151, -6), (key84, -6), (key90, -6), (key90, 2), (key151, 2), (key84, 2), (key193, 2), (key202, 2), (key7, 2), (key151, 2), (key1, 2), (key84, 2), (key151, 2), (key7, 2), (key90, 2)]

def rawRow7426 : Integer.Sparse Key := [(key151, -6), (key90, -6), (key84, -6), (key90, -6), (key151, 2), (key90, 2), (key84, 2), (key202, 2), (key193, 2), (key151, 2), (key7, 2), (key84, 2), (key1, 2), (key151, 2), (key90, 2), (key7, 2)]

def rawRow7427 : Integer.Sparse Key := [(key90, -6), (key90, -6), (key151, -6), (key84, -6), (key193, 2), (key193, 2), (key202, 2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key1, 2), (key84, 2), (key84, 2)]

def rawRow7428 : Integer.Sparse Key := [(key90, -6), (key151, -6), (key90, -6), (key84, -6), (key193, 2), (key202, 2), (key193, 2), (key90, 2), (key151, 2), (key7, 2), (key151, 2), (key7, 2), (key90, 2), (key84, 2), (key1, 2), (key84, 2)]

def rawRow7429 : Integer.Sparse Key := [(key151, -6), (key90, -6), (key90, -6), (key84, -6), (key202, 2), (key193, 2), (key193, 2), (key151, 2), (key90, 2), (key151, 2), (key7, 2), (key90, 2), (key7, 2), (key84, 2), (key84, 2), (key1, 2)]

def rawRow7430 : Integer.Sparse Key := [(key2377, 2), (key2377, 2), (key2377, 2), (key2471, 2), (key2471, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2502, 2), (key2389, -2), (key2389, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2518, -2), (key2518, -2)]

def rawRow7431 : Integer.Sparse Key := [(key2471, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2377, 2), (key2471, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2479, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2)]

def rawRow7432 : Integer.Sparse Key := [(key2502, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2377, 2), (key2471, 2), (key2479, -2), (key2518, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2479, -2)]

def rawRow7433 : Integer.Sparse Key := [(key2502, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2377, 2), (key2471, 2), (key2377, 2), (key2518, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2389, -2)]

def rawRow7434 : Integer.Sparse Key := [(key2377, 2), (key2389, 2), (key2389, 2), (key2405, 2), (key2479, 2), (key2479, 2), (key2436, 2), (key2436, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2), (key2377, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2405, -2), (key2471, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2502, -2)]

def rawRow7435 : Integer.Sparse Key := [(key2389, 2), (key2377, 2), (key2389, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2502, 2), (key2518, 2), (key2436, 2), (key2518, 2), (key2436, 2), (key2502, 2), (key2377, -2), (key2389, -2), (key2377, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2436, -2), (key2502, -2)]

def rawRow7436 : Integer.Sparse Key := [(key2389, 2), (key2389, 2), (key2377, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2518, 2), (key2502, 2), (key2518, 2), (key2436, 2), (key2502, 2), (key2436, 2), (key2389, -2), (key2377, -2), (key2377, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2405, -2), (key2502, -2), (key2502, -2), (key2436, -2)]

def rawRow7437 : Integer.Sparse Key := [(key2405, 2), (key2436, 2), (key2436, 2), (key2377, 2), (key2502, 2), (key2502, 2), (key2389, 2), (key2389, 2), (key2479, 2), (key2479, 2), (key2518, 2), (key2518, 2), (key2405, -2), (key2405, -2), (key2436, -2), (key2377, -2), (key2377, -2), (key2471, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2479, -2)]

def rawRow7438 : Integer.Sparse Key := [(key2436, 2), (key2405, 2), (key2436, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2479, 2), (key2518, 2), (key2389, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2405, -2), (key2436, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2479, -2), (key2389, -2), (key2479, -2)]

def rawRow7439 : Integer.Sparse Key := [(key2436, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2389, 2), (key2436, -2), (key2405, -2), (key2405, -2), (key2502, -2), (key2471, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2377, -2), (key2479, -2), (key2479, -2), (key2389, -2)]

def rawRow7440 : Integer.Sparse Key := [(key2479, 2), (key2502, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2518, 2), (key2377, 2), (key2389, 2), (key2405, 2), (key2479, 2), (key2436, 2), (key2502, 2), (key2471, -2), (key2479, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2405, -2), (key2479, -2), (key2436, -2), (key2502, -2), (key2377, -2), (key2405, -2), (key2471, -2)]

def rawRow7441 : Integer.Sparse Key := [(key2479, 2), (key2518, 2), (key2502, 2), (key2389, 2), (key2518, 2), (key2436, 2), (key2389, 2), (key2377, 2), (key2479, 2), (key2405, 2), (key2502, 2), (key2436, 2), (key2479, -2), (key2471, -2), (key2502, -2), (key2389, -2), (key2377, -2), (key2479, -2), (key2405, -2), (key2502, -2), (key2436, -2), (key2377, -2), (key2471, -2), (key2405, -2)]

def rawRow7442 : Integer.Sparse Key := [(key2502, 2), (key2479, 2), (key2518, 2), (key2436, 2), (key2389, 2), (key2518, 2), (key2405, 2), (key2436, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2471, -2), (key2502, -2), (key2479, -2), (key2405, -2), (key2436, -2), (key2377, -2), (key2502, -2), (key2389, -2), (key2479, -2), (key2405, -2), (key2377, -2), (key2471, -2)]

def rawRow7443 : Integer.Sparse Key := [(key2502, 2), (key2518, 2), (key2479, 2), (key2436, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2479, 2), (key2389, 2), (key2502, -2), (key2471, -2), (key2479, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2377, -2), (key2479, -2), (key2389, -2), (key2405, -2), (key2471, -2), (key2377, -2)]

def rawRow7444 : Integer.Sparse Key := [(key2518, 2), (key2479, 2), (key2502, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2479, 2), (key2502, 2), (key2389, 2), (key2436, 2), (key2377, 2), (key2405, 2), (key2479, -2), (key2502, -2), (key2471, -2), (key2479, -2), (key2502, -2), (key2389, -2), (key2436, -2), (key2377, -2), (key2405, -2), (key2471, -2), (key2377, -2), (key2405, -2)]

def rawRow7445 : Integer.Sparse Key := [(key2518, 2), (key2502, 2), (key2479, 2), (key2518, 2), (key2436, 2), (key2389, 2), (key2502, 2), (key2479, 2), (key2436, 2), (key2389, 2), (key2405, 2), (key2377, 2), (key2502, -2), (key2479, -2), (key2471, -2), (key2502, -2), (key2479, -2), (key2436, -2), (key2389, -2), (key2405, -2), (key2377, -2), (key2471, -2), (key2405, -2), (key2377, -2)]

def rawRow7446 : Integer.Sparse Key := [(key1024, -24), (key989, 6), (key1102, 6), (key1102, 6), (key1102, 6)]

def rawRow7447 : Integer.Sparse Key := [(key1024, -24), (key1102, 6), (key989, 6), (key1102, 6), (key1102, 6)]

def rawRow7448 : Integer.Sparse Key := [(key1024, -24), (key1102, 6), (key1102, 6), (key989, 6), (key1102, 6)]

def rawRow7449 : Integer.Sparse Key := [(key1024, -24), (key1102, 6), (key1102, 6), (key1102, 6), (key989, 6)]

def rawRow7450 : Integer.Sparse Key := [(key1102, -24), (key989, 6), (key1024, 6), (key1102, 6), (key1102, 6)]

def rawRow7451 : Integer.Sparse Key := [(key1102, -24), (key989, 6), (key1102, 6), (key1024, 6), (key1102, 6)]

def rawRow7452 : Integer.Sparse Key := [(key1102, -24), (key989, 6), (key1102, 6), (key1102, 6), (key1024, 6)]

def rawRow7453 : Integer.Sparse Key := [(key1102, -24), (key1024, 6), (key989, 6), (key1102, 6), (key1102, 6)]

def rawRow7454 : Integer.Sparse Key := [(key1102, -24), (key1024, 6), (key1102, 6), (key989, 6), (key1102, 6)]

def rawRow7455 : Integer.Sparse Key := [(key1102, -24), (key1024, 6), (key1102, 6), (key1102, 6), (key989, 6)]

def rawRow7456 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key989, 6), (key1024, 6), (key1102, 6)]

def rawRow7457 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key989, 6), (key1102, 6), (key1024, 6)]

def rawRow7458 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1024, 6), (key989, 6), (key1102, 6)]

def rawRow7459 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1024, 6), (key1102, 6), (key989, 6)]

def rawRow7460 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1102, 6), (key989, 6), (key1024, 6)]

def rawRow7461 : Integer.Sparse Key := [(key1102, -24), (key1102, 6), (key1102, 6), (key1024, 6), (key989, 6)]

def rawRow7462 : Integer.Sparse Key := [(key1030, -6), (key1030, -6), (key1030, -6), (key1067, -6), (key995, 2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key1146, 2)]

def rawRow7463 : Integer.Sparse Key := [(key1030, -6), (key1030, -6), (key1067, -6), (key1030, -6), (key1108, 2), (key1108, 2), (key1146, 2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1108, 2)]

def rawRow7464 : Integer.Sparse Key := [(key1030, -6), (key1067, -6), (key1030, -6), (key1030, -6), (key1108, 2), (key1146, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1108, 2), (key995, 2), (key1108, 2)]

def rawRow7465 : Integer.Sparse Key := [(key1067, -6), (key1030, -6), (key1030, -6), (key1030, -6), (key1146, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1108, 2), (key995, 2), (key1108, 2), (key1108, 2), (key995, 2)]

def rawRow7466 : Integer.Sparse Key := [(key1108, -6), (key1108, -6), (key1119, -6), (key1146, -6), (key995, 2), (key995, 2), (key1011, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1067, 2), (key1146, 2), (key1146, 2)]

def rawRow7467 : Integer.Sparse Key := [(key1108, -6), (key1119, -6), (key1108, -6), (key1146, -6), (key995, 2), (key1011, 2), (key995, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1146, 2), (key1067, 2), (key1146, 2)]

def rawRow7468 : Integer.Sparse Key := [(key1119, -6), (key1108, -6), (key1108, -6), (key1146, -6), (key1011, 2), (key995, 2), (key995, 2), (key1119, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1030, 2), (key1146, 2), (key1146, 2), (key1067, 2)]

def rawRow7469 : Integer.Sparse Key := [(key1108, -6), (key1108, -6), (key1146, -6), (key1119, -6), (key1030, 2), (key1030, 2), (key1067, 2), (key995, 2), (key995, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key1011, 2), (key1119, 2), (key1119, 2)]

def rawRow7470 : Integer.Sparse Key := [(key1108, -6), (key1146, -6), (key1108, -6), (key1119, -6), (key1030, 2), (key1067, 2), (key1030, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1146, 2), (key995, 2), (key1108, 2), (key1119, 2), (key1011, 2), (key1119, 2)]

def rawRow7471 : Integer.Sparse Key := [(key1146, -6), (key1108, -6), (key1108, -6), (key1119, -6), (key1067, 2), (key1030, 2), (key1030, 2), (key1146, 2), (key1108, 2), (key1146, 2), (key995, 2), (key1108, 2), (key995, 2), (key1119, 2), (key1119, 2), (key1011, 2)]

def rawRow7472 : Integer.Sparse Key := [(key1108, -6), (key1119, -6), (key1146, -6), (key1108, -6), (key1108, 2), (key1119, 2), (key1146, 2), (key995, 2), (key1011, 2), (key1030, 2), (key1119, 2), (key1067, 2), (key1146, 2), (key995, 2), (key1030, 2), (key1108, 2)]

def rawRow7473 : Integer.Sparse Key := [(key1119, -6), (key1108, -6), (key1146, -6), (key1108, -6), (key1119, 2), (key1108, 2), (key1146, 2), (key1011, 2), (key995, 2), (key1119, 2), (key1030, 2), (key1146, 2), (key1067, 2), (key995, 2), (key1108, 2), (key1030, 2)]

def rawRow7474 : Integer.Sparse Key := [(key1108, -6), (key1146, -6), (key1119, -6), (key1108, -6), (key1108, 2), (key1146, 2), (key1119, 2), (key1030, 2), (key1067, 2), (key995, 2), (key1146, 2), (key1011, 2), (key1119, 2), (key1030, 2), (key995, 2), (key1108, 2)]

def rawRow7475 : Integer.Sparse Key := [(key1146, -6), (key1108, -6), (key1119, -6), (key1108, -6), (key1146, 2), (key1108, 2), (key1119, 2), (key1067, 2), (key1030, 2), (key1146, 2), (key995, 2), (key1119, 2), (key1011, 2), (key1030, 2), (key1108, 2), (key995, 2)]

def rawRow7476 : Integer.Sparse Key := [(key1119, -6), (key1146, -6), (key1108, -6), (key1108, -6), (key1119, 2), (key1146, 2), (key1108, 2), (key1119, 2), (key1146, 2), (key1011, 2), (key1067, 2), (key995, 2), (key1030, 2), (key1108, 2), (key995, 2), (key1030, 2)]

def rawRow7477 : Integer.Sparse Key := [(key1146, -6), (key1119, -6), (key1108, -6), (key1108, -6), (key1146, 2), (key1119, 2), (key1108, 2), (key1146, 2), (key1119, 2), (key1067, 2), (key1011, 2), (key1030, 2), (key995, 2), (key1108, 2), (key1030, 2), (key995, 2)]

def rawRow7478 : Integer.Sparse Key := [(key2606, -6), (key2799, -6), (key2799, -6), (key2799, -6), (key2622, 2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2)]

def rawRow7479 : Integer.Sparse Key := [(key2799, -6), (key2606, -6), (key2799, -6), (key2799, -6), (key2696, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2)]

def rawRow7480 : Integer.Sparse Key := [(key2799, -6), (key2799, -6), (key2606, -6), (key2799, -6), (key2849, 2), (key2696, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2622, 2), (key2696, 2)]

def rawRow7481 : Integer.Sparse Key := [(key2799, -6), (key2799, -6), (key2799, -6), (key2606, -6), (key2849, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2622, 2)]

def rawRow7482 : Integer.Sparse Key := [(key2622, -6), (key2696, -6), (key2849, -6), (key2849, -6), (key2606, 2), (key2622, 2), (key2622, 2), (key2661, 2), (key2696, 2), (key2696, 2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2)]

def rawRow7483 : Integer.Sparse Key := [(key2622, -6), (key2849, -6), (key2696, -6), (key2849, -6), (key2622, 2), (key2606, 2), (key2622, 2), (key2696, 2), (key2661, 2), (key2696, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2776, 2), (key2799, 2)]

def rawRow7484 : Integer.Sparse Key := [(key2622, -6), (key2849, -6), (key2849, -6), (key2696, -6), (key2622, 2), (key2622, 2), (key2606, 2), (key2696, 2), (key2696, 2), (key2661, 2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2799, 2), (key2776, 2)]

def rawRow7485 : Integer.Sparse Key := [(key2696, -6), (key2622, -6), (key2849, -6), (key2849, -6), (key2661, 2), (key2696, 2), (key2696, 2), (key2606, 2), (key2799, 2), (key2799, 2), (key2622, 2), (key2622, 2), (key2696, 2), (key2696, 2), (key2849, 2), (key2849, 2)]

def rawRow7486 : Integer.Sparse Key := [(key2696, -6), (key2849, -6), (key2622, -6), (key2849, -6), (key2696, 2), (key2661, 2), (key2696, 2), (key2799, 2), (key2606, 2), (key2799, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2849, 2), (key2622, 2), (key2696, 2)]

def rawRow7487 : Integer.Sparse Key := [(key2696, -6), (key2849, -6), (key2849, -6), (key2622, -6), (key2696, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2799, 2), (key2606, 2), (key2849, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2622, 2)]

def rawRow7488 : Integer.Sparse Key := [(key2849, -6), (key2622, -6), (key2696, -6), (key2849, -6), (key2776, 2), (key2799, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2849, 2), (key2606, 2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, 2), (key2799, 2)]

def rawRow7489 : Integer.Sparse Key := [(key2849, -6), (key2622, -6), (key2849, -6), (key2696, -6), (key2776, 2), (key2849, 2), (key2799, 2), (key2622, 2), (key2849, 2), (key2696, 2), (key2622, 2), (key2606, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2776, 2)]

def rawRow7490 : Integer.Sparse Key := [(key2849, -6), (key2696, -6), (key2622, -6), (key2849, -6), (key2799, 2), (key2776, 2), (key2849, 2), (key2696, 2), (key2622, 2), (key2849, 2), (key2661, 2), (key2696, 2), (key2606, 2), (key2799, 2), (key2622, 2), (key2696, 2)]

def rawRow7491 : Integer.Sparse Key := [(key2849, -6), (key2696, -6), (key2849, -6), (key2622, -6), (key2799, 2), (key2849, 2), (key2776, 2), (key2696, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2661, 2), (key2799, 2), (key2606, 2), (key2696, 2), (key2622, 2)]

def rawRow7492 : Integer.Sparse Key := [(key2849, -6), (key2849, -6), (key2622, -6), (key2696, -6), (key2849, 2), (key2776, 2), (key2799, 2), (key2849, 2), (key2622, 2), (key2696, 2), (key2776, 2), (key2799, 2), (key2622, 2), (key2696, 2), (key2606, 2), (key2661, 2)]

def rawRow7493 : Integer.Sparse Key := [(key2849, -6), (key2849, -6), (key2696, -6), (key2622, -6), (key2849, 2), (key2799, 2), (key2776, 2), (key2849, 2), (key2696, 2), (key2622, 2), (key2799, 2), (key2776, 2), (key2696, 2), (key2622, 2), (key2661, 2), (key2606, 2)]

def rawRow7494 : Integer.Sparse Key := [(key2452, 2), (key2452, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2458, 2), (key2452, 2), (key2519, 2), (key2458, 2), (key2519, 2), (key2528, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2560, -2)]

def rawRow7495 : Integer.Sparse Key := [(key2452, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2458, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2519, 2), (key2458, 2), (key2530, -2), (key2528, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2560, -2), (key2530, -2)]

def rawRow7496 : Integer.Sparse Key := [(key2458, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2519, 2), (key2458, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2530, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2530, -2)]

def rawRow7497 : Integer.Sparse Key := [(key2519, 2), (key2519, 2), (key2519, 2), (key2458, 2), (key2458, 2), (key2458, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2452, 2), (key2560, -2), (key2560, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2528, -2), (key2528, -2)]

def rawRow7498 : Integer.Sparse Key := [(key2357, 2), (key2357, 2), (key2363, 2), (key2452, 2), (key2452, 2), (key2519, 2), (key2528, 2), (key2530, 2), (key2528, 2), (key2560, 2), (key2530, 2), (key2560, 2), (key2357, -2), (key2363, -2), (key2363, -2), (key2452, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2519, -2), (key2530, -2), (key2530, -2), (key2560, -2)]

def rawRow7499 : Integer.Sparse Key := [(key2361, 2), (key2363, 2), (key2357, 2), (key2452, 2), (key2519, 2), (key2452, 2), (key2530, 2), (key2528, 2), (key2560, 2), (key2528, 2), (key2560, 2), (key2530, 2), (key2363, -2), (key2357, -2), (key2363, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2530, -2), (key2560, -2), (key2530, -2)]

def rawRow7500 : Integer.Sparse Key := [(key2366, 2), (key2361, 2), (key2361, 2), (key2519, 2), (key2452, 2), (key2452, 2), (key2560, 2), (key2560, 2), (key2530, 2), (key2530, 2), (key2528, 2), (key2528, 2), (key2363, -2), (key2363, -2), (key2357, -2), (key2519, -2), (key2519, -2), (key2458, -2), (key2458, -2), (key2452, -2), (key2452, -2), (key2560, -2), (key2530, -2), (key2530, -2)]

def rawRow7501 : Integer.Sparse Key := [(key2456, 2), (key2517, 2), (key2523, 2), (key2357, 2), (key2528, 2), (key2560, 2), (key2357, 2), (key2363, 2), (key2452, 2), (key2519, 2), (key2530, 2), (key2560, 2), (key2452, -2), (key2458, -2), (key2530, -2), (key2357, -2), (key2363, -2), (key2452, -2), (key2519, -2), (key2530, -2), (key2560, -2), (key2363, -2), (key2458, -2), (key2519, -2)]

def rawRow7502 : Integer.Sparse Key := [(key2456, 2), (key2523, 2), (key2517, 2), (key2361, 2), (key2560, 2), (key2528, 2), (key2363, 2), (key2357, 2), (key2519, 2), (key2452, 2), (key2560, 2), (key2530, 2), (key2458, -2), (key2452, -2), (key2530, -2), (key2363, -2), (key2357, -2), (key2519, -2), (key2452, -2), (key2560, -2), (key2530, -2), (key2363, -2), (key2519, -2), (key2458, -2)]

def rawRow7503 : Integer.Sparse Key := [(key2517, 2), (key2456, 2), (key2523, 2), (key2517, 2), (key2357, 2), (key2560, 2), (key2452, 2), (key2530, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2452, -2), (key2530, -2), (key2458, -2), (key2452, -2), (key2530, -2), (key2357, -2), (key2560, -2), (key2363, -2), (key2519, -2), (key2458, -2), (key2363, -2), (key2519, -2)]

def rawRow7504 : Integer.Sparse Key := [(key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2519, 2), (key2363, 2), (key2530, -2), (key2452, -2), (key2458, -2), (key2530, -2), (key2452, -2), (key2560, -2), (key2357, -2), (key2519, -2), (key2363, -2), (key2458, -2), (key2519, -2), (key2363, -2)]

def rawRow7505 : Integer.Sparse Key := [(key2523, 2), (key2456, 2), (key2517, 2), (key2579, 2), (key2361, 2), (key2517, 2), (key2519, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2357, 2), (key2452, 2), (key2458, -2), (key2530, -2), (key2452, -2), (key2519, -2), (key2560, -2), (key2363, -2), (key2530, -2), (key2357, -2), (key2452, -2), (key2519, -2), (key2363, -2), (key2458, -2)]

def rawRow7506 : Integer.Sparse Key := [(key2523, 2), (key2517, 2), (key2456, 2), (key2579, 2), (key2517, 2), (key2361, 2), (key2560, 2), (key2519, 2), (key2530, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2530, -2), (key2458, -2), (key2452, -2), (key2560, -2), (key2519, -2), (key2530, -2), (key2363, -2), (key2452, -2), (key2357, -2), (key2519, -2), (key2458, -2), (key2363, -2)]

def rawRow7507 : Integer.Sparse Key := [(key2567, 2), (key2579, 2), (key2579, 2), (key2366, 2), (key2523, 2), (key2523, 2), (key2361, 2), (key2361, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2519, -2), (key2519, -2), (key2560, -2), (key2363, -2), (key2363, -2), (key2458, -2), (key2458, -2), (key2530, -2), (key2530, -2), (key2357, -2), (key2452, -2), (key2452, -2)]

def rawRow7508 : Integer.Sparse Key := [(key2579, 2), (key2567, 2), (key2579, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2517, 2), (key2361, 2), (key2456, 2), (key2519, -2), (key2560, -2), (key2519, -2), (key2458, -2), (key2530, -2), (key2363, -2), (key2530, -2), (key2363, -2), (key2458, -2), (key2452, -2), (key2357, -2), (key2452, -2)]

def rawRow7509 : Integer.Sparse Key := [(key2579, 2), (key2579, 2), (key2567, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2517, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2456, 2), (key2361, 2), (key2560, -2), (key2519, -2), (key2519, -2), (key2530, -2), (key2458, -2), (key2530, -2), (key2363, -2), (key2458, -2), (key2363, -2), (key2452, -2), (key2452, -2), (key2357, -2)]

def rawRow7510 : Integer.Sparse Key := [(key970, -24), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6)]

def rawRow7511 : Integer.Sparse Key := [(key970, -24), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6)]

def rawRow7512 : Integer.Sparse Key := [(key970, -24), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6)]

def rawRow7513 : Integer.Sparse Key := [(key970, -24), (key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6)]

def rawRow7514 : Integer.Sparse Key := [(key1084, -24), (key970, 6), (key1084, 6), (key1084, 6), (key1226, 6)]

def rawRow7515 : Integer.Sparse Key := [(key1084, -24), (key970, 6), (key1084, 6), (key1226, 6), (key1084, 6)]

def rawRow7516 : Integer.Sparse Key := [(key1084, -24), (key970, 6), (key1226, 6), (key1084, 6), (key1084, 6)]

def rawRow7517 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key970, 6), (key1084, 6), (key1226, 6)]

def rawRow7518 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key970, 6), (key1226, 6), (key1084, 6)]

def rawRow7519 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1084, 6), (key970, 6), (key1226, 6)]

def rawRow7520 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6)]

def rawRow7521 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1226, 6), (key970, 6), (key1084, 6)]

def rawRow7522 : Integer.Sparse Key := [(key1084, -24), (key1084, 6), (key1226, 6), (key1084, 6), (key970, 6)]

def rawRow7523 : Integer.Sparse Key := [(key1084, -24), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6)]

def rawRow7524 : Integer.Sparse Key := [(key1084, -24), (key1226, 6), (key1084, 6), (key970, 6), (key1084, 6)]

def rawRow7525 : Integer.Sparse Key := [(key1084, -24), (key1226, 6), (key1084, 6), (key1084, 6), (key970, 6)]

def rawRow7526 : Integer.Sparse Key := [(key971, -6), (key979, -6), (key979, -6), (key979, -6), (key1085, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1228, 2)]

def rawRow7527 : Integer.Sparse Key := [(key979, -6), (key971, -6), (key979, -6), (key979, -6), (key1093, 2), (key1085, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key1093, 2)]

def rawRow7528 : Integer.Sparse Key := [(key979, -6), (key979, -6), (key971, -6), (key979, -6), (key1093, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1093, 2)]

def rawRow7529 : Integer.Sparse Key := [(key979, -6), (key979, -6), (key979, -6), (key971, -6), (key1228, 2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1085, 2)]

def rawRow7530 : Integer.Sparse Key := [(key1085, -6), (key1093, -6), (key1093, -6), (key1164, -6), (key971, 2), (key979, 2), (key979, 2), (key1085, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key1164, 2), (key1164, 2), (key1245, 2)]

def rawRow7531 : Integer.Sparse Key := [(key1093, -6), (key1085, -6), (key1093, -6), (key1164, -6), (key979, 2), (key971, 2), (key979, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1164, 2), (key1245, 2), (key1164, 2)]

def rawRow7532 : Integer.Sparse Key := [(key1093, -6), (key1093, -6), (key1085, -6), (key1164, -6), (key979, 2), (key979, 2), (key971, 2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1245, 2), (key1164, 2), (key1164, 2)]

def rawRow7533 : Integer.Sparse Key := [(key1085, -6), (key1093, -6), (key1164, -6), (key1093, -6), (key1085, 2), (key1093, 2), (key1164, 2), (key971, 2), (key979, 2), (key1085, 2), (key1228, 2), (key1164, 2), (key1245, 2), (key979, 2), (key1093, 2), (key1228, 2)]

def rawRow7534 : Integer.Sparse Key := [(key1093, -6), (key1085, -6), (key1164, -6), (key1093, -6), (key1093, 2), (key1085, 2), (key1164, 2), (key979, 2), (key971, 2), (key1228, 2), (key1085, 2), (key1245, 2), (key1164, 2), (key979, 2), (key1228, 2), (key1093, 2)]

def rawRow7535 : Integer.Sparse Key := [(key1085, -6), (key1164, -6), (key1093, -6), (key1093, -6), (key1085, 2), (key1164, 2), (key1093, 2), (key1085, 2), (key1164, 2), (key971, 2), (key1245, 2), (key979, 2), (key1228, 2), (key1093, 2), (key979, 2), (key1228, 2)]

def rawRow7536 : Integer.Sparse Key := [(key1164, -6), (key1085, -6), (key1093, -6), (key1093, -6), (key1164, 2), (key1085, 2), (key1093, 2), (key1164, 2), (key1085, 2), (key1245, 2), (key971, 2), (key1228, 2), (key979, 2), (key1093, 2), (key1228, 2), (key979, 2)]

def rawRow7537 : Integer.Sparse Key := [(key1093, -6), (key1164, -6), (key1085, -6), (key1093, -6), (key1093, 2), (key1164, 2), (key1085, 2), (key1228, 2), (key1245, 2), (key979, 2), (key1164, 2), (key971, 2), (key1085, 2), (key1228, 2), (key979, 2), (key1093, 2)]

def rawRow7538 : Integer.Sparse Key := [(key1164, -6), (key1093, -6), (key1085, -6), (key1093, -6), (key1164, 2), (key1093, 2), (key1085, 2), (key1245, 2), (key1228, 2), (key1164, 2), (key979, 2), (key1085, 2), (key971, 2), (key1228, 2), (key1093, 2), (key979, 2)]

def rawRow7539 : Integer.Sparse Key := [(key1093, -6), (key1093, -6), (key1164, -6), (key1085, -6), (key1228, 2), (key1228, 2), (key1245, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key971, 2), (key1085, 2), (key1085, 2)]

def rawRow7540 : Integer.Sparse Key := [(key1093, -6), (key1164, -6), (key1093, -6), (key1085, -6), (key1228, 2), (key1245, 2), (key1228, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1085, 2), (key971, 2), (key1085, 2)]

def rawRow7541 : Integer.Sparse Key := [(key1164, -6), (key1093, -6), (key1093, -6), (key1085, -6), (key1245, 2), (key1228, 2), (key1228, 2), (key1164, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1093, 2), (key979, 2), (key1085, 2), (key1085, 2), (key971, 2)]

def rawRow7542 : Integer.Sparse Key := [(key2400, -6), (key2400, -6), (key2400, -6), (key2432, -6), (key2466, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2475, 2), (key2498, 2)]

def rawRow7543 : Integer.Sparse Key := [(key2400, -6), (key2400, -6), (key2432, -6), (key2400, -6), (key2466, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2498, 2), (key2475, 2)]

def rawRow7544 : Integer.Sparse Key := [(key2400, -6), (key2432, -6), (key2400, -6), (key2400, -6), (key2475, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2475, 2), (key2475, 2), (key2466, 2), (key2466, 2)]

def rawRow7545 : Integer.Sparse Key := [(key2432, -6), (key2400, -6), (key2400, -6), (key2400, -6), (key2498, 2), (key2498, 2), (key2498, 2), (key2475, 2), (key2475, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2)]

def rawRow7546 : Integer.Sparse Key := [(key2372, -6), (key2466, -6), (key2466, -6), (key2498, -6), (key2372, 2), (key2372, 2), (key2385, 2), (key2400, 2), (key2400, 2), (key2432, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2475, 2), (key2498, 2)]

def rawRow7547 : Integer.Sparse Key := [(key2372, -6), (key2466, -6), (key2498, -6), (key2466, -6), (key2372, 2), (key2385, 2), (key2372, 2), (key2400, 2), (key2432, 2), (key2400, 2), (key2475, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2498, 2), (key2475, 2)]

def rawRow7548 : Integer.Sparse Key := [(key2372, -6), (key2498, -6), (key2466, -6), (key2466, -6), (key2385, 2), (key2372, 2), (key2372, 2), (key2432, 2), (key2400, 2), (key2400, 2), (key2498, 2), (key2498, 2), (key2475, 2), (key2475, 2), (key2466, 2), (key2466, 2)]

def rawRow7549 : Integer.Sparse Key := [(key2466, -6), (key2372, -6), (key2466, -6), (key2498, -6), (key2400, 2), (key2466, 2), (key2475, 2), (key2372, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2385, 2), (key2400, 2), (key2432, 2), (key2475, 2), (key2498, 2)]

def rawRow7550 : Integer.Sparse Key := [(key2466, -6), (key2372, -6), (key2498, -6), (key2466, -6), (key2400, 2), (key2475, 2), (key2466, 2), (key2372, 2), (key2498, 2), (key2466, 2), (key2385, 2), (key2372, 2), (key2432, 2), (key2400, 2), (key2498, 2), (key2475, 2)]

def rawRow7551 : Integer.Sparse Key := [(key2466, -6), (key2466, -6), (key2372, -6), (key2498, -6), (key2466, 2), (key2400, 2), (key2475, 2), (key2466, 2), (key2372, 2), (key2498, 2), (key2400, 2), (key2475, 2), (key2372, 2), (key2498, 2), (key2385, 2), (key2432, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7552 : Integer.Sparse Key := [(key2466, -6), (key2466, -6), (key2498, -6), (key2372, -6), (key2466, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2475, 2), (key2400, 2), (key2498, 2), (key2372, 2), (key2432, 2), (key2385, 2)]

def rawRow7553 : Integer.Sparse Key := [(key2466, -6), (key2498, -6), (key2372, -6), (key2466, -6), (key2475, 2), (key2400, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2432, 2), (key2498, 2), (key2385, 2), (key2475, 2), (key2372, 2), (key2400, 2)]

def rawRow7554 : Integer.Sparse Key := [(key2466, -6), (key2498, -6), (key2466, -6), (key2372, -6), (key2475, 2), (key2466, 2), (key2400, 2), (key2498, 2), (key2466, 2), (key2372, 2), (key2498, 2), (key2432, 2), (key2475, 2), (key2385, 2), (key2400, 2), (key2372, 2)]

def rawRow7555 : Integer.Sparse Key := [(key2498, -6), (key2372, -6), (key2466, -6), (key2466, -6), (key2432, 2), (key2498, 2), (key2498, 2), (key2385, 2), (key2475, 2), (key2475, 2), (key2372, 2), (key2372, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2)]

def rawRow7556 : Integer.Sparse Key := [(key2498, -6), (key2466, -6), (key2372, -6), (key2466, -6), (key2498, 2), (key2432, 2), (key2498, 2), (key2475, 2), (key2385, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2400, 2)]

def rawRow7557 : Integer.Sparse Key := [(key2498, -6), (key2466, -6), (key2466, -6), (key2372, -6), (key2498, 2), (key2498, 2), (key2432, 2), (key2475, 2), (key2475, 2), (key2385, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2400, 2), (key2372, 2)]

def rawRow7558 : Integer.Sparse Key := [(key2353, -6), (key2359, -6), (key2359, -6), (key2359, -6), (key2448, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2)]

def rawRow7559 : Integer.Sparse Key := [(key2359, -6), (key2353, -6), (key2359, -6), (key2359, -6), (key2454, 2), (key2448, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2454, 2)]

def rawRow7560 : Integer.Sparse Key := [(key2359, -6), (key2359, -6), (key2353, -6), (key2359, -6), (key2454, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2454, 2)]

def rawRow7561 : Integer.Sparse Key := [(key2359, -6), (key2359, -6), (key2359, -6), (key2353, -6), (key2515, 2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2448, 2)]

def rawRow7562 : Integer.Sparse Key := [(key2448, -6), (key2454, -6), (key2454, -6), (key2515, -6), (key2353, 2), (key2359, 2), (key2359, 2), (key2448, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2566, 2), (key2566, 2), (key2578, 2)]

def rawRow7563 : Integer.Sparse Key := [(key2454, -6), (key2448, -6), (key2454, -6), (key2515, -6), (key2359, 2), (key2353, 2), (key2359, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2566, 2), (key2578, 2), (key2566, 2)]

def rawRow7564 : Integer.Sparse Key := [(key2454, -6), (key2454, -6), (key2448, -6), (key2515, -6), (key2359, 2), (key2359, 2), (key2353, 2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2566, 2)]

def rawRow7565 : Integer.Sparse Key := [(key2448, -6), (key2454, -6), (key2515, -6), (key2454, -6), (key2448, 2), (key2454, 2), (key2515, 2), (key2353, 2), (key2359, 2), (key2448, 2), (key2515, 2), (key2566, 2), (key2578, 2), (key2359, 2), (key2454, 2), (key2515, 2)]

def rawRow7566 : Integer.Sparse Key := [(key2454, -6), (key2448, -6), (key2515, -6), (key2454, -6), (key2454, 2), (key2448, 2), (key2515, 2), (key2359, 2), (key2353, 2), (key2515, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2359, 2), (key2515, 2), (key2454, 2)]

def rawRow7567 : Integer.Sparse Key := [(key2448, -6), (key2515, -6), (key2454, -6), (key2454, -6), (key2448, 2), (key2515, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2353, 2), (key2578, 2), (key2359, 2), (key2515, 2), (key2454, 2), (key2359, 2), (key2515, 2)]

def rawRow7568 : Integer.Sparse Key := [(key2515, -6), (key2448, -6), (key2454, -6), (key2454, -6), (key2515, 2), (key2448, 2), (key2454, 2), (key2515, 2), (key2448, 2), (key2578, 2), (key2353, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2515, 2), (key2359, 2)]

def rawRow7569 : Integer.Sparse Key := [(key2454, -6), (key2515, -6), (key2448, -6), (key2454, -6), (key2454, 2), (key2515, 2), (key2448, 2), (key2566, 2), (key2578, 2), (key2359, 2), (key2515, 2), (key2353, 2), (key2448, 2), (key2515, 2), (key2359, 2), (key2454, 2)]

def rawRow7570 : Integer.Sparse Key := [(key2515, -6), (key2454, -6), (key2448, -6), (key2454, -6), (key2515, 2), (key2454, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2515, 2), (key2359, 2), (key2448, 2), (key2353, 2), (key2515, 2), (key2454, 2), (key2359, 2)]

def rawRow7571 : Integer.Sparse Key := [(key2454, -6), (key2454, -6), (key2515, -6), (key2448, -6), (key2566, 2), (key2566, 2), (key2578, 2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2353, 2), (key2448, 2), (key2448, 2)]

def rawRow7572 : Integer.Sparse Key := [(key2454, -6), (key2515, -6), (key2454, -6), (key2448, -6), (key2566, 2), (key2578, 2), (key2566, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2448, 2), (key2353, 2), (key2448, 2)]

def rawRow7573 : Integer.Sparse Key := [(key2515, -6), (key2454, -6), (key2454, -6), (key2448, -6), (key2578, 2), (key2566, 2), (key2566, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2359, 2), (key2448, 2), (key2448, 2), (key2353, 2)]

def rawRow7574 : Integer.Sparse Key := [(key2587, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2843, 2), (key2880, 2), (key2966, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2989, 2), (key2598, -2), (key2600, -2), (key2600, -2), (key2887, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2910, -2), (key2995, -2), (key2995, -2), (key3002, -2)]

def rawRow7575 : Integer.Sparse Key := [(key2587, 2), (key2593, 2), (key2587, 2), (key2843, 2), (key2880, 2), (key2843, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2600, -2), (key2598, -2), (key2600, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2995, -2), (key3002, -2), (key2995, -2)]

def rawRow7576 : Integer.Sparse Key := [(key2593, 2), (key2587, 2), (key2587, 2), (key2880, 2), (key2843, 2), (key2843, 2), (key2989, 2), (key2989, 2), (key2968, 2), (key2968, 2), (key2966, 2), (key2966, 2), (key2600, -2), (key2600, -2), (key2598, -2), (key2910, -2), (key2910, -2), (key2889, -2), (key2889, -2), (key2887, -2), (key2887, -2), (key3002, -2), (key2995, -2), (key2995, -2)]

def rawRow7577 : Integer.Sparse Key := [(key2843, 2), (key2966, 2), (key2968, 2), (key2587, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2880, 2), (key2968, 2), (key2989, 2), (key2887, -2), (key2889, -2), (key2995, -2), (key2598, -2), (key2600, -2), (key2887, -2), (key2910, -2), (key2995, -2), (key3002, -2), (key2600, -2), (key2889, -2), (key2910, -2)]

def rawRow7578 : Integer.Sparse Key := [(key2843, 2), (key2968, 2), (key2966, 2), (key2587, 2), (key2989, 2), (key2966, 2), (key2593, 2), (key2587, 2), (key2880, 2), (key2843, 2), (key2989, 2), (key2968, 2), (key2889, -2), (key2887, -2), (key2995, -2), (key2600, -2), (key2598, -2), (key2910, -2), (key2887, -2), (key3002, -2), (key2995, -2), (key2600, -2), (key2910, -2), (key2889, -2)]

def rawRow7579 : Integer.Sparse Key := [(key2966, 2), (key2843, 2), (key2968, 2), (key2966, 2), (key2587, 2), (key2989, 2), (key2843, 2), (key2968, 2), (key2587, 2), (key2989, 2), (key2593, 2), (key2880, 2), (key2887, -2), (key2995, -2), (key2889, -2), (key2887, -2), (key2995, -2), (key2598, -2), (key3002, -2), (key2600, -2), (key2910, -2), (key2889, -2), (key2600, -2), (key2910, -2)]

def rawRow7580 : Integer.Sparse Key := [(key2966, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2968, 2), (key2843, 2), (key2989, 2), (key2587, 2), (key2880, 2), (key2593, 2), (key2995, -2), (key2887, -2), (key2889, -2), (key2995, -2), (key2887, -2), (key3002, -2), (key2598, -2), (key2910, -2), (key2600, -2), (key2889, -2), (key2910, -2), (key2600, -2)]

def rawRow7581 : Integer.Sparse Key := [(key2968, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2880, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2587, 2), (key2843, 2), (key2889, -2), (key2995, -2), (key2887, -2), (key2910, -2), (key3002, -2), (key2600, -2), (key2995, -2), (key2598, -2), (key2887, -2), (key2910, -2), (key2600, -2), (key2889, -2)]

def rawRow7582 : Integer.Sparse Key := [(key2968, 2), (key2966, 2), (key2843, 2), (key2989, 2), (key2966, 2), (key2587, 2), (key2989, 2), (key2880, 2), (key2968, 2), (key2593, 2), (key2843, 2), (key2587, 2), (key2995, -2), (key2889, -2), (key2887, -2), (key3002, -2), (key2910, -2), (key2995, -2), (key2600, -2), (key2887, -2), (key2598, -2), (key2910, -2), (key2889, -2), (key2600, -2)]

def rawRow7583 : Integer.Sparse Key := [(key2880, 2), (key2989, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2968, 2), (key2587, 2), (key2587, 2), (key2843, 2), (key2843, 2), (key2966, 2), (key2966, 2), (key2910, -2), (key2910, -2), (key3002, -2), (key2600, -2), (key2600, -2), (key2889, -2), (key2889, -2), (key2995, -2), (key2995, -2), (key2598, -2), (key2887, -2), (key2887, -2)]

def rawRow7584 : Integer.Sparse Key := [(key2989, 2), (key2880, 2), (key2989, 2), (key2968, 2), (key2593, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2966, 2), (key2587, 2), (key2843, 2), (key2910, -2), (key3002, -2), (key2910, -2), (key2889, -2), (key2995, -2), (key2600, -2), (key2995, -2), (key2600, -2), (key2889, -2), (key2887, -2), (key2598, -2), (key2887, -2)]

def rawRow7585 : Integer.Sparse Key := [(key2989, 2), (key2989, 2), (key2880, 2), (key2968, 2), (key2968, 2), (key2593, 2), (key2966, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2843, 2), (key2587, 2), (key3002, -2), (key2910, -2), (key2910, -2), (key2995, -2), (key2889, -2), (key2995, -2), (key2600, -2), (key2889, -2), (key2600, -2), (key2887, -2), (key2887, -2), (key2598, -2)]

def rawRow7586 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2766, 2), (key2887, 2), (key2910, 2), (key2929, 2), (key2931, 2), (key2966, 2), (key2989, 2), (key2995, 2), (key3002, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def rawRow7587 : Integer.Sparse Key := [(key2378, 2), (key2394, 2), (key2390, 2), (key2766, 2), (key2910, 2), (key2887, 2), (key2931, 2), (key2929, 2), (key2989, 2), (key2966, 2), (key3002, 2), (key2995, 2), (key2593, -2), (key2587, -2), (key2600, -2), (key2772, -2), (key2766, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2889, -2), (key2931, -2), (key2989, -2), (key2968, -2)]

def rawRow7588 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2394, 2), (key2887, 2), (key2766, 2), (key2910, 2), (key2966, 2), (key2995, 2), (key2929, 2), (key3002, 2), (key2931, 2), (key2989, 2), (key2587, -2), (key2600, -2), (key2593, -2), (key2843, -2), (key2889, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2968, -2), (key2931, -2), (key2989, -2)]

def rawRow7589 : Integer.Sparse Key := [(key2390, 2), (key2394, 2), (key2378, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2995, 2), (key2966, 2), (key3002, 2), (key2929, 2), (key2989, 2), (key2931, 2), (key2600, -2), (key2587, -2), (key2593, -2), (key2889, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2880, -2), (key2772, -2), (key2968, -2), (key2989, -2), (key2931, -2)]

def rawRow7590 : Integer.Sparse Key := [(key2394, 2), (key2378, 2), (key2390, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2989, 2), (key3002, 2), (key2931, 2), (key2995, 2), (key2929, 2), (key2966, 2), (key2593, -2), (key2600, -2), (key2587, -2), (key2880, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2766, -2), (key2843, -2), (key2989, -2), (key2931, -2), (key2968, -2)]

def rawRow7591 : Integer.Sparse Key := [(key2394, 2), (key2390, 2), (key2378, 2), (key2910, 2), (key2887, 2), (key2766, 2), (key3002, 2), (key2989, 2), (key2995, 2), (key2931, 2), (key2966, 2), (key2929, 2), (key2600, -2), (key2593, -2), (key2587, -2), (key2910, -2), (key2880, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key2989, -2), (key2968, -2), (key2931, -2)]

def rawRow7592 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2587, 2), (key2966, 2), (key2989, 2), (key2598, 2), (key2600, 2), (key2887, 2), (key2910, 2), (key2995, 2), (key3002, 2), (key2766, -2), (key2772, -2), (key2931, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2880, -2), (key2968, -2), (key2989, -2), (key2600, -2), (key2889, -2), (key2910, -2)]

def rawRow7593 : Integer.Sparse Key := [(key2406, 2), (key2443, 2), (key2437, 2), (key2587, 2), (key2989, 2), (key2966, 2), (key2600, 2), (key2598, 2), (key2910, 2), (key2887, 2), (key3002, 2), (key2995, 2), (key2772, -2), (key2766, -2), (key2931, -2), (key2593, -2), (key2587, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2968, -2), (key2600, -2), (key2910, -2), (key2889, -2)]

def rawRow7594 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2443, 2), (key2966, 2), (key2587, 2), (key2989, 2), (key2887, 2), (key2995, 2), (key2598, 2), (key3002, 2), (key2600, 2), (key2910, 2), (key2766, -2), (key2931, -2), (key2772, -2), (key2843, -2), (key2968, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2889, -2), (key2600, -2), (key2910, -2)]

def rawRow7595 : Integer.Sparse Key := [(key2437, 2), (key2443, 2), (key2406, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2995, 2), (key2887, 2), (key3002, 2), (key2598, 2), (key2910, 2), (key2600, 2), (key2931, -2), (key2766, -2), (key2772, -2), (key2968, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2880, -2), (key2593, -2), (key2889, -2), (key2910, -2), (key2600, -2)]

def rawRow7596 : Integer.Sparse Key := [(key2443, 2), (key2406, 2), (key2437, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2910, 2), (key3002, 2), (key2600, 2), (key2995, 2), (key2598, 2), (key2887, 2), (key2772, -2), (key2931, -2), (key2766, -2), (key2880, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2587, -2), (key2843, -2), (key2910, -2), (key2600, -2), (key2889, -2)]

def rawRow7597 : Integer.Sparse Key := [(key2443, 2), (key2437, 2), (key2406, 2), (key2989, 2), (key2966, 2), (key2587, 2), (key3002, 2), (key2910, 2), (key2995, 2), (key2600, 2), (key2887, 2), (key2598, 2), (key2931, -2), (key2772, -2), (key2766, -2), (key2989, -2), (key2880, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key2910, -2), (key2889, -2), (key2600, -2)]

def rawRow7598 : Integer.Sparse Key := [(key2480, 2), (key2503, 2), (key2524, 2), (key2390, 2), (key2929, 2), (key3002, 2), (key2587, 2), (key2600, 2), (key2766, 2), (key2910, 2), (key2931, 2), (key2989, 2), (key2843, -2), (key2889, -2), (key2968, -2), (key2587, -2), (key2600, -2), (key2766, -2), (key2910, -2), (key2931, -2), (key2989, -2), (key2593, -2), (key2772, -2), (key2880, -2)]

def rawRow7599 : Integer.Sparse Key := [(key2480, 2), (key2524, 2), (key2503, 2), (key2390, 2), (key3002, 2), (key2929, 2), (key2600, 2), (key2587, 2), (key2910, 2), (key2766, 2), (key2989, 2), (key2931, 2), (key2889, -2), (key2843, -2), (key2968, -2), (key2600, -2), (key2587, -2), (key2910, -2), (key2766, -2), (key2989, -2), (key2931, -2), (key2593, -2), (key2880, -2), (key2772, -2)]

def rawRow7600 : Integer.Sparse Key := [(key2503, 2), (key2480, 2), (key2524, 2), (key2437, 2), (key2598, 2), (key3002, 2), (key2766, 2), (key2931, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2843, -2), (key2968, -2), (key2889, -2), (key2766, -2), (key2931, -2), (key2587, -2), (key2989, -2), (key2600, -2), (key2910, -2), (key2772, -2), (key2593, -2), (key2880, -2)]

def rawRow7601 : Integer.Sparse Key := [(key2503, 2), (key2524, 2), (key2480, 2), (key2437, 2), (key3002, 2), (key2598, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2910, 2), (key2600, 2), (key2968, -2), (key2843, -2), (key2889, -2), (key2931, -2), (key2766, -2), (key2989, -2), (key2587, -2), (key2910, -2), (key2600, -2), (key2772, -2), (key2880, -2), (key2593, -2)]

def rawRow7602 : Integer.Sparse Key := [(key2524, 2), (key2480, 2), (key2503, 2), (key2580, 2), (key2390, 2), (key2437, 2), (key2910, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2587, 2), (key2766, 2), (key2889, -2), (key2968, -2), (key2843, -2), (key2910, -2), (key2989, -2), (key2600, -2), (key2931, -2), (key2587, -2), (key2766, -2), (key2880, -2), (key2593, -2), (key2772, -2)]

def rawRow7603 : Integer.Sparse Key := [(key2524, 2), (key2503, 2), (key2480, 2), (key2580, 2), (key2437, 2), (key2390, 2), (key2989, 2), (key2910, 2), (key2931, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2968, -2), (key2889, -2), (key2843, -2), (key2989, -2), (key2910, -2), (key2931, -2), (key2600, -2), (key2766, -2), (key2587, -2), (key2880, -2), (key2772, -2), (key2593, -2)]

def rawRow7604 : Integer.Sparse Key := [(key2571, 2), (key2576, 2), (key2580, 2), (key2394, 2), (key2443, 2), (key2524, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2480, 2), (key2437, 2), (key2503, 2), (key2880, -2), (key2910, -2), (key2989, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2889, -2), (key2931, -2), (key2968, -2), (key2587, -2), (key2766, -2), (key2843, -2)]

def rawRow7605 : Integer.Sparse Key := [(key2571, 2), (key2580, 2), (key2576, 2), (key2394, 2), (key2524, 2), (key2443, 2), (key2390, 2), (key2378, 2), (key2480, 2), (key2406, 2), (key2503, 2), (key2437, 2), (key2910, -2), (key2880, -2), (key2989, -2), (key2600, -2), (key2593, -2), (key2889, -2), (key2772, -2), (key2968, -2), (key2931, -2), (key2587, -2), (key2843, -2), (key2766, -2)]

def rawRow7606 : Integer.Sparse Key := [(key2576, 2), (key2571, 2), (key2580, 2), (key2443, 2), (key2394, 2), (key2524, 2), (key2406, 2), (key2437, 2), (key2378, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2880, -2), (key2989, -2), (key2910, -2), (key2772, -2), (key2931, -2), (key2593, -2), (key2968, -2), (key2600, -2), (key2889, -2), (key2766, -2), (key2587, -2), (key2843, -2)]

def rawRow7607 : Integer.Sparse Key := [(key2576, 2), (key2580, 2), (key2571, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2437, 2), (key2406, 2), (key2503, 2), (key2378, 2), (key2480, 2), (key2390, 2), (key2989, -2), (key2880, -2), (key2910, -2), (key2931, -2), (key2772, -2), (key2968, -2), (key2593, -2), (key2889, -2), (key2600, -2), (key2766, -2), (key2843, -2), (key2587, -2)]

def rawRow7608 : Integer.Sparse Key := [(key2580, 2), (key2571, 2), (key2576, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2390, 2), (key2437, 2), (key2378, 2), (key2406, 2), (key2910, -2), (key2989, -2), (key2880, -2), (key2889, -2), (key2968, -2), (key2600, -2), (key2931, -2), (key2593, -2), (key2772, -2), (key2843, -2), (key2587, -2), (key2766, -2)]

def rawRow7609 : Integer.Sparse Key := [(key2580, 2), (key2576, 2), (key2571, 2), (key2524, 2), (key2443, 2), (key2394, 2), (key2503, 2), (key2480, 2), (key2437, 2), (key2390, 2), (key2406, 2), (key2378, 2), (key2989, -2), (key2910, -2), (key2880, -2), (key2968, -2), (key2889, -2), (key2931, -2), (key2600, -2), (key2772, -2), (key2593, -2), (key2843, -2), (key2766, -2), (key2587, -2)]

def rawRow7610 : Integer.Sparse Key := [(key1026, -24), (key991, 6), (key1104, 6), (key1104, 6), (key1230, 6)]

def rawRow7611 : Integer.Sparse Key := [(key1026, -24), (key991, 6), (key1104, 6), (key1230, 6), (key1104, 6)]

def rawRow7612 : Integer.Sparse Key := [(key1026, -24), (key991, 6), (key1230, 6), (key1104, 6), (key1104, 6)]

def rawRow7613 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key991, 6), (key1104, 6), (key1230, 6)]

def rawRow7614 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key991, 6), (key1230, 6), (key1104, 6)]

def rawRow7615 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1104, 6), (key991, 6), (key1230, 6)]

def rawRow7616 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1104, 6), (key1230, 6), (key991, 6)]

def rawRow7617 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1230, 6), (key991, 6), (key1104, 6)]

def rawRow7618 : Integer.Sparse Key := [(key1026, -24), (key1104, 6), (key1230, 6), (key1104, 6), (key991, 6)]

def rawRow7619 : Integer.Sparse Key := [(key1026, -24), (key1230, 6), (key991, 6), (key1104, 6), (key1104, 6)]

def rawRow7620 : Integer.Sparse Key := [(key1026, -24), (key1230, 6), (key1104, 6), (key991, 6), (key1104, 6)]

def rawRow7621 : Integer.Sparse Key := [(key1026, -24), (key1230, 6), (key1104, 6), (key1104, 6), (key991, 6)]

def rawRow7622 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1026, 6), (key1104, 6), (key1230, 6)]

def rawRow7623 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1026, 6), (key1230, 6), (key1104, 6)]

def rawRow7624 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1104, 6), (key1026, 6), (key1230, 6)]

def rawRow7625 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1104, 6), (key1230, 6), (key1026, 6)]

def rawRow7626 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1230, 6), (key1026, 6), (key1104, 6)]

def rawRow7627 : Integer.Sparse Key := [(key1104, -24), (key991, 6), (key1230, 6), (key1104, 6), (key1026, 6)]

def rawRow7628 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key991, 6), (key1104, 6), (key1230, 6)]

def rawRow7629 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key991, 6), (key1230, 6), (key1104, 6)]

def rawRow7630 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1104, 6), (key991, 6), (key1230, 6)]

def rawRow7631 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1104, 6), (key1230, 6), (key991, 6)]

def rawRow7632 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1230, 6), (key991, 6), (key1104, 6)]

def rawRow7633 : Integer.Sparse Key := [(key1104, -24), (key1026, 6), (key1230, 6), (key1104, 6), (key991, 6)]

def rawRow7634 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key991, 6), (key1026, 6), (key1230, 6)]

def rawRow7635 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key991, 6), (key1230, 6), (key1026, 6)]

def rawRow7636 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1026, 6), (key991, 6), (key1230, 6)]

def rawRow7637 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1026, 6), (key1230, 6), (key991, 6)]

def rawRow7638 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1230, 6), (key991, 6), (key1026, 6)]

def rawRow7639 : Integer.Sparse Key := [(key1104, -24), (key1104, 6), (key1230, 6), (key1026, 6), (key991, 6)]

def rawRow7640 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key991, 6), (key1026, 6), (key1104, 6)]

def rawRow7641 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key991, 6), (key1104, 6), (key1026, 6)]

def rawRow7642 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1026, 6), (key991, 6), (key1104, 6)]

def rawRow7643 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1026, 6), (key1104, 6), (key991, 6)]

def rawRow7644 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1104, 6), (key991, 6), (key1026, 6)]

def rawRow7645 : Integer.Sparse Key := [(key1104, -24), (key1230, 6), (key1104, 6), (key1026, 6), (key991, 6)]

def rawRow7646 : Integer.Sparse Key := [(key1028, -6), (key1036, -6), (key1036, -6), (key1071, -6), (key993, 2), (key1001, 2), (key1001, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1150, 2), (key1150, 2), (key1242, 2)]

def rawRow7647 : Integer.Sparse Key := [(key1036, -6), (key1028, -6), (key1036, -6), (key1071, -6), (key1001, 2), (key993, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1150, 2), (key1242, 2), (key1150, 2)]

def rawRow7648 : Integer.Sparse Key := [(key1036, -6), (key1036, -6), (key1028, -6), (key1071, -6), (key1001, 2), (key1001, 2), (key993, 2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1150, 2)]

def rawRow7649 : Integer.Sparse Key := [(key1028, -6), (key1036, -6), (key1071, -6), (key1036, -6), (key1106, 2), (key1114, 2), (key1150, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1232, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1114, 2), (key1232, 2)]

def rawRow7650 : Integer.Sparse Key := [(key1036, -6), (key1028, -6), (key1071, -6), (key1036, -6), (key1114, 2), (key1106, 2), (key1150, 2), (key1001, 2), (key993, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1001, 2), (key1232, 2), (key1114, 2)]

def rawRow7651 : Integer.Sparse Key := [(key1028, -6), (key1071, -6), (key1036, -6), (key1036, -6), (key1106, 2), (key1150, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key1114, 2), (key1001, 2), (key1232, 2)]

def rawRow7652 : Integer.Sparse Key := [(key1071, -6), (key1028, -6), (key1036, -6), (key1036, -6), (key1150, 2), (key1106, 2), (key1114, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1232, 2), (key1001, 2)]

def rawRow7653 : Integer.Sparse Key := [(key1036, -6), (key1071, -6), (key1028, -6), (key1036, -6), (key1114, 2), (key1150, 2), (key1106, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1232, 2), (key1001, 2), (key1114, 2)]

def rawRow7654 : Integer.Sparse Key := [(key1071, -6), (key1036, -6), (key1028, -6), (key1036, -6), (key1150, 2), (key1114, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1150, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1232, 2), (key1114, 2), (key1001, 2)]

def rawRow7655 : Integer.Sparse Key := [(key1036, -6), (key1036, -6), (key1071, -6), (key1028, -6), (key1232, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1150, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1106, 2)]

def rawRow7656 : Integer.Sparse Key := [(key1036, -6), (key1071, -6), (key1036, -6), (key1028, -6), (key1232, 2), (key1242, 2), (key1232, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key993, 2), (key1106, 2)]

def rawRow7657 : Integer.Sparse Key := [(key1071, -6), (key1036, -6), (key1036, -6), (key1028, -6), (key1242, 2), (key1232, 2), (key1232, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1106, 2), (key1106, 2), (key993, 2)]

def rawRow7658 : Integer.Sparse Key := [(key1106, -6), (key1114, -6), (key1123, -6), (key1150, -6), (key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1071, 2), (key1150, 2), (key1242, 2)]

def rawRow7659 : Integer.Sparse Key := [(key1114, -6), (key1106, -6), (key1123, -6), (key1150, -6), (key1001, 2), (key993, 2), (key1015, 2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1071, 2), (key1242, 2), (key1150, 2)]

def rawRow7660 : Integer.Sparse Key := [(key1106, -6), (key1123, -6), (key1114, -6), (key1150, -6), (key993, 2), (key1015, 2), (key1001, 2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1150, 2), (key1071, 2), (key1242, 2)]

def rawRow7661 : Integer.Sparse Key := [(key1123, -6), (key1106, -6), (key1114, -6), (key1150, -6), (key1015, 2), (key993, 2), (key1001, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1150, 2), (key1242, 2), (key1071, 2)]

def rawRow7662 : Integer.Sparse Key := [(key1114, -6), (key1123, -6), (key1106, -6), (key1150, -6), (key1001, 2), (key1015, 2), (key993, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1242, 2), (key1071, 2), (key1150, 2)]

def rawRow7663 : Integer.Sparse Key := [(key1123, -6), (key1114, -6), (key1106, -6), (key1150, -6), (key1015, 2), (key1001, 2), (key993, 2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1242, 2), (key1150, 2), (key1071, 2)]

def rawRow7664 : Integer.Sparse Key := [(key1106, -6), (key1114, -6), (key1150, -6), (key1123, -6), (key1028, 2), (key1036, 2), (key1071, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1232, 2), (key1150, 2), (key1242, 2), (key1015, 2), (key1123, 2), (key1235, 2)]

def rawRow7665 : Integer.Sparse Key := [(key1114, -6), (key1106, -6), (key1150, -6), (key1123, -6), (key1036, 2), (key1028, 2), (key1071, 2), (key1001, 2), (key993, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1015, 2), (key1235, 2), (key1123, 2)]

def rawRow7666 : Integer.Sparse Key := [(key1106, -6), (key1150, -6), (key1114, -6), (key1123, -6), (key1028, 2), (key1071, 2), (key1036, 2), (key1106, 2), (key1150, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key1123, 2), (key1015, 2), (key1235, 2)]

def rawRow7667 : Integer.Sparse Key := [(key1150, -6), (key1106, -6), (key1114, -6), (key1123, -6), (key1071, 2), (key1028, 2), (key1036, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1232, 2), (key1001, 2), (key1123, 2), (key1235, 2), (key1015, 2)]

def rawRow7668 : Integer.Sparse Key := [(key1114, -6), (key1150, -6), (key1106, -6), (key1123, -6), (key1036, 2), (key1071, 2), (key1028, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key993, 2), (key1106, 2), (key1235, 2), (key1015, 2), (key1123, 2)]

def rawRow7669 : Integer.Sparse Key := [(key1150, -6), (key1114, -6), (key1106, -6), (key1123, -6), (key1071, 2), (key1036, 2), (key1028, 2), (key1242, 2), (key1232, 2), (key1150, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1235, 2), (key1123, 2), (key1015, 2)]

def rawRow7670 : Integer.Sparse Key := [(key1106, -6), (key1123, -6), (key1150, -6), (key1114, -6), (key1106, 2), (key1123, 2), (key1150, 2), (key993, 2), (key1015, 2), (key1028, 2), (key1235, 2), (key1071, 2), (key1242, 2), (key1001, 2), (key1036, 2), (key1232, 2)]

def rawRow7671 : Integer.Sparse Key := [(key1123, -6), (key1106, -6), (key1150, -6), (key1114, -6), (key1123, 2), (key1106, 2), (key1150, 2), (key1015, 2), (key993, 2), (key1235, 2), (key1028, 2), (key1242, 2), (key1071, 2), (key1001, 2), (key1232, 2), (key1036, 2)]

def rawRow7672 : Integer.Sparse Key := [(key1106, -6), (key1150, -6), (key1123, -6), (key1114, -6), (key1106, 2), (key1150, 2), (key1123, 2), (key1028, 2), (key1071, 2), (key993, 2), (key1242, 2), (key1015, 2), (key1235, 2), (key1036, 2), (key1001, 2), (key1232, 2)]

def rawRow7673 : Integer.Sparse Key := [(key1150, -6), (key1106, -6), (key1123, -6), (key1114, -6), (key1150, 2), (key1106, 2), (key1123, 2), (key1071, 2), (key1028, 2), (key1242, 2), (key993, 2), (key1235, 2), (key1015, 2), (key1036, 2), (key1232, 2), (key1001, 2)]

def rawRow7674 : Integer.Sparse Key := [(key1123, -6), (key1150, -6), (key1106, -6), (key1114, -6), (key1123, 2), (key1150, 2), (key1106, 2), (key1235, 2), (key1242, 2), (key1015, 2), (key1071, 2), (key993, 2), (key1028, 2), (key1232, 2), (key1001, 2), (key1036, 2)]

def rawRow7675 : Integer.Sparse Key := [(key1150, -6), (key1123, -6), (key1106, -6), (key1114, -6), (key1150, 2), (key1123, 2), (key1106, 2), (key1242, 2), (key1235, 2), (key1071, 2), (key1015, 2), (key1028, 2), (key993, 2), (key1232, 2), (key1036, 2), (key1001, 2)]

def rawRow7676 : Integer.Sparse Key := [(key1114, -6), (key1123, -6), (key1150, -6), (key1106, -6), (key1232, 2), (key1235, 2), (key1242, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key993, 2), (key1028, 2), (key1106, 2)]

def rawRow7677 : Integer.Sparse Key := [(key1123, -6), (key1114, -6), (key1150, -6), (key1106, -6), (key1235, 2), (key1232, 2), (key1242, 2), (key1015, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1071, 2), (key993, 2), (key1106, 2), (key1028, 2)]

def rawRow7678 : Integer.Sparse Key := [(key1114, -6), (key1150, -6), (key1123, -6), (key1106, -6), (key1232, 2), (key1242, 2), (key1235, 2), (key1036, 2), (key1071, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1028, 2), (key993, 2), (key1106, 2)]

def rawRow7679 : Integer.Sparse Key := [(key1150, -6), (key1114, -6), (key1123, -6), (key1106, -6), (key1242, 2), (key1232, 2), (key1235, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1015, 2), (key1028, 2), (key1106, 2), (key993, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7680 : Integer.Sparse Key := [(key1123, -6), (key1150, -6), (key1114, -6), (key1106, -6), (key1235, 2), (key1242, 2), (key1232, 2), (key1123, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1001, 2), (key1036, 2), (key1106, 2), (key993, 2), (key1028, 2)]

def rawRow7681 : Integer.Sparse Key := [(key1150, -6), (key1123, -6), (key1114, -6), (key1106, -6), (key1242, 2), (key1235, 2), (key1232, 2), (key1150, 2), (key1123, 2), (key1071, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1106, 2), (key1028, 2), (key993, 2)]

def rawRow7682 : Integer.Sparse Key := [(key2610, -6), (key2803, -6), (key2803, -6), (key2824, -6), (key2626, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

def rawRow7683 : Integer.Sparse Key := [(key2610, -6), (key2803, -6), (key2824, -6), (key2803, -6), (key2626, 2), (key2635, 2), (key2626, 2), (key2700, 2), (key2721, 2), (key2700, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

def rawRow7684 : Integer.Sparse Key := [(key2610, -6), (key2824, -6), (key2803, -6), (key2803, -6), (key2635, 2), (key2626, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2700, 2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

def rawRow7685 : Integer.Sparse Key := [(key2803, -6), (key2610, -6), (key2803, -6), (key2824, -6), (key2700, 2), (key2853, 2), (key2855, 2), (key2626, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2721, 2), (key2855, 2), (key2865, 2)]

def rawRow7686 : Integer.Sparse Key := [(key2803, -6), (key2610, -6), (key2824, -6), (key2803, -6), (key2700, 2), (key2855, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2853, 2), (key2635, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2855, 2)]

def rawRow7687 : Integer.Sparse Key := [(key2803, -6), (key2803, -6), (key2610, -6), (key2824, -6), (key2853, 2), (key2700, 2), (key2855, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2700, 2), (key2855, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2721, 2)]

def rawRow7688 : Integer.Sparse Key := [(key2803, -6), (key2803, -6), (key2824, -6), (key2610, -6), (key2853, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2721, 2), (key2635, 2)]

def rawRow7689 : Integer.Sparse Key := [(key2803, -6), (key2824, -6), (key2610, -6), (key2803, -6), (key2855, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2721, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2626, 2), (key2700, 2)]

def rawRow7690 : Integer.Sparse Key := [(key2803, -6), (key2824, -6), (key2803, -6), (key2610, -6), (key2855, 2), (key2853, 2), (key2700, 2), (key2865, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2721, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2626, 2)]

def rawRow7691 : Integer.Sparse Key := [(key2824, -6), (key2610, -6), (key2803, -6), (key2803, -6), (key2721, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2855, 2), (key2626, 2), (key2626, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2)]

def rawRow7692 : Integer.Sparse Key := [(key2824, -6), (key2803, -6), (key2610, -6), (key2803, -6), (key2865, 2), (key2721, 2), (key2865, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2700, 2)]

def rawRow7693 : Integer.Sparse Key := [(key2824, -6), (key2803, -6), (key2803, -6), (key2610, -6), (key2865, 2), (key2865, 2), (key2721, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2626, 2)]

def rawRow7694 : Integer.Sparse Key := [(key2626, -6), (key2780, -6), (key2853, -6), (key2865, -6), (key2610, 2), (key2626, 2), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

def rawRow7695 : Integer.Sparse Key := [(key2626, -6), (key2780, -6), (key2865, -6), (key2853, -6), (key2610, 2), (key2635, 2), (key2626, 2), (key2665, 2), (key2721, 2), (key2700, 2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

def rawRow7696 : Integer.Sparse Key := [(key2626, -6), (key2853, -6), (key2780, -6), (key2865, -6), (key2626, 2), (key2610, 2), (key2635, 2), (key2700, 2), (key2665, 2), (key2721, 2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

def rawRow7697 : Integer.Sparse Key := [(key2626, -6), (key2853, -6), (key2865, -6), (key2780, -6), (key2626, 2), (key2635, 2), (key2610, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

def rawRow7698 : Integer.Sparse Key := [(key2626, -6), (key2865, -6), (key2780, -6), (key2853, -6), (key2635, 2), (key2610, 2), (key2626, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

def rawRow7699 : Integer.Sparse Key := [(key2626, -6), (key2865, -6), (key2853, -6), (key2780, -6), (key2635, 2), (key2626, 2), (key2610, 2), (key2721, 2), (key2700, 2), (key2665, 2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

def rawRow7700 : Integer.Sparse Key := [(key2780, -6), (key2626, -6), (key2853, -6), (key2865, -6), (key2665, 2), (key2780, 2), (key2789, 2), (key2610, 2), (key2803, 2), (key2824, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2721, 2), (key2855, 2), (key2865, 2)]

def rawRow7701 : Integer.Sparse Key := [(key2780, -6), (key2626, -6), (key2865, -6), (key2853, -6), (key2665, 2), (key2789, 2), (key2780, 2), (key2610, 2), (key2824, 2), (key2803, 2), (key2635, 2), (key2626, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2855, 2)]

def rawRow7702 : Integer.Sparse Key := [(key2780, -6), (key2853, -6), (key2626, -6), (key2865, -6), (key2780, 2), (key2665, 2), (key2789, 2), (key2803, 2), (key2610, 2), (key2824, 2), (key2700, 2), (key2855, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2721, 2)]

def rawRow7703 : Integer.Sparse Key := [(key2780, -6), (key2853, -6), (key2865, -6), (key2626, -6), (key2780, 2), (key2789, 2), (key2665, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2721, 2), (key2635, 2)]

def rawRow7704 : Integer.Sparse Key := [(key2780, -6), (key2865, -6), (key2626, -6), (key2853, -6), (key2789, 2), (key2665, 2), (key2780, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2721, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2626, 2), (key2700, 2)]

def rawRow7705 : Integer.Sparse Key := [(key2780, -6), (key2865, -6), (key2853, -6), (key2626, -6), (key2789, 2), (key2780, 2), (key2665, 2), (key2824, 2), (key2803, 2), (key2610, 2), (key2865, 2), (key2721, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2626, 2)]

def rawRow7706 : Integer.Sparse Key := [(key2853, -6), (key2626, -6), (key2780, -6), (key2865, -6), (key2700, 2), (key2803, 2), (key2855, 2), (key2626, 2), (key2780, 2), (key2865, 2), (key2610, 2), (key2635, 2), (key2665, 2), (key2721, 2), (key2789, 2), (key2824, 2)]

def rawRow7707 : Integer.Sparse Key := [(key2853, -6), (key2626, -6), (key2865, -6), (key2780, -6), (key2700, 2), (key2855, 2), (key2803, 2), (key2626, 2), (key2865, 2), (key2780, 2), (key2635, 2), (key2610, 2), (key2721, 2), (key2665, 2), (key2824, 2), (key2789, 2)]

def rawRow7708 : Integer.Sparse Key := [(key2853, -6), (key2780, -6), (key2626, -6), (key2865, -6), (key2803, 2), (key2700, 2), (key2855, 2), (key2780, 2), (key2626, 2), (key2865, 2), (key2665, 2), (key2789, 2), (key2610, 2), (key2824, 2), (key2635, 2), (key2721, 2)]

def rawRow7709 : Integer.Sparse Key := [(key2853, -6), (key2780, -6), (key2865, -6), (key2626, -6), (key2803, 2), (key2855, 2), (key2700, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2789, 2), (key2665, 2), (key2824, 2), (key2610, 2), (key2721, 2), (key2635, 2)]

def rawRow7710 : Integer.Sparse Key := [(key2853, -6), (key2865, -6), (key2626, -6), (key2780, -6), (key2855, 2), (key2700, 2), (key2803, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2721, 2), (key2824, 2), (key2635, 2), (key2789, 2), (key2610, 2), (key2665, 2)]

def rawRow7711 : Integer.Sparse Key := [(key2853, -6), (key2865, -6), (key2780, -6), (key2626, -6), (key2855, 2), (key2803, 2), (key2700, 2), (key2865, 2), (key2780, 2), (key2626, 2), (key2824, 2), (key2721, 2), (key2789, 2), (key2635, 2), (key2665, 2), (key2610, 2)]

def rawRow7712 : Integer.Sparse Key := [(key2865, -6), (key2626, -6), (key2780, -6), (key2853, -6), (key2721, 2), (key2824, 2), (key2865, 2), (key2635, 2), (key2789, 2), (key2855, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2780, 2), (key2803, 2)]

def rawRow7713 : Integer.Sparse Key := [(key2865, -6), (key2626, -6), (key2853, -6), (key2780, -6), (key2721, 2), (key2865, 2), (key2824, 2), (key2635, 2), (key2855, 2), (key2789, 2), (key2626, 2), (key2610, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2780, 2)]

def rawRow7714 : Integer.Sparse Key := [(key2865, -6), (key2780, -6), (key2626, -6), (key2853, -6), (key2824, 2), (key2721, 2), (key2865, 2), (key2789, 2), (key2635, 2), (key2855, 2), (key2665, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2700, 2)]

def rawRow7715 : Integer.Sparse Key := [(key2865, -6), (key2780, -6), (key2853, -6), (key2626, -6), (key2824, 2), (key2865, 2), (key2721, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2700, 2), (key2626, 2)]

def rawRow7716 : Integer.Sparse Key := [(key2865, -6), (key2853, -6), (key2626, -6), (key2780, -6), (key2865, 2), (key2721, 2), (key2824, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2700, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2610, 2), (key2665, 2)]

def rawRow7717 : Integer.Sparse Key := [(key2865, -6), (key2853, -6), (key2780, -6), (key2626, -6), (key2865, 2), (key2824, 2), (key2721, 2), (key2855, 2), (key2789, 2), (key2635, 2), (key2803, 2), (key2700, 2), (key2780, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

def rawRow7718 : Integer.Sparse Key := [(key2398, -6), (key2404, -6), (key2404, -6), (key2435, -6), (key2583, 2), (key2589, 2), (key2589, 2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key3019, 2), (key3019, 2), (key3028, 2)]

def rawRow7719 : Integer.Sparse Key := [(key2404, -6), (key2398, -6), (key2404, -6), (key2435, -6), (key2589, 2), (key2583, 2), (key2589, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key3019, 2), (key3028, 2), (key3019, 2)]

def rawRow7720 : Integer.Sparse Key := [(key2404, -6), (key2404, -6), (key2398, -6), (key2435, -6), (key2589, 2), (key2589, 2), (key2583, 2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key3019, 2)]

def rawRow7721 : Integer.Sparse Key := [(key2398, -6), (key2404, -6), (key2435, -6), (key2404, -6), (key2839, 2), (key2845, 2), (key3019, 2), (key2583, 2), (key2589, 2), (key2839, 2), (key2876, 2), (key3019, 2), (key3028, 2), (key2589, 2), (key2845, 2), (key2876, 2)]

def rawRow7722 : Integer.Sparse Key := [(key2404, -6), (key2398, -6), (key2435, -6), (key2404, -6), (key2845, 2), (key2839, 2), (key3019, 2), (key2589, 2), (key2583, 2), (key2876, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key2589, 2), (key2876, 2), (key2845, 2)]

def rawRow7723 : Integer.Sparse Key := [(key2398, -6), (key2435, -6), (key2404, -6), (key2404, -6), (key2839, 2), (key3019, 2), (key2845, 2), (key2839, 2), (key3019, 2), (key2583, 2), (key3028, 2), (key2589, 2), (key2876, 2), (key2845, 2), (key2589, 2), (key2876, 2)]

def rawRow7724 : Integer.Sparse Key := [(key2435, -6), (key2398, -6), (key2404, -6), (key2404, -6), (key3019, 2), (key2839, 2), (key2845, 2), (key3019, 2), (key2839, 2), (key3028, 2), (key2583, 2), (key2876, 2), (key2589, 2), (key2845, 2), (key2876, 2), (key2589, 2)]

def rawRow7725 : Integer.Sparse Key := [(key2404, -6), (key2435, -6), (key2398, -6), (key2404, -6), (key2845, 2), (key3019, 2), (key2839, 2), (key2876, 2), (key3028, 2), (key2589, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2876, 2), (key2589, 2), (key2845, 2)]

def rawRow7726 : Integer.Sparse Key := [(key2435, -6), (key2404, -6), (key2398, -6), (key2404, -6), (key3019, 2), (key2845, 2), (key2839, 2), (key3028, 2), (key2876, 2), (key3019, 2), (key2589, 2), (key2839, 2), (key2583, 2), (key2876, 2), (key2845, 2), (key2589, 2)]

def rawRow7727 : Integer.Sparse Key := [(key2404, -6), (key2404, -6), (key2435, -6), (key2398, -6), (key2876, 2), (key2876, 2), (key3028, 2), (key2589, 2), (key2589, 2), (key2845, 2), (key2845, 2), (key3019, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2839, 2)]

def rawRow7728 : Integer.Sparse Key := [(key2404, -6), (key2435, -6), (key2404, -6), (key2398, -6), (key2876, 2), (key3028, 2), (key2876, 2), (key2845, 2), (key3019, 2), (key2589, 2), (key3019, 2), (key2589, 2), (key2845, 2), (key2839, 2), (key2583, 2), (key2839, 2)]

def rawRow7729 : Integer.Sparse Key := [(key2435, -6), (key2404, -6), (key2404, -6), (key2398, -6), (key3028, 2), (key2876, 2), (key2876, 2), (key3019, 2), (key2845, 2), (key3019, 2), (key2589, 2), (key2845, 2), (key2589, 2), (key2839, 2), (key2839, 2), (key2583, 2)]

def rawRow7730 : Integer.Sparse Key := [(key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2370, 2), (key2376, 2), (key2388, 2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def rawRow7731 : Integer.Sparse Key := [(key2470, -6), (key2464, -6), (key2478, -6), (key2501, -6), (key2376, 2), (key2370, 2), (key2388, 2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key3005, 2), (key3028, 2), (key3019, 2)]

def rawRow7732 : Integer.Sparse Key := [(key2464, -6), (key2478, -6), (key2470, -6), (key2501, -6), (key2370, 2), (key2388, 2), (key2376, 2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key3019, 2), (key3005, 2), (key3028, 2)]

def rawRow7733 : Integer.Sparse Key := [(key2478, -6), (key2464, -6), (key2470, -6), (key2501, -6), (key2388, 2), (key2370, 2), (key2376, 2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key3019, 2), (key3028, 2), (key3005, 2)]

def rawRow7734 : Integer.Sparse Key := [(key2470, -6), (key2478, -6), (key2464, -6), (key2501, -6), (key2376, 2), (key2388, 2), (key2370, 2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key3028, 2), (key3005, 2), (key3019, 2)]

def rawRow7735 : Integer.Sparse Key := [(key2478, -6), (key2470, -6), (key2464, -6), (key2501, -6), (key2388, 2), (key2376, 2), (key2370, 2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key3028, 2), (key3019, 2), (key3005, 2)]

def rawRow7736 : Integer.Sparse Key := [(key2464, -6), (key2470, -6), (key2501, -6), (key2478, -6), (key2398, 2), (key2404, 2), (key2435, 2), (key2583, 2), (key2589, 2), (key2839, 2), (key2876, 2), (key3019, 2), (key3028, 2), (key2604, 2), (key2916, 2), (key2925, 2)]

def rawRow7737 : Integer.Sparse Key := [(key2470, -6), (key2464, -6), (key2501, -6), (key2478, -6), (key2404, 2), (key2398, 2), (key2435, 2), (key2589, 2), (key2583, 2), (key2876, 2), (key2839, 2), (key3028, 2), (key3019, 2), (key2604, 2), (key2925, 2), (key2916, 2)]

def rawRow7738 : Integer.Sparse Key := [(key2464, -6), (key2501, -6), (key2470, -6), (key2478, -6), (key2398, 2), (key2435, 2), (key2404, 2), (key2839, 2), (key3019, 2), (key2583, 2), (key3028, 2), (key2589, 2), (key2876, 2), (key2916, 2), (key2604, 2), (key2925, 2)]

def rawRow7739 : Integer.Sparse Key := [(key2501, -6), (key2464, -6), (key2470, -6), (key2478, -6), (key2435, 2), (key2398, 2), (key2404, 2), (key3019, 2), (key2839, 2), (key3028, 2), (key2583, 2), (key2876, 2), (key2589, 2), (key2916, 2), (key2925, 2), (key2604, 2)]

def rawRow7740 : Integer.Sparse Key := [(key2470, -6), (key2501, -6), (key2464, -6), (key2478, -6), (key2404, 2), (key2435, 2), (key2398, 2), (key2876, 2), (key3028, 2), (key2589, 2), (key3019, 2), (key2583, 2), (key2839, 2), (key2925, 2), (key2604, 2), (key2916, 2)]

def rawRow7741 : Integer.Sparse Key := [(key2501, -6), (key2470, -6), (key2464, -6), (key2478, -6), (key2435, 2), (key2404, 2), (key2398, 2), (key3028, 2), (key2876, 2), (key3019, 2), (key2589, 2), (key2839, 2), (key2583, 2), (key2925, 2), (key2916, 2), (key2604, 2)]

def rawRow7742 : Integer.Sparse Key := [(key2464, -6), (key2478, -6), (key2501, -6), (key2470, -6), (key2464, 2), (key2478, 2), (key2501, 2), (key2370, 2), (key2388, 2), (key2762, 2), (key2925, 2), (key3005, 2), (key3028, 2), (key2589, 2), (key2768, 2), (key2876, 2)]

def rawRow7743 : Integer.Sparse Key := [(key2478, -6), (key2464, -6), (key2501, -6), (key2470, -6), (key2478, 2), (key2464, 2), (key2501, 2), (key2388, 2), (key2370, 2), (key2925, 2), (key2762, 2), (key3028, 2), (key3005, 2), (key2589, 2), (key2876, 2), (key2768, 2)]

def rawRow7744 : Integer.Sparse Key := [(key2464, -6), (key2501, -6), (key2478, -6), (key2470, -6), (key2464, 2), (key2501, 2), (key2478, 2), (key2398, 2), (key2435, 2), (key2583, 2), (key3028, 2), (key2604, 2), (key2925, 2), (key2768, 2), (key2589, 2), (key2876, 2)]

def rawRow7745 : Integer.Sparse Key := [(key2501, -6), (key2464, -6), (key2478, -6), (key2470, -6), (key2501, 2), (key2464, 2), (key2478, 2), (key2435, 2), (key2398, 2), (key3028, 2), (key2583, 2), (key2925, 2), (key2604, 2), (key2768, 2), (key2876, 2), (key2589, 2)]

def rawRow7746 : Integer.Sparse Key := [(key2478, -6), (key2501, -6), (key2464, -6), (key2470, -6), (key2478, 2), (key2501, 2), (key2464, 2), (key2570, 2), (key2575, 2), (key2388, 2), (key2435, 2), (key2370, 2), (key2762, 2), (key2876, 2), (key2589, 2), (key2768, 2)]

def rawRow7747 : Integer.Sparse Key := [(key2501, -6), (key2478, -6), (key2464, -6), (key2470, -6), (key2501, 2), (key2478, 2), (key2464, 2), (key2575, 2), (key2570, 2), (key2435, 2), (key2388, 2), (key2398, 2), (key2583, 2), (key2876, 2), (key2768, 2), (key2589, 2)]

def rawRow7748 : Integer.Sparse Key := [(key2470, -6), (key2478, -6), (key2501, -6), (key2464, -6), (key2568, 2), (key2570, 2), (key2575, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2370, 2), (key2762, 2), (key2839, 2)]

def rawRow7749 : Integer.Sparse Key := [(key2478, -6), (key2470, -6), (key2501, -6), (key2464, -6), (key2570, 2), (key2568, 2), (key2575, 2), (key2388, 2), (key2376, 2), (key2478, 2), (key2404, 2), (key2501, 2), (key2435, 2), (key2370, 2), (key2839, 2), (key2762, 2)]

def rawRow7750 : Integer.Sparse Key := [(key2470, -6), (key2501, -6), (key2478, -6), (key2464, -6), (key2568, 2), (key2575, 2), (key2570, 2), (key2404, 2), (key2435, 2), (key2376, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2398, 2), (key2583, 2), (key2839, 2)]

def rawRow7751 : Integer.Sparse Key := [(key2501, -6), (key2470, -6), (key2478, -6), (key2464, -6), (key2575, 2), (key2568, 2), (key2570, 2), (key2435, 2), (key2404, 2), (key2501, 2), (key2376, 2), (key2478, 2), (key2388, 2), (key2398, 2), (key2839, 2), (key2583, 2)]

def rawRow7752 : Integer.Sparse Key := [(key2478, -6), (key2501, -6), (key2470, -6), (key2464, -6), (key2570, 2), (key2575, 2), (key2568, 2), (key2478, 2), (key2501, 2), (key2388, 2), (key2435, 2), (key2376, 2), (key2404, 2), (key2464, 2), (key2370, 2), (key2762, 2)]

def rawRow7753 : Integer.Sparse Key := [(key2501, -6), (key2478, -6), (key2470, -6), (key2464, -6), (key2575, 2), (key2570, 2), (key2568, 2), (key2501, 2), (key2478, 2), (key2435, 2), (key2388, 2), (key2404, 2), (key2376, 2), (key2464, 2), (key2398, 2), (key2583, 2)]

def rawRow7754 : Integer.Sparse Key := [(key2608, -2), (key2614, -2), (key2614, -2), (key2801, -2), (key2807, -2), (key2801, -2), (key2827, -2), (key2807, -2), (key2827, -2), (key3011, -2), (key3011, -2), (key3016, -2), (key2624, 1), (key2630, 1), (key2624, 1), (key2638, 1), (key2630, 1), (key2638, 1), (key2698, 1), (key2704, 1), (key2698, 1), (key2724, 1), (key2704, 1), (key2724, 1), (key2851, 1), (key2858, 1), (key2851, 1), (key2868, 1), (key2858, 1), (key2868, 1), (key3021, 1), (key3022, 1), (key3021, 1), (key3025, 1), (key3022, 1), (key3025, 1)]

def rawRow7755 : Integer.Sparse Key := [(key2614, -2), (key2608, -2), (key2614, -2), (key2807, -2), (key2801, -2), (key2827, -2), (key2801, -2), (key2827, -2), (key2807, -2), (key3011, -2), (key3016, -2), (key3011, -2), (key2630, 1), (key2624, 1), (key2638, 1), (key2624, 1), (key2638, 1), (key2630, 1), (key2704, 1), (key2698, 1), (key2724, 1), (key2698, 1), (key2724, 1), (key2704, 1), (key2858, 1), (key2851, 1), (key2868, 1), (key2851, 1), (key2868, 1), (key2858, 1), (key3022, 1), (key3021, 1), (key3025, 1), (key3021, 1), (key3025, 1), (key3022, 1)]

def rawRow7756 : Integer.Sparse Key := [(key2614, -2), (key2614, -2), (key2608, -2), (key2827, -2), (key2827, -2), (key2807, -2), (key2807, -2), (key2801, -2), (key2801, -2), (key3016, -2), (key3011, -2), (key3011, -2), (key2638, 1), (key2638, 1), (key2630, 1), (key2630, 1), (key2624, 1), (key2624, 1), (key2724, 1), (key2724, 1), (key2704, 1), (key2704, 1), (key2698, 1), (key2698, 1), (key2868, 1), (key2868, 1), (key2858, 1), (key2858, 1), (key2851, 1), (key2851, 1), (key3025, 1), (key3025, 1), (key3022, 1), (key3022, 1), (key3021, 1), (key3021, 1)]

def rawRow7757 : Integer.Sparse Key := [(key2801, -2), (key2807, -2), (key2827, -2), (key2608, -2), (key2614, -2), (key2801, -2), (key2827, -2), (key3011, -2), (key3016, -2), (key2614, -2), (key2807, -2), (key2827, -2), (key2698, 1), (key2704, 1), (key2851, 1), (key2858, 1), (key3021, 1), (key3022, 1), (key2624, 1), (key2630, 1), (key2851, 1), (key2868, 1), (key3021, 1), (key3025, 1), (key2624, 1), (key2638, 1), (key2698, 1), (key2724, 1), (key3022, 1), (key3025, 1), (key2630, 1), (key2638, 1), (key2704, 1), (key2724, 1), (key2858, 1), (key2868, 1)]

def rawRow7758 : Integer.Sparse Key := [(key2807, -2), (key2801, -2), (key2827, -2), (key2614, -2), (key2608, -2), (key2827, -2), (key2801, -2), (key3016, -2), (key3011, -2), (key2614, -2), (key2827, -2), (key2807, -2), (key2704, 1), (key2698, 1), (key2858, 1), (key2851, 1), (key3022, 1), (key3021, 1), (key2630, 1), (key2624, 1), (key2868, 1), (key2851, 1), (key3025, 1), (key3021, 1), (key2638, 1), (key2624, 1), (key2724, 1), (key2698, 1), (key3025, 1), (key3022, 1), (key2638, 1), (key2630, 1), (key2724, 1), (key2704, 1), (key2868, 1), (key2858, 1)]

def rawRow7759 : Integer.Sparse Key := [(key2801, -2), (key2827, -2), (key2807, -2), (key2801, -2), (key2827, -2), (key2608, -2), (key3016, -2), (key2614, -2), (key2827, -2), (key2807, -2), (key2614, -2), (key2827, -2), (key2851, 1), (key3021, 1), (key2698, 1), (key3022, 1), (key2704, 1), (key2858, 1), (key2851, 1), (key3021, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2698, 1), (key3022, 1), (key2624, 1), (key3025, 1), (key2638, 1), (key2724, 1), (key2704, 1), (key2858, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2724, 1)]

def rawRow7760 : Integer.Sparse Key := [(key2827, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2801, -2), (key3016, -2), (key2608, -2), (key2827, -2), (key2614, -2), (key2807, -2), (key2827, -2), (key2614, -2), (key3021, 1), (key2851, 1), (key3022, 1), (key2698, 1), (key2858, 1), (key2704, 1), (key3021, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key2868, 1), (key2630, 1), (key3022, 1), (key2698, 1), (key3025, 1), (key2624, 1), (key2724, 1), (key2638, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2724, 1), (key2638, 1)]

def rawRow7761 : Integer.Sparse Key := [(key2807, -2), (key2827, -2), (key2801, -2), (key3011, -2), (key3016, -2), (key2614, -2), (key2827, -2), (key2608, -2), (key2801, -2), (key2827, -2), (key2614, -2), (key2807, -2), (key2858, 1), (key3022, 1), (key2704, 1), (key3021, 1), (key2698, 1), (key2851, 1), (key2868, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2624, 1), (key2851, 1), (key2724, 1), (key3025, 1), (key2638, 1), (key3022, 1), (key2624, 1), (key2698, 1), (key2724, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2630, 1), (key2704, 1)]

def rawRow7762 : Integer.Sparse Key := [(key2827, -2), (key2807, -2), (key2801, -2), (key3016, -2), (key3011, -2), (key2827, -2), (key2614, -2), (key2801, -2), (key2608, -2), (key2827, -2), (key2807, -2), (key2614, -2), (key3022, 1), (key2858, 1), (key3021, 1), (key2704, 1), (key2851, 1), (key2698, 1), (key3025, 1), (key2868, 1), (key3021, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key3025, 1), (key2724, 1), (key3022, 1), (key2638, 1), (key2698, 1), (key2624, 1), (key2868, 1), (key2724, 1), (key2858, 1), (key2638, 1), (key2704, 1), (key2630, 1)]

def rawRow7763 : Integer.Sparse Key := [(key3011, -2), (key3011, -2), (key3016, -2), (key2614, -2), (key2614, -2), (key2807, -2), (key2807, -2), (key2827, -2), (key2827, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2724, 1), (key2724, 1), (key2868, 1), (key2868, 1), (key3025, 1), (key3025, 1), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1), (key2630, 1), (key2630, 1), (key2704, 1), (key2704, 1), (key3021, 1), (key3021, 1), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

def rawRow7764 : Integer.Sparse Key := [(key3011, -2), (key3016, -2), (key3011, -2), (key2807, -2), (key2827, -2), (key2614, -2), (key2827, -2), (key2614, -2), (key2807, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2868, 1), (key3025, 1), (key2724, 1), (key3025, 1), (key2724, 1), (key2868, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2704, 1), (key3021, 1), (key2630, 1), (key3021, 1), (key2630, 1), (key2704, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

def rawRow7765 : Integer.Sparse Key := [(key3016, -2), (key3011, -2), (key3011, -2), (key2827, -2), (key2807, -2), (key2827, -2), (key2614, -2), (key2807, -2), (key2614, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key3025, 1), (key2868, 1), (key3025, 1), (key2724, 1), (key2868, 1), (key2724, 1), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key3021, 1), (key2704, 1), (key3021, 1), (key2630, 1), (key2704, 1), (key2630, 1), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

def rawRow7766 : Integer.Sparse Key := [(key2624, -2), (key2630, -2), (key2638, -2), (key2698, -2), (key2704, -2), (key2851, -2), (key3021, -2), (key2858, -2), (key3022, -2), (key2724, -2), (key2868, -2), (key3025, -2), (key2608, 1), (key2614, 1), (key2624, 1), (key2638, 1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def rawRow7767 : Integer.Sparse Key := [(key2630, -2), (key2624, -2), (key2638, -2), (key2704, -2), (key2698, -2), (key3021, -2), (key2851, -2), (key3022, -2), (key2858, -2), (key2724, -2), (key3025, -2), (key2868, -2), (key2614, 1), (key2608, 1), (key2638, 1), (key2624, 1), (key2659, 1), (key2657, 1), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1), (key2792, 1), (key2778, 1), (key2827, 1), (key2801, 1), (key2922, 1), (key2919, 1), (key3009, 1), (key3007, 1), (key3016, 1), (key3011, 1), (key3025, 1), (key3022, 1)]

def rawRow7768 : Integer.Sparse Key := [(key2624, -2), (key2638, -2), (key2630, -2), (key2851, -2), (key2858, -2), (key2698, -2), (key3022, -2), (key2704, -2), (key3021, -2), (key2868, -2), (key2724, -2), (key3025, -2), (key2624, 1), (key2638, 1), (key2608, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2801, 1), (key2919, 1), (key2778, 1), (key2922, 1), (key2792, 1), (key2827, 1), (key3011, 1), (key3022, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3016, 1)]

def rawRow7769 : Integer.Sparse Key := [(key2638, -2), (key2624, -2), (key2630, -2), (key2858, -2), (key2851, -2), (key3022, -2), (key2698, -2), (key3021, -2), (key2704, -2), (key2868, -2), (key3025, -2), (key2724, -2), (key2638, 1), (key2624, 1), (key2659, 1), (key2608, 1), (key2638, 1), (key2614, 1), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1), (key2919, 1), (key2801, 1), (key2922, 1), (key2778, 1), (key2827, 1), (key2792, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3016, 1), (key3009, 1)]

def rawRow7770 : Integer.Sparse Key := [(key2630, -2), (key2638, -2), (key2624, -2), (key3021, -2), (key3022, -2), (key2704, -2), (key2858, -2), (key2698, -2), (key2851, -2), (key3025, -2), (key2724, -2), (key2868, -2), (key2657, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2608, 1), (key2624, 1), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1), (key2827, 1), (key2922, 1), (key2792, 1), (key2919, 1), (key2778, 1), (key2801, 1), (key3016, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key3007, 1), (key3011, 1)]

def rawRow7771 : Integer.Sparse Key := [(key2638, -2), (key2630, -2), (key2624, -2), (key3022, -2), (key3021, -2), (key2858, -2), (key2704, -2), (key2851, -2), (key2698, -2), (key3025, -2), (key2868, -2), (key2724, -2), (key2659, 1), (key2657, 1), (key2638, 1), (key2614, 1), (key2624, 1), (key2608, 1), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2922, 1), (key2827, 1), (key2919, 1), (key2792, 1), (key2801, 1), (key2778, 1), (key3025, 1), (key3016, 1), (key3022, 1), (key3009, 1), (key3011, 1), (key3007, 1)]

def rawRow7772 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2624, -2), (key2630, -2), (key2851, -2), (key3021, -2), (key2868, -2), (key3025, -2), (key2638, -2), (key2858, -2), (key3022, -2), (key2663, 1), (key2669, 1), (key2698, 1), (key2752, 1), (key2724, 1), (key2757, 1), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2624, 1), (key2638, 1), (key2698, 1), (key2724, 1), (key3022, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2752, 1), (key2757, 1), (key2919, 1), (key2922, 1)]

def rawRow7773 : Integer.Sparse Key := [(key2704, -2), (key2698, -2), (key2724, -2), (key2630, -2), (key2624, -2), (key3021, -2), (key2851, -2), (key3025, -2), (key2868, -2), (key2638, -2), (key3022, -2), (key2858, -2), (key2669, 1), (key2663, 1), (key2752, 1), (key2698, 1), (key2757, 1), (key2724, 1), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2638, 1), (key2624, 1), (key2724, 1), (key2698, 1), (key3025, 1), (key3022, 1), (key2659, 1), (key2657, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2919, 1)]

def rawRow7774 : Integer.Sparse Key := [(key2698, -2), (key2724, -2), (key2704, -2), (key2851, -2), (key2868, -2), (key2624, -2), (key3025, -2), (key2630, -2), (key3021, -2), (key2858, -2), (key2638, -2), (key3022, -2), (key2698, 1), (key2724, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2698, 1), (key3022, 1), (key2624, 1), (key3025, 1), (key2638, 1), (key2724, 1), (key2752, 1), (key2919, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2757, 1)]

def rawRow7775 : Integer.Sparse Key := [(key2724, -2), (key2698, -2), (key2704, -2), (key2868, -2), (key2851, -2), (key3025, -2), (key2624, -2), (key3021, -2), (key2630, -2), (key2858, -2), (key3022, -2), (key2638, -2), (key2724, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2752, 1), (key2669, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key3022, 1), (key2698, 1), (key3025, 1), (key2624, 1), (key2724, 1), (key2638, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2757, 1), (key2659, 1)]

def rawRow7776 : Integer.Sparse Key := [(key2704, -2), (key2724, -2), (key2698, -2), (key3021, -2), (key3025, -2), (key2630, -2), (key2868, -2), (key2624, -2), (key2851, -2), (key3022, -2), (key2638, -2), (key2858, -2), (key2752, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2663, 1), (key2698, 1), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2724, 1), (key3025, 1), (key2638, 1), (key3022, 1), (key2624, 1), (key2698, 1), (key2757, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2657, 1), (key2752, 1)]

def rawRow7777 : Integer.Sparse Key := [(key2724, -2), (key2704, -2), (key2698, -2), (key3025, -2), (key3021, -2), (key2868, -2), (key2630, -2), (key2851, -2), (key2624, -2), (key3022, -2), (key2858, -2), (key2638, -2), (key2757, 1), (key2752, 1), (key2724, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key3025, 1), (key2724, 1), (key3022, 1), (key2638, 1), (key2698, 1), (key2624, 1), (key2922, 1), (key2757, 1), (key2919, 1), (key2659, 1), (key2752, 1), (key2657, 1)]

def rawRow7778 : Integer.Sparse Key := [(key2851, -2), (key2858, -2), (key2868, -2), (key2624, -2), (key2638, -2), (key2698, -2), (key3022, -2), (key2724, -2), (key3025, -2), (key2630, -2), (key2704, -2), (key3021, -2), (key2778, 1), (key2792, 1), (key2801, 1), (key2919, 1), (key2827, 1), (key2922, 1), (key2624, 1), (key2638, 1), (key2698, 1), (key3022, 1), (key2724, 1), (key3025, 1), (key2608, 1), (key2659, 1), (key2663, 1), (key2757, 1), (key3009, 1), (key3016, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2724, 1), (key2792, 1), (key2827, 1)]

def rawRow7779 : Integer.Sparse Key := [(key2858, -2), (key2851, -2), (key2868, -2), (key2638, -2), (key2624, -2), (key3022, -2), (key2698, -2), (key3025, -2), (key2724, -2), (key2630, -2), (key3021, -2), (key2704, -2), (key2792, 1), (key2778, 1), (key2919, 1), (key2801, 1), (key2922, 1), (key2827, 1), (key2638, 1), (key2624, 1), (key3022, 1), (key2698, 1), (key3025, 1), (key2724, 1), (key2659, 1), (key2608, 1), (key2757, 1), (key2663, 1), (key3016, 1), (key3009, 1), (key2638, 1), (key2614, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2792, 1)]

def rawRow7780 : Integer.Sparse Key := [(key2851, -2), (key2868, -2), (key2858, -2), (key2698, -2), (key2724, -2), (key2624, -2), (key3025, -2), (key2638, -2), (key3022, -2), (key2704, -2), (key2630, -2), (key3021, -2), (key2801, 1), (key2827, 1), (key2778, 1), (key2922, 1), (key2792, 1), (key2919, 1), (key2698, 1), (key2724, 1), (key2624, 1), (key3025, 1), (key2638, 1), (key3022, 1), (key2663, 1), (key2757, 1), (key2608, 1), (key3016, 1), (key2659, 1), (key2757, 1), (key2669, 1), (key2792, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2724, 1)]

def rawRow7781 : Integer.Sparse Key := [(key2868, -2), (key2851, -2), (key2858, -2), (key2724, -2), (key2698, -2), (key3025, -2), (key2624, -2), (key3022, -2), (key2638, -2), (key2704, -2), (key3021, -2), (key2630, -2), (key2827, 1), (key2801, 1), (key2922, 1), (key2778, 1), (key2919, 1), (key2792, 1), (key2724, 1), (key2698, 1), (key3025, 1), (key2624, 1), (key3022, 1), (key2638, 1), (key2757, 1), (key2663, 1), (key3016, 1), (key2608, 1), (key2757, 1), (key2659, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2724, 1), (key2638, 1)]

def rawRow7782 : Integer.Sparse Key := [(key2858, -2), (key2868, -2), (key2851, -2), (key3022, -2), (key3025, -2), (key2638, -2), (key2724, -2), (key2624, -2), (key2698, -2), (key3021, -2), (key2630, -2), (key2704, -2), (key2919, 1), (key2922, 1), (key2792, 1), (key2827, 1), (key2778, 1), (key2801, 1), (key3022, 1), (key3025, 1), (key2638, 1), (key2724, 1), (key2624, 1), (key2698, 1), (key3009, 1), (key3016, 1), (key2659, 1), (key2757, 1), (key2608, 1), (key2663, 1), (key2724, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2614, 1), (key2669, 1)]

def rawRow7783 : Integer.Sparse Key := [(key2868, -2), (key2858, -2), (key2851, -2), (key3025, -2), (key3022, -2), (key2724, -2), (key2638, -2), (key2698, -2), (key2624, -2), (key3021, -2), (key2704, -2), (key2630, -2), (key2922, 1), (key2919, 1), (key2827, 1), (key2792, 1), (key2801, 1), (key2778, 1), (key3025, 1), (key3022, 1), (key2724, 1), (key2638, 1), (key2698, 1), (key2624, 1), (key3016, 1), (key3009, 1), (key2757, 1), (key2659, 1), (key2663, 1), (key2608, 1), (key2827, 1), (key2724, 1), (key2792, 1), (key2638, 1), (key2669, 1), (key2614, 1)]

def rawRow7784 : Integer.Sparse Key := [(key3021, -2), (key3022, -2), (key3025, -2), (key2630, -2), (key2638, -2), (key2704, -2), (key2858, -2), (key2724, -2), (key2868, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key3007, 1), (key3009, 1), (key3011, 1), (key3022, 1), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2792, 1), (key2724, 1), (key2827, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

def rawRow7785 : Integer.Sparse Key := [(key3022, -2), (key3021, -2), (key3025, -2), (key2638, -2), (key2630, -2), (key2858, -2), (key2704, -2), (key2868, -2), (key2724, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key3009, 1), (key3007, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1), (key2638, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2724, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

def rawRow7786 : Integer.Sparse Key := [(key3021, -2), (key3025, -2), (key3022, -2), (key2704, -2), (key2724, -2), (key2630, -2), (key2868, -2), (key2638, -2), (key2858, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key3011, 1), (key3016, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2669, 1), (key2724, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

def rawRow7787 : Integer.Sparse Key := [(key3025, -2), (key3021, -2), (key3022, -2), (key2724, -2), (key2704, -2), (key2868, -2), (key2630, -2), (key2858, -2), (key2638, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key3016, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2792, 1), (key2638, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

def rawRow7788 : Integer.Sparse Key := [(key3022, -2), (key3025, -2), (key3021, -2), (key2858, -2), (key2868, -2), (key2638, -2), (key2724, -2), (key2630, -2), (key2704, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key3022, 1), (key3025, 1), (key3009, 1), (key3016, 1), (key3007, 1), (key3011, 1), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1), (key2792, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2614, 1), (key2669, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

def rawRow7789 : Integer.Sparse Key := [(key3025, -2), (key3022, -2), (key3021, -2), (key2868, -2), (key2858, -2), (key2724, -2), (key2638, -2), (key2704, -2), (key2630, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key3025, 1), (key3022, 1), (key3016, 1), (key3009, 1), (key3011, 1), (key3007, 1), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1), (key2827, 1), (key2792, 1), (key2724, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

def rawRow7790 : Integer.Sparse Key := [(key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2), (key2516, -2)]

def rawRow7791 : Integer.Sparse Key := [(key2360, 2), (key2360, 2), (key2360, 2), (key2455, 2), (key2455, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2516, 2), (key2360, -2), (key2360, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2516, -2), (key2516, -2)]

def rawRow7792 : Integer.Sparse Key := [(key2455, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2360, 2), (key2455, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2455, -2), (key2455, -2), (key2516, -2), (key2360, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2516, -2), (key2360, -2), (key2455, -2), (key2455, -2)]

def rawRow7793 : Integer.Sparse Key := [(key2516, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2455, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2360, 2), (key2455, 2), (key2455, -2), (key2516, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2360, -2), (key2516, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2360, -2), (key2455, -2)]

def rawRow7794 : Integer.Sparse Key := [(key2516, 2), (key2516, 2), (key2455, 2), (key2516, 2), (key2516, 2), (key2360, 2), (key2516, 2), (key2455, 2), (key2516, 2), (key2360, 2), (key2455, 2), (key2360, 2), (key2516, -2), (key2455, -2), (key2455, -2), (key2516, -2), (key2455, -2), (key2516, -2), (key2360, -2), (key2455, -2), (key2360, -2), (key2455, -2), (key2455, -2), (key2360, -2)]

def rawRow7795 : Integer.Sparse Key := [(key968, -24), (key1082, 6), (key1082, 6), (key1082, 6), (key1082, 6)]

def rawRow7796 : Integer.Sparse Key := [(key1082, -24), (key968, 6), (key1082, 6), (key1082, 6), (key1082, 6)]

def rawRow7797 : Integer.Sparse Key := [(key1082, -24), (key1082, 6), (key968, 6), (key1082, 6), (key1082, 6)]

def rawRow7798 : Integer.Sparse Key := [(key1082, -24), (key1082, 6), (key1082, 6), (key968, 6), (key1082, 6)]

def rawRow7799 : Integer.Sparse Key := [(key1082, -24), (key1082, 6), (key1082, 6), (key1082, 6), (key968, 6)]

def rawRow7800 : Integer.Sparse Key := [(key973, -6), (key973, -6), (key973, -6), (key973, -6), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2)]

def rawRow7801 : Integer.Sparse Key := [(key1087, -6), (key1087, -6), (key1087, -6), (key1160, -6), (key973, 2), (key973, 2), (key973, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key1160, 2), (key1160, 2)]

def rawRow7802 : Integer.Sparse Key := [(key1087, -6), (key1087, -6), (key1160, -6), (key1087, -6), (key1087, 2), (key1087, 2), (key1160, 2), (key973, 2), (key973, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key1160, 2), (key973, 2), (key1087, 2), (key1087, 2)]

def rawRow7803 : Integer.Sparse Key := [(key1087, -6), (key1160, -6), (key1087, -6), (key1087, -6), (key1087, 2), (key1160, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key973, 2), (key1160, 2), (key973, 2), (key1087, 2), (key1087, 2), (key973, 2), (key1087, 2)]

def rawRow7804 : Integer.Sparse Key := [(key1160, -6), (key1087, -6), (key1087, -6), (key1087, -6), (key1160, 2), (key1087, 2), (key1087, 2), (key1160, 2), (key1087, 2), (key1160, 2), (key973, 2), (key1087, 2), (key973, 2), (key1087, 2), (key1087, 2), (key973, 2)]

def rawRow7805 : Integer.Sparse Key := [(key2396, -6), (key2396, -6), (key2396, -6), (key2396, -6), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2)]

def rawRow7806 : Integer.Sparse Key := [(key2581, -6), (key2837, -6), (key2837, -6), (key2837, -6), (key2368, 2), (key2368, 2), (key2368, 2), (key2396, 2), (key2396, 2), (key2396, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2), (key2462, 2)]

def rawRow7807 : Integer.Sparse Key := [(key2837, -6), (key2581, -6), (key2837, -6), (key2837, -6), (key2760, 2), (key2837, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2837, 2), (key2368, 2), (key2368, 2), (key2396, 2), (key2396, 2), (key2462, 2), (key2462, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7808 : Integer.Sparse Key := [(key2837, -6), (key2837, -6), (key2581, -6), (key2837, -6), (key2837, 2), (key2760, 2), (key2837, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2760, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2368, 2), (key2396, 2)]

def rawRow7809 : Integer.Sparse Key := [(key2837, -6), (key2837, -6), (key2837, -6), (key2581, -6), (key2837, 2), (key2837, 2), (key2760, 2), (key2837, 2), (key2837, 2), (key2581, 2), (key2837, 2), (key2760, 2), (key2837, 2), (key2581, 2), (key2760, 2), (key2581, 2)]

def rawRow7810 : Integer.Sparse Key := [(key2355, -6), (key2355, -6), (key2355, -6), (key2355, -6), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2)]

def rawRow7811 : Integer.Sparse Key := [(key2450, -6), (key2450, -6), (key2450, -6), (key2512, -6), (key2355, 2), (key2355, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2512, 2), (key2512, 2)]

def rawRow7812 : Integer.Sparse Key := [(key2450, -6), (key2450, -6), (key2512, -6), (key2450, -6), (key2450, 2), (key2450, 2), (key2512, 2), (key2355, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2512, 2), (key2355, 2), (key2450, 2), (key2450, 2)]

def rawRow7813 : Integer.Sparse Key := [(key2450, -6), (key2512, -6), (key2450, -6), (key2450, -6), (key2450, 2), (key2512, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2355, 2), (key2512, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2355, 2), (key2450, 2)]

def rawRow7814 : Integer.Sparse Key := [(key2512, -6), (key2450, -6), (key2450, -6), (key2450, -6), (key2512, 2), (key2450, 2), (key2450, 2), (key2512, 2), (key2450, 2), (key2512, 2), (key2355, 2), (key2450, 2), (key2355, 2), (key2450, 2), (key2450, 2), (key2355, 2)]

def rawRow7815 : Integer.Sparse Key := [(key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2764, -2), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1)]

def rawRow7816 : Integer.Sparse Key := [(key2585, -2), (key2585, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2873, -2), (key2873, -2), (key2585, 1), (key2585, 1), (key2585, 1), (key2585, 1), (key2585, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2764, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2873, 1), (key2873, 1), (key2873, 1), (key2873, 1), (key2873, 1)]

def rawRow7817 : Integer.Sparse Key := [(key2841, -2), (key2841, -2), (key2873, -2), (key2585, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2873, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2764, 1), (key2764, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2873, 1), (key2585, 1), (key2585, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2873, 1), (key2585, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2873, 1), (key2873, 1), (key2585, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2841, 1), (key2841, 1)]

def rawRow7818 : Integer.Sparse Key := [(key2841, -2), (key2873, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2585, -2), (key2873, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2585, -2), (key2841, -2), (key2841, 1), (key2873, 1), (key2764, 1), (key2873, 1), (key2764, 1), (key2841, 1), (key2841, 1), (key2873, 1), (key2585, 1), (key2873, 1), (key2585, 1), (key2841, 1), (key2764, 1), (key2873, 1), (key2585, 1), (key2873, 1), (key2585, 1), (key2764, 1), (key2764, 1), (key2841, 1), (key2585, 1), (key2841, 1), (key2585, 1), (key2764, 1)]

def rawRow7819 : Integer.Sparse Key := [(key2873, -2), (key2841, -2), (key2841, -2), (key2873, -2), (key2841, -2), (key2873, -2), (key2585, -2), (key2841, -2), (key2585, -2), (key2841, -2), (key2841, -2), (key2585, -2), (key2873, 1), (key2841, 1), (key2873, 1), (key2764, 1), (key2841, 1), (key2764, 1), (key2873, 1), (key2841, 1), (key2873, 1), (key2585, 1), (key2841, 1), (key2585, 1), (key2873, 1), (key2764, 1), (key2873, 1), (key2585, 1), (key2764, 1), (key2585, 1), (key2841, 1), (key2764, 1), (key2841, 1), (key2585, 1), (key2764, 1), (key2585, 1)]

def rawRow7820 : Integer.Sparse Key := [(key2351, -24), (key2446, 6), (key2446, 6), (key2446, 6), (key2446, 6)]

def rawRow7821 : Integer.Sparse Key := [(key2446, -24), (key2351, 6), (key2446, 6), (key2446, 6), (key2446, 6)]

def rawRow7822 : Integer.Sparse Key := [(key2446, -24), (key2446, 6), (key2351, 6), (key2446, 6), (key2446, 6)]

def rawRow7823 : Integer.Sparse Key := [(key2446, -24), (key2446, 6), (key2446, 6), (key2351, 6), (key2446, 6)]

def rawRow7824 : Integer.Sparse Key := [(key2446, -24), (key2446, 6), (key2446, 6), (key2446, 6), (key2351, 6)]

def rawRow7825 : Integer.Sparse Key := [(key2766, 2), (key2766, 2), (key2772, 2), (key2843, 2), (key2843, 2), (key2880, 2), (key2887, 2), (key2889, 2), (key2887, 2), (key2910, 2), (key2889, 2), (key2910, 2), (key2929, -2), (key2931, -2), (key2931, -2), (key2966, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2989, -2), (key2995, -2), (key2995, -2), (key3002, -2)]

def rawRow7826 : Integer.Sparse Key := [(key2766, 2), (key2772, 2), (key2766, 2), (key2843, 2), (key2880, 2), (key2843, 2), (key2889, 2), (key2887, 2), (key2910, 2), (key2887, 2), (key2910, 2), (key2889, 2), (key2931, -2), (key2929, -2), (key2931, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2995, -2), (key3002, -2), (key2995, -2)]

def rawRow7827 : Integer.Sparse Key := [(key2772, 2), (key2766, 2), (key2766, 2), (key2880, 2), (key2843, 2), (key2843, 2), (key2910, 2), (key2910, 2), (key2889, 2), (key2889, 2), (key2887, 2), (key2887, 2), (key2931, -2), (key2931, -2), (key2929, -2), (key2989, -2), (key2989, -2), (key2968, -2), (key2968, -2), (key2966, -2), (key2966, -2), (key3002, -2), (key2995, -2), (key2995, -2)]

def rawRow7828 : Integer.Sparse Key := [(key2843, 2), (key2887, 2), (key2889, 2), (key2766, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2772, 2), (key2843, 2), (key2880, 2), (key2889, 2), (key2910, 2), (key2966, -2), (key2968, -2), (key2995, -2), (key2929, -2), (key2931, -2), (key2966, -2), (key2989, -2), (key2995, -2), (key3002, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def rawRow7829 : Integer.Sparse Key := [(key2843, 2), (key2889, 2), (key2887, 2), (key2766, 2), (key2910, 2), (key2887, 2), (key2772, 2), (key2766, 2), (key2880, 2), (key2843, 2), (key2910, 2), (key2889, 2), (key2968, -2), (key2966, -2), (key2995, -2), (key2931, -2), (key2929, -2), (key2989, -2), (key2966, -2), (key3002, -2), (key2995, -2), (key2931, -2), (key2989, -2), (key2968, -2)]

def rawRow7830 : Integer.Sparse Key := [(key2887, 2), (key2843, 2), (key2889, 2), (key2887, 2), (key2766, 2), (key2910, 2), (key2843, 2), (key2889, 2), (key2766, 2), (key2910, 2), (key2772, 2), (key2880, 2), (key2966, -2), (key2995, -2), (key2968, -2), (key2966, -2), (key2995, -2), (key2929, -2), (key3002, -2), (key2931, -2), (key2989, -2), (key2968, -2), (key2931, -2), (key2989, -2)]

def rawRow7831 : Integer.Sparse Key := [(key2887, 2), (key2889, 2), (key2843, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2889, 2), (key2843, 2), (key2910, 2), (key2766, 2), (key2880, 2), (key2772, 2), (key2995, -2), (key2966, -2), (key2968, -2), (key2995, -2), (key2966, -2), (key3002, -2), (key2929, -2), (key2989, -2), (key2931, -2), (key2968, -2), (key2989, -2), (key2931, -2)]

def rawRow7832 : Integer.Sparse Key := [(key2889, 2), (key2843, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2880, 2), (key2910, 2), (key2772, 2), (key2889, 2), (key2766, 2), (key2843, 2), (key2968, -2), (key2995, -2), (key2966, -2), (key2989, -2), (key3002, -2), (key2931, -2), (key2995, -2), (key2929, -2), (key2966, -2), (key2989, -2), (key2931, -2), (key2968, -2)]

def rawRow7833 : Integer.Sparse Key := [(key2889, 2), (key2887, 2), (key2843, 2), (key2910, 2), (key2887, 2), (key2766, 2), (key2910, 2), (key2880, 2), (key2889, 2), (key2772, 2), (key2843, 2), (key2766, 2), (key2995, -2), (key2968, -2), (key2966, -2), (key3002, -2), (key2989, -2), (key2995, -2), (key2931, -2), (key2966, -2), (key2929, -2), (key2989, -2), (key2968, -2), (key2931, -2)]

def rawRow7834 : Integer.Sparse Key := [(key2880, 2), (key2910, 2), (key2910, 2), (key2772, 2), (key2889, 2), (key2889, 2), (key2766, 2), (key2766, 2), (key2843, 2), (key2843, 2), (key2887, 2), (key2887, 2), (key2989, -2), (key2989, -2), (key3002, -2), (key2931, -2), (key2931, -2), (key2968, -2), (key2968, -2), (key2995, -2), (key2995, -2), (key2929, -2), (key2966, -2), (key2966, -2)]

def rawRow7835 : Integer.Sparse Key := [(key2910, 2), (key2880, 2), (key2910, 2), (key2889, 2), (key2772, 2), (key2889, 2), (key2843, 2), (key2887, 2), (key2766, 2), (key2887, 2), (key2766, 2), (key2843, 2), (key2989, -2), (key3002, -2), (key2989, -2), (key2968, -2), (key2995, -2), (key2931, -2), (key2995, -2), (key2931, -2), (key2968, -2), (key2966, -2), (key2929, -2), (key2966, -2)]

def rawRow7836 : Integer.Sparse Key := [(key2910, 2), (key2910, 2), (key2880, 2), (key2889, 2), (key2889, 2), (key2772, 2), (key2887, 2), (key2843, 2), (key2887, 2), (key2766, 2), (key2843, 2), (key2766, 2), (key3002, -2), (key2989, -2), (key2989, -2), (key2995, -2), (key2968, -2), (key2995, -2), (key2931, -2), (key2968, -2), (key2931, -2), (key2966, -2), (key2966, -2), (key2929, -2)]

def rawRow7837 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 6), (key1104, 6), (key1230, 6)]

def rawRow7838 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 6), (key1230, 6), (key1104, 6)]

def rawRow7839 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1230, 6), (key1104, 6), (key1104, 6)]

def rawRow7840 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1026, 6), (key1104, 6), (key1230, 6)]

def rawRow7841 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1026, 6), (key1230, 6), (key1104, 6)]

def rawRow7842 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1104, 6), (key1026, 6), (key1230, 6)]

def rawRow7843 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1104, 6), (key1230, 6), (key1026, 6)]

def rawRow7844 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1230, 6), (key1026, 6), (key1104, 6)]

def rawRow7845 : Integer.Sparse Key := [(key991, -24), (key1104, 6), (key1230, 6), (key1104, 6), (key1026, 6)]

def rawRow7846 : Integer.Sparse Key := [(key991, -24), (key1230, 6), (key1026, 6), (key1104, 6), (key1104, 6)]

def rawRow7847 : Integer.Sparse Key := [(key991, -24), (key1230, 6), (key1104, 6), (key1026, 6), (key1104, 6)]

def rawRow7848 : Integer.Sparse Key := [(key991, -24), (key1230, 6), (key1104, 6), (key1104, 6), (key1026, 6)]

def rawRow7849 : Integer.Sparse Key := [(key993, -6), (key1001, -6), (key1001, -6), (key1015, -6), (key1028, 2), (key1036, 2), (key1036, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1123, 2), (key1123, 2), (key1235, 2)]

def rawRow7850 : Integer.Sparse Key := [(key1001, -6), (key993, -6), (key1001, -6), (key1015, -6), (key1036, 2), (key1028, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1123, 2), (key1235, 2), (key1123, 2)]

def rawRow7851 : Integer.Sparse Key := [(key1001, -6), (key1001, -6), (key993, -6), (key1015, -6), (key1036, 2), (key1036, 2), (key1028, 2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1123, 2)]

def rawRow7852 : Integer.Sparse Key := [(key993, -6), (key1001, -6), (key1015, -6), (key1001, -6), (key1106, 2), (key1114, 2), (key1123, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1114, 2), (key1232, 2)]

def rawRow7853 : Integer.Sparse Key := [(key1001, -6), (key993, -6), (key1015, -6), (key1001, -6), (key1114, 2), (key1106, 2), (key1123, 2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1114, 2)]

def rawRow7854 : Integer.Sparse Key := [(key993, -6), (key1015, -6), (key1001, -6), (key1001, -6), (key1106, 2), (key1123, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1114, 2), (key1036, 2), (key1232, 2)]

def rawRow7855 : Integer.Sparse Key := [(key1015, -6), (key993, -6), (key1001, -6), (key1001, -6), (key1123, 2), (key1106, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1232, 2), (key1036, 2)]

def rawRow7856 : Integer.Sparse Key := [(key1001, -6), (key1015, -6), (key993, -6), (key1001, -6), (key1114, 2), (key1123, 2), (key1106, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1232, 2), (key1036, 2), (key1114, 2)]

def rawRow7857 : Integer.Sparse Key := [(key1015, -6), (key1001, -6), (key993, -6), (key1001, -6), (key1123, 2), (key1114, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1232, 2), (key1114, 2), (key1036, 2)]

def rawRow7858 : Integer.Sparse Key := [(key1001, -6), (key1001, -6), (key1015, -6), (key993, -6), (key1232, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1106, 2)]

def rawRow7859 : Integer.Sparse Key := [(key1001, -6), (key1015, -6), (key1001, -6), (key993, -6), (key1232, 2), (key1235, 2), (key1232, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1028, 2), (key1106, 2)]

def rawRow7860 : Integer.Sparse Key := [(key1015, -6), (key1001, -6), (key1001, -6), (key993, -6), (key1235, 2), (key1232, 2), (key1232, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1106, 2), (key1106, 2), (key1028, 2)]

def rawRow7861 : Integer.Sparse Key := [(key2665, -6), (key2700, -6), (key2700, -6), (key2721, -6), (key2780, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

def rawRow7862 : Integer.Sparse Key := [(key2665, -6), (key2700, -6), (key2721, -6), (key2700, -6), (key2780, 2), (key2789, 2), (key2780, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

def rawRow7863 : Integer.Sparse Key := [(key2665, -6), (key2721, -6), (key2700, -6), (key2700, -6), (key2789, 2), (key2780, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

def rawRow7864 : Integer.Sparse Key := [(key2700, -6), (key2665, -6), (key2700, -6), (key2721, -6), (key2803, 2), (key2853, 2), (key2855, 2), (key2780, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

def rawRow7865 : Integer.Sparse Key := [(key2700, -6), (key2665, -6), (key2721, -6), (key2700, -6), (key2803, 2), (key2855, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2853, 2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

def rawRow7866 : Integer.Sparse Key := [(key2700, -6), (key2700, -6), (key2665, -6), (key2721, -6), (key2853, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

def rawRow7867 : Integer.Sparse Key := [(key2700, -6), (key2700, -6), (key2721, -6), (key2665, -6), (key2853, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

def rawRow7868 : Integer.Sparse Key := [(key2700, -6), (key2721, -6), (key2665, -6), (key2700, -6), (key2855, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

def rawRow7869 : Integer.Sparse Key := [(key2700, -6), (key2721, -6), (key2700, -6), (key2665, -6), (key2855, 2), (key2853, 2), (key2803, 2), (key2865, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

def rawRow7870 : Integer.Sparse Key := [(key2721, -6), (key2665, -6), (key2700, -6), (key2700, -6), (key2824, 2), (key2865, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

def rawRow7871 : Integer.Sparse Key := [(key2721, -6), (key2700, -6), (key2665, -6), (key2700, -6), (key2865, 2), (key2824, 2), (key2865, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

def rawRow7872 : Integer.Sparse Key := [(key2721, -6), (key2700, -6), (key2700, -6), (key2665, -6), (key2865, 2), (key2865, 2), (key2824, 2), (key2855, 2), (key2855, 2), (key2789, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

def rawRow7873 : Integer.Sparse Key := [(key2370, -6), (key2376, -6), (key2376, -6), (key2388, -6), (key2762, 2), (key2768, 2), (key2768, 2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key2916, 2), (key2916, 2), (key2925, 2)]

def rawRow7874 : Integer.Sparse Key := [(key2376, -6), (key2370, -6), (key2376, -6), (key2388, -6), (key2768, 2), (key2762, 2), (key2768, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2916, 2), (key2925, 2), (key2916, 2)]

def rawRow7875 : Integer.Sparse Key := [(key2376, -6), (key2376, -6), (key2370, -6), (key2388, -6), (key2768, 2), (key2768, 2), (key2762, 2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key2916, 2)]

def rawRow7876 : Integer.Sparse Key := [(key2370, -6), (key2376, -6), (key2388, -6), (key2376, -6), (key2839, 2), (key2845, 2), (key2916, 2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key2768, 2), (key2845, 2), (key2876, 2)]

def rawRow7877 : Integer.Sparse Key := [(key2376, -6), (key2370, -6), (key2388, -6), (key2376, -6), (key2845, 2), (key2839, 2), (key2916, 2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key2768, 2), (key2876, 2), (key2845, 2)]

def rawRow7878 : Integer.Sparse Key := [(key2370, -6), (key2388, -6), (key2376, -6), (key2376, -6), (key2839, 2), (key2916, 2), (key2845, 2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key2845, 2), (key2768, 2), (key2876, 2)]

def rawRow7879 : Integer.Sparse Key := [(key2388, -6), (key2370, -6), (key2376, -6), (key2376, -6), (key2916, 2), (key2839, 2), (key2845, 2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key2845, 2), (key2876, 2), (key2768, 2)]

def rawRow7880 : Integer.Sparse Key := [(key2376, -6), (key2388, -6), (key2370, -6), (key2376, -6), (key2845, 2), (key2916, 2), (key2839, 2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key2876, 2), (key2768, 2), (key2845, 2)]

def rawRow7881 : Integer.Sparse Key := [(key2388, -6), (key2376, -6), (key2370, -6), (key2376, -6), (key2916, 2), (key2845, 2), (key2839, 2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key2876, 2), (key2845, 2), (key2768, 2)]

def rawRow7882 : Integer.Sparse Key := [(key2376, -6), (key2376, -6), (key2388, -6), (key2370, -6), (key2876, 2), (key2876, 2), (key2925, 2), (key2768, 2), (key2768, 2), (key2845, 2), (key2845, 2), (key2916, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key2839, 2)]

def rawRow7883 : Integer.Sparse Key := [(key2376, -6), (key2388, -6), (key2376, -6), (key2370, -6), (key2876, 2), (key2925, 2), (key2876, 2), (key2845, 2), (key2916, 2), (key2768, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2839, 2), (key2762, 2), (key2839, 2)]

def rawRow7884 : Integer.Sparse Key := [(key2388, -6), (key2376, -6), (key2376, -6), (key2370, -6), (key2925, 2), (key2876, 2), (key2876, 2), (key2916, 2), (key2845, 2), (key2916, 2), (key2768, 2), (key2845, 2), (key2768, 2), (key2839, 2), (key2839, 2), (key2762, 2)]

def rawRow7885 : Integer.Sparse Key := [(key2663, -2), (key2669, -2), (key2669, -2), (key2698, -2), (key2704, -2), (key2698, -2), (key2724, -2), (key2704, -2), (key2724, -2), (key2752, -2), (key2752, -2), (key2757, -2), (key2778, 1), (key2784, 1), (key2778, 1), (key2792, 1), (key2784, 1), (key2792, 1), (key2801, 1), (key2807, 1), (key2801, 1), (key2827, 1), (key2807, 1), (key2827, 1), (key2851, 1), (key2858, 1), (key2851, 1), (key2868, 1), (key2858, 1), (key2868, 1), (key2918, 1), (key2919, 1), (key2918, 1), (key2922, 1), (key2919, 1), (key2922, 1)]

def rawRow7886 : Integer.Sparse Key := [(key2669, -2), (key2663, -2), (key2669, -2), (key2704, -2), (key2698, -2), (key2724, -2), (key2698, -2), (key2724, -2), (key2704, -2), (key2752, -2), (key2757, -2), (key2752, -2), (key2784, 1), (key2778, 1), (key2792, 1), (key2778, 1), (key2792, 1), (key2784, 1), (key2807, 1), (key2801, 1), (key2827, 1), (key2801, 1), (key2827, 1), (key2807, 1), (key2858, 1), (key2851, 1), (key2868, 1), (key2851, 1), (key2868, 1), (key2858, 1), (key2919, 1), (key2918, 1), (key2922, 1), (key2918, 1), (key2922, 1), (key2919, 1)]

def rawRow7887 : Integer.Sparse Key := [(key2669, -2), (key2669, -2), (key2663, -2), (key2724, -2), (key2724, -2), (key2704, -2), (key2704, -2), (key2698, -2), (key2698, -2), (key2757, -2), (key2752, -2), (key2752, -2), (key2792, 1), (key2792, 1), (key2784, 1), (key2784, 1), (key2778, 1), (key2778, 1), (key2827, 1), (key2827, 1), (key2807, 1), (key2807, 1), (key2801, 1), (key2801, 1), (key2868, 1), (key2868, 1), (key2858, 1), (key2858, 1), (key2851, 1), (key2851, 1), (key2922, 1), (key2922, 1), (key2919, 1), (key2919, 1), (key2918, 1), (key2918, 1)]

def rawRow7888 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2752, -2), (key2663, -2), (key2669, -2), (key2698, -2), (key2724, -2), (key2752, -2), (key2757, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2801, 1), (key2807, 1), (key2851, 1), (key2858, 1), (key2918, 1), (key2919, 1), (key2778, 1), (key2784, 1), (key2851, 1), (key2868, 1), (key2918, 1), (key2922, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2919, 1), (key2922, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2858, 1), (key2868, 1)]

def rawRow7889 : Integer.Sparse Key := [(key2704, -2), (key2698, -2), (key2752, -2), (key2669, -2), (key2663, -2), (key2724, -2), (key2698, -2), (key2757, -2), (key2752, -2), (key2669, -2), (key2724, -2), (key2704, -2), (key2807, 1), (key2801, 1), (key2858, 1), (key2851, 1), (key2919, 1), (key2918, 1), (key2784, 1), (key2778, 1), (key2868, 1), (key2851, 1), (key2922, 1), (key2918, 1), (key2792, 1), (key2778, 1), (key2827, 1), (key2801, 1), (key2922, 1), (key2919, 1), (key2792, 1), (key2784, 1), (key2827, 1), (key2807, 1), (key2868, 1), (key2858, 1)]

def rawRow7890 : Integer.Sparse Key := [(key2698, -2), (key2752, -2), (key2704, -2), (key2698, -2), (key2752, -2), (key2663, -2), (key2757, -2), (key2669, -2), (key2724, -2), (key2704, -2), (key2669, -2), (key2724, -2), (key2851, 1), (key2918, 1), (key2801, 1), (key2919, 1), (key2807, 1), (key2858, 1), (key2851, 1), (key2918, 1), (key2778, 1), (key2922, 1), (key2784, 1), (key2868, 1), (key2801, 1), (key2919, 1), (key2778, 1), (key2922, 1), (key2792, 1), (key2827, 1), (key2807, 1), (key2858, 1), (key2784, 1), (key2868, 1), (key2792, 1), (key2827, 1)]

def rawRow7891 : Integer.Sparse Key := [(key2752, -2), (key2698, -2), (key2704, -2), (key2752, -2), (key2698, -2), (key2757, -2), (key2663, -2), (key2724, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2669, -2), (key2918, 1), (key2851, 1), (key2919, 1), (key2801, 1), (key2858, 1), (key2807, 1), (key2918, 1), (key2851, 1), (key2922, 1), (key2778, 1), (key2868, 1), (key2784, 1), (key2919, 1), (key2801, 1), (key2922, 1), (key2778, 1), (key2827, 1), (key2792, 1), (key2858, 1), (key2807, 1), (key2868, 1), (key2784, 1), (key2827, 1), (key2792, 1)]

def rawRow7892 : Integer.Sparse Key := [(key2704, -2), (key2752, -2), (key2698, -2), (key2724, -2), (key2757, -2), (key2669, -2), (key2752, -2), (key2663, -2), (key2698, -2), (key2724, -2), (key2669, -2), (key2704, -2), (key2858, 1), (key2919, 1), (key2807, 1), (key2918, 1), (key2801, 1), (key2851, 1), (key2868, 1), (key2922, 1), (key2784, 1), (key2918, 1), (key2778, 1), (key2851, 1), (key2827, 1), (key2922, 1), (key2792, 1), (key2919, 1), (key2778, 1), (key2801, 1), (key2827, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key2784, 1), (key2807, 1)]

def rawRow7893 : Integer.Sparse Key := [(key2752, -2), (key2704, -2), (key2698, -2), (key2757, -2), (key2724, -2), (key2752, -2), (key2669, -2), (key2698, -2), (key2663, -2), (key2724, -2), (key2704, -2), (key2669, -2), (key2919, 1), (key2858, 1), (key2918, 1), (key2807, 1), (key2851, 1), (key2801, 1), (key2922, 1), (key2868, 1), (key2918, 1), (key2784, 1), (key2851, 1), (key2778, 1), (key2922, 1), (key2827, 1), (key2919, 1), (key2792, 1), (key2801, 1), (key2778, 1), (key2868, 1), (key2827, 1), (key2858, 1), (key2792, 1), (key2807, 1), (key2784, 1)]

def rawRow7894 : Integer.Sparse Key := [(key2724, -2), (key2724, -2), (key2757, -2), (key2669, -2), (key2669, -2), (key2704, -2), (key2704, -2), (key2752, -2), (key2752, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2827, 1), (key2827, 1), (key2868, 1), (key2868, 1), (key2922, 1), (key2922, 1), (key2792, 1), (key2792, 1), (key2858, 1), (key2858, 1), (key2919, 1), (key2919, 1), (key2784, 1), (key2784, 1), (key2807, 1), (key2807, 1), (key2918, 1), (key2918, 1), (key2778, 1), (key2778, 1), (key2801, 1), (key2801, 1), (key2851, 1), (key2851, 1)]

def rawRow7895 : Integer.Sparse Key := [(key2724, -2), (key2757, -2), (key2724, -2), (key2704, -2), (key2752, -2), (key2669, -2), (key2752, -2), (key2669, -2), (key2704, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2868, 1), (key2922, 1), (key2827, 1), (key2922, 1), (key2827, 1), (key2868, 1), (key2858, 1), (key2919, 1), (key2792, 1), (key2919, 1), (key2792, 1), (key2858, 1), (key2807, 1), (key2918, 1), (key2784, 1), (key2918, 1), (key2784, 1), (key2807, 1), (key2801, 1), (key2851, 1), (key2778, 1), (key2851, 1), (key2778, 1), (key2801, 1)]

def rawRow7896 : Integer.Sparse Key := [(key2757, -2), (key2724, -2), (key2724, -2), (key2752, -2), (key2704, -2), (key2752, -2), (key2669, -2), (key2704, -2), (key2669, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2922, 1), (key2868, 1), (key2922, 1), (key2827, 1), (key2868, 1), (key2827, 1), (key2919, 1), (key2858, 1), (key2919, 1), (key2792, 1), (key2858, 1), (key2792, 1), (key2918, 1), (key2807, 1), (key2918, 1), (key2784, 1), (key2807, 1), (key2784, 1), (key2851, 1), (key2801, 1), (key2851, 1), (key2778, 1), (key2801, 1), (key2778, 1)]

def rawRow7897 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 6), (key2841, 6), (key2873, 6)]

def rawRow7898 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 6), (key2873, 6), (key2841, 6)]

def rawRow7899 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2873, 6), (key2841, 6), (key2841, 6)]

def rawRow7900 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2764, 6), (key2841, 6), (key2873, 6)]

def rawRow7901 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2764, 6), (key2873, 6), (key2841, 6)]

def rawRow7902 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2841, 6), (key2764, 6), (key2873, 6)]

def rawRow7903 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2841, 6), (key2873, 6), (key2764, 6)]

def rawRow7904 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2873, 6), (key2764, 6), (key2841, 6)]

def rawRow7905 : Integer.Sparse Key := [(key2585, -24), (key2841, 6), (key2873, 6), (key2841, 6), (key2764, 6)]

def rawRow7906 : Integer.Sparse Key := [(key2585, -24), (key2873, 6), (key2764, 6), (key2841, 6), (key2841, 6)]

def rawRow7907 : Integer.Sparse Key := [(key2585, -24), (key2873, 6), (key2841, 6), (key2764, 6), (key2841, 6)]

def rawRow7908 : Integer.Sparse Key := [(key2585, -24), (key2873, 6), (key2841, 6), (key2841, 6), (key2764, 6)]

def rawRow7909 : Integer.Sparse Key := [(key2764, -24), (key2585, 6), (key2841, 6), (key2841, 6), (key2873, 6)]

def rawRow7910 : Integer.Sparse Key := [(key2764, -24), (key2585, 6), (key2841, 6), (key2873, 6), (key2841, 6)]

def rawRow7911 : Integer.Sparse Key := [(key2764, -24), (key2585, 6), (key2873, 6), (key2841, 6), (key2841, 6)]

def rawRow7912 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2585, 6), (key2841, 6), (key2873, 6)]

def rawRow7913 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2585, 6), (key2873, 6), (key2841, 6)]

def rawRow7914 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2841, 6), (key2585, 6), (key2873, 6)]

def rawRow7915 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2841, 6), (key2873, 6), (key2585, 6)]

def rawRow7916 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2873, 6), (key2585, 6), (key2841, 6)]

def rawRow7917 : Integer.Sparse Key := [(key2764, -24), (key2841, 6), (key2873, 6), (key2841, 6), (key2585, 6)]

def rawRow7918 : Integer.Sparse Key := [(key2764, -24), (key2873, 6), (key2585, 6), (key2841, 6), (key2841, 6)]

def rawRow7919 : Integer.Sparse Key := [(key2764, -24), (key2873, 6), (key2841, 6), (key2585, 6), (key2841, 6)]

def rawRow7920 : Integer.Sparse Key := [(key2764, -24), (key2873, 6), (key2841, 6), (key2841, 6), (key2585, 6)]

def rawRow7921 : Integer.Sparse Key := [(key2608, -2), (key2614, -2), (key2614, -2), (key2624, -2), (key2630, -2), (key2624, -2), (key2638, -2), (key2630, -2), (key2638, -2), (key2657, -2), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 2), (key2669, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2752, 2), (key2752, 2), (key2757, 2)]

def rawRow7922 : Integer.Sparse Key := [(key2614, -2), (key2608, -2), (key2614, -2), (key2630, -2), (key2624, -2), (key2638, -2), (key2624, -2), (key2638, -2), (key2630, -2), (key2657, -2), (key2659, -2), (key2657, -2), (key2669, 2), (key2663, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2752, 2), (key2757, 2), (key2752, 2)]

def rawRow7923 : Integer.Sparse Key := [(key2614, -2), (key2614, -2), (key2608, -2), (key2638, -2), (key2638, -2), (key2630, -2), (key2630, -2), (key2624, -2), (key2624, -2), (key2659, -2), (key2657, -2), (key2657, -2), (key2669, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2724, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2752, 2)]

def rawRow7924 : Integer.Sparse Key := [(key2624, -2), (key2630, -2), (key2638, -2), (key2608, -2), (key2614, -2), (key2624, -2), (key2638, -2), (key2657, -2), (key2659, -2), (key2614, -2), (key2630, -2), (key2638, -2), (key2698, 2), (key2704, 2), (key2752, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2724, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2704, 2), (key2724, 2)]

def rawRow7925 : Integer.Sparse Key := [(key2630, -2), (key2624, -2), (key2638, -2), (key2614, -2), (key2608, -2), (key2638, -2), (key2624, -2), (key2659, -2), (key2657, -2), (key2614, -2), (key2638, -2), (key2630, -2), (key2704, 2), (key2698, 2), (key2752, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2669, 2), (key2724, 2), (key2704, 2)]

def rawRow7926 : Integer.Sparse Key := [(key2624, -2), (key2638, -2), (key2630, -2), (key2624, -2), (key2638, -2), (key2608, -2), (key2659, -2), (key2614, -2), (key2638, -2), (key2630, -2), (key2614, -2), (key2638, -2), (key2698, 2), (key2752, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2669, 2), (key2724, 2)]

def rawRow7927 : Integer.Sparse Key := [(key2638, -2), (key2624, -2), (key2630, -2), (key2638, -2), (key2624, -2), (key2659, -2), (key2608, -2), (key2638, -2), (key2614, -2), (key2630, -2), (key2638, -2), (key2614, -2), (key2752, 2), (key2698, 2), (key2704, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2669, 2)]

def rawRow7928 : Integer.Sparse Key := [(key2630, -2), (key2638, -2), (key2624, -2), (key2657, -2), (key2659, -2), (key2614, -2), (key2638, -2), (key2608, -2), (key2624, -2), (key2638, -2), (key2614, -2), (key2630, -2), (key2704, 2), (key2752, 2), (key2698, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2724, 2), (key2669, 2), (key2704, 2)]

def rawRow7929 : Integer.Sparse Key := [(key2638, -2), (key2630, -2), (key2624, -2), (key2659, -2), (key2657, -2), (key2638, -2), (key2614, -2), (key2624, -2), (key2608, -2), (key2638, -2), (key2630, -2), (key2614, -2), (key2752, 2), (key2704, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2752, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key2724, 2), (key2704, 2), (key2669, 2)]

def rawRow7930 : Integer.Sparse Key := [(key2657, -2), (key2657, -2), (key2659, -2), (key2614, -2), (key2614, -2), (key2630, -2), (key2630, -2), (key2638, -2), (key2638, -2), (key2608, -2), (key2624, -2), (key2624, -2), (key2724, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2669, 2), (key2704, 2), (key2704, 2), (key2752, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2698, 2)]

def rawRow7931 : Integer.Sparse Key := [(key2657, -2), (key2659, -2), (key2657, -2), (key2630, -2), (key2638, -2), (key2614, -2), (key2638, -2), (key2614, -2), (key2630, -2), (key2624, -2), (key2608, -2), (key2624, -2), (key2724, 2), (key2757, 2), (key2724, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2663, 2), (key2698, 2)]

def rawRow7932 : Integer.Sparse Key := [(key2659, -2), (key2657, -2), (key2657, -2), (key2638, -2), (key2630, -2), (key2638, -2), (key2614, -2), (key2630, -2), (key2614, -2), (key2624, -2), (key2624, -2), (key2608, -2), (key2757, 2), (key2724, 2), (key2724, 2), (key2752, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2669, 2), (key2698, 2), (key2698, 2), (key2663, 2)]

def rawRow7933 : Integer.Sparse Key := [(key2663, -2), (key2669, -2), (key2669, -2), (key2698, -2), (key2704, -2), (key2698, -2), (key2752, -2), (key2704, -2), (key2752, -2), (key2724, -2), (key2724, -2), (key2757, -2), (key2608, 2), (key2614, 2), (key2614, 2), (key2801, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key3011, 2), (key3011, 2), (key3016, 2)]

def rawRow7934 : Integer.Sparse Key := [(key2669, -2), (key2663, -2), (key2669, -2), (key2704, -2), (key2698, -2), (key2752, -2), (key2698, -2), (key2752, -2), (key2704, -2), (key2724, -2), (key2757, -2), (key2724, -2), (key2614, 2), (key2608, 2), (key2614, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key3011, 2), (key3016, 2), (key3011, 2)]

def rawRow7935 : Integer.Sparse Key := [(key2669, -2), (key2669, -2), (key2663, -2), (key2752, -2), (key2752, -2), (key2704, -2), (key2704, -2), (key2698, -2), (key2698, -2), (key2757, -2), (key2724, -2), (key2724, -2), (key2614, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2827, 2), (key2807, 2), (key2807, 2), (key2801, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key3011, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7936 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2663, -2), (key2669, -2), (key2698, -2), (key2752, -2), (key2724, -2), (key2757, -2), (key2669, -2), (key2704, -2), (key2752, -2), (key2801, 2), (key2807, 2), (key2827, 2), (key2608, 2), (key2614, 2), (key2801, 2), (key2827, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2807, 2), (key2827, 2)]

def rawRow7937 : Integer.Sparse Key := [(key2704, -2), (key2698, -2), (key2724, -2), (key2669, -2), (key2663, -2), (key2752, -2), (key2698, -2), (key2757, -2), (key2724, -2), (key2669, -2), (key2752, -2), (key2704, -2), (key2807, 2), (key2801, 2), (key2827, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2614, 2), (key2827, 2), (key2807, 2)]

def rawRow7938 : Integer.Sparse Key := [(key2698, -2), (key2724, -2), (key2704, -2), (key2698, -2), (key2724, -2), (key2663, -2), (key2757, -2), (key2669, -2), (key2752, -2), (key2704, -2), (key2669, -2), (key2752, -2), (key2801, 2), (key2827, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2608, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2807, 2), (key2614, 2), (key2827, 2)]

def rawRow7939 : Integer.Sparse Key := [(key2724, -2), (key2698, -2), (key2704, -2), (key2724, -2), (key2698, -2), (key2757, -2), (key2663, -2), (key2752, -2), (key2669, -2), (key2704, -2), (key2752, -2), (key2669, -2), (key2827, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key2608, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2827, 2), (key2614, 2)]

def rawRow7940 : Integer.Sparse Key := [(key2704, -2), (key2724, -2), (key2698, -2), (key2752, -2), (key2757, -2), (key2669, -2), (key2724, -2), (key2663, -2), (key2698, -2), (key2752, -2), (key2669, -2), (key2704, -2), (key2807, 2), (key2827, 2), (key2801, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2827, 2), (key2614, 2), (key2807, 2)]

def rawRow7941 : Integer.Sparse Key := [(key2724, -2), (key2704, -2), (key2698, -2), (key2757, -2), (key2752, -2), (key2724, -2), (key2669, -2), (key2698, -2), (key2663, -2), (key2752, -2), (key2704, -2), (key2669, -2), (key2827, 2), (key2807, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2827, 2), (key2614, 2), (key2801, 2), (key2608, 2), (key2827, 2), (key2807, 2), (key2614, 2)]

def rawRow7942 : Integer.Sparse Key := [(key2752, -2), (key2752, -2), (key2757, -2), (key2669, -2), (key2669, -2), (key2704, -2), (key2704, -2), (key2724, -2), (key2724, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2614, 2), (key2807, 2), (key2807, 2), (key2827, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2801, 2)]

def rawRow7943 : Integer.Sparse Key := [(key2752, -2), (key2757, -2), (key2752, -2), (key2704, -2), (key2724, -2), (key2669, -2), (key2724, -2), (key2669, -2), (key2704, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2801, 2), (key2608, 2), (key2801, 2)]

def rawRow7944 : Integer.Sparse Key := [(key2757, -2), (key2752, -2), (key2752, -2), (key2724, -2), (key2704, -2), (key2724, -2), (key2669, -2), (key2704, -2), (key2669, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2614, 2), (key2801, 2), (key2801, 2), (key2608, 2)]

def rawRow7945 : Integer.Sparse Key := [(key1256, 2), (key1256, 2), (key1261, 2), (key1609, 2), (key1609, 2), (key1642, 2), (key1806, 2), (key1809, 2), (key1806, 2), (key1832, 2), (key1809, 2), (key1832, 2), (key1265, -2), (key1268, -2), (key1268, -2), (key1648, -2), (key1651, -2), (key1648, -2), (key1674, -2), (key1651, -2), (key1674, -2), (key1837, -2), (key1837, -2), (key1848, -2)]

def rawRow7946 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1256, 2), (key1609, 2), (key1642, 2), (key1609, 2), (key1809, 2), (key1806, 2), (key1832, 2), (key1806, 2), (key1832, 2), (key1809, 2), (key1268, -2), (key1265, -2), (key1268, -2), (key1651, -2), (key1648, -2), (key1674, -2), (key1648, -2), (key1674, -2), (key1651, -2), (key1837, -2), (key1848, -2), (key1837, -2)]

def rawRow7947 : Integer.Sparse Key := [(key1261, 2), (key1256, 2), (key1256, 2), (key1642, 2), (key1609, 2), (key1609, 2), (key1832, 2), (key1832, 2), (key1809, 2), (key1809, 2), (key1806, 2), (key1806, 2), (key1268, -2), (key1268, -2), (key1265, -2), (key1674, -2), (key1674, -2), (key1651, -2), (key1651, -2), (key1648, -2), (key1648, -2), (key1848, -2), (key1837, -2), (key1837, -2)]

def rawRow7948 : Integer.Sparse Key := [(key1609, 2), (key1806, 2), (key1809, 2), (key1256, 2), (key1806, 2), (key1832, 2), (key1256, 2), (key1261, 2), (key1609, 2), (key1642, 2), (key1809, 2), (key1832, 2), (key1648, -2), (key1651, -2), (key1837, -2), (key1265, -2), (key1268, -2), (key1648, -2), (key1674, -2), (key1837, -2), (key1848, -2), (key1268, -2), (key1651, -2), (key1674, -2)]

def rawRow7949 : Integer.Sparse Key := [(key1609, 2), (key1809, 2), (key1806, 2), (key1256, 2), (key1832, 2), (key1806, 2), (key1261, 2), (key1256, 2), (key1642, 2), (key1609, 2), (key1832, 2), (key1809, 2), (key1651, -2), (key1648, -2), (key1837, -2), (key1268, -2), (key1265, -2), (key1674, -2), (key1648, -2), (key1848, -2), (key1837, -2), (key1268, -2), (key1674, -2), (key1651, -2)]

def rawRow7950 : Integer.Sparse Key := [(key1806, 2), (key1609, 2), (key1809, 2), (key1806, 2), (key1256, 2), (key1832, 2), (key1609, 2), (key1809, 2), (key1256, 2), (key1832, 2), (key1261, 2), (key1642, 2), (key1648, -2), (key1837, -2), (key1651, -2), (key1648, -2), (key1837, -2), (key1265, -2), (key1848, -2), (key1268, -2), (key1674, -2), (key1651, -2), (key1268, -2), (key1674, -2)]

def rawRow7951 : Integer.Sparse Key := [(key1806, 2), (key1809, 2), (key1609, 2), (key1806, 2), (key1832, 2), (key1256, 2), (key1809, 2), (key1609, 2), (key1832, 2), (key1256, 2), (key1642, 2), (key1261, 2), (key1837, -2), (key1648, -2), (key1651, -2), (key1837, -2), (key1648, -2), (key1848, -2), (key1265, -2), (key1674, -2), (key1268, -2), (key1651, -2), (key1674, -2), (key1268, -2)]

def rawRow7952 : Integer.Sparse Key := [(key1809, 2), (key1609, 2), (key1806, 2), (key1832, 2), (key1256, 2), (key1806, 2), (key1642, 2), (key1832, 2), (key1261, 2), (key1809, 2), (key1256, 2), (key1609, 2), (key1651, -2), (key1837, -2), (key1648, -2), (key1674, -2), (key1848, -2), (key1268, -2), (key1837, -2), (key1265, -2), (key1648, -2), (key1674, -2), (key1268, -2), (key1651, -2)]

def rawRow7953 : Integer.Sparse Key := [(key1809, 2), (key1806, 2), (key1609, 2), (key1832, 2), (key1806, 2), (key1256, 2), (key1832, 2), (key1642, 2), (key1809, 2), (key1261, 2), (key1609, 2), (key1256, 2), (key1837, -2), (key1651, -2), (key1648, -2), (key1848, -2), (key1674, -2), (key1837, -2), (key1268, -2), (key1648, -2), (key1265, -2), (key1674, -2), (key1651, -2), (key1268, -2)]

def rawRow7954 : Integer.Sparse Key := [(key1642, 2), (key1832, 2), (key1832, 2), (key1261, 2), (key1809, 2), (key1809, 2), (key1256, 2), (key1256, 2), (key1609, 2), (key1609, 2), (key1806, 2), (key1806, 2), (key1674, -2), (key1674, -2), (key1848, -2), (key1268, -2), (key1268, -2), (key1651, -2), (key1651, -2), (key1837, -2), (key1837, -2), (key1265, -2), (key1648, -2), (key1648, -2)]

def rawRow7955 : Integer.Sparse Key := [(key1832, 2), (key1642, 2), (key1832, 2), (key1809, 2), (key1261, 2), (key1809, 2), (key1609, 2), (key1806, 2), (key1256, 2), (key1806, 2), (key1256, 2), (key1609, 2), (key1674, -2), (key1848, -2), (key1674, -2), (key1651, -2), (key1837, -2), (key1268, -2), (key1837, -2), (key1268, -2), (key1651, -2), (key1648, -2), (key1265, -2), (key1648, -2)]

def rawRow7956 : Integer.Sparse Key := [(key1832, 2), (key1832, 2), (key1642, 2), (key1809, 2), (key1809, 2), (key1261, 2), (key1806, 2), (key1609, 2), (key1806, 2), (key1256, 2), (key1609, 2), (key1256, 2), (key1848, -2), (key1674, -2), (key1674, -2), (key1837, -2), (key1651, -2), (key1837, -2), (key1268, -2), (key1651, -2), (key1268, -2), (key1648, -2), (key1648, -2), (key1265, -2)]

def rawRow7957 : Integer.Sparse Key := [(key1256, 2), (key1265, 2), (key1268, 2), (key1531, 2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, 2), (key1832, 2), (key1837, 2), (key1848, 2), (key1256, -2), (key1261, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1609, -2), (key1642, -2), (key1651, -2), (key1674, -2), (key1768, -2), (key1809, -2), (key1832, -2)]

def rawRow7958 : Integer.Sparse Key := [(key1256, 2), (key1268, 2), (key1265, 2), (key1531, 2), (key1674, 2), (key1648, 2), (key1768, 2), (key1765, 2), (key1832, 2), (key1806, 2), (key1848, 2), (key1837, 2), (key1261, -2), (key1256, -2), (key1268, -2), (key1536, -2), (key1531, -2), (key1642, -2), (key1609, -2), (key1674, -2), (key1651, -2), (key1768, -2), (key1832, -2), (key1809, -2)]

def rawRow7959 : Integer.Sparse Key := [(key1265, 2), (key1256, 2), (key1268, 2), (key1648, 2), (key1531, 2), (key1674, 2), (key1806, 2), (key1837, 2), (key1765, 2), (key1848, 2), (key1768, 2), (key1832, 2), (key1256, -2), (key1268, -2), (key1261, -2), (key1609, -2), (key1651, -2), (key1531, -2), (key1674, -2), (key1536, -2), (key1642, -2), (key1809, -2), (key1768, -2), (key1832, -2)]

def rawRow7960 : Integer.Sparse Key := [(key1265, 2), (key1268, 2), (key1256, 2), (key1648, 2), (key1674, 2), (key1531, 2), (key1837, 2), (key1806, 2), (key1848, 2), (key1765, 2), (key1832, 2), (key1768, 2), (key1268, -2), (key1256, -2), (key1261, -2), (key1651, -2), (key1609, -2), (key1674, -2), (key1531, -2), (key1642, -2), (key1536, -2), (key1809, -2), (key1832, -2), (key1768, -2)]

def rawRow7961 : Integer.Sparse Key := [(key1268, 2), (key1256, 2), (key1265, 2), (key1674, 2), (key1531, 2), (key1648, 2), (key1832, 2), (key1848, 2), (key1768, 2), (key1837, 2), (key1765, 2), (key1806, 2), (key1261, -2), (key1268, -2), (key1256, -2), (key1642, -2), (key1674, -2), (key1536, -2), (key1651, -2), (key1531, -2), (key1609, -2), (key1832, -2), (key1768, -2), (key1809, -2)]

def rawRow7962 : Integer.Sparse Key := [(key1268, 2), (key1265, 2), (key1256, 2), (key1674, 2), (key1648, 2), (key1531, 2), (key1848, 2), (key1832, 2), (key1837, 2), (key1768, 2), (key1806, 2), (key1765, 2), (key1268, -2), (key1261, -2), (key1256, -2), (key1674, -2), (key1642, -2), (key1651, -2), (key1536, -2), (key1609, -2), (key1531, -2), (key1832, -2), (key1809, -2), (key1768, -2)]

def rawRow7963 : Integer.Sparse Key := [(key1531, 2), (key1765, 2), (key1768, 2), (key1256, 2), (key1806, 2), (key1832, 2), (key1265, 2), (key1268, 2), (key1648, 2), (key1674, 2), (key1837, 2), (key1848, 2), (key1531, -2), (key1536, -2), (key1768, -2), (key1256, -2), (key1261, -2), (key1609, -2), (key1642, -2), (key1809, -2), (key1832, -2), (key1268, -2), (key1651, -2), (key1674, -2)]

def rawRow7964 : Integer.Sparse Key := [(key1531, 2), (key1768, 2), (key1765, 2), (key1256, 2), (key1832, 2), (key1806, 2), (key1268, 2), (key1265, 2), (key1674, 2), (key1648, 2), (key1848, 2), (key1837, 2), (key1536, -2), (key1531, -2), (key1768, -2), (key1261, -2), (key1256, -2), (key1642, -2), (key1609, -2), (key1832, -2), (key1809, -2), (key1268, -2), (key1674, -2), (key1651, -2)]

def rawRow7965 : Integer.Sparse Key := [(key1765, 2), (key1531, 2), (key1768, 2), (key1806, 2), (key1256, 2), (key1832, 2), (key1648, 2), (key1837, 2), (key1265, 2), (key1848, 2), (key1268, 2), (key1674, 2), (key1531, -2), (key1768, -2), (key1536, -2), (key1609, -2), (key1809, -2), (key1256, -2), (key1832, -2), (key1261, -2), (key1642, -2), (key1651, -2), (key1268, -2), (key1674, -2)]

def rawRow7966 : Integer.Sparse Key := [(key1765, 2), (key1768, 2), (key1531, 2), (key1806, 2), (key1832, 2), (key1256, 2), (key1837, 2), (key1648, 2), (key1848, 2), (key1265, 2), (key1674, 2), (key1268, 2), (key1768, -2), (key1531, -2), (key1536, -2), (key1809, -2), (key1609, -2), (key1832, -2), (key1256, -2), (key1642, -2), (key1261, -2), (key1651, -2), (key1674, -2), (key1268, -2)]

def rawRow7967 : Integer.Sparse Key := [(key1768, 2), (key1531, 2), (key1765, 2), (key1832, 2), (key1256, 2), (key1806, 2), (key1674, 2), (key1848, 2), (key1268, 2), (key1837, 2), (key1265, 2), (key1648, 2), (key1536, -2), (key1768, -2), (key1531, -2), (key1642, -2), (key1832, -2), (key1261, -2), (key1809, -2), (key1256, -2), (key1609, -2), (key1674, -2), (key1268, -2), (key1651, -2)]

def rawRow7968 : Integer.Sparse Key := [(key1768, 2), (key1765, 2), (key1531, 2), (key1832, 2), (key1806, 2), (key1256, 2), (key1848, 2), (key1674, 2), (key1837, 2), (key1268, 2), (key1648, 2), (key1265, 2), (key1768, -2), (key1536, -2), (key1531, -2), (key1832, -2), (key1642, -2), (key1809, -2), (key1261, -2), (key1609, -2), (key1256, -2), (key1674, -2), (key1651, -2), (key1268, -2)]

def rawRow7969 : Integer.Sparse Key := [(key1648, 2), (key1806, 2), (key1837, 2), (key1265, 2), (key1765, 2), (key1848, 2), (key1256, 2), (key1268, 2), (key1531, 2), (key1674, 2), (key1768, 2), (key1832, 2), (key1609, -2), (key1651, -2), (key1809, -2), (key1256, -2), (key1268, -2), (key1531, -2), (key1674, -2), (key1768, -2), (key1832, -2), (key1261, -2), (key1536, -2), (key1642, -2)]

def rawRow7970 : Integer.Sparse Key := [(key1648, 2), (key1837, 2), (key1806, 2), (key1265, 2), (key1848, 2), (key1765, 2), (key1268, 2), (key1256, 2), (key1674, 2), (key1531, 2), (key1832, 2), (key1768, 2), (key1651, -2), (key1609, -2), (key1809, -2), (key1268, -2), (key1256, -2), (key1674, -2), (key1531, -2), (key1832, -2), (key1768, -2), (key1261, -2), (key1642, -2), (key1536, -2)]

def rawRow7971 : Integer.Sparse Key := [(key1806, 2), (key1648, 2), (key1837, 2), (key1765, 2), (key1265, 2), (key1848, 2), (key1531, 2), (key1768, 2), (key1256, 2), (key1832, 2), (key1268, 2), (key1674, 2), (key1609, -2), (key1809, -2), (key1651, -2), (key1531, -2), (key1768, -2), (key1256, -2), (key1832, -2), (key1268, -2), (key1674, -2), (key1536, -2), (key1261, -2), (key1642, -2)]

def rawRow7972 : Integer.Sparse Key := [(key1806, 2), (key1837, 2), (key1648, 2), (key1765, 2), (key1848, 2), (key1265, 2), (key1768, 2), (key1531, 2), (key1832, 2), (key1256, 2), (key1674, 2), (key1268, 2), (key1809, -2), (key1609, -2), (key1651, -2), (key1768, -2), (key1531, -2), (key1832, -2), (key1256, -2), (key1674, -2), (key1268, -2), (key1536, -2), (key1642, -2), (key1261, -2)]

def rawRow7973 : Integer.Sparse Key := [(key1837, 2), (key1648, 2), (key1806, 2), (key1848, 2), (key1265, 2), (key1765, 2), (key1674, 2), (key1832, 2), (key1268, 2), (key1768, 2), (key1256, 2), (key1531, 2), (key1651, -2), (key1809, -2), (key1609, -2), (key1674, -2), (key1832, -2), (key1268, -2), (key1768, -2), (key1256, -2), (key1531, -2), (key1642, -2), (key1261, -2), (key1536, -2)]

def rawRow7974 : Integer.Sparse Key := [(key1837, 2), (key1806, 2), (key1648, 2), (key1848, 2), (key1765, 2), (key1265, 2), (key1832, 2), (key1674, 2), (key1768, 2), (key1268, 2), (key1531, 2), (key1256, 2), (key1809, -2), (key1651, -2), (key1609, -2), (key1832, -2), (key1674, -2), (key1768, -2), (key1268, -2), (key1531, -2), (key1256, -2), (key1642, -2), (key1536, -2), (key1261, -2)]

def rawRow7975 : Integer.Sparse Key := [(key1674, 2), (key1832, 2), (key1848, 2), (key1268, 2), (key1768, 2), (key1837, 2), (key1256, 2), (key1265, 2), (key1531, 2), (key1648, 2), (key1765, 2), (key1806, 2), (key1642, -2), (key1674, -2), (key1832, -2), (key1261, -2), (key1268, -2), (key1536, -2), (key1651, -2), (key1768, -2), (key1809, -2), (key1256, -2), (key1531, -2), (key1609, -2)]

def rawRow7976 : Integer.Sparse Key := [(key1674, 2), (key1848, 2), (key1832, 2), (key1268, 2), (key1837, 2), (key1768, 2), (key1265, 2), (key1256, 2), (key1648, 2), (key1531, 2), (key1806, 2), (key1765, 2), (key1674, -2), (key1642, -2), (key1832, -2), (key1268, -2), (key1261, -2), (key1651, -2), (key1536, -2), (key1809, -2), (key1768, -2), (key1256, -2), (key1609, -2), (key1531, -2)]

def rawRow7977 : Integer.Sparse Key := [(key1832, 2), (key1674, 2), (key1848, 2), (key1768, 2), (key1268, 2), (key1837, 2), (key1531, 2), (key1765, 2), (key1256, 2), (key1806, 2), (key1265, 2), (key1648, 2), (key1642, -2), (key1832, -2), (key1674, -2), (key1536, -2), (key1768, -2), (key1261, -2), (key1809, -2), (key1268, -2), (key1651, -2), (key1531, -2), (key1256, -2), (key1609, -2)]

def rawRow7978 : Integer.Sparse Key := [(key1832, 2), (key1848, 2), (key1674, 2), (key1768, 2), (key1837, 2), (key1268, 2), (key1765, 2), (key1531, 2), (key1806, 2), (key1256, 2), (key1648, 2), (key1265, 2), (key1832, -2), (key1642, -2), (key1674, -2), (key1768, -2), (key1536, -2), (key1809, -2), (key1261, -2), (key1651, -2), (key1268, -2), (key1531, -2), (key1609, -2), (key1256, -2)]

def rawRow7979 : Integer.Sparse Key := [(key1848, 2), (key1674, 2), (key1832, 2), (key1837, 2), (key1268, 2), (key1768, 2), (key1648, 2), (key1806, 2), (key1265, 2), (key1765, 2), (key1256, 2), (key1531, 2), (key1674, -2), (key1832, -2), (key1642, -2), (key1651, -2), (key1809, -2), (key1268, -2), (key1768, -2), (key1261, -2), (key1536, -2), (key1609, -2), (key1256, -2), (key1531, -2)]

def rawRow7980 : Integer.Sparse Key := [(key1848, 2), (key1832, 2), (key1674, 2), (key1837, 2), (key1768, 2), (key1268, 2), (key1806, 2), (key1648, 2), (key1765, 2), (key1265, 2), (key1531, 2), (key1256, 2), (key1832, -2), (key1674, -2), (key1642, -2), (key1809, -2), (key1651, -2), (key1768, -2), (key1268, -2), (key1536, -2), (key1261, -2), (key1609, -2), (key1531, -2), (key1256, -2)]

def rawRow7981 : Integer.Sparse Key := [(key377, -24), (key208, 6), (key428, 6), (key428, 6), (key456, 6)]

def rawRow7982 : Integer.Sparse Key := [(key377, -24), (key208, 6), (key428, 6), (key456, 6), (key428, 6)]

def rawRow7983 : Integer.Sparse Key := [(key377, -24), (key208, 6), (key456, 6), (key428, 6), (key428, 6)]

def rawRow7984 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key208, 6), (key428, 6), (key456, 6)]

def rawRow7985 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key208, 6), (key456, 6), (key428, 6)]

def rawRow7986 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key428, 6), (key208, 6), (key456, 6)]

def rawRow7987 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key428, 6), (key456, 6), (key208, 6)]

def rawRow7988 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key456, 6), (key208, 6), (key428, 6)]

def rawRow7989 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key456, 6), (key428, 6), (key208, 6)]

def rawRow7990 : Integer.Sparse Key := [(key377, -24), (key456, 6), (key208, 6), (key428, 6), (key428, 6)]

def rawRow7991 : Integer.Sparse Key := [(key377, -24), (key456, 6), (key428, 6), (key208, 6), (key428, 6)]

def rawRow7992 : Integer.Sparse Key := [(key377, -24), (key456, 6), (key428, 6), (key428, 6), (key208, 6)]

def rawRow7993 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key377, 6), (key428, 6), (key456, 6)]

def rawRow7994 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key377, 6), (key456, 6), (key428, 6)]

def rawRow7995 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key428, 6), (key377, 6), (key456, 6)]

def rawRow7996 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key428, 6), (key456, 6), (key377, 6)]

def rawRow7997 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key456, 6), (key377, 6), (key428, 6)]

def rawRow7998 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key456, 6), (key428, 6), (key377, 6)]

def rawRow7999 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key208, 6), (key428, 6), (key456, 6)]

def rawRow8000 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key208, 6), (key456, 6), (key428, 6)]

def rawRow8001 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key428, 6), (key208, 6), (key456, 6)]

def rawRow8002 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key428, 6), (key456, 6), (key208, 6)]

def rawRow8003 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key456, 6), (key208, 6), (key428, 6)]

def rawRow8004 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key456, 6), (key428, 6), (key208, 6)]

def rawRow8005 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key208, 6), (key377, 6), (key456, 6)]

def rawRow8006 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key208, 6), (key456, 6), (key377, 6)]

def rawRow8007 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key377, 6), (key208, 6), (key456, 6)]

def rawRow8008 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key377, 6), (key456, 6), (key208, 6)]

def rawRow8009 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key456, 6), (key208, 6), (key377, 6)]

def rawRow8010 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key456, 6), (key377, 6), (key208, 6)]

def rawRow8011 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key208, 6), (key377, 6), (key428, 6)]

def rawRow8012 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key208, 6), (key428, 6), (key377, 6)]

def rawRow8013 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key377, 6), (key208, 6), (key428, 6)]

def rawRow8014 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key377, 6), (key428, 6), (key208, 6)]

def rawRow8015 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key428, 6), (key208, 6), (key377, 6)]

def rawRow8016 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key428, 6), (key377, 6), (key208, 6)]

def rawRow8017 : Integer.Sparse Key := [(key43, -6), (key48, -6), (key48, -6), (key74, -6), (key206, 2), (key212, 2), (key212, 2), (key426, 2), (key432, 2), (key426, 2), (key460, 2), (key432, 2), (key460, 2), (key659, 2), (key659, 2), (key663, 2)]

def rawRow8018 : Integer.Sparse Key := [(key48, -6), (key43, -6), (key48, -6), (key74, -6), (key212, 2), (key206, 2), (key212, 2), (key432, 2), (key426, 2), (key460, 2), (key426, 2), (key460, 2), (key432, 2), (key659, 2), (key663, 2), (key659, 2)]

def rawRow8019 : Integer.Sparse Key := [(key48, -6), (key48, -6), (key43, -6), (key74, -6), (key212, 2), (key212, 2), (key206, 2), (key460, 2), (key460, 2), (key432, 2), (key432, 2), (key426, 2), (key426, 2), (key663, 2), (key659, 2), (key659, 2)]

def rawRow8020 : Integer.Sparse Key := [(key43, -6), (key48, -6), (key74, -6), (key48, -6), (key426, 2), (key432, 2), (key659, 2), (key206, 2), (key212, 2), (key426, 2), (key460, 2), (key659, 2), (key663, 2), (key212, 2), (key432, 2), (key460, 2)]

def rawRow8021 : Integer.Sparse Key := [(key48, -6), (key43, -6), (key74, -6), (key48, -6), (key432, 2), (key426, 2), (key659, 2), (key212, 2), (key206, 2), (key460, 2), (key426, 2), (key663, 2), (key659, 2), (key212, 2), (key460, 2), (key432, 2)]

def rawRow8022 : Integer.Sparse Key := [(key43, -6), (key74, -6), (key48, -6), (key48, -6), (key426, 2), (key659, 2), (key432, 2), (key426, 2), (key659, 2), (key206, 2), (key663, 2), (key212, 2), (key460, 2), (key432, 2), (key212, 2), (key460, 2)]

def rawRow8023 : Integer.Sparse Key := [(key74, -6), (key43, -6), (key48, -6), (key48, -6), (key659, 2), (key426, 2), (key432, 2), (key659, 2), (key426, 2), (key663, 2), (key206, 2), (key460, 2), (key212, 2), (key432, 2), (key460, 2), (key212, 2)]

def rawRow8024 : Integer.Sparse Key := [(key48, -6), (key74, -6), (key43, -6), (key48, -6), (key432, 2), (key659, 2), (key426, 2), (key460, 2), (key663, 2), (key212, 2), (key659, 2), (key206, 2), (key426, 2), (key460, 2), (key212, 2), (key432, 2)]

def rawRow8025 : Integer.Sparse Key := [(key74, -6), (key48, -6), (key43, -6), (key48, -6), (key659, 2), (key432, 2), (key426, 2), (key663, 2), (key460, 2), (key659, 2), (key212, 2), (key426, 2), (key206, 2), (key460, 2), (key432, 2), (key212, 2)]

def rawRow8026 : Integer.Sparse Key := [(key48, -6), (key48, -6), (key74, -6), (key43, -6), (key460, 2), (key460, 2), (key663, 2), (key212, 2), (key212, 2), (key432, 2), (key432, 2), (key659, 2), (key659, 2), (key206, 2), (key426, 2), (key426, 2)]

def rawRow8027 : Integer.Sparse Key := [(key48, -6), (key74, -6), (key48, -6), (key43, -6), (key460, 2), (key663, 2), (key460, 2), (key432, 2), (key659, 2), (key212, 2), (key659, 2), (key212, 2), (key432, 2), (key426, 2), (key206, 2), (key426, 2)]

def rawRow8028 : Integer.Sparse Key := [(key74, -6), (key48, -6), (key48, -6), (key43, -6), (key663, 2), (key460, 2), (key460, 2), (key659, 2), (key432, 2), (key659, 2), (key212, 2), (key432, 2), (key212, 2), (key426, 2), (key426, 2), (key206, 2)]

def rawRow8029 : Integer.Sparse Key := [(key100, -6), (key105, -6), (key115, -6), (key137, -6), (key18, 2), (key23, 2), (key35, 2), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def rawRow8030 : Integer.Sparse Key := [(key105, -6), (key100, -6), (key115, -6), (key137, -6), (key23, 2), (key18, 2), (key35, 2), (key381, 2), (key375, 2), (key460, 2), (key426, 2), (key490, 2), (key486, 2), (key654, 2), (key663, 2), (key659, 2)]

def rawRow8031 : Integer.Sparse Key := [(key100, -6), (key115, -6), (key105, -6), (key137, -6), (key18, 2), (key35, 2), (key23, 2), (key426, 2), (key486, 2), (key375, 2), (key490, 2), (key381, 2), (key460, 2), (key659, 2), (key654, 2), (key663, 2)]

def rawRow8032 : Integer.Sparse Key := [(key115, -6), (key100, -6), (key105, -6), (key137, -6), (key35, 2), (key18, 2), (key23, 2), (key486, 2), (key426, 2), (key490, 2), (key375, 2), (key460, 2), (key381, 2), (key659, 2), (key663, 2), (key654, 2)]

def rawRow8033 : Integer.Sparse Key := [(key105, -6), (key115, -6), (key100, -6), (key137, -6), (key23, 2), (key35, 2), (key18, 2), (key460, 2), (key490, 2), (key381, 2), (key486, 2), (key375, 2), (key426, 2), (key663, 2), (key654, 2), (key659, 2)]

def rawRow8034 : Integer.Sparse Key := [(key115, -6), (key105, -6), (key100, -6), (key137, -6), (key35, 2), (key23, 2), (key18, 2), (key490, 2), (key460, 2), (key486, 2), (key381, 2), (key426, 2), (key375, 2), (key663, 2), (key659, 2), (key654, 2)]

def rawRow8035 : Integer.Sparse Key := [(key100, -6), (key105, -6), (key137, -6), (key115, -6), (key43, 2), (key48, 2), (key74, 2), (key206, 2), (key212, 2), (key426, 2), (key460, 2), (key659, 2), (key663, 2), (key218, 2), (key486, 2), (key490, 2)]

def rawRow8036 : Integer.Sparse Key := [(key105, -6), (key100, -6), (key137, -6), (key115, -6), (key48, 2), (key43, 2), (key74, 2), (key212, 2), (key206, 2), (key460, 2), (key426, 2), (key663, 2), (key659, 2), (key218, 2), (key490, 2), (key486, 2)]

def rawRow8037 : Integer.Sparse Key := [(key100, -6), (key137, -6), (key105, -6), (key115, -6), (key43, 2), (key74, 2), (key48, 2), (key426, 2), (key659, 2), (key206, 2), (key663, 2), (key212, 2), (key460, 2), (key486, 2), (key218, 2), (key490, 2)]

def rawRow8038 : Integer.Sparse Key := [(key137, -6), (key100, -6), (key105, -6), (key115, -6), (key74, 2), (key43, 2), (key48, 2), (key659, 2), (key426, 2), (key663, 2), (key206, 2), (key460, 2), (key212, 2), (key486, 2), (key490, 2), (key218, 2)]

def rawRow8039 : Integer.Sparse Key := [(key105, -6), (key137, -6), (key100, -6), (key115, -6), (key48, 2), (key74, 2), (key43, 2), (key460, 2), (key663, 2), (key212, 2), (key659, 2), (key206, 2), (key426, 2), (key490, 2), (key218, 2), (key486, 2)]

def rawRow8040 : Integer.Sparse Key := [(key137, -6), (key105, -6), (key100, -6), (key115, -6), (key74, 2), (key48, 2), (key43, 2), (key663, 2), (key460, 2), (key659, 2), (key212, 2), (key426, 2), (key206, 2), (key490, 2), (key486, 2), (key218, 2)]

def rawRow8041 : Integer.Sparse Key := [(key100, -6), (key115, -6), (key137, -6), (key105, -6), (key100, 2), (key115, 2), (key137, 2), (key18, 2), (key35, 2), (key375, 2), (key490, 2), (key654, 2), (key663, 2), (key212, 2), (key381, 2), (key460, 2)]

def rawRow8042 : Integer.Sparse Key := [(key115, -6), (key100, -6), (key137, -6), (key105, -6), (key115, 2), (key100, 2), (key137, 2), (key35, 2), (key18, 2), (key490, 2), (key375, 2), (key663, 2), (key654, 2), (key212, 2), (key460, 2), (key381, 2)]

def rawRow8043 : Integer.Sparse Key := [(key100, -6), (key137, -6), (key115, -6), (key105, -6), (key100, 2), (key137, 2), (key115, 2), (key43, 2), (key74, 2), (key206, 2), (key663, 2), (key218, 2), (key490, 2), (key381, 2), (key212, 2), (key460, 2)]

def rawRow8044 : Integer.Sparse Key := [(key137, -6), (key100, -6), (key115, -6), (key105, -6), (key137, 2), (key100, 2), (key115, 2), (key74, 2), (key43, 2), (key663, 2), (key206, 2), (key490, 2), (key218, 2), (key381, 2), (key460, 2), (key212, 2)]

def rawRow8045 : Integer.Sparse Key := [(key115, -6), (key137, -6), (key100, -6), (key105, -6), (key115, 2), (key137, 2), (key100, 2), (key196, 2), (key200, 2), (key35, 2), (key74, 2), (key18, 2), (key375, 2), (key460, 2), (key212, 2), (key381, 2)]

def rawRow8046 : Integer.Sparse Key := [(key137, -6), (key115, -6), (key100, -6), (key105, -6), (key137, 2), (key115, 2), (key100, 2), (key200, 2), (key196, 2), (key74, 2), (key35, 2), (key43, 2), (key206, 2), (key460, 2), (key381, 2), (key212, 2)]

def rawRow8047 : Integer.Sparse Key := [(key105, -6), (key115, -6), (key137, -6), (key100, -6), (key195, 2), (key196, 2), (key200, 2), (key23, 2), (key35, 2), (key48, 2), (key115, 2), (key74, 2), (key137, 2), (key18, 2), (key375, 2), (key426, 2)]

def rawRow8048 : Integer.Sparse Key := [(key115, -6), (key105, -6), (key137, -6), (key100, -6), (key196, 2), (key195, 2), (key200, 2), (key35, 2), (key23, 2), (key115, 2), (key48, 2), (key137, 2), (key74, 2), (key18, 2), (key426, 2), (key375, 2)]

def rawRow8049 : Integer.Sparse Key := [(key105, -6), (key137, -6), (key115, -6), (key100, -6), (key195, 2), (key200, 2), (key196, 2), (key48, 2), (key74, 2), (key23, 2), (key137, 2), (key35, 2), (key115, 2), (key43, 2), (key206, 2), (key426, 2)]

def rawRow8050 : Integer.Sparse Key := [(key137, -6), (key105, -6), (key115, -6), (key100, -6), (key200, 2), (key195, 2), (key196, 2), (key74, 2), (key48, 2), (key137, 2), (key23, 2), (key115, 2), (key35, 2), (key43, 2), (key426, 2), (key206, 2)]

def rawRow8051 : Integer.Sparse Key := [(key115, -6), (key137, -6), (key105, -6), (key100, -6), (key196, 2), (key200, 2), (key195, 2), (key115, 2), (key137, 2), (key35, 2), (key74, 2), (key23, 2), (key48, 2), (key100, 2), (key18, 2), (key375, 2)]

def rawRow8052 : Integer.Sparse Key := [(key137, -6), (key115, -6), (key105, -6), (key100, -6), (key200, 2), (key196, 2), (key195, 2), (key137, 2), (key115, 2), (key74, 2), (key35, 2), (key48, 2), (key23, 2), (key100, 2), (key43, 2), (key206, 2)]

def rawRow8053 : Integer.Sparse Key := [(key1293, -6), (key1570, -6), (key1570, -6), (key1590, -6), (key1313, 2), (key1313, 2), (key1323, 2), (key1421, 2), (key1421, 2), (key1441, 2), (key1619, 2), (key1621, 2), (key1619, 2), (key1630, 2), (key1621, 2), (key1630, 2)]

def rawRow8054 : Integer.Sparse Key := [(key1293, -6), (key1570, -6), (key1590, -6), (key1570, -6), (key1313, 2), (key1323, 2), (key1313, 2), (key1421, 2), (key1441, 2), (key1421, 2), (key1621, 2), (key1619, 2), (key1630, 2), (key1619, 2), (key1630, 2), (key1621, 2)]

def rawRow8055 : Integer.Sparse Key := [(key1293, -6), (key1590, -6), (key1570, -6), (key1570, -6), (key1323, 2), (key1313, 2), (key1313, 2), (key1441, 2), (key1421, 2), (key1421, 2), (key1630, 2), (key1630, 2), (key1621, 2), (key1621, 2), (key1619, 2), (key1619, 2)]

def rawRow8056 : Integer.Sparse Key := [(key1570, -6), (key1293, -6), (key1570, -6), (key1590, -6), (key1421, 2), (key1619, 2), (key1621, 2), (key1313, 2), (key1619, 2), (key1630, 2), (key1313, 2), (key1323, 2), (key1421, 2), (key1441, 2), (key1621, 2), (key1630, 2)]

def rawRow8057 : Integer.Sparse Key := [(key1570, -6), (key1293, -6), (key1590, -6), (key1570, -6), (key1421, 2), (key1621, 2), (key1619, 2), (key1313, 2), (key1630, 2), (key1619, 2), (key1323, 2), (key1313, 2), (key1441, 2), (key1421, 2), (key1630, 2), (key1621, 2)]

def rawRow8058 : Integer.Sparse Key := [(key1570, -6), (key1570, -6), (key1293, -6), (key1590, -6), (key1619, 2), (key1421, 2), (key1621, 2), (key1619, 2), (key1313, 2), (key1630, 2), (key1421, 2), (key1621, 2), (key1313, 2), (key1630, 2), (key1323, 2), (key1441, 2)]

def rawRow8059 : Integer.Sparse Key := [(key1570, -6), (key1570, -6), (key1590, -6), (key1293, -6), (key1619, 2), (key1621, 2), (key1421, 2), (key1619, 2), (key1630, 2), (key1313, 2), (key1621, 2), (key1421, 2), (key1630, 2), (key1313, 2), (key1441, 2), (key1323, 2)]

def rawRow8060 : Integer.Sparse Key := [(key1570, -6), (key1590, -6), (key1293, -6), (key1570, -6), (key1621, 2), (key1421, 2), (key1619, 2), (key1630, 2), (key1313, 2), (key1619, 2), (key1441, 2), (key1630, 2), (key1323, 2), (key1621, 2), (key1313, 2), (key1421, 2)]

def rawRow8061 : Integer.Sparse Key := [(key1570, -6), (key1590, -6), (key1570, -6), (key1293, -6), (key1621, 2), (key1619, 2), (key1421, 2), (key1630, 2), (key1619, 2), (key1313, 2), (key1630, 2), (key1441, 2), (key1621, 2), (key1323, 2), (key1421, 2), (key1313, 2)]

def rawRow8062 : Integer.Sparse Key := [(key1590, -6), (key1293, -6), (key1570, -6), (key1570, -6), (key1441, 2), (key1630, 2), (key1630, 2), (key1323, 2), (key1621, 2), (key1621, 2), (key1313, 2), (key1313, 2), (key1421, 2), (key1421, 2), (key1619, 2), (key1619, 2)]

def rawRow8063 : Integer.Sparse Key := [(key1590, -6), (key1570, -6), (key1293, -6), (key1570, -6), (key1630, 2), (key1441, 2), (key1630, 2), (key1621, 2), (key1323, 2), (key1621, 2), (key1421, 2), (key1619, 2), (key1313, 2), (key1619, 2), (key1313, 2), (key1421, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8064 : Integer.Sparse Key := [(key1590, -6), (key1570, -6), (key1570, -6), (key1293, -6), (key1630, 2), (key1630, 2), (key1441, 2), (key1621, 2), (key1621, 2), (key1323, 2), (key1619, 2), (key1421, 2), (key1619, 2), (key1313, 2), (key1421, 2), (key1313, 2)]

def rawRow8065 : Integer.Sparse Key := [(key1313, -6), (key1543, -6), (key1619, -6), (key1630, -6), (key1293, 2), (key1313, 2), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, 2), (key1553, 2), (key1570, 2), (key1590, 2), (key1621, 2), (key1630, 2)]

def rawRow8066 : Integer.Sparse Key := [(key1313, -6), (key1543, -6), (key1630, -6), (key1619, -6), (key1293, 2), (key1323, 2), (key1313, 2), (key1388, 2), (key1441, 2), (key1421, 2), (key1553, 2), (key1543, 2), (key1590, 2), (key1570, 2), (key1630, 2), (key1621, 2)]

def rawRow8067 : Integer.Sparse Key := [(key1313, -6), (key1619, -6), (key1543, -6), (key1630, -6), (key1313, 2), (key1293, 2), (key1323, 2), (key1421, 2), (key1388, 2), (key1441, 2), (key1570, 2), (key1621, 2), (key1543, 2), (key1630, 2), (key1553, 2), (key1590, 2)]

def rawRow8068 : Integer.Sparse Key := [(key1313, -6), (key1619, -6), (key1630, -6), (key1543, -6), (key1313, 2), (key1323, 2), (key1293, 2), (key1421, 2), (key1441, 2), (key1388, 2), (key1621, 2), (key1570, 2), (key1630, 2), (key1543, 2), (key1590, 2), (key1553, 2)]

def rawRow8069 : Integer.Sparse Key := [(key1313, -6), (key1630, -6), (key1543, -6), (key1619, -6), (key1323, 2), (key1293, 2), (key1313, 2), (key1441, 2), (key1388, 2), (key1421, 2), (key1590, 2), (key1630, 2), (key1553, 2), (key1621, 2), (key1543, 2), (key1570, 2)]

def rawRow8070 : Integer.Sparse Key := [(key1313, -6), (key1630, -6), (key1619, -6), (key1543, -6), (key1323, 2), (key1313, 2), (key1293, 2), (key1441, 2), (key1421, 2), (key1388, 2), (key1630, 2), (key1590, 2), (key1621, 2), (key1553, 2), (key1570, 2), (key1543, 2)]

def rawRow8071 : Integer.Sparse Key := [(key1543, -6), (key1313, -6), (key1619, -6), (key1630, -6), (key1388, 2), (key1543, 2), (key1553, 2), (key1293, 2), (key1570, 2), (key1590, 2), (key1313, 2), (key1323, 2), (key1421, 2), (key1441, 2), (key1621, 2), (key1630, 2)]

def rawRow8072 : Integer.Sparse Key := [(key1543, -6), (key1313, -6), (key1630, -6), (key1619, -6), (key1388, 2), (key1553, 2), (key1543, 2), (key1293, 2), (key1590, 2), (key1570, 2), (key1323, 2), (key1313, 2), (key1441, 2), (key1421, 2), (key1630, 2), (key1621, 2)]

def rawRow8073 : Integer.Sparse Key := [(key1543, -6), (key1619, -6), (key1313, -6), (key1630, -6), (key1543, 2), (key1388, 2), (key1553, 2), (key1570, 2), (key1293, 2), (key1590, 2), (key1421, 2), (key1621, 2), (key1313, 2), (key1630, 2), (key1323, 2), (key1441, 2)]

def rawRow8074 : Integer.Sparse Key := [(key1543, -6), (key1619, -6), (key1630, -6), (key1313, -6), (key1543, 2), (key1553, 2), (key1388, 2), (key1570, 2), (key1590, 2), (key1293, 2), (key1621, 2), (key1421, 2), (key1630, 2), (key1313, 2), (key1441, 2), (key1323, 2)]

def rawRow8075 : Integer.Sparse Key := [(key1543, -6), (key1630, -6), (key1313, -6), (key1619, -6), (key1553, 2), (key1388, 2), (key1543, 2), (key1590, 2), (key1293, 2), (key1570, 2), (key1441, 2), (key1630, 2), (key1323, 2), (key1621, 2), (key1313, 2), (key1421, 2)]

def rawRow8076 : Integer.Sparse Key := [(key1543, -6), (key1630, -6), (key1619, -6), (key1313, -6), (key1553, 2), (key1543, 2), (key1388, 2), (key1590, 2), (key1570, 2), (key1293, 2), (key1630, 2), (key1441, 2), (key1621, 2), (key1323, 2), (key1421, 2), (key1313, 2)]

def rawRow8077 : Integer.Sparse Key := [(key1619, -6), (key1313, -6), (key1543, -6), (key1630, -6), (key1421, 2), (key1570, 2), (key1621, 2), (key1313, 2), (key1543, 2), (key1630, 2), (key1293, 2), (key1323, 2), (key1388, 2), (key1441, 2), (key1553, 2), (key1590, 2)]

def rawRow8078 : Integer.Sparse Key := [(key1619, -6), (key1313, -6), (key1630, -6), (key1543, -6), (key1421, 2), (key1621, 2), (key1570, 2), (key1313, 2), (key1630, 2), (key1543, 2), (key1323, 2), (key1293, 2), (key1441, 2), (key1388, 2), (key1590, 2), (key1553, 2)]

def rawRow8079 : Integer.Sparse Key := [(key1619, -6), (key1543, -6), (key1313, -6), (key1630, -6), (key1570, 2), (key1421, 2), (key1621, 2), (key1543, 2), (key1313, 2), (key1630, 2), (key1388, 2), (key1553, 2), (key1293, 2), (key1590, 2), (key1323, 2), (key1441, 2)]

def rawRow8080 : Integer.Sparse Key := [(key1619, -6), (key1543, -6), (key1630, -6), (key1313, -6), (key1570, 2), (key1621, 2), (key1421, 2), (key1543, 2), (key1630, 2), (key1313, 2), (key1553, 2), (key1388, 2), (key1590, 2), (key1293, 2), (key1441, 2), (key1323, 2)]

def rawRow8081 : Integer.Sparse Key := [(key1619, -6), (key1630, -6), (key1313, -6), (key1543, -6), (key1621, 2), (key1421, 2), (key1570, 2), (key1630, 2), (key1313, 2), (key1543, 2), (key1441, 2), (key1590, 2), (key1323, 2), (key1553, 2), (key1293, 2), (key1388, 2)]

def rawRow8082 : Integer.Sparse Key := [(key1619, -6), (key1630, -6), (key1543, -6), (key1313, -6), (key1621, 2), (key1570, 2), (key1421, 2), (key1630, 2), (key1543, 2), (key1313, 2), (key1590, 2), (key1441, 2), (key1553, 2), (key1323, 2), (key1388, 2), (key1293, 2)]

def rawRow8083 : Integer.Sparse Key := [(key1630, -6), (key1313, -6), (key1543, -6), (key1619, -6), (key1441, 2), (key1590, 2), (key1630, 2), (key1323, 2), (key1553, 2), (key1621, 2), (key1293, 2), (key1313, 2), (key1388, 2), (key1421, 2), (key1543, 2), (key1570, 2)]

def rawRow8084 : Integer.Sparse Key := [(key1630, -6), (key1313, -6), (key1619, -6), (key1543, -6), (key1441, 2), (key1630, 2), (key1590, 2), (key1323, 2), (key1621, 2), (key1553, 2), (key1313, 2), (key1293, 2), (key1421, 2), (key1388, 2), (key1570, 2), (key1543, 2)]

def rawRow8085 : Integer.Sparse Key := [(key1630, -6), (key1543, -6), (key1313, -6), (key1619, -6), (key1590, 2), (key1441, 2), (key1630, 2), (key1553, 2), (key1323, 2), (key1621, 2), (key1388, 2), (key1543, 2), (key1293, 2), (key1570, 2), (key1313, 2), (key1421, 2)]

def rawRow8086 : Integer.Sparse Key := [(key1630, -6), (key1543, -6), (key1619, -6), (key1313, -6), (key1590, 2), (key1630, 2), (key1441, 2), (key1553, 2), (key1621, 2), (key1323, 2), (key1543, 2), (key1388, 2), (key1570, 2), (key1293, 2), (key1421, 2), (key1313, 2)]

def rawRow8087 : Integer.Sparse Key := [(key1630, -6), (key1619, -6), (key1313, -6), (key1543, -6), (key1630, 2), (key1441, 2), (key1590, 2), (key1621, 2), (key1323, 2), (key1553, 2), (key1421, 2), (key1570, 2), (key1313, 2), (key1543, 2), (key1293, 2), (key1388, 2)]

def rawRow8088 : Integer.Sparse Key := [(key1630, -6), (key1619, -6), (key1543, -6), (key1313, -6), (key1630, 2), (key1590, 2), (key1441, 2), (key1621, 2), (key1553, 2), (key1323, 2), (key1570, 2), (key1421, 2), (key1543, 2), (key1313, 2), (key1388, 2), (key1293, 2)]

def rawRow8089 : Integer.Sparse Key := [(key1526, -6), (key1534, -6), (key1534, -6), (key1894, -6), (key1251, 2), (key1259, 2), (key1259, 2), (key1604, 2), (key1612, 2), (key1604, 2), (key1640, 2), (key1612, 2), (key1640, 2), (key1916, 2), (key1916, 2), (key1930, 2)]

def rawRow8090 : Integer.Sparse Key := [(key1534, -6), (key1526, -6), (key1534, -6), (key1894, -6), (key1259, 2), (key1251, 2), (key1259, 2), (key1612, 2), (key1604, 2), (key1640, 2), (key1604, 2), (key1640, 2), (key1612, 2), (key1916, 2), (key1930, 2), (key1916, 2)]

def rawRow8091 : Integer.Sparse Key := [(key1534, -6), (key1534, -6), (key1526, -6), (key1894, -6), (key1259, 2), (key1259, 2), (key1251, 2), (key1640, 2), (key1640, 2), (key1612, 2), (key1612, 2), (key1604, 2), (key1604, 2), (key1930, 2), (key1916, 2), (key1916, 2)]

def rawRow8092 : Integer.Sparse Key := [(key1526, -6), (key1534, -6), (key1894, -6), (key1534, -6), (key1604, 2), (key1612, 2), (key1916, 2), (key1251, 2), (key1259, 2), (key1604, 2), (key1640, 2), (key1916, 2), (key1930, 2), (key1259, 2), (key1612, 2), (key1640, 2)]

def rawRow8093 : Integer.Sparse Key := [(key1534, -6), (key1526, -6), (key1894, -6), (key1534, -6), (key1612, 2), (key1604, 2), (key1916, 2), (key1259, 2), (key1251, 2), (key1640, 2), (key1604, 2), (key1930, 2), (key1916, 2), (key1259, 2), (key1640, 2), (key1612, 2)]

def rawRow8094 : Integer.Sparse Key := [(key1526, -6), (key1894, -6), (key1534, -6), (key1534, -6), (key1604, 2), (key1916, 2), (key1612, 2), (key1604, 2), (key1916, 2), (key1251, 2), (key1930, 2), (key1259, 2), (key1640, 2), (key1612, 2), (key1259, 2), (key1640, 2)]

def rawRow8095 : Integer.Sparse Key := [(key1894, -6), (key1526, -6), (key1534, -6), (key1534, -6), (key1916, 2), (key1604, 2), (key1612, 2), (key1916, 2), (key1604, 2), (key1930, 2), (key1251, 2), (key1640, 2), (key1259, 2), (key1612, 2), (key1640, 2), (key1259, 2)]

def rawRow8096 : Integer.Sparse Key := [(key1534, -6), (key1894, -6), (key1526, -6), (key1534, -6), (key1612, 2), (key1916, 2), (key1604, 2), (key1640, 2), (key1930, 2), (key1259, 2), (key1916, 2), (key1251, 2), (key1604, 2), (key1640, 2), (key1259, 2), (key1612, 2)]

def rawRow8097 : Integer.Sparse Key := [(key1894, -6), (key1534, -6), (key1526, -6), (key1534, -6), (key1916, 2), (key1612, 2), (key1604, 2), (key1930, 2), (key1640, 2), (key1916, 2), (key1259, 2), (key1604, 2), (key1251, 2), (key1640, 2), (key1612, 2), (key1259, 2)]

def rawRow8098 : Integer.Sparse Key := [(key1534, -6), (key1534, -6), (key1894, -6), (key1526, -6), (key1640, 2), (key1640, 2), (key1930, 2), (key1259, 2), (key1259, 2), (key1612, 2), (key1612, 2), (key1916, 2), (key1916, 2), (key1251, 2), (key1604, 2), (key1604, 2)]

def rawRow8099 : Integer.Sparse Key := [(key1534, -6), (key1894, -6), (key1534, -6), (key1526, -6), (key1640, 2), (key1930, 2), (key1640, 2), (key1612, 2), (key1916, 2), (key1259, 2), (key1916, 2), (key1259, 2), (key1612, 2), (key1604, 2), (key1251, 2), (key1604, 2)]

def rawRow8100 : Integer.Sparse Key := [(key1894, -6), (key1534, -6), (key1534, -6), (key1526, -6), (key1930, 2), (key1640, 2), (key1640, 2), (key1916, 2), (key1612, 2), (key1916, 2), (key1259, 2), (key1612, 2), (key1259, 2), (key1604, 2), (key1604, 2), (key1251, 2)]

def rawRow8101 : Integer.Sparse Key := [(key1604, -6), (key1612, -6), (key1679, -6), (key1916, -6), (key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, 2), (key1640, 2), (key1679, 2), (key1693, 2), (key1894, 2), (key1916, 2), (key1930, 2)]

def rawRow8102 : Integer.Sparse Key := [(key1612, -6), (key1604, -6), (key1679, -6), (key1916, -6), (key1259, 2), (key1251, 2), (key1271, 2), (key1534, 2), (key1526, 2), (key1640, 2), (key1604, 2), (key1693, 2), (key1679, 2), (key1894, 2), (key1930, 2), (key1916, 2)]

def rawRow8103 : Integer.Sparse Key := [(key1604, -6), (key1679, -6), (key1612, -6), (key1916, -6), (key1251, 2), (key1271, 2), (key1259, 2), (key1604, 2), (key1679, 2), (key1526, 2), (key1693, 2), (key1534, 2), (key1640, 2), (key1916, 2), (key1894, 2), (key1930, 2)]

def rawRow8104 : Integer.Sparse Key := [(key1679, -6), (key1604, -6), (key1612, -6), (key1916, -6), (key1271, 2), (key1251, 2), (key1259, 2), (key1679, 2), (key1604, 2), (key1693, 2), (key1526, 2), (key1640, 2), (key1534, 2), (key1916, 2), (key1930, 2), (key1894, 2)]

def rawRow8105 : Integer.Sparse Key := [(key1612, -6), (key1679, -6), (key1604, -6), (key1916, -6), (key1259, 2), (key1271, 2), (key1251, 2), (key1640, 2), (key1693, 2), (key1534, 2), (key1679, 2), (key1526, 2), (key1604, 2), (key1930, 2), (key1894, 2), (key1916, 2)]

def rawRow8106 : Integer.Sparse Key := [(key1679, -6), (key1612, -6), (key1604, -6), (key1916, -6), (key1271, 2), (key1259, 2), (key1251, 2), (key1693, 2), (key1640, 2), (key1679, 2), (key1534, 2), (key1604, 2), (key1526, 2), (key1930, 2), (key1916, 2), (key1894, 2)]

def rawRow8107 : Integer.Sparse Key := [(key1604, -6), (key1612, -6), (key1916, -6), (key1679, -6), (key1526, 2), (key1534, 2), (key1894, 2), (key1251, 2), (key1259, 2), (key1604, 2), (key1640, 2), (key1916, 2), (key1930, 2), (key1271, 2), (key1679, 2), (key1693, 2)]

def rawRow8108 : Integer.Sparse Key := [(key1612, -6), (key1604, -6), (key1916, -6), (key1679, -6), (key1534, 2), (key1526, 2), (key1894, 2), (key1259, 2), (key1251, 2), (key1640, 2), (key1604, 2), (key1930, 2), (key1916, 2), (key1271, 2), (key1693, 2), (key1679, 2)]

def rawRow8109 : Integer.Sparse Key := [(key1604, -6), (key1916, -6), (key1612, -6), (key1679, -6), (key1526, 2), (key1894, 2), (key1534, 2), (key1604, 2), (key1916, 2), (key1251, 2), (key1930, 2), (key1259, 2), (key1640, 2), (key1679, 2), (key1271, 2), (key1693, 2)]

def rawRow8110 : Integer.Sparse Key := [(key1916, -6), (key1604, -6), (key1612, -6), (key1679, -6), (key1894, 2), (key1526, 2), (key1534, 2), (key1916, 2), (key1604, 2), (key1930, 2), (key1251, 2), (key1640, 2), (key1259, 2), (key1679, 2), (key1693, 2), (key1271, 2)]

def rawRow8111 : Integer.Sparse Key := [(key1612, -6), (key1916, -6), (key1604, -6), (key1679, -6), (key1534, 2), (key1894, 2), (key1526, 2), (key1640, 2), (key1930, 2), (key1259, 2), (key1916, 2), (key1251, 2), (key1604, 2), (key1693, 2), (key1271, 2), (key1679, 2)]

def rawRow8112 : Integer.Sparse Key := [(key1916, -6), (key1612, -6), (key1604, -6), (key1679, -6), (key1894, 2), (key1534, 2), (key1526, 2), (key1930, 2), (key1640, 2), (key1916, 2), (key1259, 2), (key1604, 2), (key1251, 2), (key1693, 2), (key1679, 2), (key1271, 2)]

def rawRow8113 : Integer.Sparse Key := [(key1604, -6), (key1679, -6), (key1916, -6), (key1612, -6), (key1604, 2), (key1679, 2), (key1916, 2), (key1251, 2), (key1271, 2), (key1526, 2), (key1693, 2), (key1894, 2), (key1930, 2), (key1259, 2), (key1534, 2), (key1640, 2)]

def rawRow8114 : Integer.Sparse Key := [(key1679, -6), (key1604, -6), (key1916, -6), (key1612, -6), (key1679, 2), (key1604, 2), (key1916, 2), (key1271, 2), (key1251, 2), (key1693, 2), (key1526, 2), (key1930, 2), (key1894, 2), (key1259, 2), (key1640, 2), (key1534, 2)]

def rawRow8115 : Integer.Sparse Key := [(key1604, -6), (key1916, -6), (key1679, -6), (key1612, -6), (key1604, 2), (key1916, 2), (key1679, 2), (key1526, 2), (key1894, 2), (key1251, 2), (key1930, 2), (key1271, 2), (key1693, 2), (key1534, 2), (key1259, 2), (key1640, 2)]

def rawRow8116 : Integer.Sparse Key := [(key1916, -6), (key1604, -6), (key1679, -6), (key1612, -6), (key1916, 2), (key1604, 2), (key1679, 2), (key1894, 2), (key1526, 2), (key1930, 2), (key1251, 2), (key1693, 2), (key1271, 2), (key1534, 2), (key1640, 2), (key1259, 2)]

def rawRow8117 : Integer.Sparse Key := [(key1679, -6), (key1916, -6), (key1604, -6), (key1612, -6), (key1679, 2), (key1916, 2), (key1604, 2), (key1693, 2), (key1930, 2), (key1271, 2), (key1894, 2), (key1251, 2), (key1526, 2), (key1640, 2), (key1259, 2), (key1534, 2)]

def rawRow8118 : Integer.Sparse Key := [(key1916, -6), (key1679, -6), (key1604, -6), (key1612, -6), (key1916, 2), (key1679, 2), (key1604, 2), (key1930, 2), (key1693, 2), (key1894, 2), (key1271, 2), (key1526, 2), (key1251, 2), (key1640, 2), (key1534, 2), (key1259, 2)]

def rawRow8119 : Integer.Sparse Key := [(key1612, -6), (key1679, -6), (key1916, -6), (key1604, -6), (key1640, 2), (key1693, 2), (key1930, 2), (key1259, 2), (key1271, 2), (key1534, 2), (key1679, 2), (key1894, 2), (key1916, 2), (key1251, 2), (key1526, 2), (key1604, 2)]

def rawRow8120 : Integer.Sparse Key := [(key1679, -6), (key1612, -6), (key1916, -6), (key1604, -6), (key1693, 2), (key1640, 2), (key1930, 2), (key1271, 2), (key1259, 2), (key1679, 2), (key1534, 2), (key1916, 2), (key1894, 2), (key1251, 2), (key1604, 2), (key1526, 2)]

def rawRow8121 : Integer.Sparse Key := [(key1612, -6), (key1916, -6), (key1679, -6), (key1604, -6), (key1640, 2), (key1930, 2), (key1693, 2), (key1534, 2), (key1894, 2), (key1259, 2), (key1916, 2), (key1271, 2), (key1679, 2), (key1526, 2), (key1251, 2), (key1604, 2)]

def rawRow8122 : Integer.Sparse Key := [(key1916, -6), (key1612, -6), (key1679, -6), (key1604, -6), (key1930, 2), (key1640, 2), (key1693, 2), (key1894, 2), (key1534, 2), (key1916, 2), (key1259, 2), (key1679, 2), (key1271, 2), (key1526, 2), (key1604, 2), (key1251, 2)]

def rawRow8123 : Integer.Sparse Key := [(key1679, -6), (key1916, -6), (key1612, -6), (key1604, -6), (key1693, 2), (key1930, 2), (key1640, 2), (key1679, 2), (key1916, 2), (key1271, 2), (key1894, 2), (key1259, 2), (key1534, 2), (key1604, 2), (key1251, 2), (key1526, 2)]

def rawRow8124 : Integer.Sparse Key := [(key1916, -6), (key1679, -6), (key1612, -6), (key1604, -6), (key1930, 2), (key1693, 2), (key1640, 2), (key1916, 2), (key1679, 2), (key1894, 2), (key1271, 2), (key1534, 2), (key1259, 2), (key1604, 2), (key1526, 2), (key1251, 2)]

def rawRow8125 : Integer.Sparse Key := [(key1291, -2), (key1299, -2), (key1299, -2), (key1568, -2), (key1576, -2), (key1568, -2), (key1594, -2), (key1576, -2), (key1594, -2), (key1904, -2), (key1904, -2), (key1912, -2), (key1311, 1), (key1319, 1), (key1311, 1), (key1327, 1), (key1319, 1), (key1327, 1), (key1419, 1), (key1427, 1), (key1419, 1), (key1445, 1), (key1427, 1), (key1445, 1), (key1617, 1), (key1625, 1), (key1617, 1), (key1634, 1), (key1625, 1), (key1634, 1), (key1919, 1), (key1921, 1), (key1919, 1), (key1927, 1), (key1921, 1), (key1927, 1)]

def rawRow8126 : Integer.Sparse Key := [(key1299, -2), (key1291, -2), (key1299, -2), (key1576, -2), (key1568, -2), (key1594, -2), (key1568, -2), (key1594, -2), (key1576, -2), (key1904, -2), (key1912, -2), (key1904, -2), (key1319, 1), (key1311, 1), (key1327, 1), (key1311, 1), (key1327, 1), (key1319, 1), (key1427, 1), (key1419, 1), (key1445, 1), (key1419, 1), (key1445, 1), (key1427, 1), (key1625, 1), (key1617, 1), (key1634, 1), (key1617, 1), (key1634, 1), (key1625, 1), (key1921, 1), (key1919, 1), (key1927, 1), (key1919, 1), (key1927, 1), (key1921, 1)]

def rawRow8127 : Integer.Sparse Key := [(key1299, -2), (key1299, -2), (key1291, -2), (key1594, -2), (key1594, -2), (key1576, -2), (key1576, -2), (key1568, -2), (key1568, -2), (key1912, -2), (key1904, -2), (key1904, -2), (key1327, 1), (key1327, 1), (key1319, 1), (key1319, 1), (key1311, 1), (key1311, 1), (key1445, 1), (key1445, 1), (key1427, 1), (key1427, 1), (key1419, 1), (key1419, 1), (key1634, 1), (key1634, 1), (key1625, 1), (key1625, 1), (key1617, 1), (key1617, 1), (key1927, 1), (key1927, 1), (key1921, 1), (key1921, 1), (key1919, 1), (key1919, 1)]

def rawRow8128 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1904, -2), (key1291, -2), (key1299, -2), (key1568, -2), (key1594, -2), (key1904, -2), (key1912, -2), (key1299, -2), (key1576, -2), (key1594, -2), (key1419, 1), (key1427, 1), (key1617, 1), (key1625, 1), (key1919, 1), (key1921, 1), (key1311, 1), (key1319, 1), (key1617, 1), (key1634, 1), (key1919, 1), (key1927, 1), (key1311, 1), (key1327, 1), (key1419, 1), (key1445, 1), (key1921, 1), (key1927, 1), (key1319, 1), (key1327, 1), (key1427, 1), (key1445, 1), (key1625, 1), (key1634, 1)]

def rawRow8129 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1904, -2), (key1299, -2), (key1291, -2), (key1594, -2), (key1568, -2), (key1912, -2), (key1904, -2), (key1299, -2), (key1594, -2), (key1576, -2), (key1427, 1), (key1419, 1), (key1625, 1), (key1617, 1), (key1921, 1), (key1919, 1), (key1319, 1), (key1311, 1), (key1634, 1), (key1617, 1), (key1927, 1), (key1919, 1), (key1327, 1), (key1311, 1), (key1445, 1), (key1419, 1), (key1927, 1), (key1921, 1), (key1327, 1), (key1319, 1), (key1445, 1), (key1427, 1), (key1634, 1), (key1625, 1)]

def rawRow8130 : Integer.Sparse Key := [(key1568, -2), (key1904, -2), (key1576, -2), (key1568, -2), (key1904, -2), (key1291, -2), (key1912, -2), (key1299, -2), (key1594, -2), (key1576, -2), (key1299, -2), (key1594, -2), (key1617, 1), (key1919, 1), (key1419, 1), (key1921, 1), (key1427, 1), (key1625, 1), (key1617, 1), (key1919, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1634, 1), (key1419, 1), (key1921, 1), (key1311, 1), (key1927, 1), (key1327, 1), (key1445, 1), (key1427, 1), (key1625, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1445, 1)]

def rawRow8131 : Integer.Sparse Key := [(key1904, -2), (key1568, -2), (key1576, -2), (key1904, -2), (key1568, -2), (key1912, -2), (key1291, -2), (key1594, -2), (key1299, -2), (key1576, -2), (key1594, -2), (key1299, -2), (key1919, 1), (key1617, 1), (key1921, 1), (key1419, 1), (key1625, 1), (key1427, 1), (key1919, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1634, 1), (key1319, 1), (key1921, 1), (key1419, 1), (key1927, 1), (key1311, 1), (key1445, 1), (key1327, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1445, 1), (key1327, 1)]

def rawRow8132 : Integer.Sparse Key := [(key1576, -2), (key1904, -2), (key1568, -2), (key1594, -2), (key1912, -2), (key1299, -2), (key1904, -2), (key1291, -2), (key1568, -2), (key1594, -2), (key1299, -2), (key1576, -2), (key1625, 1), (key1921, 1), (key1427, 1), (key1919, 1), (key1419, 1), (key1617, 1), (key1634, 1), (key1927, 1), (key1319, 1), (key1919, 1), (key1311, 1), (key1617, 1), (key1445, 1), (key1927, 1), (key1327, 1), (key1921, 1), (key1311, 1), (key1419, 1), (key1445, 1), (key1634, 1), (key1327, 1), (key1625, 1), (key1319, 1), (key1427, 1)]

def rawRow8133 : Integer.Sparse Key := [(key1904, -2), (key1576, -2), (key1568, -2), (key1912, -2), (key1594, -2), (key1904, -2), (key1299, -2), (key1568, -2), (key1291, -2), (key1594, -2), (key1576, -2), (key1299, -2), (key1921, 1), (key1625, 1), (key1919, 1), (key1427, 1), (key1617, 1), (key1419, 1), (key1927, 1), (key1634, 1), (key1919, 1), (key1319, 1), (key1617, 1), (key1311, 1), (key1927, 1), (key1445, 1), (key1921, 1), (key1327, 1), (key1419, 1), (key1311, 1), (key1634, 1), (key1445, 1), (key1625, 1), (key1327, 1), (key1427, 1), (key1319, 1)]

def rawRow8134 : Integer.Sparse Key := [(key1594, -2), (key1594, -2), (key1912, -2), (key1299, -2), (key1299, -2), (key1576, -2), (key1576, -2), (key1904, -2), (key1904, -2), (key1291, -2), (key1568, -2), (key1568, -2), (key1445, 1), (key1445, 1), (key1634, 1), (key1634, 1), (key1927, 1), (key1927, 1), (key1327, 1), (key1327, 1), (key1625, 1), (key1625, 1), (key1921, 1), (key1921, 1), (key1319, 1), (key1319, 1), (key1427, 1), (key1427, 1), (key1919, 1), (key1919, 1), (key1311, 1), (key1311, 1), (key1419, 1), (key1419, 1), (key1617, 1), (key1617, 1)]

def rawRow8135 : Integer.Sparse Key := [(key1594, -2), (key1912, -2), (key1594, -2), (key1576, -2), (key1904, -2), (key1299, -2), (key1904, -2), (key1299, -2), (key1576, -2), (key1568, -2), (key1291, -2), (key1568, -2), (key1634, 1), (key1927, 1), (key1445, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1625, 1), (key1921, 1), (key1327, 1), (key1921, 1), (key1327, 1), (key1625, 1), (key1427, 1), (key1919, 1), (key1319, 1), (key1919, 1), (key1319, 1), (key1427, 1), (key1419, 1), (key1617, 1), (key1311, 1), (key1617, 1), (key1311, 1), (key1419, 1)]

def rawRow8136 : Integer.Sparse Key := [(key1912, -2), (key1594, -2), (key1594, -2), (key1904, -2), (key1576, -2), (key1904, -2), (key1299, -2), (key1576, -2), (key1299, -2), (key1568, -2), (key1568, -2), (key1291, -2), (key1927, 1), (key1634, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1445, 1), (key1921, 1), (key1625, 1), (key1921, 1), (key1327, 1), (key1625, 1), (key1327, 1), (key1919, 1), (key1427, 1), (key1919, 1), (key1319, 1), (key1427, 1), (key1319, 1), (key1617, 1), (key1419, 1), (key1617, 1), (key1311, 1), (key1419, 1), (key1311, 1)]

def rawRow8137 : Integer.Sparse Key := [(key1311, -2), (key1319, -2), (key1352, -2), (key1541, -2), (key1549, -2), (key1617, -2), (key1634, -2), (key1682, -2), (key1690, -2), (key1897, -2), (key1919, -2), (key1927, -2), (key1291, 1), (key1299, 1), (key1311, 1), (key1327, 1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1921, 1), (key1927, 1)]

def rawRow8138 : Integer.Sparse Key := [(key1319, -2), (key1311, -2), (key1352, -2), (key1549, -2), (key1541, -2), (key1634, -2), (key1617, -2), (key1690, -2), (key1682, -2), (key1897, -2), (key1927, -2), (key1919, -2), (key1299, 1), (key1291, 1), (key1327, 1), (key1311, 1), (key1355, 1), (key1352, 1), (key1394, 1), (key1386, 1), (key1445, 1), (key1419, 1), (key1481, 1), (key1473, 1), (key1557, 1), (key1541, 1), (key1594, 1), (key1568, 1), (key1690, 1), (key1684, 1), (key1900, 1), (key1897, 1), (key1912, 1), (key1904, 1), (key1927, 1), (key1921, 1)]

def rawRow8139 : Integer.Sparse Key := [(key1311, -2), (key1352, -2), (key1319, -2), (key1617, -2), (key1682, -2), (key1541, -2), (key1690, -2), (key1549, -2), (key1634, -2), (key1919, -2), (key1897, -2), (key1927, -2), (key1311, 1), (key1352, 1), (key1291, 1), (key1355, 1), (key1299, 1), (key1327, 1), (key1419, 1), (key1473, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1445, 1), (key1568, 1), (key1684, 1), (key1541, 1), (key1690, 1), (key1557, 1), (key1594, 1), (key1904, 1), (key1921, 1), (key1897, 1), (key1927, 1), (key1900, 1), (key1912, 1)]

def rawRow8140 : Integer.Sparse Key := [(key1352, -2), (key1311, -2), (key1319, -2), (key1682, -2), (key1617, -2), (key1690, -2), (key1541, -2), (key1634, -2), (key1549, -2), (key1919, -2), (key1927, -2), (key1897, -2), (key1352, 1), (key1311, 1), (key1355, 1), (key1291, 1), (key1327, 1), (key1299, 1), (key1473, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1445, 1), (key1394, 1), (key1684, 1), (key1568, 1), (key1690, 1), (key1541, 1), (key1594, 1), (key1557, 1), (key1921, 1), (key1904, 1), (key1927, 1), (key1897, 1), (key1912, 1), (key1900, 1)]

def rawRow8141 : Integer.Sparse Key := [(key1319, -2), (key1352, -2), (key1311, -2), (key1634, -2), (key1690, -2), (key1549, -2), (key1682, -2), (key1541, -2), (key1617, -2), (key1927, -2), (key1897, -2), (key1919, -2), (key1327, 1), (key1355, 1), (key1299, 1), (key1352, 1), (key1291, 1), (key1311, 1), (key1445, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1386, 1), (key1419, 1), (key1594, 1), (key1690, 1), (key1557, 1), (key1684, 1), (key1541, 1), (key1568, 1), (key1912, 1), (key1927, 1), (key1900, 1), (key1921, 1), (key1897, 1), (key1904, 1)]

def rawRow8142 : Integer.Sparse Key := [(key1352, -2), (key1319, -2), (key1311, -2), (key1690, -2), (key1634, -2), (key1682, -2), (key1549, -2), (key1617, -2), (key1541, -2), (key1927, -2), (key1919, -2), (key1897, -2), (key1355, 1), (key1327, 1), (key1352, 1), (key1299, 1), (key1311, 1), (key1291, 1), (key1481, 1), (key1445, 1), (key1473, 1), (key1394, 1), (key1419, 1), (key1386, 1), (key1690, 1), (key1594, 1), (key1684, 1), (key1557, 1), (key1568, 1), (key1541, 1), (key1927, 1), (key1912, 1), (key1921, 1), (key1900, 1), (key1904, 1), (key1897, 1)]

def rawRow8143 : Integer.Sparse Key := [(key1541, -2), (key1549, -2), (key1897, -2), (key1311, -2), (key1319, -2), (key1617, -2), (key1634, -2), (key1919, -2), (key1927, -2), (key1352, -2), (key1682, -2), (key1690, -2), (key1386, 1), (key1394, 1), (key1541, 1), (key1557, 1), (key1897, 1), (key1900, 1), (key1291, 1), (key1299, 1), (key1568, 1), (key1594, 1), (key1904, 1), (key1912, 1), (key1311, 1), (key1327, 1), (key1419, 1), (key1445, 1), (key1921, 1), (key1927, 1), (key1352, 1), (key1355, 1), (key1473, 1), (key1481, 1), (key1684, 1), (key1690, 1)]

def rawRow8144 : Integer.Sparse Key := [(key1549, -2), (key1541, -2), (key1897, -2), (key1319, -2), (key1311, -2), (key1634, -2), (key1617, -2), (key1927, -2), (key1919, -2), (key1352, -2), (key1690, -2), (key1682, -2), (key1394, 1), (key1386, 1), (key1557, 1), (key1541, 1), (key1900, 1), (key1897, 1), (key1299, 1), (key1291, 1), (key1594, 1), (key1568, 1), (key1912, 1), (key1904, 1), (key1327, 1), (key1311, 1), (key1445, 1), (key1419, 1), (key1927, 1), (key1921, 1), (key1355, 1), (key1352, 1), (key1481, 1), (key1473, 1), (key1690, 1), (key1684, 1)]

def rawRow8145 : Integer.Sparse Key := [(key1541, -2), (key1897, -2), (key1549, -2), (key1617, -2), (key1919, -2), (key1311, -2), (key1927, -2), (key1319, -2), (key1634, -2), (key1682, -2), (key1352, -2), (key1690, -2), (key1541, 1), (key1897, 1), (key1386, 1), (key1900, 1), (key1394, 1), (key1557, 1), (key1568, 1), (key1904, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1419, 1), (key1921, 1), (key1311, 1), (key1927, 1), (key1327, 1), (key1445, 1), (key1473, 1), (key1684, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1481, 1)]

def rawRow8146 : Integer.Sparse Key := [(key1897, -2), (key1541, -2), (key1549, -2), (key1919, -2), (key1617, -2), (key1927, -2), (key1311, -2), (key1634, -2), (key1319, -2), (key1682, -2), (key1690, -2), (key1352, -2), (key1897, 1), (key1541, 1), (key1900, 1), (key1386, 1), (key1557, 1), (key1394, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1594, 1), (key1299, 1), (key1921, 1), (key1419, 1), (key1927, 1), (key1311, 1), (key1445, 1), (key1327, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1481, 1), (key1355, 1)]

def rawRow8147 : Integer.Sparse Key := [(key1549, -2), (key1897, -2), (key1541, -2), (key1634, -2), (key1927, -2), (key1319, -2), (key1919, -2), (key1311, -2), (key1617, -2), (key1690, -2), (key1352, -2), (key1682, -2), (key1557, 1), (key1900, 1), (key1394, 1), (key1897, 1), (key1386, 1), (key1541, 1), (key1594, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1291, 1), (key1568, 1), (key1445, 1), (key1927, 1), (key1327, 1), (key1921, 1), (key1311, 1), (key1419, 1), (key1481, 1), (key1690, 1), (key1355, 1), (key1684, 1), (key1352, 1), (key1473, 1)]

def rawRow8148 : Integer.Sparse Key := [(key1897, -2), (key1549, -2), (key1541, -2), (key1927, -2), (key1634, -2), (key1919, -2), (key1319, -2), (key1617, -2), (key1311, -2), (key1690, -2), (key1682, -2), (key1352, -2), (key1900, 1), (key1557, 1), (key1897, 1), (key1394, 1), (key1541, 1), (key1386, 1), (key1912, 1), (key1594, 1), (key1904, 1), (key1299, 1), (key1568, 1), (key1291, 1), (key1927, 1), (key1445, 1), (key1921, 1), (key1327, 1), (key1419, 1), (key1311, 1), (key1690, 1), (key1481, 1), (key1684, 1), (key1355, 1), (key1473, 1), (key1352, 1)]

def rawRow8149 : Integer.Sparse Key := [(key1617, -2), (key1682, -2), (key1919, -2), (key1311, -2), (key1352, -2), (key1541, -2), (key1690, -2), (key1897, -2), (key1927, -2), (key1319, -2), (key1549, -2), (key1634, -2), (key1419, 1), (key1473, 1), (key1568, 1), (key1684, 1), (key1904, 1), (key1921, 1), (key1311, 1), (key1352, 1), (key1541, 1), (key1690, 1), (key1897, 1), (key1927, 1), (key1291, 1), (key1355, 1), (key1386, 1), (key1481, 1), (key1900, 1), (key1912, 1), (key1299, 1), (key1327, 1), (key1394, 1), (key1445, 1), (key1557, 1), (key1594, 1)]

def rawRow8150 : Integer.Sparse Key := [(key1682, -2), (key1617, -2), (key1919, -2), (key1352, -2), (key1311, -2), (key1690, -2), (key1541, -2), (key1927, -2), (key1897, -2), (key1319, -2), (key1634, -2), (key1549, -2), (key1473, 1), (key1419, 1), (key1684, 1), (key1568, 1), (key1921, 1), (key1904, 1), (key1352, 1), (key1311, 1), (key1690, 1), (key1541, 1), (key1927, 1), (key1897, 1), (key1355, 1), (key1291, 1), (key1481, 1), (key1386, 1), (key1912, 1), (key1900, 1), (key1327, 1), (key1299, 1), (key1445, 1), (key1394, 1), (key1594, 1), (key1557, 1)]

def rawRow8151 : Integer.Sparse Key := [(key1617, -2), (key1919, -2), (key1682, -2), (key1541, -2), (key1897, -2), (key1311, -2), (key1927, -2), (key1352, -2), (key1690, -2), (key1549, -2), (key1319, -2), (key1634, -2), (key1568, 1), (key1904, 1), (key1419, 1), (key1921, 1), (key1473, 1), (key1684, 1), (key1541, 1), (key1897, 1), (key1311, 1), (key1927, 1), (key1352, 1), (key1690, 1), (key1386, 1), (key1900, 1), (key1291, 1), (key1912, 1), (key1355, 1), (key1481, 1), (key1394, 1), (key1557, 1), (key1299, 1), (key1594, 1), (key1327, 1), (key1445, 1)]

def rawRow8152 : Integer.Sparse Key := [(key1919, -2), (key1617, -2), (key1682, -2), (key1897, -2), (key1541, -2), (key1927, -2), (key1311, -2), (key1690, -2), (key1352, -2), (key1549, -2), (key1634, -2), (key1319, -2), (key1904, 1), (key1568, 1), (key1921, 1), (key1419, 1), (key1684, 1), (key1473, 1), (key1897, 1), (key1541, 1), (key1927, 1), (key1311, 1), (key1690, 1), (key1352, 1), (key1900, 1), (key1386, 1), (key1912, 1), (key1291, 1), (key1481, 1), (key1355, 1), (key1557, 1), (key1394, 1), (key1594, 1), (key1299, 1), (key1445, 1), (key1327, 1)]

def rawRow8153 : Integer.Sparse Key := [(key1682, -2), (key1919, -2), (key1617, -2), (key1690, -2), (key1927, -2), (key1352, -2), (key1897, -2), (key1311, -2), (key1541, -2), (key1634, -2), (key1319, -2), (key1549, -2), (key1684, 1), (key1921, 1), (key1473, 1), (key1904, 1), (key1419, 1), (key1568, 1), (key1690, 1), (key1927, 1), (key1352, 1), (key1897, 1), (key1311, 1), (key1541, 1), (key1481, 1), (key1912, 1), (key1355, 1), (key1900, 1), (key1291, 1), (key1386, 1), (key1445, 1), (key1594, 1), (key1327, 1), (key1557, 1), (key1299, 1), (key1394, 1)]

def rawRow8154 : Integer.Sparse Key := [(key1919, -2), (key1682, -2), (key1617, -2), (key1927, -2), (key1690, -2), (key1897, -2), (key1352, -2), (key1541, -2), (key1311, -2), (key1634, -2), (key1549, -2), (key1319, -2), (key1921, 1), (key1684, 1), (key1904, 1), (key1473, 1), (key1568, 1), (key1419, 1), (key1927, 1), (key1690, 1), (key1897, 1), (key1352, 1), (key1541, 1), (key1311, 1), (key1912, 1), (key1481, 1), (key1900, 1), (key1355, 1), (key1386, 1), (key1291, 1), (key1594, 1), (key1445, 1), (key1557, 1), (key1327, 1), (key1394, 1), (key1299, 1)]

def rawRow8155 : Integer.Sparse Key := [(key1634, -2), (key1690, -2), (key1927, -2), (key1319, -2), (key1352, -2), (key1549, -2), (key1682, -2), (key1897, -2), (key1919, -2), (key1311, -2), (key1541, -2), (key1617, -2), (key1445, 1), (key1481, 1), (key1594, 1), (key1690, 1), (key1912, 1), (key1927, 1), (key1327, 1), (key1355, 1), (key1557, 1), (key1684, 1), (key1900, 1), (key1921, 1), (key1299, 1), (key1352, 1), (key1394, 1), (key1473, 1), (key1897, 1), (key1904, 1), (key1291, 1), (key1311, 1), (key1386, 1), (key1419, 1), (key1541, 1), (key1568, 1)]

def rawRow8156 : Integer.Sparse Key := [(key1690, -2), (key1634, -2), (key1927, -2), (key1352, -2), (key1319, -2), (key1682, -2), (key1549, -2), (key1919, -2), (key1897, -2), (key1311, -2), (key1617, -2), (key1541, -2), (key1481, 1), (key1445, 1), (key1690, 1), (key1594, 1), (key1927, 1), (key1912, 1), (key1355, 1), (key1327, 1), (key1684, 1), (key1557, 1), (key1921, 1), (key1900, 1), (key1352, 1), (key1299, 1), (key1473, 1), (key1394, 1), (key1904, 1), (key1897, 1), (key1311, 1), (key1291, 1), (key1419, 1), (key1386, 1), (key1568, 1), (key1541, 1)]

def rawRow8157 : Integer.Sparse Key := [(key1634, -2), (key1927, -2), (key1690, -2), (key1549, -2), (key1897, -2), (key1319, -2), (key1919, -2), (key1352, -2), (key1682, -2), (key1541, -2), (key1311, -2), (key1617, -2), (key1594, 1), (key1912, 1), (key1445, 1), (key1927, 1), (key1481, 1), (key1690, 1), (key1557, 1), (key1900, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1684, 1), (key1394, 1), (key1897, 1), (key1299, 1), (key1904, 1), (key1352, 1), (key1473, 1), (key1386, 1), (key1541, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1419, 1)]

def rawRow8158 : Integer.Sparse Key := [(key1927, -2), (key1634, -2), (key1690, -2), (key1897, -2), (key1549, -2), (key1919, -2), (key1319, -2), (key1682, -2), (key1352, -2), (key1541, -2), (key1617, -2), (key1311, -2), (key1912, 1), (key1594, 1), (key1927, 1), (key1445, 1), (key1690, 1), (key1481, 1), (key1900, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1684, 1), (key1355, 1), (key1897, 1), (key1394, 1), (key1904, 1), (key1299, 1), (key1473, 1), (key1352, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1419, 1), (key1311, 1)]

def rawRow8159 : Integer.Sparse Key := [(key1690, -2), (key1927, -2), (key1634, -2), (key1682, -2), (key1919, -2), (key1352, -2), (key1897, -2), (key1319, -2), (key1549, -2), (key1617, -2), (key1311, -2), (key1541, -2), (key1690, 1), (key1927, 1), (key1481, 1), (key1912, 1), (key1445, 1), (key1594, 1), (key1684, 1), (key1921, 1), (key1355, 1), (key1900, 1), (key1327, 1), (key1557, 1), (key1473, 1), (key1904, 1), (key1352, 1), (key1897, 1), (key1299, 1), (key1394, 1), (key1419, 1), (key1568, 1), (key1311, 1), (key1541, 1), (key1291, 1), (key1386, 1)]

def rawRow8160 : Integer.Sparse Key := [(key1927, -2), (key1690, -2), (key1634, -2), (key1919, -2), (key1682, -2), (key1897, -2), (key1352, -2), (key1549, -2), (key1319, -2), (key1617, -2), (key1541, -2), (key1311, -2), (key1927, 1), (key1690, 1), (key1912, 1), (key1481, 1), (key1594, 1), (key1445, 1), (key1921, 1), (key1684, 1), (key1900, 1), (key1355, 1), (key1557, 1), (key1327, 1), (key1904, 1), (key1473, 1), (key1897, 1), (key1352, 1), (key1394, 1), (key1299, 1), (key1568, 1), (key1419, 1), (key1541, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

def rawRow8161 : Integer.Sparse Key := [(key1528, -24), (key1253, 6), (key1606, 6), (key1606, 6), (key1636, 6)]

def rawRow8162 : Integer.Sparse Key := [(key1528, -24), (key1253, 6), (key1606, 6), (key1636, 6), (key1606, 6)]

def rawRow8163 : Integer.Sparse Key := [(key1528, -24), (key1253, 6), (key1636, 6), (key1606, 6), (key1606, 6)]

def rawRow8164 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1253, 6), (key1606, 6), (key1636, 6)]

def rawRow8165 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1253, 6), (key1636, 6), (key1606, 6)]

def rawRow8166 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1606, 6), (key1253, 6), (key1636, 6)]

def rawRow8167 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1606, 6), (key1636, 6), (key1253, 6)]

def rawRow8168 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1636, 6), (key1253, 6), (key1606, 6)]

def rawRow8169 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1636, 6), (key1606, 6), (key1253, 6)]

def rawRow8170 : Integer.Sparse Key := [(key1528, -24), (key1636, 6), (key1253, 6), (key1606, 6), (key1606, 6)]

def rawRow8171 : Integer.Sparse Key := [(key1528, -24), (key1636, 6), (key1606, 6), (key1253, 6), (key1606, 6)]

def rawRow8172 : Integer.Sparse Key := [(key1528, -24), (key1636, 6), (key1606, 6), (key1606, 6), (key1253, 6)]

def rawRow8173 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1528, 6), (key1606, 6), (key1636, 6)]

def rawRow8174 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1528, 6), (key1636, 6), (key1606, 6)]

def rawRow8175 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1606, 6), (key1528, 6), (key1636, 6)]

def rawRow8176 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1606, 6), (key1636, 6), (key1528, 6)]

def rawRow8177 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1636, 6), (key1528, 6), (key1606, 6)]

def rawRow8178 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1636, 6), (key1606, 6), (key1528, 6)]

def rawRow8179 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1253, 6), (key1606, 6), (key1636, 6)]

def rawRow8180 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1253, 6), (key1636, 6), (key1606, 6)]

def rawRow8181 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1606, 6), (key1253, 6), (key1636, 6)]

def rawRow8182 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1606, 6), (key1636, 6), (key1253, 6)]

def rawRow8183 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1636, 6), (key1253, 6), (key1606, 6)]

def rawRow8184 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1636, 6), (key1606, 6), (key1253, 6)]

def rawRow8185 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1253, 6), (key1528, 6), (key1636, 6)]

def rawRow8186 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1253, 6), (key1636, 6), (key1528, 6)]

def rawRow8187 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1528, 6), (key1253, 6), (key1636, 6)]

def rawRow8188 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1528, 6), (key1636, 6), (key1253, 6)]

def rawRow8189 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1636, 6), (key1253, 6), (key1528, 6)]

def rawRow8190 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1636, 6), (key1528, 6), (key1253, 6)]

def rawRow8191 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1253, 6), (key1528, 6), (key1606, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8192 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1253, 6), (key1606, 6), (key1528, 6)]

def rawRow8193 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1528, 6), (key1253, 6), (key1606, 6)]

def rawRow8194 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1528, 6), (key1606, 6), (key1253, 6)]

def rawRow8195 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1606, 6), (key1253, 6), (key1528, 6)]

def rawRow8196 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1606, 6), (key1528, 6), (key1253, 6)]

def rawRow8197 : Integer.Sparse Key := [(key1386, -2), (key1394, -2), (key1394, -2), (key1541, -2), (key1549, -2), (key1541, -2), (key1557, -2), (key1549, -2), (key1557, -2), (key1897, -2), (key1897, -2), (key1900, -2), (key1291, 2), (key1299, 2), (key1299, 2), (key1568, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1594, 2), (key1904, 2), (key1904, 2), (key1912, 2)]

def rawRow8198 : Integer.Sparse Key := [(key1394, -2), (key1386, -2), (key1394, -2), (key1549, -2), (key1541, -2), (key1557, -2), (key1541, -2), (key1557, -2), (key1549, -2), (key1897, -2), (key1900, -2), (key1897, -2), (key1299, 2), (key1291, 2), (key1299, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1904, 2), (key1912, 2), (key1904, 2)]

def rawRow8199 : Integer.Sparse Key := [(key1394, -2), (key1394, -2), (key1386, -2), (key1557, -2), (key1557, -2), (key1549, -2), (key1549, -2), (key1541, -2), (key1541, -2), (key1900, -2), (key1897, -2), (key1897, -2), (key1299, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1594, 2), (key1576, 2), (key1576, 2), (key1568, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1904, 2)]

def rawRow8200 : Integer.Sparse Key := [(key1541, -2), (key1549, -2), (key1897, -2), (key1386, -2), (key1394, -2), (key1541, -2), (key1557, -2), (key1897, -2), (key1900, -2), (key1394, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1904, 2), (key1291, 2), (key1299, 2), (key1568, 2), (key1594, 2), (key1904, 2), (key1912, 2), (key1299, 2), (key1576, 2), (key1594, 2)]

def rawRow8201 : Integer.Sparse Key := [(key1549, -2), (key1541, -2), (key1897, -2), (key1394, -2), (key1386, -2), (key1557, -2), (key1541, -2), (key1900, -2), (key1897, -2), (key1394, -2), (key1557, -2), (key1549, -2), (key1576, 2), (key1568, 2), (key1904, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1299, 2), (key1594, 2), (key1576, 2)]

def rawRow8202 : Integer.Sparse Key := [(key1541, -2), (key1897, -2), (key1549, -2), (key1541, -2), (key1897, -2), (key1386, -2), (key1900, -2), (key1394, -2), (key1557, -2), (key1549, -2), (key1394, -2), (key1557, -2), (key1568, 2), (key1904, 2), (key1576, 2), (key1568, 2), (key1904, 2), (key1291, 2), (key1912, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1594, 2)]

def rawRow8203 : Integer.Sparse Key := [(key1897, -2), (key1541, -2), (key1549, -2), (key1897, -2), (key1541, -2), (key1900, -2), (key1386, -2), (key1557, -2), (key1394, -2), (key1549, -2), (key1557, -2), (key1394, -2), (key1904, 2), (key1568, 2), (key1576, 2), (key1904, 2), (key1568, 2), (key1912, 2), (key1291, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1299, 2)]

def rawRow8204 : Integer.Sparse Key := [(key1549, -2), (key1897, -2), (key1541, -2), (key1557, -2), (key1900, -2), (key1394, -2), (key1897, -2), (key1386, -2), (key1541, -2), (key1557, -2), (key1394, -2), (key1549, -2), (key1576, 2), (key1904, 2), (key1568, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1594, 2), (key1299, 2), (key1576, 2)]

def rawRow8205 : Integer.Sparse Key := [(key1897, -2), (key1549, -2), (key1541, -2), (key1900, -2), (key1557, -2), (key1897, -2), (key1394, -2), (key1541, -2), (key1386, -2), (key1557, -2), (key1549, -2), (key1394, -2), (key1904, 2), (key1576, 2), (key1568, 2), (key1912, 2), (key1594, 2), (key1904, 2), (key1299, 2), (key1568, 2), (key1291, 2), (key1594, 2), (key1576, 2), (key1299, 2)]

def rawRow8206 : Integer.Sparse Key := [(key1557, -2), (key1557, -2), (key1900, -2), (key1394, -2), (key1394, -2), (key1549, -2), (key1549, -2), (key1897, -2), (key1897, -2), (key1386, -2), (key1541, -2), (key1541, -2), (key1594, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1299, 2), (key1576, 2), (key1576, 2), (key1904, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1568, 2)]

def rawRow8207 : Integer.Sparse Key := [(key1557, -2), (key1900, -2), (key1557, -2), (key1549, -2), (key1897, -2), (key1394, -2), (key1897, -2), (key1394, -2), (key1549, -2), (key1541, -2), (key1386, -2), (key1541, -2), (key1594, 2), (key1912, 2), (key1594, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1568, 2), (key1291, 2), (key1568, 2)]

def rawRow8208 : Integer.Sparse Key := [(key1900, -2), (key1557, -2), (key1557, -2), (key1897, -2), (key1549, -2), (key1897, -2), (key1394, -2), (key1549, -2), (key1394, -2), (key1541, -2), (key1541, -2), (key1386, -2), (key1912, 2), (key1594, 2), (key1594, 2), (key1904, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1299, 2), (key1568, 2), (key1568, 2), (key1291, 2)]

def rawRow8209 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1473, -2), (key1568, -2), (key1576, -2), (key1617, -2), (key1625, -2), (key1682, -2), (key1684, -2), (key1904, -2), (key1919, -2), (key1921, -2), (key1311, 2), (key1319, 2), (key1352, 2), (key1541, 2), (key1549, 2), (key1617, 2), (key1634, 2), (key1682, 2), (key1690, 2), (key1897, 2), (key1919, 2), (key1927, 2)]

def rawRow8210 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1473, -2), (key1576, -2), (key1568, -2), (key1625, -2), (key1617, -2), (key1684, -2), (key1682, -2), (key1904, -2), (key1921, -2), (key1919, -2), (key1319, 2), (key1311, 2), (key1352, 2), (key1549, 2), (key1541, 2), (key1634, 2), (key1617, 2), (key1690, 2), (key1682, 2), (key1897, 2), (key1927, 2), (key1919, 2)]

def rawRow8211 : Integer.Sparse Key := [(key1419, -2), (key1473, -2), (key1427, -2), (key1617, -2), (key1682, -2), (key1568, -2), (key1684, -2), (key1576, -2), (key1625, -2), (key1919, -2), (key1904, -2), (key1921, -2), (key1311, 2), (key1352, 2), (key1319, 2), (key1617, 2), (key1682, 2), (key1541, 2), (key1690, 2), (key1549, 2), (key1634, 2), (key1919, 2), (key1897, 2), (key1927, 2)]

def rawRow8212 : Integer.Sparse Key := [(key1473, -2), (key1419, -2), (key1427, -2), (key1682, -2), (key1617, -2), (key1684, -2), (key1568, -2), (key1625, -2), (key1576, -2), (key1919, -2), (key1921, -2), (key1904, -2), (key1352, 2), (key1311, 2), (key1319, 2), (key1682, 2), (key1617, 2), (key1690, 2), (key1541, 2), (key1634, 2), (key1549, 2), (key1919, 2), (key1927, 2), (key1897, 2)]

def rawRow8213 : Integer.Sparse Key := [(key1427, -2), (key1473, -2), (key1419, -2), (key1625, -2), (key1684, -2), (key1576, -2), (key1682, -2), (key1568, -2), (key1617, -2), (key1921, -2), (key1904, -2), (key1919, -2), (key1319, 2), (key1352, 2), (key1311, 2), (key1634, 2), (key1690, 2), (key1549, 2), (key1682, 2), (key1541, 2), (key1617, 2), (key1927, 2), (key1897, 2), (key1919, 2)]

def rawRow8214 : Integer.Sparse Key := [(key1473, -2), (key1427, -2), (key1419, -2), (key1684, -2), (key1625, -2), (key1682, -2), (key1576, -2), (key1617, -2), (key1568, -2), (key1921, -2), (key1919, -2), (key1904, -2), (key1352, 2), (key1319, 2), (key1311, 2), (key1690, 2), (key1634, 2), (key1682, 2), (key1549, 2), (key1617, 2), (key1541, 2), (key1927, 2), (key1919, 2), (key1897, 2)]

def rawRow8215 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1904, -2), (key1419, -2), (key1427, -2), (key1617, -2), (key1625, -2), (key1919, -2), (key1921, -2), (key1473, -2), (key1682, -2), (key1684, -2), (key1541, 2), (key1549, 2), (key1897, 2), (key1311, 2), (key1319, 2), (key1617, 2), (key1634, 2), (key1919, 2), (key1927, 2), (key1352, 2), (key1682, 2), (key1690, 2)]

def rawRow8216 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1904, -2), (key1427, -2), (key1419, -2), (key1625, -2), (key1617, -2), (key1921, -2), (key1919, -2), (key1473, -2), (key1684, -2), (key1682, -2), (key1549, 2), (key1541, 2), (key1897, 2), (key1319, 2), (key1311, 2), (key1634, 2), (key1617, 2), (key1927, 2), (key1919, 2), (key1352, 2), (key1690, 2), (key1682, 2)]

def rawRow8217 : Integer.Sparse Key := [(key1568, -2), (key1904, -2), (key1576, -2), (key1617, -2), (key1919, -2), (key1419, -2), (key1921, -2), (key1427, -2), (key1625, -2), (key1682, -2), (key1473, -2), (key1684, -2), (key1541, 2), (key1897, 2), (key1549, 2), (key1617, 2), (key1919, 2), (key1311, 2), (key1927, 2), (key1319, 2), (key1634, 2), (key1682, 2), (key1352, 2), (key1690, 2)]

def rawRow8218 : Integer.Sparse Key := [(key1904, -2), (key1568, -2), (key1576, -2), (key1919, -2), (key1617, -2), (key1921, -2), (key1419, -2), (key1625, -2), (key1427, -2), (key1682, -2), (key1684, -2), (key1473, -2), (key1897, 2), (key1541, 2), (key1549, 2), (key1919, 2), (key1617, 2), (key1927, 2), (key1311, 2), (key1634, 2), (key1319, 2), (key1682, 2), (key1690, 2), (key1352, 2)]

def rawRow8219 : Integer.Sparse Key := [(key1576, -2), (key1904, -2), (key1568, -2), (key1625, -2), (key1921, -2), (key1427, -2), (key1919, -2), (key1419, -2), (key1617, -2), (key1684, -2), (key1473, -2), (key1682, -2), (key1549, 2), (key1897, 2), (key1541, 2), (key1634, 2), (key1927, 2), (key1319, 2), (key1919, 2), (key1311, 2), (key1617, 2), (key1690, 2), (key1352, 2), (key1682, 2)]

def rawRow8220 : Integer.Sparse Key := [(key1904, -2), (key1576, -2), (key1568, -2), (key1921, -2), (key1625, -2), (key1919, -2), (key1427, -2), (key1617, -2), (key1419, -2), (key1684, -2), (key1682, -2), (key1473, -2), (key1897, 2), (key1549, 2), (key1541, 2), (key1927, 2), (key1634, 2), (key1919, 2), (key1319, 2), (key1617, 2), (key1311, 2), (key1690, 2), (key1682, 2), (key1352, 2)]

def rawRow8221 : Integer.Sparse Key := [(key1617, -2), (key1682, -2), (key1919, -2), (key1419, -2), (key1473, -2), (key1568, -2), (key1684, -2), (key1904, -2), (key1921, -2), (key1427, -2), (key1576, -2), (key1625, -2), (key1617, 2), (key1682, 2), (key1919, 2), (key1311, 2), (key1352, 2), (key1541, 2), (key1690, 2), (key1897, 2), (key1927, 2), (key1319, 2), (key1549, 2), (key1634, 2)]

def rawRow8222 : Integer.Sparse Key := [(key1682, -2), (key1617, -2), (key1919, -2), (key1473, -2), (key1419, -2), (key1684, -2), (key1568, -2), (key1921, -2), (key1904, -2), (key1427, -2), (key1625, -2), (key1576, -2), (key1682, 2), (key1617, 2), (key1919, 2), (key1352, 2), (key1311, 2), (key1690, 2), (key1541, 2), (key1927, 2), (key1897, 2), (key1319, 2), (key1634, 2), (key1549, 2)]

def rawRow8223 : Integer.Sparse Key := [(key1617, -2), (key1919, -2), (key1682, -2), (key1568, -2), (key1904, -2), (key1419, -2), (key1921, -2), (key1473, -2), (key1684, -2), (key1576, -2), (key1427, -2), (key1625, -2), (key1617, 2), (key1919, 2), (key1682, 2), (key1541, 2), (key1897, 2), (key1311, 2), (key1927, 2), (key1352, 2), (key1690, 2), (key1549, 2), (key1319, 2), (key1634, 2)]

def rawRow8224 : Integer.Sparse Key := [(key1919, -2), (key1617, -2), (key1682, -2), (key1904, -2), (key1568, -2), (key1921, -2), (key1419, -2), (key1684, -2), (key1473, -2), (key1576, -2), (key1625, -2), (key1427, -2), (key1919, 2), (key1617, 2), (key1682, 2), (key1897, 2), (key1541, 2), (key1927, 2), (key1311, 2), (key1690, 2), (key1352, 2), (key1549, 2), (key1634, 2), (key1319, 2)]

def rawRow8225 : Integer.Sparse Key := [(key1682, -2), (key1919, -2), (key1617, -2), (key1684, -2), (key1921, -2), (key1473, -2), (key1904, -2), (key1419, -2), (key1568, -2), (key1625, -2), (key1427, -2), (key1576, -2), (key1682, 2), (key1919, 2), (key1617, 2), (key1690, 2), (key1927, 2), (key1352, 2), (key1897, 2), (key1311, 2), (key1541, 2), (key1634, 2), (key1319, 2), (key1549, 2)]

def rawRow8226 : Integer.Sparse Key := [(key1919, -2), (key1682, -2), (key1617, -2), (key1921, -2), (key1684, -2), (key1904, -2), (key1473, -2), (key1568, -2), (key1419, -2), (key1625, -2), (key1576, -2), (key1427, -2), (key1919, 2), (key1682, 2), (key1617, 2), (key1927, 2), (key1690, 2), (key1897, 2), (key1352, 2), (key1541, 2), (key1311, 2), (key1634, 2), (key1549, 2), (key1319, 2)]

def rawRow8227 : Integer.Sparse Key := [(key1625, -2), (key1684, -2), (key1921, -2), (key1427, -2), (key1473, -2), (key1576, -2), (key1682, -2), (key1904, -2), (key1919, -2), (key1419, -2), (key1568, -2), (key1617, -2), (key1634, 2), (key1690, 2), (key1927, 2), (key1319, 2), (key1352, 2), (key1549, 2), (key1682, 2), (key1897, 2), (key1919, 2), (key1311, 2), (key1541, 2), (key1617, 2)]

def rawRow8228 : Integer.Sparse Key := [(key1684, -2), (key1625, -2), (key1921, -2), (key1473, -2), (key1427, -2), (key1682, -2), (key1576, -2), (key1919, -2), (key1904, -2), (key1419, -2), (key1617, -2), (key1568, -2), (key1690, 2), (key1634, 2), (key1927, 2), (key1352, 2), (key1319, 2), (key1682, 2), (key1549, 2), (key1919, 2), (key1897, 2), (key1311, 2), (key1617, 2), (key1541, 2)]

def rawRow8229 : Integer.Sparse Key := [(key1625, -2), (key1921, -2), (key1684, -2), (key1576, -2), (key1904, -2), (key1427, -2), (key1919, -2), (key1473, -2), (key1682, -2), (key1568, -2), (key1419, -2), (key1617, -2), (key1634, 2), (key1927, 2), (key1690, 2), (key1549, 2), (key1897, 2), (key1319, 2), (key1919, 2), (key1352, 2), (key1682, 2), (key1541, 2), (key1311, 2), (key1617, 2)]

def rawRow8230 : Integer.Sparse Key := [(key1921, -2), (key1625, -2), (key1684, -2), (key1904, -2), (key1576, -2), (key1919, -2), (key1427, -2), (key1682, -2), (key1473, -2), (key1568, -2), (key1617, -2), (key1419, -2), (key1927, 2), (key1634, 2), (key1690, 2), (key1897, 2), (key1549, 2), (key1919, 2), (key1319, 2), (key1682, 2), (key1352, 2), (key1541, 2), (key1617, 2), (key1311, 2)]

def rawRow8231 : Integer.Sparse Key := [(key1684, -2), (key1921, -2), (key1625, -2), (key1682, -2), (key1919, -2), (key1473, -2), (key1904, -2), (key1427, -2), (key1576, -2), (key1617, -2), (key1419, -2), (key1568, -2), (key1690, 2), (key1927, 2), (key1634, 2), (key1682, 2), (key1919, 2), (key1352, 2), (key1897, 2), (key1319, 2), (key1549, 2), (key1617, 2), (key1311, 2), (key1541, 2)]

def rawRow8232 : Integer.Sparse Key := [(key1921, -2), (key1684, -2), (key1625, -2), (key1919, -2), (key1682, -2), (key1904, -2), (key1473, -2), (key1576, -2), (key1427, -2), (key1617, -2), (key1568, -2), (key1419, -2), (key1927, 2), (key1690, 2), (key1634, 2), (key1919, 2), (key1682, 2), (key1897, 2), (key1352, 2), (key1549, 2), (key1319, 2), (key1617, 2), (key1541, 2), (key1311, 2)]

def rawRow8233 : Integer.Sparse Key := [(key236, -2), (key241, -2), (key241, -2), (key406, -2), (key411, -2), (key406, -2), (key421, -2), (key411, -2), (key421, -2), (key657, -2), (key657, -2), (key658, -2), (key248, 1), (key253, 1), (key248, 1), (key263, 1), (key253, 1), (key263, 1), (key316, 1), (key321, 1), (key316, 1), (key331, 1), (key321, 1), (key331, 1), (key435, 1), (key445, 1), (key435, 1), (key453, 1), (key445, 1), (key453, 1), (key660, 1), (key661, 1), (key660, 1), (key662, 1), (key661, 1), (key662, 1)]

def rawRow8234 : Integer.Sparse Key := [(key241, -2), (key236, -2), (key241, -2), (key411, -2), (key406, -2), (key421, -2), (key406, -2), (key421, -2), (key411, -2), (key657, -2), (key658, -2), (key657, -2), (key253, 1), (key248, 1), (key263, 1), (key248, 1), (key263, 1), (key253, 1), (key321, 1), (key316, 1), (key331, 1), (key316, 1), (key331, 1), (key321, 1), (key445, 1), (key435, 1), (key453, 1), (key435, 1), (key453, 1), (key445, 1), (key661, 1), (key660, 1), (key662, 1), (key660, 1), (key662, 1), (key661, 1)]

def rawRow8235 : Integer.Sparse Key := [(key241, -2), (key241, -2), (key236, -2), (key421, -2), (key421, -2), (key411, -2), (key411, -2), (key406, -2), (key406, -2), (key658, -2), (key657, -2), (key657, -2), (key263, 1), (key263, 1), (key253, 1), (key253, 1), (key248, 1), (key248, 1), (key331, 1), (key331, 1), (key321, 1), (key321, 1), (key316, 1), (key316, 1), (key453, 1), (key453, 1), (key445, 1), (key445, 1), (key435, 1), (key435, 1), (key662, 1), (key662, 1), (key661, 1), (key661, 1), (key660, 1), (key660, 1)]

def rawRow8236 : Integer.Sparse Key := [(key406, -2), (key411, -2), (key421, -2), (key236, -2), (key241, -2), (key406, -2), (key421, -2), (key657, -2), (key658, -2), (key241, -2), (key411, -2), (key421, -2), (key316, 1), (key321, 1), (key435, 1), (key445, 1), (key660, 1), (key661, 1), (key248, 1), (key253, 1), (key435, 1), (key453, 1), (key660, 1), (key662, 1), (key248, 1), (key263, 1), (key316, 1), (key331, 1), (key661, 1), (key662, 1), (key253, 1), (key263, 1), (key321, 1), (key331, 1), (key445, 1), (key453, 1)]

def rawRow8237 : Integer.Sparse Key := [(key411, -2), (key406, -2), (key421, -2), (key241, -2), (key236, -2), (key421, -2), (key406, -2), (key658, -2), (key657, -2), (key241, -2), (key421, -2), (key411, -2), (key321, 1), (key316, 1), (key445, 1), (key435, 1), (key661, 1), (key660, 1), (key253, 1), (key248, 1), (key453, 1), (key435, 1), (key662, 1), (key660, 1), (key263, 1), (key248, 1), (key331, 1), (key316, 1), (key662, 1), (key661, 1), (key263, 1), (key253, 1), (key331, 1), (key321, 1), (key453, 1), (key445, 1)]

def rawRow8238 : Integer.Sparse Key := [(key406, -2), (key421, -2), (key411, -2), (key406, -2), (key421, -2), (key236, -2), (key658, -2), (key241, -2), (key421, -2), (key411, -2), (key241, -2), (key421, -2), (key435, 1), (key660, 1), (key316, 1), (key661, 1), (key321, 1), (key445, 1), (key435, 1), (key660, 1), (key248, 1), (key662, 1), (key253, 1), (key453, 1), (key316, 1), (key661, 1), (key248, 1), (key662, 1), (key263, 1), (key331, 1), (key321, 1), (key445, 1), (key253, 1), (key453, 1), (key263, 1), (key331, 1)]

def rawRow8239 : Integer.Sparse Key := [(key421, -2), (key406, -2), (key411, -2), (key421, -2), (key406, -2), (key658, -2), (key236, -2), (key421, -2), (key241, -2), (key411, -2), (key421, -2), (key241, -2), (key660, 1), (key435, 1), (key661, 1), (key316, 1), (key445, 1), (key321, 1), (key660, 1), (key435, 1), (key662, 1), (key248, 1), (key453, 1), (key253, 1), (key661, 1), (key316, 1), (key662, 1), (key248, 1), (key331, 1), (key263, 1), (key445, 1), (key321, 1), (key453, 1), (key253, 1), (key331, 1), (key263, 1)]

def rawRow8240 : Integer.Sparse Key := [(key411, -2), (key421, -2), (key406, -2), (key657, -2), (key658, -2), (key241, -2), (key421, -2), (key236, -2), (key406, -2), (key421, -2), (key241, -2), (key411, -2), (key445, 1), (key661, 1), (key321, 1), (key660, 1), (key316, 1), (key435, 1), (key453, 1), (key662, 1), (key253, 1), (key660, 1), (key248, 1), (key435, 1), (key331, 1), (key662, 1), (key263, 1), (key661, 1), (key248, 1), (key316, 1), (key331, 1), (key453, 1), (key263, 1), (key445, 1), (key253, 1), (key321, 1)]

def rawRow8241 : Integer.Sparse Key := [(key421, -2), (key411, -2), (key406, -2), (key658, -2), (key657, -2), (key421, -2), (key241, -2), (key406, -2), (key236, -2), (key421, -2), (key411, -2), (key241, -2), (key661, 1), (key445, 1), (key660, 1), (key321, 1), (key435, 1), (key316, 1), (key662, 1), (key453, 1), (key660, 1), (key253, 1), (key435, 1), (key248, 1), (key662, 1), (key331, 1), (key661, 1), (key263, 1), (key316, 1), (key248, 1), (key453, 1), (key331, 1), (key445, 1), (key263, 1), (key321, 1), (key253, 1)]

def rawRow8242 : Integer.Sparse Key := [(key657, -2), (key657, -2), (key658, -2), (key241, -2), (key241, -2), (key411, -2), (key411, -2), (key421, -2), (key421, -2), (key236, -2), (key406, -2), (key406, -2), (key331, 1), (key331, 1), (key453, 1), (key453, 1), (key662, 1), (key662, 1), (key263, 1), (key263, 1), (key445, 1), (key445, 1), (key661, 1), (key661, 1), (key253, 1), (key253, 1), (key321, 1), (key321, 1), (key660, 1), (key660, 1), (key248, 1), (key248, 1), (key316, 1), (key316, 1), (key435, 1), (key435, 1)]

def rawRow8243 : Integer.Sparse Key := [(key657, -2), (key658, -2), (key657, -2), (key411, -2), (key421, -2), (key241, -2), (key421, -2), (key241, -2), (key411, -2), (key406, -2), (key236, -2), (key406, -2), (key453, 1), (key662, 1), (key331, 1), (key662, 1), (key331, 1), (key453, 1), (key445, 1), (key661, 1), (key263, 1), (key661, 1), (key263, 1), (key445, 1), (key321, 1), (key660, 1), (key253, 1), (key660, 1), (key253, 1), (key321, 1), (key316, 1), (key435, 1), (key248, 1), (key435, 1), (key248, 1), (key316, 1)]

def rawRow8244 : Integer.Sparse Key := [(key658, -2), (key657, -2), (key657, -2), (key421, -2), (key411, -2), (key421, -2), (key241, -2), (key411, -2), (key241, -2), (key406, -2), (key406, -2), (key236, -2), (key662, 1), (key453, 1), (key662, 1), (key331, 1), (key453, 1), (key331, 1), (key661, 1), (key445, 1), (key661, 1), (key263, 1), (key445, 1), (key263, 1), (key660, 1), (key321, 1), (key660, 1), (key253, 1), (key321, 1), (key253, 1), (key435, 1), (key316, 1), (key435, 1), (key248, 1), (key316, 1), (key248, 1)]

def rawRow8245 : Integer.Sparse Key := [(key248, -2), (key253, -2), (key263, -2), (key316, -2), (key321, -2), (key435, -2), (key660, -2), (key445, -2), (key661, -2), (key331, -2), (key453, -2), (key662, -2), (key236, 1), (key241, 1), (key248, 1), (key263, 1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, 1), (key331, 1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key661, 1), (key662, 1)]

def rawRow8246 : Integer.Sparse Key := [(key253, -2), (key248, -2), (key263, -2), (key321, -2), (key316, -2), (key660, -2), (key435, -2), (key661, -2), (key445, -2), (key331, -2), (key662, -2), (key453, -2), (key241, 1), (key236, 1), (key263, 1), (key248, 1), (key278, 1), (key277, 1), (key307, 1), (key302, 1), (key331, 1), (key316, 1), (key347, 1), (key346, 1), (key400, 1), (key385, 1), (key421, 1), (key406, 1), (key489, 1), (key488, 1), (key656, 1), (key655, 1), (key658, 1), (key657, 1), (key662, 1), (key661, 1)]

def rawRow8247 : Integer.Sparse Key := [(key248, -2), (key263, -2), (key253, -2), (key435, -2), (key445, -2), (key316, -2), (key661, -2), (key321, -2), (key660, -2), (key453, -2), (key331, -2), (key662, -2), (key248, 1), (key263, 1), (key236, 1), (key278, 1), (key241, 1), (key263, 1), (key316, 1), (key346, 1), (key302, 1), (key347, 1), (key307, 1), (key331, 1), (key406, 1), (key488, 1), (key385, 1), (key489, 1), (key400, 1), (key421, 1), (key657, 1), (key661, 1), (key655, 1), (key662, 1), (key656, 1), (key658, 1)]

def rawRow8248 : Integer.Sparse Key := [(key263, -2), (key248, -2), (key253, -2), (key445, -2), (key435, -2), (key661, -2), (key316, -2), (key660, -2), (key321, -2), (key453, -2), (key662, -2), (key331, -2), (key263, 1), (key248, 1), (key278, 1), (key236, 1), (key263, 1), (key241, 1), (key346, 1), (key316, 1), (key347, 1), (key302, 1), (key331, 1), (key307, 1), (key488, 1), (key406, 1), (key489, 1), (key385, 1), (key421, 1), (key400, 1), (key661, 1), (key657, 1), (key662, 1), (key655, 1), (key658, 1), (key656, 1)]

def rawRow8249 : Integer.Sparse Key := [(key253, -2), (key263, -2), (key248, -2), (key660, -2), (key661, -2), (key321, -2), (key445, -2), (key316, -2), (key435, -2), (key662, -2), (key331, -2), (key453, -2), (key277, 1), (key278, 1), (key241, 1), (key263, 1), (key236, 1), (key248, 1), (key331, 1), (key347, 1), (key307, 1), (key346, 1), (key302, 1), (key316, 1), (key421, 1), (key489, 1), (key400, 1), (key488, 1), (key385, 1), (key406, 1), (key658, 1), (key662, 1), (key656, 1), (key661, 1), (key655, 1), (key657, 1)]

def rawRow8250 : Integer.Sparse Key := [(key263, -2), (key253, -2), (key248, -2), (key661, -2), (key660, -2), (key445, -2), (key321, -2), (key435, -2), (key316, -2), (key662, -2), (key453, -2), (key331, -2), (key278, 1), (key277, 1), (key263, 1), (key241, 1), (key248, 1), (key236, 1), (key347, 1), (key331, 1), (key346, 1), (key307, 1), (key316, 1), (key302, 1), (key489, 1), (key421, 1), (key488, 1), (key400, 1), (key406, 1), (key385, 1), (key662, 1), (key658, 1), (key661, 1), (key656, 1), (key657, 1), (key655, 1)]

def rawRow8251 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key248, -2), (key253, -2), (key435, -2), (key660, -2), (key453, -2), (key662, -2), (key263, -2), (key445, -2), (key661, -2), (key302, 1), (key307, 1), (key316, 1), (key346, 1), (key331, 1), (key347, 1), (key236, 1), (key241, 1), (key406, 1), (key421, 1), (key657, 1), (key658, 1), (key248, 1), (key263, 1), (key316, 1), (key331, 1), (key661, 1), (key662, 1), (key277, 1), (key278, 1), (key346, 1), (key347, 1), (key488, 1), (key489, 1)]

def rawRow8252 : Integer.Sparse Key := [(key321, -2), (key316, -2), (key331, -2), (key253, -2), (key248, -2), (key660, -2), (key435, -2), (key662, -2), (key453, -2), (key263, -2), (key661, -2), (key445, -2), (key307, 1), (key302, 1), (key346, 1), (key316, 1), (key347, 1), (key331, 1), (key241, 1), (key236, 1), (key421, 1), (key406, 1), (key658, 1), (key657, 1), (key263, 1), (key248, 1), (key331, 1), (key316, 1), (key662, 1), (key661, 1), (key278, 1), (key277, 1), (key347, 1), (key346, 1), (key489, 1), (key488, 1)]

def rawRow8253 : Integer.Sparse Key := [(key316, -2), (key331, -2), (key321, -2), (key435, -2), (key453, -2), (key248, -2), (key662, -2), (key253, -2), (key660, -2), (key445, -2), (key263, -2), (key661, -2), (key316, 1), (key331, 1), (key302, 1), (key347, 1), (key307, 1), (key346, 1), (key406, 1), (key421, 1), (key236, 1), (key658, 1), (key241, 1), (key421, 1), (key316, 1), (key661, 1), (key248, 1), (key662, 1), (key263, 1), (key331, 1), (key346, 1), (key488, 1), (key277, 1), (key489, 1), (key278, 1), (key347, 1)]

def rawRow8254 : Integer.Sparse Key := [(key331, -2), (key316, -2), (key321, -2), (key453, -2), (key435, -2), (key662, -2), (key248, -2), (key660, -2), (key253, -2), (key445, -2), (key661, -2), (key263, -2), (key331, 1), (key316, 1), (key347, 1), (key302, 1), (key346, 1), (key307, 1), (key421, 1), (key406, 1), (key658, 1), (key236, 1), (key421, 1), (key241, 1), (key661, 1), (key316, 1), (key662, 1), (key248, 1), (key331, 1), (key263, 1), (key488, 1), (key346, 1), (key489, 1), (key277, 1), (key347, 1), (key278, 1)]

def rawRow8255 : Integer.Sparse Key := [(key321, -2), (key331, -2), (key316, -2), (key660, -2), (key662, -2), (key253, -2), (key453, -2), (key248, -2), (key435, -2), (key661, -2), (key263, -2), (key445, -2), (key346, 1), (key347, 1), (key307, 1), (key331, 1), (key302, 1), (key316, 1), (key657, 1), (key658, 1), (key241, 1), (key421, 1), (key236, 1), (key406, 1), (key331, 1), (key662, 1), (key263, 1), (key661, 1), (key248, 1), (key316, 1), (key347, 1), (key489, 1), (key278, 1), (key488, 1), (key277, 1), (key346, 1)]

def rawRow8256 : Integer.Sparse Key := [(key331, -2), (key321, -2), (key316, -2), (key662, -2), (key660, -2), (key453, -2), (key253, -2), (key435, -2), (key248, -2), (key661, -2), (key445, -2), (key263, -2), (key347, 1), (key346, 1), (key331, 1), (key307, 1), (key316, 1), (key302, 1), (key658, 1), (key657, 1), (key421, 1), (key241, 1), (key406, 1), (key236, 1), (key662, 1), (key331, 1), (key661, 1), (key263, 1), (key316, 1), (key248, 1), (key489, 1), (key347, 1), (key488, 1), (key278, 1), (key346, 1), (key277, 1)]

def rawRow8257 : Integer.Sparse Key := [(key435, -2), (key445, -2), (key453, -2), (key248, -2), (key263, -2), (key316, -2), (key661, -2), (key331, -2), (key662, -2), (key253, -2), (key321, -2), (key660, -2), (key385, 1), (key400, 1), (key406, 1), (key488, 1), (key421, 1), (key489, 1), (key248, 1), (key263, 1), (key316, 1), (key661, 1), (key331, 1), (key662, 1), (key236, 1), (key278, 1), (key302, 1), (key347, 1), (key656, 1), (key658, 1), (key241, 1), (key263, 1), (key307, 1), (key331, 1), (key400, 1), (key421, 1)]

def rawRow8258 : Integer.Sparse Key := [(key445, -2), (key435, -2), (key453, -2), (key263, -2), (key248, -2), (key661, -2), (key316, -2), (key662, -2), (key331, -2), (key253, -2), (key660, -2), (key321, -2), (key400, 1), (key385, 1), (key488, 1), (key406, 1), (key489, 1), (key421, 1), (key263, 1), (key248, 1), (key661, 1), (key316, 1), (key662, 1), (key331, 1), (key278, 1), (key236, 1), (key347, 1), (key302, 1), (key658, 1), (key656, 1), (key263, 1), (key241, 1), (key331, 1), (key307, 1), (key421, 1), (key400, 1)]

def rawRow8259 : Integer.Sparse Key := [(key435, -2), (key453, -2), (key445, -2), (key316, -2), (key331, -2), (key248, -2), (key662, -2), (key263, -2), (key661, -2), (key321, -2), (key253, -2), (key660, -2), (key406, 1), (key421, 1), (key385, 1), (key489, 1), (key400, 1), (key488, 1), (key316, 1), (key331, 1), (key248, 1), (key662, 1), (key263, 1), (key661, 1), (key302, 1), (key347, 1), (key236, 1), (key658, 1), (key278, 1), (key347, 1), (key307, 1), (key400, 1), (key241, 1), (key421, 1), (key263, 1), (key331, 1)]

def rawRow8260 : Integer.Sparse Key := [(key453, -2), (key435, -2), (key445, -2), (key331, -2), (key316, -2), (key662, -2), (key248, -2), (key661, -2), (key263, -2), (key321, -2), (key660, -2), (key253, -2), (key421, 1), (key406, 1), (key489, 1), (key385, 1), (key488, 1), (key400, 1), (key331, 1), (key316, 1), (key662, 1), (key248, 1), (key661, 1), (key263, 1), (key347, 1), (key302, 1), (key658, 1), (key236, 1), (key347, 1), (key278, 1), (key400, 1), (key307, 1), (key421, 1), (key241, 1), (key331, 1), (key263, 1)]

def rawRow8261 : Integer.Sparse Key := [(key445, -2), (key453, -2), (key435, -2), (key661, -2), (key662, -2), (key263, -2), (key331, -2), (key248, -2), (key316, -2), (key660, -2), (key253, -2), (key321, -2), (key488, 1), (key489, 1), (key400, 1), (key421, 1), (key385, 1), (key406, 1), (key661, 1), (key662, 1), (key263, 1), (key331, 1), (key248, 1), (key316, 1), (key656, 1), (key658, 1), (key278, 1), (key347, 1), (key236, 1), (key302, 1), (key331, 1), (key421, 1), (key263, 1), (key400, 1), (key241, 1), (key307, 1)]

def rawRow8262 : Integer.Sparse Key := [(key453, -2), (key445, -2), (key435, -2), (key662, -2), (key661, -2), (key331, -2), (key263, -2), (key316, -2), (key248, -2), (key660, -2), (key321, -2), (key253, -2), (key489, 1), (key488, 1), (key421, 1), (key400, 1), (key406, 1), (key385, 1), (key662, 1), (key661, 1), (key331, 1), (key263, 1), (key316, 1), (key248, 1), (key658, 1), (key656, 1), (key347, 1), (key278, 1), (key302, 1), (key236, 1), (key421, 1), (key331, 1), (key400, 1), (key263, 1), (key307, 1), (key241, 1)]

def rawRow8263 : Integer.Sparse Key := [(key660, -2), (key661, -2), (key662, -2), (key253, -2), (key263, -2), (key321, -2), (key445, -2), (key331, -2), (key453, -2), (key248, -2), (key316, -2), (key435, -2), (key655, 1), (key656, 1), (key657, 1), (key661, 1), (key658, 1), (key662, 1), (key277, 1), (key278, 1), (key346, 1), (key488, 1), (key347, 1), (key489, 1), (key241, 1), (key263, 1), (key307, 1), (key400, 1), (key331, 1), (key421, 1), (key236, 1), (key248, 1), (key302, 1), (key316, 1), (key385, 1), (key406, 1)]

def rawRow8264 : Integer.Sparse Key := [(key661, -2), (key660, -2), (key662, -2), (key263, -2), (key253, -2), (key445, -2), (key321, -2), (key453, -2), (key331, -2), (key248, -2), (key435, -2), (key316, -2), (key656, 1), (key655, 1), (key661, 1), (key657, 1), (key662, 1), (key658, 1), (key278, 1), (key277, 1), (key488, 1), (key346, 1), (key489, 1), (key347, 1), (key263, 1), (key241, 1), (key400, 1), (key307, 1), (key421, 1), (key331, 1), (key248, 1), (key236, 1), (key316, 1), (key302, 1), (key406, 1), (key385, 1)]

def rawRow8265 : Integer.Sparse Key := [(key660, -2), (key662, -2), (key661, -2), (key321, -2), (key331, -2), (key253, -2), (key453, -2), (key263, -2), (key445, -2), (key316, -2), (key248, -2), (key435, -2), (key657, 1), (key658, 1), (key655, 1), (key662, 1), (key656, 1), (key661, 1), (key346, 1), (key347, 1), (key277, 1), (key489, 1), (key278, 1), (key488, 1), (key307, 1), (key331, 1), (key241, 1), (key421, 1), (key263, 1), (key400, 1), (key302, 1), (key316, 1), (key236, 1), (key406, 1), (key248, 1), (key316, 1)]

def rawRow8266 : Integer.Sparse Key := [(key662, -2), (key660, -2), (key661, -2), (key331, -2), (key321, -2), (key453, -2), (key253, -2), (key445, -2), (key263, -2), (key316, -2), (key435, -2), (key248, -2), (key658, 1), (key657, 1), (key662, 1), (key655, 1), (key661, 1), (key656, 1), (key347, 1), (key346, 1), (key489, 1), (key277, 1), (key488, 1), (key278, 1), (key331, 1), (key307, 1), (key421, 1), (key241, 1), (key400, 1), (key263, 1), (key316, 1), (key302, 1), (key406, 1), (key236, 1), (key316, 1), (key248, 1)]

def rawRow8267 : Integer.Sparse Key := [(key661, -2), (key662, -2), (key660, -2), (key445, -2), (key453, -2), (key263, -2), (key331, -2), (key253, -2), (key321, -2), (key435, -2), (key248, -2), (key316, -2), (key661, 1), (key662, 1), (key656, 1), (key658, 1), (key655, 1), (key657, 1), (key488, 1), (key489, 1), (key278, 1), (key347, 1), (key277, 1), (key346, 1), (key400, 1), (key421, 1), (key263, 1), (key331, 1), (key241, 1), (key307, 1), (key385, 1), (key406, 1), (key248, 1), (key316, 1), (key236, 1), (key302, 1)]

def rawRow8268 : Integer.Sparse Key := [(key662, -2), (key661, -2), (key660, -2), (key453, -2), (key445, -2), (key331, -2), (key263, -2), (key321, -2), (key253, -2), (key435, -2), (key316, -2), (key248, -2), (key662, 1), (key661, 1), (key658, 1), (key656, 1), (key657, 1), (key655, 1), (key489, 1), (key488, 1), (key347, 1), (key278, 1), (key346, 1), (key277, 1), (key421, 1), (key400, 1), (key331, 1), (key263, 1), (key307, 1), (key241, 1), (key406, 1), (key385, 1), (key316, 1), (key248, 1), (key302, 1), (key236, 1)]

def rawRow8269 : Integer.Sparse Key := [(key2383, 2), (key2394, 2), (key2394, 2), (key2411, 2), (key2484, 2), (key2484, 2), (key2443, 2), (key2443, 2), (key2509, 2), (key2509, 2), (key2524, 2), (key2524, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2503, -2)]

def rawRow8270 : Integer.Sparse Key := [(key2394, 2), (key2383, 2), (key2394, 2), (key2484, 2), (key2411, 2), (key2484, 2), (key2509, 2), (key2524, 2), (key2443, 2), (key2524, 2), (key2443, 2), (key2509, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, -2), (key2437, -2), (key2503, -2)]

def rawRow8271 : Integer.Sparse Key := [(key2394, 2), (key2394, 2), (key2383, 2), (key2484, 2), (key2484, 2), (key2411, 2), (key2524, 2), (key2509, 2), (key2524, 2), (key2443, 2), (key2509, 2), (key2443, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, -2), (key2503, -2), (key2437, -2)]

def rawRow8272 : Integer.Sparse Key := [(key2411, 2), (key2443, 2), (key2443, 2), (key2383, 2), (key2509, 2), (key2509, 2), (key2394, 2), (key2394, 2), (key2484, 2), (key2484, 2), (key2524, 2), (key2524, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2480, -2)]

def rawRow8273 : Integer.Sparse Key := [(key2443, 2), (key2411, 2), (key2443, 2), (key2509, 2), (key2383, 2), (key2509, 2), (key2484, 2), (key2524, 2), (key2394, 2), (key2524, 2), (key2394, 2), (key2484, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, -2), (key2390, -2), (key2480, -2)]

def rawRow8274 : Integer.Sparse Key := [(key2443, 2), (key2443, 2), (key2411, 2), (key2509, 2), (key2509, 2), (key2383, 2), (key2524, 2), (key2484, 2), (key2524, 2), (key2394, 2), (key2484, 2), (key2394, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, -2), (key2480, -2), (key2390, -2)]

def rawRow8275 : Integer.Sparse Key := [(key2484, 2), (key2509, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2524, 2), (key2383, 2), (key2394, 2), (key2411, 2), (key2484, 2), (key2443, 2), (key2509, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, -2), (key2406, -2), (key2472, -2)]

def rawRow8276 : Integer.Sparse Key := [(key2484, 2), (key2524, 2), (key2509, 2), (key2394, 2), (key2524, 2), (key2443, 2), (key2394, 2), (key2383, 2), (key2484, 2), (key2411, 2), (key2509, 2), (key2443, 2), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, -2), (key2472, -2), (key2406, -2)]

def rawRow8277 : Integer.Sparse Key := [(key2509, 2), (key2484, 2), (key2524, 2), (key2443, 2), (key2394, 2), (key2524, 2), (key2411, 2), (key2443, 2), (key2383, 2), (key2509, 2), (key2394, 2), (key2484, 2), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, -2), (key2378, -2), (key2472, -2)]

def rawRow8278 : Integer.Sparse Key := [(key2509, 2), (key2524, 2), (key2484, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2411, 2), (key2509, 2), (key2383, 2), (key2484, 2), (key2394, 2), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, -2), (key2472, -2), (key2378, -2)]

def rawRow8279 : Integer.Sparse Key := [(key2524, 2), (key2484, 2), (key2509, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2484, 2), (key2509, 2), (key2394, 2), (key2443, 2), (key2383, 2), (key2411, 2), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, -2), (key2378, -2), (key2406, -2)]

def rawRow8280 : Integer.Sparse Key := [(key2524, 2), (key2509, 2), (key2484, 2), (key2524, 2), (key2443, 2), (key2394, 2), (key2509, 2), (key2484, 2), (key2443, 2), (key2394, 2), (key2411, 2), (key2383, 2), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, -2), (key2406, -2), (key2378, -2)]

def rawRow8281 : Integer.Sparse Key := [(key1230, -24), (key991, 6), (key1026, 6), (key1104, 6), (key1104, 6)]

def rawRow8282 : Integer.Sparse Key := [(key1230, -24), (key991, 6), (key1104, 6), (key1026, 6), (key1104, 6)]

def rawRow8283 : Integer.Sparse Key := [(key1230, -24), (key991, 6), (key1104, 6), (key1104, 6), (key1026, 6)]

def rawRow8284 : Integer.Sparse Key := [(key1230, -24), (key1026, 6), (key991, 6), (key1104, 6), (key1104, 6)]

def rawRow8285 : Integer.Sparse Key := [(key1230, -24), (key1026, 6), (key1104, 6), (key991, 6), (key1104, 6)]

def rawRow8286 : Integer.Sparse Key := [(key1230, -24), (key1026, 6), (key1104, 6), (key1104, 6), (key991, 6)]

def rawRow8287 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key991, 6), (key1026, 6), (key1104, 6)]

def rawRow8288 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key991, 6), (key1104, 6), (key1026, 6)]

def rawRow8289 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1026, 6), (key991, 6), (key1104, 6)]

def rawRow8290 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1026, 6), (key1104, 6), (key991, 6)]

def rawRow8291 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1104, 6), (key991, 6), (key1026, 6)]

def rawRow8292 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1104, 6), (key1026, 6), (key991, 6)]

def rawRow8293 : Integer.Sparse Key := [(key1232, -6), (key1232, -6), (key1235, -6), (key1242, -6), (key1001, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key1150, 2)]

def rawRow8294 : Integer.Sparse Key := [(key1232, -6), (key1235, -6), (key1232, -6), (key1242, -6), (key1001, 2), (key1015, 2), (key1001, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1071, 2), (key1150, 2)]

def rawRow8295 : Integer.Sparse Key := [(key1235, -6), (key1232, -6), (key1232, -6), (key1242, -6), (key1015, 2), (key1001, 2), (key1001, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1150, 2), (key1150, 2), (key1071, 2)]

def rawRow8296 : Integer.Sparse Key := [(key1232, -6), (key1232, -6), (key1242, -6), (key1235, -6), (key1036, 2), (key1036, 2), (key1071, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1150, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1123, 2)]

def rawRow8297 : Integer.Sparse Key := [(key1232, -6), (key1242, -6), (key1232, -6), (key1235, -6), (key1036, 2), (key1071, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1123, 2), (key1015, 2), (key1123, 2)]

def rawRow8298 : Integer.Sparse Key := [(key1242, -6), (key1232, -6), (key1232, -6), (key1235, -6), (key1071, 2), (key1036, 2), (key1036, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1123, 2), (key1123, 2), (key1015, 2)]

def rawRow8299 : Integer.Sparse Key := [(key1232, -6), (key1235, -6), (key1242, -6), (key1232, -6), (key1114, 2), (key1123, 2), (key1150, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key1001, 2), (key1036, 2), (key1114, 2)]

def rawRow8300 : Integer.Sparse Key := [(key1235, -6), (key1232, -6), (key1242, -6), (key1232, -6), (key1123, 2), (key1114, 2), (key1150, 2), (key1015, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1071, 2), (key1001, 2), (key1114, 2), (key1036, 2)]

def rawRow8301 : Integer.Sparse Key := [(key1232, -6), (key1242, -6), (key1235, -6), (key1232, -6), (key1114, 2), (key1150, 2), (key1123, 2), (key1036, 2), (key1071, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1001, 2), (key1114, 2)]

def rawRow8302 : Integer.Sparse Key := [(key1242, -6), (key1232, -6), (key1235, -6), (key1232, -6), (key1150, 2), (key1114, 2), (key1123, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1015, 2), (key1036, 2), (key1114, 2), (key1001, 2)]

def rawRow8303 : Integer.Sparse Key := [(key1235, -6), (key1242, -6), (key1232, -6), (key1232, -6), (key1123, 2), (key1150, 2), (key1114, 2), (key1123, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1001, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1036, 2)]

def rawRow8304 : Integer.Sparse Key := [(key1242, -6), (key1235, -6), (key1232, -6), (key1232, -6), (key1150, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1071, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1114, 2), (key1036, 2), (key1001, 2)]

def rawRow8305 : Integer.Sparse Key := [(key2635, -6), (key2789, -6), (key2855, -6), (key2855, -6), (key2610, 2), (key2626, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

def rawRow8306 : Integer.Sparse Key := [(key2635, -6), (key2855, -6), (key2789, -6), (key2855, -6), (key2626, 2), (key2610, 2), (key2626, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

def rawRow8307 : Integer.Sparse Key := [(key2635, -6), (key2855, -6), (key2855, -6), (key2789, -6), (key2626, 2), (key2626, 2), (key2610, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

def rawRow8308 : Integer.Sparse Key := [(key2789, -6), (key2635, -6), (key2855, -6), (key2855, -6), (key2665, 2), (key2780, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2626, 2), (key2626, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2)]

def rawRow8309 : Integer.Sparse Key := [(key2789, -6), (key2855, -6), (key2635, -6), (key2855, -6), (key2780, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2700, 2)]

def rawRow8310 : Integer.Sparse Key := [(key2789, -6), (key2855, -6), (key2855, -6), (key2635, -6), (key2780, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2626, 2)]

def rawRow8311 : Integer.Sparse Key := [(key2855, -6), (key2635, -6), (key2789, -6), (key2855, -6), (key2700, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2853, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2780, 2), (key2803, 2)]

def rawRow8312 : Integer.Sparse Key := [(key2855, -6), (key2635, -6), (key2855, -6), (key2789, -6), (key2700, 2), (key2853, 2), (key2803, 2), (key2626, 2), (key2853, 2), (key2780, 2), (key2626, 2), (key2610, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2780, 2)]

def rawRow8313 : Integer.Sparse Key := [(key2855, -6), (key2789, -6), (key2635, -6), (key2855, -6), (key2803, 2), (key2700, 2), (key2853, 2), (key2780, 2), (key2626, 2), (key2853, 2), (key2665, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2700, 2)]

def rawRow8314 : Integer.Sparse Key := [(key2855, -6), (key2789, -6), (key2855, -6), (key2635, -6), (key2803, 2), (key2853, 2), (key2700, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2700, 2), (key2626, 2)]

def rawRow8315 : Integer.Sparse Key := [(key2855, -6), (key2855, -6), (key2635, -6), (key2789, -6), (key2853, 2), (key2700, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2700, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2610, 2), (key2665, 2)]

def rawRow8316 : Integer.Sparse Key := [(key2855, -6), (key2855, -6), (key2789, -6), (key2635, -6), (key2853, 2), (key2803, 2), (key2700, 2), (key2853, 2), (key2780, 2), (key2626, 2), (key2803, 2), (key2700, 2), (key2780, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

def rawRow8317 : Integer.Sparse Key := [(key2568, -6), (key2568, -6), (key2570, -6), (key2575, -6), (key2376, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2404, 2), (key2470, 2), (key2470, 2), (key2478, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2501, 2)]

def rawRow8318 : Integer.Sparse Key := [(key2568, -6), (key2570, -6), (key2568, -6), (key2575, -6), (key2376, 2), (key2388, 2), (key2376, 2), (key2470, 2), (key2478, 2), (key2404, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2501, 2), (key2435, 2), (key2501, 2)]

def rawRow8319 : Integer.Sparse Key := [(key2570, -6), (key2568, -6), (key2568, -6), (key2575, -6), (key2388, 2), (key2376, 2), (key2376, 2), (key2478, 2), (key2470, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2404, 2), (key2501, 2), (key2501, 2), (key2435, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8320 : Integer.Sparse Key := [(key2568, -6), (key2568, -6), (key2575, -6), (key2570, -6), (key2404, 2), (key2404, 2), (key2435, 2), (key2376, 2), (key2376, 2), (key2470, 2), (key2470, 2), (key2501, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2478, 2)]

def rawRow8321 : Integer.Sparse Key := [(key2568, -6), (key2575, -6), (key2568, -6), (key2570, -6), (key2404, 2), (key2435, 2), (key2404, 2), (key2470, 2), (key2501, 2), (key2376, 2), (key2501, 2), (key2376, 2), (key2470, 2), (key2478, 2), (key2388, 2), (key2478, 2)]

def rawRow8322 : Integer.Sparse Key := [(key2575, -6), (key2568, -6), (key2568, -6), (key2570, -6), (key2435, 2), (key2404, 2), (key2404, 2), (key2501, 2), (key2470, 2), (key2501, 2), (key2376, 2), (key2470, 2), (key2376, 2), (key2478, 2), (key2478, 2), (key2388, 2)]

def rawRow8323 : Integer.Sparse Key := [(key2568, -6), (key2570, -6), (key2575, -6), (key2568, -6), (key2470, 2), (key2478, 2), (key2501, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2376, 2), (key2404, 2), (key2470, 2)]

def rawRow8324 : Integer.Sparse Key := [(key2570, -6), (key2568, -6), (key2575, -6), (key2568, -6), (key2478, 2), (key2470, 2), (key2501, 2), (key2388, 2), (key2376, 2), (key2478, 2), (key2404, 2), (key2501, 2), (key2435, 2), (key2376, 2), (key2470, 2), (key2404, 2)]

def rawRow8325 : Integer.Sparse Key := [(key2568, -6), (key2575, -6), (key2570, -6), (key2568, -6), (key2470, 2), (key2501, 2), (key2478, 2), (key2404, 2), (key2435, 2), (key2376, 2), (key2501, 2), (key2388, 2), (key2478, 2), (key2404, 2), (key2376, 2), (key2470, 2)]

def rawRow8326 : Integer.Sparse Key := [(key2575, -6), (key2568, -6), (key2570, -6), (key2568, -6), (key2501, 2), (key2470, 2), (key2478, 2), (key2435, 2), (key2404, 2), (key2501, 2), (key2376, 2), (key2478, 2), (key2388, 2), (key2404, 2), (key2470, 2), (key2376, 2)]

def rawRow8327 : Integer.Sparse Key := [(key2570, -6), (key2575, -6), (key2568, -6), (key2568, -6), (key2478, 2), (key2501, 2), (key2470, 2), (key2478, 2), (key2501, 2), (key2388, 2), (key2435, 2), (key2376, 2), (key2404, 2), (key2470, 2), (key2376, 2), (key2404, 2)]

def rawRow8328 : Integer.Sparse Key := [(key2575, -6), (key2570, -6), (key2568, -6), (key2568, -6), (key2501, 2), (key2478, 2), (key2470, 2), (key2501, 2), (key2478, 2), (key2435, 2), (key2388, 2), (key2404, 2), (key2376, 2), (key2470, 2), (key2404, 2), (key2376, 2)]

def rawRow8329 : Integer.Sparse Key := [(key2657, -2), (key2657, -2), (key2659, -2), (key2752, -2), (key2752, -2), (key2918, -2), (key2918, -2), (key2919, -2), (key2919, -2), (key2757, -2), (key2922, -2), (key2922, -2), (key2614, 1), (key2614, 1), (key2630, 1), (key2630, 1), (key2638, 1), (key2638, 1), (key2669, 1), (key2669, 1), (key2784, 1), (key2784, 1), (key2792, 1), (key2792, 1), (key2704, 1), (key2704, 1), (key2807, 1), (key2807, 1), (key2858, 1), (key2858, 1), (key2724, 1), (key2724, 1), (key2827, 1), (key2827, 1), (key2868, 1), (key2868, 1)]

def rawRow8330 : Integer.Sparse Key := [(key2657, -2), (key2659, -2), (key2657, -2), (key2918, -2), (key2919, -2), (key2752, -2), (key2919, -2), (key2752, -2), (key2918, -2), (key2922, -2), (key2757, -2), (key2922, -2), (key2630, 1), (key2638, 1), (key2614, 1), (key2638, 1), (key2614, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2807, 1), (key2858, 1), (key2704, 1), (key2858, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2868, 1), (key2724, 1), (key2868, 1), (key2724, 1), (key2827, 1)]

def rawRow8331 : Integer.Sparse Key := [(key2659, -2), (key2657, -2), (key2657, -2), (key2919, -2), (key2918, -2), (key2919, -2), (key2752, -2), (key2918, -2), (key2752, -2), (key2922, -2), (key2922, -2), (key2757, -2), (key2638, 1), (key2630, 1), (key2638, 1), (key2614, 1), (key2630, 1), (key2614, 1), (key2792, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2669, 1), (key2858, 1), (key2807, 1), (key2858, 1), (key2704, 1), (key2807, 1), (key2704, 1), (key2868, 1), (key2827, 1), (key2868, 1), (key2724, 1), (key2827, 1), (key2724, 1)]

def rawRow8332 : Integer.Sparse Key := [(key2752, -2), (key2752, -2), (key2757, -2), (key2657, -2), (key2657, -2), (key2918, -2), (key2918, -2), (key2922, -2), (key2922, -2), (key2659, -2), (key2919, -2), (key2919, -2), (key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2724, 1), (key2724, 1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2630, 1), (key2630, 1), (key2784, 1), (key2784, 1), (key2868, 1), (key2868, 1), (key2638, 1), (key2638, 1), (key2792, 1), (key2792, 1), (key2858, 1), (key2858, 1)]

def rawRow8333 : Integer.Sparse Key := [(key2752, -2), (key2757, -2), (key2752, -2), (key2918, -2), (key2922, -2), (key2657, -2), (key2922, -2), (key2657, -2), (key2918, -2), (key2919, -2), (key2659, -2), (key2919, -2), (key2704, 1), (key2724, 1), (key2669, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2784, 1), (key2868, 1), (key2630, 1), (key2868, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2858, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2792, 1)]

def rawRow8334 : Integer.Sparse Key := [(key2757, -2), (key2752, -2), (key2752, -2), (key2922, -2), (key2918, -2), (key2922, -2), (key2657, -2), (key2918, -2), (key2657, -2), (key2919, -2), (key2919, -2), (key2659, -2), (key2724, 1), (key2704, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2868, 1), (key2784, 1), (key2868, 1), (key2630, 1), (key2784, 1), (key2630, 1), (key2858, 1), (key2792, 1), (key2858, 1), (key2638, 1), (key2792, 1), (key2638, 1)]

def rawRow8335 : Integer.Sparse Key := [(key2918, -2), (key2919, -2), (key2922, -2), (key2657, -2), (key2659, -2), (key2752, -2), (key2919, -2), (key2757, -2), (key2922, -2), (key2657, -2), (key2752, -2), (key2918, -2), (key2784, 1), (key2792, 1), (key2807, 1), (key2858, 1), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2792, 1), (key2724, 1), (key2827, 1), (key2614, 1), (key2630, 1), (key2669, 1), (key2784, 1), (key2704, 1), (key2807, 1)]

def rawRow8336 : Integer.Sparse Key := [(key2919, -2), (key2918, -2), (key2922, -2), (key2659, -2), (key2657, -2), (key2919, -2), (key2752, -2), (key2922, -2), (key2757, -2), (key2657, -2), (key2918, -2), (key2752, -2), (key2792, 1), (key2784, 1), (key2858, 1), (key2807, 1), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1), (key2638, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2724, 1), (key2630, 1), (key2614, 1), (key2784, 1), (key2669, 1), (key2807, 1), (key2704, 1)]

def rawRow8337 : Integer.Sparse Key := [(key2918, -2), (key2922, -2), (key2919, -2), (key2752, -2), (key2757, -2), (key2657, -2), (key2922, -2), (key2659, -2), (key2919, -2), (key2752, -2), (key2657, -2), (key2918, -2), (key2807, 1), (key2827, 1), (key2784, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2669, 1), (key2724, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2669, 1), (key2704, 1), (key2614, 1), (key2807, 1), (key2630, 1), (key2784, 1)]

def rawRow8338 : Integer.Sparse Key := [(key2922, -2), (key2918, -2), (key2919, -2), (key2757, -2), (key2752, -2), (key2922, -2), (key2657, -2), (key2919, -2), (key2659, -2), (key2752, -2), (key2918, -2), (key2657, -2), (key2827, 1), (key2807, 1), (key2868, 1), (key2784, 1), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2792, 1), (key2638, 1), (key2704, 1), (key2669, 1), (key2807, 1), (key2614, 1), (key2784, 1), (key2630, 1)]

def rawRow8339 : Integer.Sparse Key := [(key2919, -2), (key2922, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key2659, -2), (key2757, -2), (key2657, -2), (key2752, -2), (key2918, -2), (key2657, -2), (key2752, -2), (key2858, 1), (key2868, 1), (key2792, 1), (key2827, 1), (key2784, 1), (key2807, 1), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1), (key2792, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2614, 1), (key2669, 1), (key2784, 1), (key2807, 1), (key2630, 1), (key2704, 1), (key2614, 1), (key2669, 1)]

def rawRow8340 : Integer.Sparse Key := [(key2922, -2), (key2919, -2), (key2918, -2), (key2922, -2), (key2919, -2), (key2757, -2), (key2659, -2), (key2752, -2), (key2657, -2), (key2918, -2), (key2752, -2), (key2657, -2), (key2868, 1), (key2858, 1), (key2827, 1), (key2792, 1), (key2807, 1), (key2784, 1), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1), (key2827, 1), (key2792, 1), (key2724, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2807, 1), (key2784, 1), (key2704, 1), (key2630, 1), (key2669, 1), (key2614, 1)]

def rawRow8341 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2764, 6), (key2841, 6), (key2873, 6)]

def rawRow8342 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2764, 6), (key2873, 6), (key2841, 6)]

def rawRow8343 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2841, 6), (key2764, 6), (key2873, 6)]

def rawRow8344 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2841, 6), (key2873, 6), (key2764, 6)]

def rawRow8345 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2873, 6), (key2764, 6), (key2841, 6)]

def rawRow8346 : Integer.Sparse Key := [(key2841, -24), (key2585, 6), (key2873, 6), (key2841, 6), (key2764, 6)]

def rawRow8347 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2585, 6), (key2841, 6), (key2873, 6)]

def rawRow8348 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2585, 6), (key2873, 6), (key2841, 6)]

def rawRow8349 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2841, 6), (key2585, 6), (key2873, 6)]

def rawRow8350 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2841, 6), (key2873, 6), (key2585, 6)]

def rawRow8351 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2873, 6), (key2585, 6), (key2841, 6)]

def rawRow8352 : Integer.Sparse Key := [(key2841, -24), (key2764, 6), (key2873, 6), (key2841, 6), (key2585, 6)]

def rawRow8353 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2585, 6), (key2764, 6), (key2873, 6)]

def rawRow8354 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2585, 6), (key2873, 6), (key2764, 6)]

def rawRow8355 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2764, 6), (key2585, 6), (key2873, 6)]

def rawRow8356 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2764, 6), (key2873, 6), (key2585, 6)]

def rawRow8357 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2873, 6), (key2585, 6), (key2764, 6)]

def rawRow8358 : Integer.Sparse Key := [(key2841, -24), (key2841, 6), (key2873, 6), (key2764, 6), (key2585, 6)]

def rawRow8359 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2585, 6), (key2764, 6), (key2841, 6)]

def rawRow8360 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2585, 6), (key2841, 6), (key2764, 6)]

def rawRow8361 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2764, 6), (key2585, 6), (key2841, 6)]

def rawRow8362 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2764, 6), (key2841, 6), (key2585, 6)]

def rawRow8363 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2841, 6), (key2585, 6), (key2764, 6)]

def rawRow8364 : Integer.Sparse Key := [(key2841, -24), (key2873, 6), (key2841, 6), (key2764, 6), (key2585, 6)]

def rawRow8365 : Integer.Sparse Key := [(key2873, -24), (key2585, 6), (key2764, 6), (key2841, 6), (key2841, 6)]

def rawRow8366 : Integer.Sparse Key := [(key2873, -24), (key2585, 6), (key2841, 6), (key2764, 6), (key2841, 6)]

def rawRow8367 : Integer.Sparse Key := [(key2873, -24), (key2585, 6), (key2841, 6), (key2841, 6), (key2764, 6)]

def rawRow8368 : Integer.Sparse Key := [(key2873, -24), (key2764, 6), (key2585, 6), (key2841, 6), (key2841, 6)]

def rawRow8369 : Integer.Sparse Key := [(key2873, -24), (key2764, 6), (key2841, 6), (key2585, 6), (key2841, 6)]

def rawRow8370 : Integer.Sparse Key := [(key2873, -24), (key2764, 6), (key2841, 6), (key2841, 6), (key2585, 6)]

def rawRow8371 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2585, 6), (key2764, 6), (key2841, 6)]

def rawRow8372 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2585, 6), (key2841, 6), (key2764, 6)]

def rawRow8373 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2764, 6), (key2585, 6), (key2841, 6)]

def rawRow8374 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2764, 6), (key2841, 6), (key2585, 6)]

def rawRow8375 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2841, 6), (key2585, 6), (key2764, 6)]

def rawRow8376 : Integer.Sparse Key := [(key2873, -24), (key2841, 6), (key2841, 6), (key2764, 6), (key2585, 6)]

def rawRow8377 : Integer.Sparse Key := [(key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2851, -2), (key2918, -2), (key2858, -2), (key2919, -2), (key2827, -2), (key2868, -2), (key2922, -2), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2851, 2), (key3021, 2), (key2858, 2), (key3022, 2), (key2724, 2), (key2868, 2), (key3025, 2)]

def rawRow8378 : Integer.Sparse Key := [(key2784, -2), (key2778, -2), (key2792, -2), (key2807, -2), (key2801, -2), (key2918, -2), (key2851, -2), (key2919, -2), (key2858, -2), (key2827, -2), (key2922, -2), (key2868, -2), (key2630, 2), (key2624, 2), (key2638, 2), (key2704, 2), (key2698, 2), (key3021, 2), (key2851, 2), (key3022, 2), (key2858, 2), (key2724, 2), (key3025, 2), (key2868, 2)]

def rawRow8379 : Integer.Sparse Key := [(key2778, -2), (key2792, -2), (key2784, -2), (key2851, -2), (key2858, -2), (key2801, -2), (key2919, -2), (key2807, -2), (key2918, -2), (key2868, -2), (key2827, -2), (key2922, -2), (key2624, 2), (key2638, 2), (key2630, 2), (key2851, 2), (key2858, 2), (key2698, 2), (key3022, 2), (key2704, 2), (key3021, 2), (key2868, 2), (key2724, 2), (key3025, 2)]

def rawRow8380 : Integer.Sparse Key := [(key2792, -2), (key2778, -2), (key2784, -2), (key2858, -2), (key2851, -2), (key2919, -2), (key2801, -2), (key2918, -2), (key2807, -2), (key2868, -2), (key2922, -2), (key2827, -2), (key2638, 2), (key2624, 2), (key2630, 2), (key2858, 2), (key2851, 2), (key3022, 2), (key2698, 2), (key3021, 2), (key2704, 2), (key2868, 2), (key3025, 2), (key2724, 2)]

def rawRow8381 : Integer.Sparse Key := [(key2784, -2), (key2792, -2), (key2778, -2), (key2918, -2), (key2919, -2), (key2807, -2), (key2858, -2), (key2801, -2), (key2851, -2), (key2922, -2), (key2827, -2), (key2868, -2), (key2630, 2), (key2638, 2), (key2624, 2), (key3021, 2), (key3022, 2), (key2704, 2), (key2858, 2), (key2698, 2), (key2851, 2), (key3025, 2), (key2724, 2), (key2868, 2)]

def rawRow8382 : Integer.Sparse Key := [(key2792, -2), (key2784, -2), (key2778, -2), (key2919, -2), (key2918, -2), (key2858, -2), (key2807, -2), (key2851, -2), (key2801, -2), (key2922, -2), (key2868, -2), (key2827, -2), (key2638, 2), (key2630, 2), (key2624, 2), (key3022, 2), (key3021, 2), (key2858, 2), (key2704, 2), (key2851, 2), (key2698, 2), (key3025, 2), (key2868, 2), (key2724, 2)]

def rawRow8383 : Integer.Sparse Key := [(key2801, -2), (key2807, -2), (key2827, -2), (key2778, -2), (key2784, -2), (key2851, -2), (key2918, -2), (key2868, -2), (key2922, -2), (key2792, -2), (key2858, -2), (key2919, -2), (key2698, 2), (key2704, 2), (key2724, 2), (key2624, 2), (key2630, 2), (key2851, 2), (key3021, 2), (key2868, 2), (key3025, 2), (key2638, 2), (key2858, 2), (key3022, 2)]

def rawRow8384 : Integer.Sparse Key := [(key2807, -2), (key2801, -2), (key2827, -2), (key2784, -2), (key2778, -2), (key2918, -2), (key2851, -2), (key2922, -2), (key2868, -2), (key2792, -2), (key2919, -2), (key2858, -2), (key2704, 2), (key2698, 2), (key2724, 2), (key2630, 2), (key2624, 2), (key3021, 2), (key2851, 2), (key3025, 2), (key2868, 2), (key2638, 2), (key3022, 2), (key2858, 2)]

def rawRow8385 : Integer.Sparse Key := [(key2801, -2), (key2827, -2), (key2807, -2), (key2851, -2), (key2868, -2), (key2778, -2), (key2922, -2), (key2784, -2), (key2918, -2), (key2858, -2), (key2792, -2), (key2919, -2), (key2698, 2), (key2724, 2), (key2704, 2), (key2851, 2), (key2868, 2), (key2624, 2), (key3025, 2), (key2630, 2), (key3021, 2), (key2858, 2), (key2638, 2), (key3022, 2)]

def rawRow8386 : Integer.Sparse Key := [(key2827, -2), (key2801, -2), (key2807, -2), (key2868, -2), (key2851, -2), (key2922, -2), (key2778, -2), (key2918, -2), (key2784, -2), (key2858, -2), (key2919, -2), (key2792, -2), (key2724, 2), (key2698, 2), (key2704, 2), (key2868, 2), (key2851, 2), (key3025, 2), (key2624, 2), (key3021, 2), (key2630, 2), (key2858, 2), (key3022, 2), (key2638, 2)]

def rawRow8387 : Integer.Sparse Key := [(key2807, -2), (key2827, -2), (key2801, -2), (key2918, -2), (key2922, -2), (key2784, -2), (key2868, -2), (key2778, -2), (key2851, -2), (key2919, -2), (key2792, -2), (key2858, -2), (key2704, 2), (key2724, 2), (key2698, 2), (key3021, 2), (key3025, 2), (key2630, 2), (key2868, 2), (key2624, 2), (key2851, 2), (key3022, 2), (key2638, 2), (key2858, 2)]

def rawRow8388 : Integer.Sparse Key := [(key2827, -2), (key2807, -2), (key2801, -2), (key2922, -2), (key2918, -2), (key2868, -2), (key2784, -2), (key2851, -2), (key2778, -2), (key2919, -2), (key2858, -2), (key2792, -2), (key2724, 2), (key2704, 2), (key2698, 2), (key3025, 2), (key3021, 2), (key2868, 2), (key2630, 2), (key2851, 2), (key2624, 2), (key3022, 2), (key2858, 2), (key2638, 2)]

def rawRow8389 : Integer.Sparse Key := [(key2851, -2), (key2858, -2), (key2868, -2), (key2778, -2), (key2792, -2), (key2801, -2), (key2919, -2), (key2827, -2), (key2922, -2), (key2784, -2), (key2807, -2), (key2918, -2), (key2851, 2), (key2858, 2), (key2868, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key3022, 2), (key2724, 2), (key3025, 2), (key2630, 2), (key2704, 2), (key3021, 2)]

def rawRow8390 : Integer.Sparse Key := [(key2858, -2), (key2851, -2), (key2868, -2), (key2792, -2), (key2778, -2), (key2919, -2), (key2801, -2), (key2922, -2), (key2827, -2), (key2784, -2), (key2918, -2), (key2807, -2), (key2858, 2), (key2851, 2), (key2868, 2), (key2638, 2), (key2624, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2724, 2), (key2630, 2), (key3021, 2), (key2704, 2)]

def rawRow8391 : Integer.Sparse Key := [(key2851, -2), (key2868, -2), (key2858, -2), (key2801, -2), (key2827, -2), (key2778, -2), (key2922, -2), (key2792, -2), (key2919, -2), (key2807, -2), (key2784, -2), (key2918, -2), (key2851, 2), (key2868, 2), (key2858, 2), (key2698, 2), (key2724, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2704, 2), (key2630, 2), (key3021, 2)]

def rawRow8392 : Integer.Sparse Key := [(key2868, -2), (key2851, -2), (key2858, -2), (key2827, -2), (key2801, -2), (key2922, -2), (key2778, -2), (key2919, -2), (key2792, -2), (key2807, -2), (key2918, -2), (key2784, -2), (key2868, 2), (key2851, 2), (key2858, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key3022, 2), (key2638, 2), (key2704, 2), (key3021, 2), (key2630, 2)]

def rawRow8393 : Integer.Sparse Key := [(key2858, -2), (key2868, -2), (key2851, -2), (key2919, -2), (key2922, -2), (key2792, -2), (key2827, -2), (key2778, -2), (key2801, -2), (key2918, -2), (key2784, -2), (key2807, -2), (key2858, 2), (key2868, 2), (key2851, 2), (key3022, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2624, 2), (key2698, 2), (key3021, 2), (key2630, 2), (key2704, 2)]

def rawRow8394 : Integer.Sparse Key := [(key2868, -2), (key2858, -2), (key2851, -2), (key2922, -2), (key2919, -2), (key2827, -2), (key2792, -2), (key2801, -2), (key2778, -2), (key2918, -2), (key2807, -2), (key2784, -2), (key2868, 2), (key2858, 2), (key2851, 2), (key3025, 2), (key3022, 2), (key2724, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key3021, 2), (key2704, 2), (key2630, 2)]

def rawRow8395 : Integer.Sparse Key := [(key2918, -2), (key2919, -2), (key2922, -2), (key2784, -2), (key2792, -2), (key2807, -2), (key2858, -2), (key2827, -2), (key2868, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key3021, 2), (key3022, 2), (key3025, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2858, 2), (key2724, 2), (key2868, 2), (key2624, 2), (key2698, 2), (key2851, 2)]

def rawRow8396 : Integer.Sparse Key := [(key2919, -2), (key2918, -2), (key2922, -2), (key2792, -2), (key2784, -2), (key2858, -2), (key2807, -2), (key2868, -2), (key2827, -2), (key2778, -2), (key2851, -2), (key2801, -2), (key3022, 2), (key3021, 2), (key3025, 2), (key2638, 2), (key2630, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2724, 2), (key2624, 2), (key2851, 2), (key2698, 2)]

def rawRow8397 : Integer.Sparse Key := [(key2918, -2), (key2922, -2), (key2919, -2), (key2807, -2), (key2827, -2), (key2784, -2), (key2868, -2), (key2792, -2), (key2858, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key3021, 2), (key3025, 2), (key3022, 2), (key2704, 2), (key2724, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2698, 2), (key2624, 2), (key2851, 2)]

def rawRow8398 : Integer.Sparse Key := [(key2922, -2), (key2918, -2), (key2919, -2), (key2827, -2), (key2807, -2), (key2868, -2), (key2784, -2), (key2858, -2), (key2792, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key3025, 2), (key3021, 2), (key3022, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2858, 2), (key2638, 2), (key2698, 2), (key2851, 2), (key2624, 2)]

def rawRow8399 : Integer.Sparse Key := [(key2919, -2), (key2922, -2), (key2918, -2), (key2858, -2), (key2868, -2), (key2792, -2), (key2827, -2), (key2784, -2), (key2807, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key3022, 2), (key3025, 2), (key3021, 2), (key2858, 2), (key2868, 2), (key2638, 2), (key2724, 2), (key2630, 2), (key2704, 2), (key2851, 2), (key2624, 2), (key2698, 2)]

def rawRow8400 : Integer.Sparse Key := [(key2922, -2), (key2919, -2), (key2918, -2), (key2868, -2), (key2858, -2), (key2827, -2), (key2792, -2), (key2807, -2), (key2784, -2), (key2851, -2), (key2801, -2), (key2778, -2), (key3025, 2), (key3022, 2), (key3021, 2), (key2868, 2), (key2858, 2), (key2724, 2), (key2638, 2), (key2704, 2), (key2630, 2), (key2851, 2), (key2698, 2), (key2624, 2)]

def rawRow8401 : Integer.Sparse Key := [(key3007, -2), (key3007, -2), (key3009, -2), (key3011, -2), (key3011, -2), (key3021, -2), (key3021, -2), (key3022, -2), (key3022, -2), (key3016, -2), (key3025, -2), (key3025, -2), (key2657, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2752, 2), (key2918, 2), (key2918, 2), (key2919, 2), (key2919, 2), (key2757, 2), (key2922, 2), (key2922, 2)]

def rawRow8402 : Integer.Sparse Key := [(key3007, -2), (key3009, -2), (key3007, -2), (key3021, -2), (key3022, -2), (key3011, -2), (key3022, -2), (key3011, -2), (key3021, -2), (key3025, -2), (key3016, -2), (key3025, -2), (key2657, 2), (key2659, 2), (key2657, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2757, 2), (key2922, 2)]

def rawRow8403 : Integer.Sparse Key := [(key3009, -2), (key3007, -2), (key3007, -2), (key3022, -2), (key3021, -2), (key3022, -2), (key3011, -2), (key3021, -2), (key3011, -2), (key3025, -2), (key3025, -2), (key3016, -2), (key2659, 2), (key2657, 2), (key2657, 2), (key2919, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2752, 2), (key2922, 2), (key2922, 2), (key2757, 2)]

def rawRow8404 : Integer.Sparse Key := [(key3011, -2), (key3011, -2), (key3016, -2), (key3007, -2), (key3007, -2), (key3021, -2), (key3021, -2), (key3025, -2), (key3025, -2), (key3009, -2), (key3022, -2), (key3022, -2), (key2752, 2), (key2752, 2), (key2757, 2), (key2657, 2), (key2657, 2), (key2918, 2), (key2918, 2), (key2922, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2919, 2)]

def rawRow8405 : Integer.Sparse Key := [(key3011, -2), (key3016, -2), (key3011, -2), (key3021, -2), (key3025, -2), (key3007, -2), (key3025, -2), (key3007, -2), (key3021, -2), (key3022, -2), (key3009, -2), (key3022, -2), (key2752, 2), (key2757, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2919, 2), (key2659, 2), (key2919, 2)]

def rawRow8406 : Integer.Sparse Key := [(key3016, -2), (key3011, -2), (key3011, -2), (key3025, -2), (key3021, -2), (key3025, -2), (key3007, -2), (key3021, -2), (key3007, -2), (key3022, -2), (key3022, -2), (key3009, -2), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2657, 2), (key2919, 2), (key2919, 2), (key2659, 2)]

def rawRow8407 : Integer.Sparse Key := [(key3021, -2), (key3022, -2), (key3025, -2), (key3007, -2), (key3009, -2), (key3011, -2), (key3022, -2), (key3016, -2), (key3025, -2), (key3007, -2), (key3011, -2), (key3021, -2), (key2918, 2), (key2919, 2), (key2922, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2919, 2), (key2757, 2), (key2922, 2), (key2657, 2), (key2752, 2), (key2918, 2)]

def rawRow8408 : Integer.Sparse Key := [(key3022, -2), (key3021, -2), (key3025, -2), (key3009, -2), (key3007, -2), (key3022, -2), (key3011, -2), (key3025, -2), (key3016, -2), (key3007, -2), (key3021, -2), (key3011, -2), (key2919, 2), (key2918, 2), (key2922, 2), (key2659, 2), (key2657, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2757, 2), (key2657, 2), (key2918, 2), (key2752, 2)]

def rawRow8409 : Integer.Sparse Key := [(key3021, -2), (key3025, -2), (key3022, -2), (key3011, -2), (key3016, -2), (key3007, -2), (key3025, -2), (key3009, -2), (key3022, -2), (key3011, -2), (key3007, -2), (key3021, -2), (key2918, 2), (key2922, 2), (key2919, 2), (key2752, 2), (key2757, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2752, 2), (key2657, 2), (key2918, 2)]

def rawRow8410 : Integer.Sparse Key := [(key3025, -2), (key3021, -2), (key3022, -2), (key3016, -2), (key3011, -2), (key3025, -2), (key3007, -2), (key3022, -2), (key3009, -2), (key3011, -2), (key3021, -2), (key3007, -2), (key2922, 2), (key2918, 2), (key2919, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2919, 2), (key2659, 2), (key2752, 2), (key2918, 2), (key2657, 2)]

def rawRow8411 : Integer.Sparse Key := [(key3022, -2), (key3025, -2), (key3021, -2), (key3022, -2), (key3025, -2), (key3009, -2), (key3016, -2), (key3007, -2), (key3011, -2), (key3021, -2), (key3007, -2), (key3011, -2), (key2919, 2), (key2922, 2), (key2918, 2), (key2919, 2), (key2922, 2), (key2659, 2), (key2757, 2), (key2657, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2752, 2)]

def rawRow8412 : Integer.Sparse Key := [(key3025, -2), (key3022, -2), (key3021, -2), (key3025, -2), (key3022, -2), (key3016, -2), (key3009, -2), (key3011, -2), (key3007, -2), (key3021, -2), (key3011, -2), (key3007, -2), (key2922, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2757, 2), (key2659, 2), (key2752, 2), (key2657, 2), (key2918, 2), (key2752, 2), (key2657, 2)]

def rawRow8413 : Integer.Sparse Key := [(key1311, -2), (key1319, -2), (key1327, -2), (key1419, -2), (key1427, -2), (key1617, -2), (key1919, -2), (key1625, -2), (key1921, -2), (key1445, -2), (key1634, -2), (key1927, -2), (key1291, 1), (key1299, 1), (key1311, 1), (key1352, 1), (key1327, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1541, 1), (key1897, 1), (key1557, 1), (key1900, 1), (key1419, 1), (key1473, 1), (key1568, 1), (key1904, 1), (key1684, 1), (key1921, 1), (key1445, 1), (key1481, 1), (key1594, 1), (key1912, 1), (key1690, 1), (key1927, 1)]

def rawRow8414 : Integer.Sparse Key := [(key1319, -2), (key1311, -2), (key1327, -2), (key1427, -2), (key1419, -2), (key1919, -2), (key1617, -2), (key1921, -2), (key1625, -2), (key1445, -2), (key1927, -2), (key1634, -2), (key1299, 1), (key1291, 1), (key1352, 1), (key1311, 1), (key1355, 1), (key1327, 1), (key1394, 1), (key1386, 1), (key1897, 1), (key1541, 1), (key1900, 1), (key1557, 1), (key1473, 1), (key1419, 1), (key1904, 1), (key1568, 1), (key1921, 1), (key1684, 1), (key1481, 1), (key1445, 1), (key1912, 1), (key1594, 1), (key1927, 1), (key1690, 1)]

def rawRow8415 : Integer.Sparse Key := [(key1311, -2), (key1327, -2), (key1319, -2), (key1617, -2), (key1625, -2), (key1419, -2), (key1921, -2), (key1427, -2), (key1919, -2), (key1634, -2), (key1445, -2), (key1927, -2), (key1311, 1), (key1327, 1), (key1291, 1), (key1355, 1), (key1299, 1), (key1352, 1), (key1541, 1), (key1557, 1), (key1386, 1), (key1900, 1), (key1394, 1), (key1897, 1), (key1568, 1), (key1684, 1), (key1419, 1), (key1921, 1), (key1473, 1), (key1904, 1), (key1594, 1), (key1690, 1), (key1445, 1), (key1927, 1), (key1481, 1), (key1912, 1)]

def rawRow8416 : Integer.Sparse Key := [(key1327, -2), (key1311, -2), (key1319, -2), (key1625, -2), (key1617, -2), (key1921, -2), (key1419, -2), (key1919, -2), (key1427, -2), (key1634, -2), (key1927, -2), (key1445, -2), (key1327, 1), (key1311, 1), (key1355, 1), (key1291, 1), (key1352, 1), (key1299, 1), (key1557, 1), (key1541, 1), (key1900, 1), (key1386, 1), (key1897, 1), (key1394, 1), (key1684, 1), (key1568, 1), (key1921, 1), (key1419, 1), (key1904, 1), (key1473, 1), (key1690, 1), (key1594, 1), (key1927, 1), (key1445, 1), (key1912, 1), (key1481, 1)]

def rawRow8417 : Integer.Sparse Key := [(key1319, -2), (key1327, -2), (key1311, -2), (key1919, -2), (key1921, -2), (key1427, -2), (key1625, -2), (key1419, -2), (key1617, -2), (key1927, -2), (key1445, -2), (key1634, -2), (key1352, 1), (key1355, 1), (key1299, 1), (key1327, 1), (key1291, 1), (key1311, 1), (key1897, 1), (key1900, 1), (key1394, 1), (key1557, 1), (key1386, 1), (key1541, 1), (key1904, 1), (key1921, 1), (key1473, 1), (key1684, 1), (key1419, 1), (key1568, 1), (key1912, 1), (key1927, 1), (key1481, 1), (key1690, 1), (key1445, 1), (key1594, 1)]

def rawRow8418 : Integer.Sparse Key := [(key1327, -2), (key1319, -2), (key1311, -2), (key1921, -2), (key1919, -2), (key1625, -2), (key1427, -2), (key1617, -2), (key1419, -2), (key1927, -2), (key1634, -2), (key1445, -2), (key1355, 1), (key1352, 1), (key1327, 1), (key1299, 1), (key1311, 1), (key1291, 1), (key1900, 1), (key1897, 1), (key1557, 1), (key1394, 1), (key1541, 1), (key1386, 1), (key1921, 1), (key1904, 1), (key1684, 1), (key1473, 1), (key1568, 1), (key1419, 1), (key1927, 1), (key1912, 1), (key1690, 1), (key1481, 1), (key1594, 1), (key1445, 1)]

def rawRow8419 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1445, -2), (key1311, -2), (key1319, -2), (key1617, -2), (key1919, -2), (key1634, -2), (key1927, -2), (key1327, -2), (key1625, -2), (key1921, -2), (key1386, 1), (key1394, 1), (key1419, 1), (key1473, 1), (key1445, 1), (key1481, 1), (key1291, 1), (key1299, 1), (key1568, 1), (key1904, 1), (key1594, 1), (key1912, 1), (key1311, 1), (key1352, 1), (key1541, 1), (key1897, 1), (key1690, 1), (key1927, 1), (key1327, 1), (key1355, 1), (key1557, 1), (key1900, 1), (key1684, 1), (key1921, 1)]

def rawRow8420 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1445, -2), (key1319, -2), (key1311, -2), (key1919, -2), (key1617, -2), (key1927, -2), (key1634, -2), (key1327, -2), (key1921, -2), (key1625, -2), (key1394, 1), (key1386, 1), (key1473, 1), (key1419, 1), (key1481, 1), (key1445, 1), (key1299, 1), (key1291, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1594, 1), (key1352, 1), (key1311, 1), (key1897, 1), (key1541, 1), (key1927, 1), (key1690, 1), (key1355, 1), (key1327, 1), (key1900, 1), (key1557, 1), (key1921, 1), (key1684, 1)]

def rawRow8421 : Integer.Sparse Key := [(key1419, -2), (key1445, -2), (key1427, -2), (key1617, -2), (key1634, -2), (key1311, -2), (key1927, -2), (key1319, -2), (key1919, -2), (key1625, -2), (key1327, -2), (key1921, -2), (key1419, 1), (key1445, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1568, 1), (key1594, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1541, 1), (key1690, 1), (key1311, 1), (key1927, 1), (key1352, 1), (key1897, 1), (key1557, 1), (key1684, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1900, 1)]

def rawRow8422 : Integer.Sparse Key := [(key1445, -2), (key1419, -2), (key1427, -2), (key1634, -2), (key1617, -2), (key1927, -2), (key1311, -2), (key1919, -2), (key1319, -2), (key1625, -2), (key1921, -2), (key1327, -2), (key1445, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1473, 1), (key1394, 1), (key1594, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1904, 1), (key1299, 1), (key1690, 1), (key1541, 1), (key1927, 1), (key1311, 1), (key1897, 1), (key1352, 1), (key1684, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1900, 1), (key1355, 1)]

def rawRow8423 : Integer.Sparse Key := [(key1427, -2), (key1445, -2), (key1419, -2), (key1919, -2), (key1927, -2), (key1319, -2), (key1634, -2), (key1311, -2), (key1617, -2), (key1921, -2), (key1327, -2), (key1625, -2), (key1473, 1), (key1481, 1), (key1394, 1), (key1445, 1), (key1386, 1), (key1419, 1), (key1904, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1291, 1), (key1568, 1), (key1897, 1), (key1927, 1), (key1352, 1), (key1690, 1), (key1311, 1), (key1541, 1), (key1900, 1), (key1921, 1), (key1355, 1), (key1684, 1), (key1327, 1), (key1557, 1)]

def rawRow8424 : Integer.Sparse Key := [(key1445, -2), (key1427, -2), (key1419, -2), (key1927, -2), (key1919, -2), (key1634, -2), (key1319, -2), (key1617, -2), (key1311, -2), (key1921, -2), (key1625, -2), (key1327, -2), (key1481, 1), (key1473, 1), (key1445, 1), (key1394, 1), (key1419, 1), (key1386, 1), (key1912, 1), (key1904, 1), (key1594, 1), (key1299, 1), (key1568, 1), (key1291, 1), (key1927, 1), (key1897, 1), (key1690, 1), (key1352, 1), (key1541, 1), (key1311, 1), (key1921, 1), (key1900, 1), (key1684, 1), (key1355, 1), (key1557, 1), (key1327, 1)]

def rawRow8425 : Integer.Sparse Key := [(key1617, -2), (key1625, -2), (key1634, -2), (key1311, -2), (key1327, -2), (key1419, -2), (key1921, -2), (key1445, -2), (key1927, -2), (key1319, -2), (key1427, -2), (key1919, -2), (key1541, 1), (key1557, 1), (key1568, 1), (key1684, 1), (key1594, 1), (key1690, 1), (key1311, 1), (key1327, 1), (key1419, 1), (key1921, 1), (key1445, 1), (key1927, 1), (key1291, 1), (key1355, 1), (key1386, 1), (key1900, 1), (key1481, 1), (key1912, 1), (key1299, 1), (key1352, 1), (key1394, 1), (key1897, 1), (key1473, 1), (key1904, 1)]

def rawRow8426 : Integer.Sparse Key := [(key1625, -2), (key1617, -2), (key1634, -2), (key1327, -2), (key1311, -2), (key1921, -2), (key1419, -2), (key1927, -2), (key1445, -2), (key1319, -2), (key1919, -2), (key1427, -2), (key1557, 1), (key1541, 1), (key1684, 1), (key1568, 1), (key1690, 1), (key1594, 1), (key1327, 1), (key1311, 1), (key1921, 1), (key1419, 1), (key1927, 1), (key1445, 1), (key1355, 1), (key1291, 1), (key1900, 1), (key1386, 1), (key1912, 1), (key1481, 1), (key1352, 1), (key1299, 1), (key1897, 1), (key1394, 1), (key1904, 1), (key1473, 1)]

def rawRow8427 : Integer.Sparse Key := [(key1617, -2), (key1634, -2), (key1625, -2), (key1419, -2), (key1445, -2), (key1311, -2), (key1927, -2), (key1327, -2), (key1921, -2), (key1427, -2), (key1319, -2), (key1919, -2), (key1568, 1), (key1594, 1), (key1541, 1), (key1690, 1), (key1557, 1), (key1684, 1), (key1419, 1), (key1445, 1), (key1311, 1), (key1927, 1), (key1327, 1), (key1921, 1), (key1386, 1), (key1481, 1), (key1291, 1), (key1912, 1), (key1355, 1), (key1900, 1), (key1394, 1), (key1473, 1), (key1299, 1), (key1904, 1), (key1352, 1), (key1897, 1)]

def rawRow8428 : Integer.Sparse Key := [(key1634, -2), (key1617, -2), (key1625, -2), (key1445, -2), (key1419, -2), (key1927, -2), (key1311, -2), (key1921, -2), (key1327, -2), (key1427, -2), (key1919, -2), (key1319, -2), (key1594, 1), (key1568, 1), (key1690, 1), (key1541, 1), (key1684, 1), (key1557, 1), (key1445, 1), (key1419, 1), (key1927, 1), (key1311, 1), (key1921, 1), (key1327, 1), (key1481, 1), (key1386, 1), (key1912, 1), (key1291, 1), (key1900, 1), (key1355, 1), (key1473, 1), (key1394, 1), (key1904, 1), (key1299, 1), (key1897, 1), (key1352, 1)]

def rawRow8429 : Integer.Sparse Key := [(key1625, -2), (key1634, -2), (key1617, -2), (key1921, -2), (key1927, -2), (key1327, -2), (key1445, -2), (key1311, -2), (key1419, -2), (key1919, -2), (key1319, -2), (key1427, -2), (key1684, 1), (key1690, 1), (key1557, 1), (key1594, 1), (key1541, 1), (key1568, 1), (key1921, 1), (key1927, 1), (key1327, 1), (key1445, 1), (key1311, 1), (key1419, 1), (key1900, 1), (key1912, 1), (key1355, 1), (key1481, 1), (key1291, 1), (key1386, 1), (key1897, 1), (key1904, 1), (key1352, 1), (key1473, 1), (key1299, 1), (key1394, 1)]

def rawRow8430 : Integer.Sparse Key := [(key1634, -2), (key1625, -2), (key1617, -2), (key1927, -2), (key1921, -2), (key1445, -2), (key1327, -2), (key1419, -2), (key1311, -2), (key1919, -2), (key1427, -2), (key1319, -2), (key1690, 1), (key1684, 1), (key1594, 1), (key1557, 1), (key1568, 1), (key1541, 1), (key1927, 1), (key1921, 1), (key1445, 1), (key1327, 1), (key1419, 1), (key1311, 1), (key1912, 1), (key1900, 1), (key1481, 1), (key1355, 1), (key1386, 1), (key1291, 1), (key1904, 1), (key1897, 1), (key1473, 1), (key1352, 1), (key1394, 1), (key1299, 1)]

def rawRow8431 : Integer.Sparse Key := [(key1919, -2), (key1921, -2), (key1927, -2), (key1319, -2), (key1327, -2), (key1427, -2), (key1625, -2), (key1445, -2), (key1634, -2), (key1311, -2), (key1419, -2), (key1617, -2), (key1897, 1), (key1900, 1), (key1904, 1), (key1921, 1), (key1912, 1), (key1927, 1), (key1352, 1), (key1355, 1), (key1473, 1), (key1684, 1), (key1481, 1), (key1690, 1), (key1299, 1), (key1327, 1), (key1394, 1), (key1557, 1), (key1445, 1), (key1594, 1), (key1291, 1), (key1311, 1), (key1386, 1), (key1541, 1), (key1419, 1), (key1568, 1)]

def rawRow8432 : Integer.Sparse Key := [(key1921, -2), (key1919, -2), (key1927, -2), (key1327, -2), (key1319, -2), (key1625, -2), (key1427, -2), (key1634, -2), (key1445, -2), (key1311, -2), (key1617, -2), (key1419, -2), (key1900, 1), (key1897, 1), (key1921, 1), (key1904, 1), (key1927, 1), (key1912, 1), (key1355, 1), (key1352, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1481, 1), (key1327, 1), (key1299, 1), (key1557, 1), (key1394, 1), (key1594, 1), (key1445, 1), (key1311, 1), (key1291, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1419, 1)]

def rawRow8433 : Integer.Sparse Key := [(key1919, -2), (key1927, -2), (key1921, -2), (key1427, -2), (key1445, -2), (key1319, -2), (key1634, -2), (key1327, -2), (key1625, -2), (key1419, -2), (key1311, -2), (key1617, -2), (key1904, 1), (key1912, 1), (key1897, 1), (key1927, 1), (key1900, 1), (key1921, 1), (key1473, 1), (key1481, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1684, 1), (key1394, 1), (key1445, 1), (key1299, 1), (key1594, 1), (key1327, 1), (key1557, 1), (key1386, 1), (key1419, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1541, 1)]

def rawRow8434 : Integer.Sparse Key := [(key1927, -2), (key1919, -2), (key1921, -2), (key1445, -2), (key1427, -2), (key1634, -2), (key1319, -2), (key1625, -2), (key1327, -2), (key1419, -2), (key1617, -2), (key1311, -2), (key1912, 1), (key1904, 1), (key1927, 1), (key1897, 1), (key1921, 1), (key1900, 1), (key1481, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1684, 1), (key1355, 1), (key1445, 1), (key1394, 1), (key1594, 1), (key1299, 1), (key1557, 1), (key1327, 1), (key1419, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1541, 1), (key1311, 1)]

def rawRow8435 : Integer.Sparse Key := [(key1921, -2), (key1927, -2), (key1919, -2), (key1625, -2), (key1634, -2), (key1327, -2), (key1445, -2), (key1319, -2), (key1427, -2), (key1617, -2), (key1311, -2), (key1419, -2), (key1921, 1), (key1927, 1), (key1900, 1), (key1912, 1), (key1897, 1), (key1904, 1), (key1684, 1), (key1690, 1), (key1355, 1), (key1481, 1), (key1352, 1), (key1473, 1), (key1557, 1), (key1594, 1), (key1327, 1), (key1445, 1), (key1299, 1), (key1394, 1), (key1541, 1), (key1568, 1), (key1311, 1), (key1419, 1), (key1291, 1), (key1386, 1)]

def rawRow8436 : Integer.Sparse Key := [(key1927, -2), (key1921, -2), (key1919, -2), (key1634, -2), (key1625, -2), (key1445, -2), (key1327, -2), (key1427, -2), (key1319, -2), (key1617, -2), (key1419, -2), (key1311, -2), (key1927, 1), (key1921, 1), (key1912, 1), (key1900, 1), (key1904, 1), (key1897, 1), (key1690, 1), (key1684, 1), (key1481, 1), (key1355, 1), (key1473, 1), (key1352, 1), (key1594, 1), (key1557, 1), (key1445, 1), (key1327, 1), (key1394, 1), (key1299, 1), (key1568, 1), (key1541, 1), (key1419, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

def rawRow8437 : Integer.Sparse Key := [(key1352, -2), (key1352, -2), (key1355, -2), (key1473, -2), (key1473, -2), (key1682, -2), (key1682, -2), (key1684, -2), (key1684, -2), (key1481, -2), (key1690, -2), (key1690, -2), (key1299, 1), (key1299, 1), (key1319, 1), (key1319, 1), (key1327, 1), (key1327, 1), (key1394, 1), (key1394, 1), (key1549, 1), (key1549, 1), (key1557, 1), (key1557, 1), (key1427, 1), (key1427, 1), (key1576, 1), (key1576, 1), (key1625, 1), (key1625, 1), (key1445, 1), (key1445, 1), (key1594, 1), (key1594, 1), (key1634, 1), (key1634, 1)]

def rawRow8438 : Integer.Sparse Key := [(key1352, -2), (key1355, -2), (key1352, -2), (key1682, -2), (key1684, -2), (key1473, -2), (key1684, -2), (key1473, -2), (key1682, -2), (key1690, -2), (key1481, -2), (key1690, -2), (key1319, 1), (key1327, 1), (key1299, 1), (key1327, 1), (key1299, 1), (key1319, 1), (key1549, 1), (key1557, 1), (key1394, 1), (key1557, 1), (key1394, 1), (key1549, 1), (key1576, 1), (key1625, 1), (key1427, 1), (key1625, 1), (key1427, 1), (key1576, 1), (key1594, 1), (key1634, 1), (key1445, 1), (key1634, 1), (key1445, 1), (key1594, 1)]

def rawRow8439 : Integer.Sparse Key := [(key1355, -2), (key1352, -2), (key1352, -2), (key1684, -2), (key1682, -2), (key1684, -2), (key1473, -2), (key1682, -2), (key1473, -2), (key1690, -2), (key1690, -2), (key1481, -2), (key1327, 1), (key1319, 1), (key1327, 1), (key1299, 1), (key1319, 1), (key1299, 1), (key1557, 1), (key1549, 1), (key1557, 1), (key1394, 1), (key1549, 1), (key1394, 1), (key1625, 1), (key1576, 1), (key1625, 1), (key1427, 1), (key1576, 1), (key1427, 1), (key1634, 1), (key1594, 1), (key1634, 1), (key1445, 1), (key1594, 1), (key1445, 1)]

def rawRow8440 : Integer.Sparse Key := [(key1473, -2), (key1473, -2), (key1481, -2), (key1352, -2), (key1352, -2), (key1682, -2), (key1682, -2), (key1690, -2), (key1690, -2), (key1355, -2), (key1684, -2), (key1684, -2), (key1394, 1), (key1394, 1), (key1427, 1), (key1427, 1), (key1445, 1), (key1445, 1), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1594, 1), (key1594, 1), (key1319, 1), (key1319, 1), (key1549, 1), (key1549, 1), (key1634, 1), (key1634, 1), (key1327, 1), (key1327, 1), (key1557, 1), (key1557, 1), (key1625, 1), (key1625, 1)]

def rawRow8441 : Integer.Sparse Key := [(key1473, -2), (key1481, -2), (key1473, -2), (key1682, -2), (key1690, -2), (key1352, -2), (key1690, -2), (key1352, -2), (key1682, -2), (key1684, -2), (key1355, -2), (key1684, -2), (key1427, 1), (key1445, 1), (key1394, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1549, 1), (key1634, 1), (key1319, 1), (key1634, 1), (key1319, 1), (key1549, 1), (key1557, 1), (key1625, 1), (key1327, 1), (key1625, 1), (key1327, 1), (key1557, 1)]

def rawRow8442 : Integer.Sparse Key := [(key1481, -2), (key1473, -2), (key1473, -2), (key1690, -2), (key1682, -2), (key1690, -2), (key1352, -2), (key1682, -2), (key1352, -2), (key1684, -2), (key1684, -2), (key1355, -2), (key1445, 1), (key1427, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1394, 1), (key1594, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1299, 1), (key1634, 1), (key1549, 1), (key1634, 1), (key1319, 1), (key1549, 1), (key1319, 1), (key1625, 1), (key1557, 1), (key1625, 1), (key1327, 1), (key1557, 1), (key1327, 1)]

def rawRow8443 : Integer.Sparse Key := [(key1682, -2), (key1684, -2), (key1690, -2), (key1352, -2), (key1355, -2), (key1473, -2), (key1684, -2), (key1481, -2), (key1690, -2), (key1352, -2), (key1473, -2), (key1682, -2), (key1549, 1), (key1557, 1), (key1576, 1), (key1625, 1), (key1594, 1), (key1634, 1), (key1319, 1), (key1327, 1), (key1427, 1), (key1625, 1), (key1445, 1), (key1634, 1), (key1299, 1), (key1327, 1), (key1394, 1), (key1557, 1), (key1445, 1), (key1594, 1), (key1299, 1), (key1319, 1), (key1394, 1), (key1549, 1), (key1427, 1), (key1576, 1)]

def rawRow8444 : Integer.Sparse Key := [(key1684, -2), (key1682, -2), (key1690, -2), (key1355, -2), (key1352, -2), (key1684, -2), (key1473, -2), (key1690, -2), (key1481, -2), (key1352, -2), (key1682, -2), (key1473, -2), (key1557, 1), (key1549, 1), (key1625, 1), (key1576, 1), (key1634, 1), (key1594, 1), (key1327, 1), (key1319, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1445, 1), (key1327, 1), (key1299, 1), (key1557, 1), (key1394, 1), (key1594, 1), (key1445, 1), (key1319, 1), (key1299, 1), (key1549, 1), (key1394, 1), (key1576, 1), (key1427, 1)]

def rawRow8445 : Integer.Sparse Key := [(key1682, -2), (key1690, -2), (key1684, -2), (key1473, -2), (key1481, -2), (key1352, -2), (key1690, -2), (key1355, -2), (key1684, -2), (key1473, -2), (key1352, -2), (key1682, -2), (key1576, 1), (key1594, 1), (key1549, 1), (key1634, 1), (key1557, 1), (key1625, 1), (key1427, 1), (key1445, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1625, 1), (key1394, 1), (key1445, 1), (key1299, 1), (key1594, 1), (key1327, 1), (key1557, 1), (key1394, 1), (key1427, 1), (key1299, 1), (key1576, 1), (key1319, 1), (key1549, 1)]

def rawRow8446 : Integer.Sparse Key := [(key1690, -2), (key1682, -2), (key1684, -2), (key1481, -2), (key1473, -2), (key1690, -2), (key1352, -2), (key1684, -2), (key1355, -2), (key1473, -2), (key1682, -2), (key1352, -2), (key1594, 1), (key1576, 1), (key1634, 1), (key1549, 1), (key1625, 1), (key1557, 1), (key1445, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1625, 1), (key1327, 1), (key1445, 1), (key1394, 1), (key1594, 1), (key1299, 1), (key1557, 1), (key1327, 1), (key1427, 1), (key1394, 1), (key1576, 1), (key1299, 1), (key1549, 1), (key1319, 1)]

def rawRow8447 : Integer.Sparse Key := [(key1684, -2), (key1690, -2), (key1682, -2), (key1684, -2), (key1690, -2), (key1355, -2), (key1481, -2), (key1352, -2), (key1473, -2), (key1682, -2), (key1352, -2), (key1473, -2), (key1625, 1), (key1634, 1), (key1557, 1), (key1594, 1), (key1549, 1), (key1576, 1), (key1625, 1), (key1634, 1), (key1327, 1), (key1445, 1), (key1319, 1), (key1427, 1), (key1557, 1), (key1594, 1), (key1327, 1), (key1445, 1), (key1299, 1), (key1394, 1), (key1549, 1), (key1576, 1), (key1319, 1), (key1427, 1), (key1299, 1), (key1394, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8448 : Integer.Sparse Key := [(key1690, -2), (key1684, -2), (key1682, -2), (key1690, -2), (key1684, -2), (key1481, -2), (key1355, -2), (key1473, -2), (key1352, -2), (key1682, -2), (key1473, -2), (key1352, -2), (key1634, 1), (key1625, 1), (key1594, 1), (key1557, 1), (key1576, 1), (key1549, 1), (key1634, 1), (key1625, 1), (key1445, 1), (key1327, 1), (key1427, 1), (key1319, 1), (key1594, 1), (key1557, 1), (key1445, 1), (key1327, 1), (key1394, 1), (key1299, 1), (key1576, 1), (key1549, 1), (key1427, 1), (key1319, 1), (key1394, 1), (key1299, 1)]

def rawRow8449 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, 1), (key2638, 1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1), (key2614, -2), (key2630, -2), (key2638, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2784, -2), (key2792, -2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2)]

def rawRow8450 : Integer.Sparse Key := [(key2614, 1), (key2608, 1), (key2638, 1), (key2624, 1), (key2659, 1), (key2657, 1), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1), (key2792, 1), (key2778, 1), (key2827, 1), (key2801, 1), (key2922, 1), (key2919, 1), (key3009, 1), (key3007, 1), (key3016, 1), (key3011, 1), (key3025, 1), (key3022, 1), (key2614, -2), (key2638, -2), (key2630, -2), (key2669, -2), (key2724, -2), (key2704, -2), (key2792, -2), (key2784, -2), (key2827, -2), (key2807, -2), (key2868, -2), (key2858, -2)]

def rawRow8451 : Integer.Sparse Key := [(key2624, 1), (key2638, 1), (key2608, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2801, 1), (key2919, 1), (key2778, 1), (key2922, 1), (key2792, 1), (key2827, 1), (key3011, 1), (key3022, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3016, 1), (key2630, -2), (key2614, -2), (key2638, -2), (key2704, -2), (key2669, -2), (key2724, -2), (key2807, -2), (key2858, -2), (key2784, -2), (key2868, -2), (key2792, -2), (key2827, -2)]

def rawRow8452 : Integer.Sparse Key := [(key2638, 1), (key2624, 1), (key2659, 1), (key2608, 1), (key2638, 1), (key2614, 1), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1), (key2919, 1), (key2801, 1), (key2922, 1), (key2778, 1), (key2827, 1), (key2792, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3016, 1), (key3009, 1), (key2630, -2), (key2638, -2), (key2614, -2), (key2704, -2), (key2724, -2), (key2669, -2), (key2858, -2), (key2807, -2), (key2868, -2), (key2784, -2), (key2827, -2), (key2792, -2)]

def rawRow8453 : Integer.Sparse Key := [(key2657, 1), (key2659, 1), (key2614, 1), (key2638, 1), (key2608, 1), (key2624, 1), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1), (key2827, 1), (key2922, 1), (key2792, 1), (key2919, 1), (key2778, 1), (key2801, 1), (key3016, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key3007, 1), (key3011, 1), (key2638, -2), (key2614, -2), (key2630, -2), (key2724, -2), (key2669, -2), (key2704, -2), (key2827, -2), (key2868, -2), (key2792, -2), (key2858, -2), (key2784, -2), (key2807, -2)]

def rawRow8454 : Integer.Sparse Key := [(key2659, 1), (key2657, 1), (key2638, 1), (key2614, 1), (key2624, 1), (key2608, 1), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2922, 1), (key2827, 1), (key2919, 1), (key2792, 1), (key2801, 1), (key2778, 1), (key3025, 1), (key3016, 1), (key3022, 1), (key3009, 1), (key3011, 1), (key3007, 1), (key2638, -2), (key2630, -2), (key2614, -2), (key2724, -2), (key2704, -2), (key2669, -2), (key2868, -2), (key2827, -2), (key2858, -2), (key2792, -2), (key2807, -2), (key2784, -2)]

def rawRow8455 : Integer.Sparse Key := [(key2663, 1), (key2669, 1), (key2698, 1), (key2752, 1), (key2724, 1), (key2757, 1), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2624, 1), (key2638, 1), (key2698, 1), (key2724, 1), (key3022, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2752, 1), (key2757, 1), (key2919, 1), (key2922, 1), (key2669, -2), (key2784, -2), (key2792, -2), (key2614, -2), (key2807, -2), (key2827, -2), (key2630, -2), (key2638, -2), (key2704, -2), (key2724, -2), (key2858, -2), (key2868, -2)]

def rawRow8456 : Integer.Sparse Key := [(key2669, 1), (key2663, 1), (key2752, 1), (key2698, 1), (key2757, 1), (key2724, 1), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2638, 1), (key2624, 1), (key2724, 1), (key2698, 1), (key3025, 1), (key3022, 1), (key2659, 1), (key2657, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2919, 1), (key2669, -2), (key2792, -2), (key2784, -2), (key2614, -2), (key2827, -2), (key2807, -2), (key2638, -2), (key2630, -2), (key2724, -2), (key2704, -2), (key2868, -2), (key2858, -2)]

def rawRow8457 : Integer.Sparse Key := [(key2698, 1), (key2724, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2698, 1), (key3022, 1), (key2624, 1), (key3025, 1), (key2638, 1), (key2724, 1), (key2752, 1), (key2919, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2784, -2), (key2669, -2), (key2792, -2), (key2807, -2), (key2614, -2), (key2827, -2), (key2704, -2), (key2858, -2), (key2630, -2), (key2868, -2), (key2638, -2), (key2724, -2)]

def rawRow8458 : Integer.Sparse Key := [(key2724, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2752, 1), (key2669, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key3022, 1), (key2698, 1), (key3025, 1), (key2624, 1), (key2724, 1), (key2638, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2757, 1), (key2659, 1), (key2784, -2), (key2792, -2), (key2669, -2), (key2807, -2), (key2827, -2), (key2614, -2), (key2858, -2), (key2704, -2), (key2868, -2), (key2630, -2), (key2724, -2), (key2638, -2)]

def rawRow8459 : Integer.Sparse Key := [(key2752, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2663, 1), (key2698, 1), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2724, 1), (key3025, 1), (key2638, 1), (key3022, 1), (key2624, 1), (key2698, 1), (key2757, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2657, 1), (key2752, 1), (key2792, -2), (key2669, -2), (key2784, -2), (key2827, -2), (key2614, -2), (key2807, -2), (key2724, -2), (key2868, -2), (key2638, -2), (key2858, -2), (key2630, -2), (key2704, -2)]

def rawRow8460 : Integer.Sparse Key := [(key2757, 1), (key2752, 1), (key2724, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key3025, 1), (key2724, 1), (key3022, 1), (key2638, 1), (key2698, 1), (key2624, 1), (key2922, 1), (key2757, 1), (key2919, 1), (key2659, 1), (key2752, 1), (key2657, 1), (key2792, -2), (key2784, -2), (key2669, -2), (key2827, -2), (key2807, -2), (key2614, -2), (key2868, -2), (key2724, -2), (key2858, -2), (key2638, -2), (key2704, -2), (key2630, -2)]

def rawRow8461 : Integer.Sparse Key := [(key2778, 1), (key2792, 1), (key2801, 1), (key2919, 1), (key2827, 1), (key2922, 1), (key2624, 1), (key2638, 1), (key2698, 1), (key3022, 1), (key2724, 1), (key3025, 1), (key2608, 1), (key2659, 1), (key2663, 1), (key2757, 1), (key3009, 1), (key3016, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2724, 1), (key2792, 1), (key2827, 1), (key2704, -2), (key2807, -2), (key2858, -2), (key2630, -2), (key2784, -2), (key2868, -2), (key2614, -2), (key2638, -2), (key2669, -2), (key2724, -2), (key2792, -2), (key2827, -2)]

def rawRow8462 : Integer.Sparse Key := [(key2792, 1), (key2778, 1), (key2919, 1), (key2801, 1), (key2922, 1), (key2827, 1), (key2638, 1), (key2624, 1), (key3022, 1), (key2698, 1), (key3025, 1), (key2724, 1), (key2659, 1), (key2608, 1), (key2757, 1), (key2663, 1), (key3016, 1), (key3009, 1), (key2638, 1), (key2614, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2792, 1), (key2704, -2), (key2858, -2), (key2807, -2), (key2630, -2), (key2868, -2), (key2784, -2), (key2638, -2), (key2614, -2), (key2724, -2), (key2669, -2), (key2827, -2), (key2792, -2)]

def rawRow8463 : Integer.Sparse Key := [(key2801, 1), (key2827, 1), (key2778, 1), (key2922, 1), (key2792, 1), (key2919, 1), (key2698, 1), (key2724, 1), (key2624, 1), (key3025, 1), (key2638, 1), (key3022, 1), (key2663, 1), (key2757, 1), (key2608, 1), (key3016, 1), (key2659, 1), (key2757, 1), (key2669, 1), (key2792, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2807, -2), (key2704, -2), (key2858, -2), (key2784, -2), (key2630, -2), (key2868, -2), (key2669, -2), (key2792, -2), (key2614, -2), (key2827, -2), (key2638, -2), (key2724, -2)]

def rawRow8464 : Integer.Sparse Key := [(key2827, 1), (key2801, 1), (key2922, 1), (key2778, 1), (key2919, 1), (key2792, 1), (key2724, 1), (key2698, 1), (key3025, 1), (key2624, 1), (key3022, 1), (key2638, 1), (key2757, 1), (key2663, 1), (key3016, 1), (key2608, 1), (key2757, 1), (key2659, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2724, 1), (key2638, 1), (key2807, -2), (key2858, -2), (key2704, -2), (key2784, -2), (key2868, -2), (key2630, -2), (key2792, -2), (key2669, -2), (key2827, -2), (key2614, -2), (key2724, -2), (key2638, -2)]

def rawRow8465 : Integer.Sparse Key := [(key2919, 1), (key2922, 1), (key2792, 1), (key2827, 1), (key2778, 1), (key2801, 1), (key3022, 1), (key3025, 1), (key2638, 1), (key2724, 1), (key2624, 1), (key2698, 1), (key3009, 1), (key3016, 1), (key2659, 1), (key2757, 1), (key2608, 1), (key2663, 1), (key2724, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2614, 1), (key2669, 1), (key2858, -2), (key2704, -2), (key2807, -2), (key2868, -2), (key2630, -2), (key2784, -2), (key2724, -2), (key2827, -2), (key2638, -2), (key2792, -2), (key2614, -2), (key2669, -2)]

def rawRow8466 : Integer.Sparse Key := [(key2922, 1), (key2919, 1), (key2827, 1), (key2792, 1), (key2801, 1), (key2778, 1), (key3025, 1), (key3022, 1), (key2724, 1), (key2638, 1), (key2698, 1), (key2624, 1), (key3016, 1), (key3009, 1), (key2757, 1), (key2659, 1), (key2663, 1), (key2608, 1), (key2827, 1), (key2724, 1), (key2792, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2858, -2), (key2807, -2), (key2704, -2), (key2868, -2), (key2784, -2), (key2630, -2), (key2827, -2), (key2724, -2), (key2792, -2), (key2638, -2), (key2669, -2), (key2614, -2)]

def rawRow8467 : Integer.Sparse Key := [(key3007, 1), (key3009, 1), (key3011, 1), (key3022, 1), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2792, 1), (key2724, 1), (key2827, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1), (key2724, -2), (key2827, -2), (key2868, -2), (key2638, -2), (key2792, -2), (key2858, -2), (key2614, -2), (key2630, -2), (key2669, -2), (key2704, -2), (key2784, -2), (key2807, -2)]

def rawRow8468 : Integer.Sparse Key := [(key3009, 1), (key3007, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1), (key2638, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2724, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1), (key2724, -2), (key2868, -2), (key2827, -2), (key2638, -2), (key2858, -2), (key2792, -2), (key2630, -2), (key2614, -2), (key2704, -2), (key2669, -2), (key2807, -2), (key2784, -2)]

def rawRow8469 : Integer.Sparse Key := [(key3011, 1), (key3016, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2669, 1), (key2724, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2827, -2), (key2724, -2), (key2868, -2), (key2792, -2), (key2638, -2), (key2858, -2), (key2669, -2), (key2784, -2), (key2614, -2), (key2807, -2), (key2630, -2), (key2704, -2)]

def rawRow8470 : Integer.Sparse Key := [(key3016, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2792, 1), (key2638, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1), (key2827, -2), (key2868, -2), (key2724, -2), (key2792, -2), (key2858, -2), (key2638, -2), (key2784, -2), (key2669, -2), (key2807, -2), (key2614, -2), (key2704, -2), (key2630, -2)]

def rawRow8471 : Integer.Sparse Key := [(key3022, 1), (key3025, 1), (key3009, 1), (key3016, 1), (key3007, 1), (key3011, 1), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1), (key2792, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2614, 1), (key2669, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1), (key2868, -2), (key2724, -2), (key2827, -2), (key2858, -2), (key2638, -2), (key2792, -2), (key2704, -2), (key2807, -2), (key2630, -2), (key2784, -2), (key2614, -2), (key2669, -2)]

def rawRow8472 : Integer.Sparse Key := [(key3025, 1), (key3022, 1), (key3016, 1), (key3009, 1), (key3011, 1), (key3007, 1), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1), (key2827, 1), (key2792, 1), (key2724, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1), (key2868, -2), (key2827, -2), (key2724, -2), (key2858, -2), (key2792, -2), (key2638, -2), (key2807, -2), (key2704, -2), (key2784, -2), (key2630, -2), (key2669, -2), (key2614, -2)]

def rawRow8473 : Integer.Sparse Key := [(key2614, 1), (key2614, 1), (key2630, 1), (key2630, 1), (key2638, 1), (key2638, 1), (key2669, 1), (key2669, 1), (key2784, 1), (key2784, 1), (key2792, 1), (key2792, 1), (key2704, 1), (key2704, 1), (key2807, 1), (key2807, 1), (key2858, 1), (key2858, 1), (key2724, 1), (key2724, 1), (key2827, 1), (key2827, 1), (key2868, 1), (key2868, 1), (key2608, -2), (key2624, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2778, -2), (key2778, -2), (key2801, -2), (key2801, -2), (key2851, -2), (key2851, -2)]

def rawRow8474 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2614, 1), (key2638, 1), (key2614, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2807, 1), (key2858, 1), (key2704, 1), (key2858, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2868, 1), (key2724, 1), (key2868, 1), (key2724, 1), (key2827, 1), (key2624, -2), (key2608, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2851, -2), (key2778, -2), (key2801, -2)]

def rawRow8475 : Integer.Sparse Key := [(key2638, 1), (key2630, 1), (key2638, 1), (key2614, 1), (key2630, 1), (key2614, 1), (key2792, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2669, 1), (key2858, 1), (key2807, 1), (key2858, 1), (key2704, 1), (key2807, 1), (key2704, 1), (key2868, 1), (key2827, 1), (key2868, 1), (key2724, 1), (key2827, 1), (key2724, 1), (key2624, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2851, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key2778, -2)]

def rawRow8476 : Integer.Sparse Key := [(key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2724, 1), (key2724, 1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2630, 1), (key2630, 1), (key2784, 1), (key2784, 1), (key2868, 1), (key2868, 1), (key2638, 1), (key2638, 1), (key2792, 1), (key2792, 1), (key2858, 1), (key2858, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, -2), (key2624, -2), (key2698, -2), (key2698, -2), (key2851, -2), (key2851, -2)]

def rawRow8477 : Integer.Sparse Key := [(key2704, 1), (key2724, 1), (key2669, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2784, 1), (key2868, 1), (key2630, 1), (key2868, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2858, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2792, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2851, -2), (key2624, -2), (key2698, -2)]

def rawRow8478 : Integer.Sparse Key := [(key2724, 1), (key2704, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2868, 1), (key2784, 1), (key2868, 1), (key2630, 1), (key2784, 1), (key2630, 1), (key2858, 1), (key2792, 1), (key2858, 1), (key2638, 1), (key2792, 1), (key2638, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2624, -2)]

def rawRow8479 : Integer.Sparse Key := [(key2784, 1), (key2792, 1), (key2807, 1), (key2858, 1), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2792, 1), (key2724, 1), (key2827, 1), (key2614, 1), (key2630, 1), (key2669, 1), (key2784, 1), (key2704, 1), (key2807, 1), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2778, -2), (key2801, -2)]

def rawRow8480 : Integer.Sparse Key := [(key2792, 1), (key2784, 1), (key2858, 1), (key2807, 1), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1), (key2638, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2724, 1), (key2630, 1), (key2614, 1), (key2784, 1), (key2669, 1), (key2807, 1), (key2704, 1), (key2778, -2), (key2851, -2), (key2801, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2778, -2)]

def rawRow8481 : Integer.Sparse Key := [(key2807, 1), (key2827, 1), (key2784, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2669, 1), (key2724, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2669, 1), (key2704, 1), (key2614, 1), (key2807, 1), (key2630, 1), (key2784, 1), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2624, -2), (key2698, -2)]

def rawRow8482 : Integer.Sparse Key := [(key2827, 1), (key2807, 1), (key2868, 1), (key2784, 1), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2792, 1), (key2638, 1), (key2704, 1), (key2669, 1), (key2807, 1), (key2614, 1), (key2784, 1), (key2630, 1), (key2801, -2), (key2851, -2), (key2778, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2608, -2), (key2698, -2), (key2624, -2)]

def rawRow8483 : Integer.Sparse Key := [(key2858, 1), (key2868, 1), (key2792, 1), (key2827, 1), (key2784, 1), (key2807, 1), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1), (key2792, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2614, 1), (key2669, 1), (key2784, 1), (key2807, 1), (key2630, 1), (key2704, 1), (key2614, 1), (key2669, 1), (key2851, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, -2), (key2801, -2), (key2624, -2), (key2698, -2), (key2608, -2), (key2663, -2)]

def rawRow8484 : Integer.Sparse Key := [(key2868, 1), (key2858, 1), (key2827, 1), (key2792, 1), (key2807, 1), (key2784, 1), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1), (key2827, 1), (key2792, 1), (key2724, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2807, 1), (key2784, 1), (key2704, 1), (key2630, 1), (key2669, 1), (key2614, 1), (key2851, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, -2), (key2778, -2), (key2698, -2), (key2624, -2), (key2663, -2), (key2608, -2)]

def rawRow8485 : Integer.Sparse Key := [(key1254, 2), (key1254, 2), (key1254, 2), (key1607, 2), (key1607, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1804, 2), (key1263, -2), (key1263, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1835, -2), (key1835, -2)]

def rawRow8486 : Integer.Sparse Key := [(key1607, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1254, 2), (key1607, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1646, -2), (key1646, -2), (key1835, -2), (key1263, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1835, -2), (key1263, -2), (key1646, -2), (key1646, -2)]

def rawRow8487 : Integer.Sparse Key := [(key1804, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1254, 2), (key1607, 2), (key1646, -2), (key1835, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1263, -2), (key1835, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1263, -2), (key1646, -2)]

def rawRow8488 : Integer.Sparse Key := [(key1804, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1254, 2), (key1607, 2), (key1254, 2), (key1835, -2), (key1646, -2), (key1646, -2), (key1835, -2), (key1646, -2), (key1835, -2), (key1263, -2), (key1646, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1263, -2)]

def rawRow8489 : Integer.Sparse Key := [(key1254, 2), (key1263, 2), (key1263, 2), (key1529, 2), (key1646, 2), (key1646, 2), (key1763, 2), (key1763, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1835, 2), (key1254, -2), (key1254, -2), (key1263, -2), (key1529, -2), (key1529, -2), (key1607, -2), (key1607, -2), (key1646, -2), (key1646, -2), (key1763, -2), (key1804, -2), (key1804, -2)]

def rawRow8490 : Integer.Sparse Key := [(key1263, 2), (key1254, 2), (key1263, 2), (key1646, 2), (key1529, 2), (key1646, 2), (key1804, 2), (key1835, 2), (key1763, 2), (key1835, 2), (key1763, 2), (key1804, 2), (key1254, -2), (key1263, -2), (key1254, -2), (key1607, -2), (key1646, -2), (key1529, -2), (key1646, -2), (key1529, -2), (key1607, -2), (key1804, -2), (key1763, -2), (key1804, -2)]

def rawRow8491 : Integer.Sparse Key := [(key1263, 2), (key1263, 2), (key1254, 2), (key1646, 2), (key1646, 2), (key1529, 2), (key1835, 2), (key1804, 2), (key1835, 2), (key1763, 2), (key1804, 2), (key1763, 2), (key1263, -2), (key1254, -2), (key1254, -2), (key1646, -2), (key1607, -2), (key1646, -2), (key1529, -2), (key1607, -2), (key1529, -2), (key1804, -2), (key1804, -2), (key1763, -2)]

def rawRow8492 : Integer.Sparse Key := [(key1529, 2), (key1763, 2), (key1763, 2), (key1254, 2), (key1804, 2), (key1804, 2), (key1263, 2), (key1263, 2), (key1646, 2), (key1646, 2), (key1835, 2), (key1835, 2), (key1529, -2), (key1529, -2), (key1763, -2), (key1254, -2), (key1254, -2), (key1607, -2), (key1607, -2), (key1804, -2), (key1804, -2), (key1263, -2), (key1646, -2), (key1646, -2)]

def rawRow8493 : Integer.Sparse Key := [(key1763, 2), (key1529, 2), (key1763, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1646, 2), (key1835, 2), (key1263, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1529, -2), (key1763, -2), (key1529, -2), (key1607, -2), (key1804, -2), (key1254, -2), (key1804, -2), (key1254, -2), (key1607, -2), (key1646, -2), (key1263, -2), (key1646, -2)]

def rawRow8494 : Integer.Sparse Key := [(key1763, 2), (key1763, 2), (key1529, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1835, 2), (key1646, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1263, 2), (key1763, -2), (key1529, -2), (key1529, -2), (key1804, -2), (key1607, -2), (key1804, -2), (key1254, -2), (key1607, -2), (key1254, -2), (key1646, -2), (key1646, -2), (key1263, -2)]

def rawRow8495 : Integer.Sparse Key := [(key1646, 2), (key1804, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1835, 2), (key1254, 2), (key1263, 2), (key1529, 2), (key1646, 2), (key1763, 2), (key1804, 2), (key1607, -2), (key1646, -2), (key1804, -2), (key1254, -2), (key1263, -2), (key1529, -2), (key1646, -2), (key1763, -2), (key1804, -2), (key1254, -2), (key1529, -2), (key1607, -2)]

def rawRow8496 : Integer.Sparse Key := [(key1646, 2), (key1835, 2), (key1804, 2), (key1263, 2), (key1835, 2), (key1763, 2), (key1263, 2), (key1254, 2), (key1646, 2), (key1529, 2), (key1804, 2), (key1763, 2), (key1646, -2), (key1607, -2), (key1804, -2), (key1263, -2), (key1254, -2), (key1646, -2), (key1529, -2), (key1804, -2), (key1763, -2), (key1254, -2), (key1607, -2), (key1529, -2)]

def rawRow8497 : Integer.Sparse Key := [(key1804, 2), (key1646, 2), (key1835, 2), (key1763, 2), (key1263, 2), (key1835, 2), (key1529, 2), (key1763, 2), (key1254, 2), (key1804, 2), (key1263, 2), (key1646, 2), (key1607, -2), (key1804, -2), (key1646, -2), (key1529, -2), (key1763, -2), (key1254, -2), (key1804, -2), (key1263, -2), (key1646, -2), (key1529, -2), (key1254, -2), (key1607, -2)]

def rawRow8498 : Integer.Sparse Key := [(key1804, 2), (key1835, 2), (key1646, 2), (key1763, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1529, 2), (key1804, 2), (key1254, 2), (key1646, 2), (key1263, 2), (key1804, -2), (key1607, -2), (key1646, -2), (key1763, -2), (key1529, -2), (key1804, -2), (key1254, -2), (key1646, -2), (key1263, -2), (key1529, -2), (key1607, -2), (key1254, -2)]

def rawRow8499 : Integer.Sparse Key := [(key1835, 2), (key1646, 2), (key1804, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1646, 2), (key1804, 2), (key1263, 2), (key1763, 2), (key1254, 2), (key1529, 2), (key1646, -2), (key1804, -2), (key1607, -2), (key1646, -2), (key1804, -2), (key1263, -2), (key1763, -2), (key1254, -2), (key1529, -2), (key1607, -2), (key1254, -2), (key1529, -2)]

def rawRow8500 : Integer.Sparse Key := [(key1835, 2), (key1804, 2), (key1646, 2), (key1835, 2), (key1763, 2), (key1263, 2), (key1804, 2), (key1646, 2), (key1763, 2), (key1263, 2), (key1529, 2), (key1254, 2), (key1804, -2), (key1646, -2), (key1607, -2), (key1804, -2), (key1646, -2), (key1763, -2), (key1263, -2), (key1529, -2), (key1254, -2), (key1607, -2), (key1529, -2), (key1254, -2)]

def rawRow8501 : Integer.Sparse Key := [(key41, -24), (key205, 6), (key425, 6), (key425, 6), (key425, 6)]

def rawRow8502 : Integer.Sparse Key := [(key41, -24), (key425, 6), (key205, 6), (key425, 6), (key425, 6)]

def rawRow8503 : Integer.Sparse Key := [(key41, -24), (key425, 6), (key425, 6), (key205, 6), (key425, 6)]

def rawRow8504 : Integer.Sparse Key := [(key41, -24), (key425, 6), (key425, 6), (key425, 6), (key205, 6)]

def rawRow8505 : Integer.Sparse Key := [(key98, -24), (key16, 6), (key374, 6), (key425, 6), (key425, 6)]

def rawRow8506 : Integer.Sparse Key := [(key98, -24), (key16, 6), (key425, 6), (key374, 6), (key425, 6)]

def rawRow8507 : Integer.Sparse Key := [(key98, -24), (key16, 6), (key425, 6), (key425, 6), (key374, 6)]

def rawRow8508 : Integer.Sparse Key := [(key98, -24), (key41, 6), (key205, 6), (key425, 6), (key425, 6)]

def rawRow8509 : Integer.Sparse Key := [(key98, -24), (key41, 6), (key425, 6), (key205, 6), (key425, 6)]

def rawRow8510 : Integer.Sparse Key := [(key98, -24), (key41, 6), (key425, 6), (key425, 6), (key205, 6)]

def rawRow8511 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key16, 6), (key374, 6), (key425, 6)]

def rawRow8512 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key16, 6), (key425, 6), (key374, 6)]

def rawRow8513 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key41, 6), (key205, 6), (key425, 6)]

def rawRow8514 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key41, 6), (key425, 6), (key205, 6)]

def rawRow8515 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key98, 6), (key16, 6), (key374, 6)]

def rawRow8516 : Integer.Sparse Key := [(key98, -24), (key98, 6), (key98, 6), (key41, 6), (key205, 6)]

def rawRow8517 : Integer.Sparse Key := [(key45, -6), (key45, -6), (key45, -6), (key70, -6), (key20, 2), (key20, 2), (key20, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key133, 2)]

def rawRow8518 : Integer.Sparse Key := [(key45, -6), (key45, -6), (key70, -6), (key45, -6), (key102, 2), (key102, 2), (key133, 2), (key20, 2), (key20, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key20, 2), (key102, 2), (key102, 2)]

def rawRow8519 : Integer.Sparse Key := [(key45, -6), (key70, -6), (key45, -6), (key45, -6), (key102, 2), (key133, 2), (key102, 2), (key102, 2), (key133, 2), (key20, 2), (key133, 2), (key20, 2), (key102, 2), (key102, 2), (key20, 2), (key102, 2)]

def rawRow8520 : Integer.Sparse Key := [(key70, -6), (key45, -6), (key45, -6), (key45, -6), (key133, 2), (key102, 2), (key102, 2), (key133, 2), (key102, 2), (key133, 2), (key20, 2), (key102, 2), (key20, 2), (key102, 2), (key102, 2), (key20, 2)]

def rawRow8521 : Integer.Sparse Key := [(key102, -6), (key102, -6), (key111, -6), (key133, -6), (key20, 2), (key20, 2), (key31, 2), (key45, 2), (key45, 2), (key102, 2), (key102, 2), (key111, 2), (key111, 2), (key70, 2), (key133, 2), (key133, 2)]

def rawRow8522 : Integer.Sparse Key := [(key102, -6), (key111, -6), (key102, -6), (key133, -6), (key20, 2), (key31, 2), (key20, 2), (key102, 2), (key111, 2), (key45, 2), (key111, 2), (key45, 2), (key102, 2), (key133, 2), (key70, 2), (key133, 2)]

def rawRow8523 : Integer.Sparse Key := [(key111, -6), (key102, -6), (key102, -6), (key133, -6), (key31, 2), (key20, 2), (key20, 2), (key111, 2), (key102, 2), (key111, 2), (key45, 2), (key102, 2), (key45, 2), (key133, 2), (key133, 2), (key70, 2)]

def rawRow8524 : Integer.Sparse Key := [(key102, -6), (key102, -6), (key133, -6), (key111, -6), (key45, 2), (key45, 2), (key70, 2), (key20, 2), (key20, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key31, 2), (key111, 2), (key111, 2)]

def rawRow8525 : Integer.Sparse Key := [(key102, -6), (key133, -6), (key102, -6), (key111, -6), (key45, 2), (key70, 2), (key45, 2), (key102, 2), (key133, 2), (key20, 2), (key133, 2), (key20, 2), (key102, 2), (key111, 2), (key31, 2), (key111, 2)]

def rawRow8526 : Integer.Sparse Key := [(key133, -6), (key102, -6), (key102, -6), (key111, -6), (key70, 2), (key45, 2), (key45, 2), (key133, 2), (key102, 2), (key133, 2), (key20, 2), (key102, 2), (key20, 2), (key111, 2), (key111, 2), (key31, 2)]

def rawRow8527 : Integer.Sparse Key := [(key102, -6), (key111, -6), (key133, -6), (key102, -6), (key102, 2), (key111, 2), (key133, 2), (key20, 2), (key31, 2), (key45, 2), (key111, 2), (key70, 2), (key133, 2), (key20, 2), (key45, 2), (key102, 2)]

def rawRow8528 : Integer.Sparse Key := [(key111, -6), (key102, -6), (key133, -6), (key102, -6), (key111, 2), (key102, 2), (key133, 2), (key31, 2), (key20, 2), (key111, 2), (key45, 2), (key133, 2), (key70, 2), (key20, 2), (key102, 2), (key45, 2)]

def rawRow8529 : Integer.Sparse Key := [(key102, -6), (key133, -6), (key111, -6), (key102, -6), (key102, 2), (key133, 2), (key111, 2), (key45, 2), (key70, 2), (key20, 2), (key133, 2), (key31, 2), (key111, 2), (key45, 2), (key20, 2), (key102, 2)]

def rawRow8530 : Integer.Sparse Key := [(key133, -6), (key102, -6), (key111, -6), (key102, -6), (key133, 2), (key102, 2), (key111, 2), (key70, 2), (key45, 2), (key133, 2), (key20, 2), (key111, 2), (key31, 2), (key45, 2), (key102, 2), (key20, 2)]

def rawRow8531 : Integer.Sparse Key := [(key111, -6), (key133, -6), (key102, -6), (key102, -6), (key111, 2), (key133, 2), (key102, 2), (key111, 2), (key133, 2), (key31, 2), (key70, 2), (key20, 2), (key45, 2), (key102, 2), (key20, 2), (key45, 2)]

def rawRow8532 : Integer.Sparse Key := [(key133, -6), (key111, -6), (key102, -6), (key102, -6), (key133, 2), (key111, 2), (key102, 2), (key133, 2), (key111, 2), (key70, 2), (key31, 2), (key45, 2), (key20, 2), (key102, 2), (key45, 2), (key20, 2)]

def rawRow8533 : Integer.Sparse Key := [(key1287, -6), (key1564, -6), (key1564, -6), (key1564, -6), (key1307, 2), (key1307, 2), (key1307, 2), (key1415, 2), (key1415, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2)]

def rawRow8534 : Integer.Sparse Key := [(key1564, -6), (key1287, -6), (key1564, -6), (key1564, -6), (key1415, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1307, 2), (key1415, 2), (key1415, 2), (key1613, 2), (key1613, 2)]

def rawRow8535 : Integer.Sparse Key := [(key1564, -6), (key1564, -6), (key1287, -6), (key1564, -6), (key1613, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1307, 2), (key1415, 2)]

def rawRow8536 : Integer.Sparse Key := [(key1564, -6), (key1564, -6), (key1564, -6), (key1287, -6), (key1613, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1415, 2), (key1307, 2)]

def rawRow8537 : Integer.Sparse Key := [(key1307, -6), (key1537, -6), (key1613, -6), (key1613, -6), (key1287, 2), (key1307, 2), (key1307, 2), (key1382, 2), (key1415, 2), (key1415, 2), (key1537, 2), (key1537, 2), (key1564, 2), (key1564, 2), (key1613, 2), (key1613, 2)]

def rawRow8538 : Integer.Sparse Key := [(key1307, -6), (key1613, -6), (key1537, -6), (key1613, -6), (key1307, 2), (key1287, 2), (key1307, 2), (key1415, 2), (key1382, 2), (key1415, 2), (key1564, 2), (key1613, 2), (key1537, 2), (key1613, 2), (key1537, 2), (key1564, 2)]

def rawRow8539 : Integer.Sparse Key := [(key1307, -6), (key1613, -6), (key1613, -6), (key1537, -6), (key1307, 2), (key1307, 2), (key1287, 2), (key1415, 2), (key1415, 2), (key1382, 2), (key1613, 2), (key1564, 2), (key1613, 2), (key1537, 2), (key1564, 2), (key1537, 2)]

def rawRow8540 : Integer.Sparse Key := [(key1537, -6), (key1307, -6), (key1613, -6), (key1613, -6), (key1382, 2), (key1537, 2), (key1537, 2), (key1287, 2), (key1564, 2), (key1564, 2), (key1307, 2), (key1307, 2), (key1415, 2), (key1415, 2), (key1613, 2), (key1613, 2)]

def rawRow8541 : Integer.Sparse Key := [(key1537, -6), (key1613, -6), (key1307, -6), (key1613, -6), (key1537, 2), (key1382, 2), (key1537, 2), (key1564, 2), (key1287, 2), (key1564, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1307, 2), (key1415, 2)]

def rawRow8542 : Integer.Sparse Key := [(key1537, -6), (key1613, -6), (key1613, -6), (key1307, -6), (key1537, 2), (key1537, 2), (key1382, 2), (key1564, 2), (key1564, 2), (key1287, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1307, 2), (key1415, 2), (key1307, 2)]

def rawRow8543 : Integer.Sparse Key := [(key1613, -6), (key1307, -6), (key1537, -6), (key1613, -6), (key1415, 2), (key1564, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1613, 2), (key1287, 2), (key1307, 2), (key1382, 2), (key1415, 2), (key1537, 2), (key1564, 2)]

def rawRow8544 : Integer.Sparse Key := [(key1613, -6), (key1307, -6), (key1613, -6), (key1537, -6), (key1415, 2), (key1613, 2), (key1564, 2), (key1307, 2), (key1613, 2), (key1537, 2), (key1307, 2), (key1287, 2), (key1415, 2), (key1382, 2), (key1564, 2), (key1537, 2)]

def rawRow8545 : Integer.Sparse Key := [(key1613, -6), (key1537, -6), (key1307, -6), (key1613, -6), (key1564, 2), (key1415, 2), (key1613, 2), (key1537, 2), (key1307, 2), (key1613, 2), (key1382, 2), (key1537, 2), (key1287, 2), (key1564, 2), (key1307, 2), (key1415, 2)]

def rawRow8546 : Integer.Sparse Key := [(key1613, -6), (key1537, -6), (key1613, -6), (key1307, -6), (key1564, 2), (key1613, 2), (key1415, 2), (key1537, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1382, 2), (key1564, 2), (key1287, 2), (key1415, 2), (key1307, 2)]

def rawRow8547 : Integer.Sparse Key := [(key1613, -6), (key1613, -6), (key1307, -6), (key1537, -6), (key1613, 2), (key1415, 2), (key1564, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1415, 2), (key1564, 2), (key1307, 2), (key1537, 2), (key1287, 2), (key1382, 2)]

def rawRow8548 : Integer.Sparse Key := [(key1613, -6), (key1613, -6), (key1537, -6), (key1307, -6), (key1613, 2), (key1564, 2), (key1415, 2), (key1613, 2), (key1537, 2), (key1307, 2), (key1564, 2), (key1415, 2), (key1537, 2), (key1307, 2), (key1382, 2), (key1287, 2)]

def rawRow8549 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1525, -6), (key1892, -6), (key1250, 2), (key1250, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1914, 2)]

def rawRow8550 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1892, -6), (key1525, -6), (key1603, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1603, 2)]

def rawRow8551 : Integer.Sparse Key := [(key1525, -6), (key1892, -6), (key1525, -6), (key1525, -6), (key1603, 2), (key1914, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2)]

def rawRow8552 : Integer.Sparse Key := [(key1892, -6), (key1525, -6), (key1525, -6), (key1525, -6), (key1914, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1250, 2)]

def rawRow8553 : Integer.Sparse Key := [(key1603, -6), (key1603, -6), (key1677, -6), (key1914, -6), (key1250, 2), (key1250, 2), (key1269, 2), (key1525, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1677, 2), (key1677, 2), (key1892, 2), (key1914, 2), (key1914, 2)]

def rawRow8554 : Integer.Sparse Key := [(key1603, -6), (key1677, -6), (key1603, -6), (key1914, -6), (key1250, 2), (key1269, 2), (key1250, 2), (key1603, 2), (key1677, 2), (key1525, 2), (key1677, 2), (key1525, 2), (key1603, 2), (key1914, 2), (key1892, 2), (key1914, 2)]

def rawRow8555 : Integer.Sparse Key := [(key1677, -6), (key1603, -6), (key1603, -6), (key1914, -6), (key1269, 2), (key1250, 2), (key1250, 2), (key1677, 2), (key1603, 2), (key1677, 2), (key1525, 2), (key1603, 2), (key1525, 2), (key1914, 2), (key1914, 2), (key1892, 2)]

def rawRow8556 : Integer.Sparse Key := [(key1603, -6), (key1603, -6), (key1914, -6), (key1677, -6), (key1525, 2), (key1525, 2), (key1892, 2), (key1250, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1269, 2), (key1677, 2), (key1677, 2)]

def rawRow8557 : Integer.Sparse Key := [(key1603, -6), (key1914, -6), (key1603, -6), (key1677, -6), (key1525, 2), (key1892, 2), (key1525, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1677, 2), (key1269, 2), (key1677, 2)]

def rawRow8558 : Integer.Sparse Key := [(key1914, -6), (key1603, -6), (key1603, -6), (key1677, -6), (key1892, 2), (key1525, 2), (key1525, 2), (key1914, 2), (key1603, 2), (key1914, 2), (key1250, 2), (key1603, 2), (key1250, 2), (key1677, 2), (key1677, 2), (key1269, 2)]

def rawRow8559 : Integer.Sparse Key := [(key1603, -6), (key1677, -6), (key1914, -6), (key1603, -6), (key1603, 2), (key1677, 2), (key1914, 2), (key1250, 2), (key1269, 2), (key1525, 2), (key1677, 2), (key1892, 2), (key1914, 2), (key1250, 2), (key1525, 2), (key1603, 2)]

def rawRow8560 : Integer.Sparse Key := [(key1677, -6), (key1603, -6), (key1914, -6), (key1603, -6), (key1677, 2), (key1603, 2), (key1914, 2), (key1269, 2), (key1250, 2), (key1677, 2), (key1525, 2), (key1914, 2), (key1892, 2), (key1250, 2), (key1603, 2), (key1525, 2)]

def rawRow8561 : Integer.Sparse Key := [(key1603, -6), (key1914, -6), (key1677, -6), (key1603, -6), (key1603, 2), (key1914, 2), (key1677, 2), (key1525, 2), (key1892, 2), (key1250, 2), (key1914, 2), (key1269, 2), (key1677, 2), (key1525, 2), (key1250, 2), (key1603, 2)]

def rawRow8562 : Integer.Sparse Key := [(key1914, -6), (key1603, -6), (key1677, -6), (key1603, -6), (key1914, 2), (key1603, 2), (key1677, 2), (key1892, 2), (key1525, 2), (key1914, 2), (key1250, 2), (key1677, 2), (key1269, 2), (key1525, 2), (key1603, 2), (key1250, 2)]

def rawRow8563 : Integer.Sparse Key := [(key1677, -6), (key1914, -6), (key1603, -6), (key1603, -6), (key1677, 2), (key1914, 2), (key1603, 2), (key1677, 2), (key1914, 2), (key1269, 2), (key1892, 2), (key1250, 2), (key1525, 2), (key1603, 2), (key1250, 2), (key1525, 2)]

def rawRow8564 : Integer.Sparse Key := [(key1914, -6), (key1677, -6), (key1603, -6), (key1603, -6), (key1914, 2), (key1677, 2), (key1603, 2), (key1914, 2), (key1677, 2), (key1892, 2), (key1269, 2), (key1525, 2), (key1250, 2), (key1603, 2), (key1525, 2), (key1250, 2)]

def rawRow8565 : Integer.Sparse Key := [(key1289, -2), (key1289, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1902, -2), (key1902, -2), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1)]

def rawRow8566 : Integer.Sparse Key := [(key1566, -2), (key1566, -2), (key1902, -2), (key1289, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1902, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1)]

def rawRow8567 : Integer.Sparse Key := [(key1566, -2), (key1902, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1289, -2), (key1902, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1289, -2), (key1566, -2), (key1615, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1417, 1)]

def rawRow8568 : Integer.Sparse Key := [(key1902, -2), (key1566, -2), (key1566, -2), (key1902, -2), (key1566, -2), (key1902, -2), (key1289, -2), (key1566, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1289, -2), (key1917, 1), (key1615, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1417, 1), (key1309, 1)]

def rawRow8569 : Integer.Sparse Key := [(key1309, -2), (key1309, -2), (key1350, -2), (key1539, -2), (key1539, -2), (key1615, -2), (key1615, -2), (key1680, -2), (key1680, -2), (key1895, -2), (key1917, -2), (key1917, -2), (key1289, 1), (key1289, 1), (key1309, 1), (key1309, 1), (key1350, 1), (key1350, 1), (key1384, 1), (key1384, 1), (key1417, 1), (key1417, 1), (key1471, 1), (key1471, 1), (key1539, 1), (key1539, 1), (key1566, 1), (key1566, 1), (key1680, 1), (key1680, 1), (key1895, 1), (key1895, 1), (key1902, 1), (key1902, 1), (key1917, 1), (key1917, 1)]

def rawRow8570 : Integer.Sparse Key := [(key1309, -2), (key1350, -2), (key1309, -2), (key1615, -2), (key1680, -2), (key1539, -2), (key1680, -2), (key1539, -2), (key1615, -2), (key1917, -2), (key1895, -2), (key1917, -2), (key1309, 1), (key1350, 1), (key1289, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1917, 1), (key1895, 1), (key1902, 1)]

def rawRow8571 : Integer.Sparse Key := [(key1350, -2), (key1309, -2), (key1309, -2), (key1680, -2), (key1615, -2), (key1680, -2), (key1539, -2), (key1615, -2), (key1539, -2), (key1917, -2), (key1917, -2), (key1895, -2), (key1350, 1), (key1309, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1289, 1), (key1471, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1384, 1), (key1680, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1539, 1), (key1917, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1902, 1), (key1895, 1)]

def rawRow8572 : Integer.Sparse Key := [(key1539, -2), (key1539, -2), (key1895, -2), (key1309, -2), (key1309, -2), (key1615, -2), (key1615, -2), (key1917, -2), (key1917, -2), (key1350, -2), (key1680, -2), (key1680, -2), (key1384, 1), (key1384, 1), (key1539, 1), (key1539, 1), (key1895, 1), (key1895, 1), (key1289, 1), (key1289, 1), (key1566, 1), (key1566, 1), (key1902, 1), (key1902, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1350, 1), (key1350, 1), (key1471, 1), (key1471, 1), (key1680, 1), (key1680, 1)]

def rawRow8573 : Integer.Sparse Key := [(key1539, -2), (key1895, -2), (key1539, -2), (key1615, -2), (key1917, -2), (key1309, -2), (key1917, -2), (key1309, -2), (key1615, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1539, 1), (key1895, 1), (key1384, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1680, 1), (key1350, 1), (key1471, 1)]

def rawRow8574 : Integer.Sparse Key := [(key1895, -2), (key1539, -2), (key1539, -2), (key1917, -2), (key1615, -2), (key1917, -2), (key1309, -2), (key1615, -2), (key1309, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1895, 1), (key1539, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1384, 1), (key1902, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1289, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1680, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1471, 1), (key1350, 1)]

def rawRow8575 : Integer.Sparse Key := [(key1615, -2), (key1680, -2), (key1917, -2), (key1309, -2), (key1350, -2), (key1539, -2), (key1680, -2), (key1895, -2), (key1917, -2), (key1309, -2), (key1539, -2), (key1615, -2), (key1417, 1), (key1471, 1), (key1566, 1), (key1680, 1), (key1902, 1), (key1917, 1), (key1309, 1), (key1350, 1), (key1539, 1), (key1680, 1), (key1895, 1), (key1917, 1), (key1289, 1), (key1350, 1), (key1384, 1), (key1471, 1), (key1895, 1), (key1902, 1), (key1289, 1), (key1309, 1), (key1384, 1), (key1417, 1), (key1539, 1), (key1566, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8576 : Integer.Sparse Key := [(key1680, -2), (key1615, -2), (key1917, -2), (key1350, -2), (key1309, -2), (key1680, -2), (key1539, -2), (key1917, -2), (key1895, -2), (key1309, -2), (key1615, -2), (key1539, -2), (key1471, 1), (key1417, 1), (key1680, 1), (key1566, 1), (key1917, 1), (key1902, 1), (key1350, 1), (key1309, 1), (key1680, 1), (key1539, 1), (key1917, 1), (key1895, 1), (key1350, 1), (key1289, 1), (key1471, 1), (key1384, 1), (key1902, 1), (key1895, 1), (key1309, 1), (key1289, 1), (key1417, 1), (key1384, 1), (key1566, 1), (key1539, 1)]

def rawRow8577 : Integer.Sparse Key := [(key1615, -2), (key1917, -2), (key1680, -2), (key1539, -2), (key1895, -2), (key1309, -2), (key1917, -2), (key1350, -2), (key1680, -2), (key1539, -2), (key1309, -2), (key1615, -2), (key1566, 1), (key1902, 1), (key1417, 1), (key1917, 1), (key1471, 1), (key1680, 1), (key1539, 1), (key1895, 1), (key1309, 1), (key1917, 1), (key1350, 1), (key1680, 1), (key1384, 1), (key1895, 1), (key1289, 1), (key1902, 1), (key1350, 1), (key1471, 1), (key1384, 1), (key1539, 1), (key1289, 1), (key1566, 1), (key1309, 1), (key1417, 1)]

def rawRow8578 : Integer.Sparse Key := [(key1917, -2), (key1615, -2), (key1680, -2), (key1895, -2), (key1539, -2), (key1917, -2), (key1309, -2), (key1680, -2), (key1350, -2), (key1539, -2), (key1615, -2), (key1309, -2), (key1902, 1), (key1566, 1), (key1917, 1), (key1417, 1), (key1680, 1), (key1471, 1), (key1895, 1), (key1539, 1), (key1917, 1), (key1309, 1), (key1680, 1), (key1350, 1), (key1895, 1), (key1384, 1), (key1902, 1), (key1289, 1), (key1471, 1), (key1350, 1), (key1539, 1), (key1384, 1), (key1566, 1), (key1289, 1), (key1417, 1), (key1309, 1)]

def rawRow8579 : Integer.Sparse Key := [(key1680, -2), (key1917, -2), (key1615, -2), (key1680, -2), (key1917, -2), (key1350, -2), (key1895, -2), (key1309, -2), (key1539, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1680, 1), (key1917, 1), (key1471, 1), (key1902, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1917, 1), (key1350, 1), (key1895, 1), (key1309, 1), (key1539, 1), (key1471, 1), (key1902, 1), (key1350, 1), (key1895, 1), (key1289, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1309, 1), (key1539, 1), (key1289, 1), (key1384, 1)]

def rawRow8580 : Integer.Sparse Key := [(key1917, -2), (key1680, -2), (key1615, -2), (key1917, -2), (key1680, -2), (key1895, -2), (key1350, -2), (key1539, -2), (key1309, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1917, 1), (key1680, 1), (key1902, 1), (key1471, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1680, 1), (key1895, 1), (key1350, 1), (key1539, 1), (key1309, 1), (key1902, 1), (key1471, 1), (key1895, 1), (key1350, 1), (key1384, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1539, 1), (key1309, 1), (key1384, 1), (key1289, 1)]

def rawRow8581 : Integer.Sparse Key := [(key1523, -24), (key1248, 6), (key1601, 6), (key1601, 6), (key1601, 6)]

def rawRow8582 : Integer.Sparse Key := [(key1523, -24), (key1601, 6), (key1248, 6), (key1601, 6), (key1601, 6)]

def rawRow8583 : Integer.Sparse Key := [(key1523, -24), (key1601, 6), (key1601, 6), (key1248, 6), (key1601, 6)]

def rawRow8584 : Integer.Sparse Key := [(key1523, -24), (key1601, 6), (key1601, 6), (key1601, 6), (key1248, 6)]

def rawRow8585 : Integer.Sparse Key := [(key1601, -24), (key1248, 6), (key1523, 6), (key1601, 6), (key1601, 6)]

def rawRow8586 : Integer.Sparse Key := [(key1601, -24), (key1248, 6), (key1601, 6), (key1523, 6), (key1601, 6)]

def rawRow8587 : Integer.Sparse Key := [(key1601, -24), (key1248, 6), (key1601, 6), (key1601, 6), (key1523, 6)]

def rawRow8588 : Integer.Sparse Key := [(key1601, -24), (key1523, 6), (key1248, 6), (key1601, 6), (key1601, 6)]

def rawRow8589 : Integer.Sparse Key := [(key1601, -24), (key1523, 6), (key1601, 6), (key1248, 6), (key1601, 6)]

def rawRow8590 : Integer.Sparse Key := [(key1601, -24), (key1523, 6), (key1601, 6), (key1601, 6), (key1248, 6)]

def rawRow8591 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1248, 6), (key1523, 6), (key1601, 6)]

def rawRow8592 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1248, 6), (key1601, 6), (key1523, 6)]

def rawRow8593 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1523, 6), (key1248, 6), (key1601, 6)]

def rawRow8594 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1523, 6), (key1601, 6), (key1248, 6)]

def rawRow8595 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1601, 6), (key1248, 6), (key1523, 6)]

def rawRow8596 : Integer.Sparse Key := [(key1601, -24), (key1601, 6), (key1601, 6), (key1523, 6), (key1248, 6)]

def rawRow8597 : Integer.Sparse Key := [(key1384, -2), (key1384, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1895, -2), (key1895, -2), (key1289, 2), (key1289, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1902, 2), (key1902, 2)]

def rawRow8598 : Integer.Sparse Key := [(key1539, -2), (key1539, -2), (key1895, -2), (key1384, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1895, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1566, 2), (key1566, 2), (key1902, 2), (key1289, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1902, 2), (key1289, 2), (key1566, 2), (key1566, 2)]

def rawRow8599 : Integer.Sparse Key := [(key1539, -2), (key1895, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1384, -2), (key1895, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1384, -2), (key1539, -2), (key1566, 2), (key1902, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1289, 2), (key1902, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1289, 2), (key1566, 2)]

def rawRow8600 : Integer.Sparse Key := [(key1895, -2), (key1539, -2), (key1539, -2), (key1895, -2), (key1539, -2), (key1895, -2), (key1384, -2), (key1539, -2), (key1384, -2), (key1539, -2), (key1539, -2), (key1384, -2), (key1902, 2), (key1566, 2), (key1566, 2), (key1902, 2), (key1566, 2), (key1902, 2), (key1289, 2), (key1566, 2), (key1289, 2), (key1566, 2), (key1566, 2), (key1289, 2)]

def rawRow8601 : Integer.Sparse Key := [(key1417, -2), (key1417, -2), (key1471, -2), (key1566, -2), (key1566, -2), (key1615, -2), (key1615, -2), (key1680, -2), (key1680, -2), (key1902, -2), (key1917, -2), (key1917, -2), (key1309, 2), (key1309, 2), (key1350, 2), (key1539, 2), (key1539, 2), (key1615, 2), (key1615, 2), (key1680, 2), (key1680, 2), (key1895, 2), (key1917, 2), (key1917, 2)]

def rawRow8602 : Integer.Sparse Key := [(key1417, -2), (key1471, -2), (key1417, -2), (key1615, -2), (key1680, -2), (key1566, -2), (key1680, -2), (key1566, -2), (key1615, -2), (key1917, -2), (key1902, -2), (key1917, -2), (key1309, 2), (key1350, 2), (key1309, 2), (key1615, 2), (key1680, 2), (key1539, 2), (key1680, 2), (key1539, 2), (key1615, 2), (key1917, 2), (key1895, 2), (key1917, 2)]

def rawRow8603 : Integer.Sparse Key := [(key1471, -2), (key1417, -2), (key1417, -2), (key1680, -2), (key1615, -2), (key1680, -2), (key1566, -2), (key1615, -2), (key1566, -2), (key1917, -2), (key1917, -2), (key1902, -2), (key1350, 2), (key1309, 2), (key1309, 2), (key1680, 2), (key1615, 2), (key1680, 2), (key1539, 2), (key1615, 2), (key1539, 2), (key1917, 2), (key1917, 2), (key1895, 2)]

def rawRow8604 : Integer.Sparse Key := [(key1566, -2), (key1566, -2), (key1902, -2), (key1417, -2), (key1417, -2), (key1615, -2), (key1615, -2), (key1917, -2), (key1917, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1539, 2), (key1539, 2), (key1895, 2), (key1309, 2), (key1309, 2), (key1615, 2), (key1615, 2), (key1917, 2), (key1917, 2), (key1350, 2), (key1680, 2), (key1680, 2)]

def rawRow8605 : Integer.Sparse Key := [(key1566, -2), (key1902, -2), (key1566, -2), (key1615, -2), (key1917, -2), (key1417, -2), (key1917, -2), (key1417, -2), (key1615, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1539, 2), (key1895, 2), (key1539, 2), (key1615, 2), (key1917, 2), (key1309, 2), (key1917, 2), (key1309, 2), (key1615, 2), (key1680, 2), (key1350, 2), (key1680, 2)]

def rawRow8606 : Integer.Sparse Key := [(key1902, -2), (key1566, -2), (key1566, -2), (key1917, -2), (key1615, -2), (key1917, -2), (key1417, -2), (key1615, -2), (key1417, -2), (key1680, -2), (key1680, -2), (key1471, -2), (key1895, 2), (key1539, 2), (key1539, 2), (key1917, 2), (key1615, 2), (key1917, 2), (key1309, 2), (key1615, 2), (key1309, 2), (key1680, 2), (key1680, 2), (key1350, 2)]

def rawRow8607 : Integer.Sparse Key := [(key1615, -2), (key1680, -2), (key1917, -2), (key1417, -2), (key1471, -2), (key1566, -2), (key1680, -2), (key1902, -2), (key1917, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1615, 2), (key1680, 2), (key1917, 2), (key1309, 2), (key1350, 2), (key1539, 2), (key1680, 2), (key1895, 2), (key1917, 2), (key1309, 2), (key1539, 2), (key1615, 2)]

def rawRow8608 : Integer.Sparse Key := [(key1680, -2), (key1615, -2), (key1917, -2), (key1471, -2), (key1417, -2), (key1680, -2), (key1566, -2), (key1917, -2), (key1902, -2), (key1417, -2), (key1615, -2), (key1566, -2), (key1680, 2), (key1615, 2), (key1917, 2), (key1350, 2), (key1309, 2), (key1680, 2), (key1539, 2), (key1917, 2), (key1895, 2), (key1309, 2), (key1615, 2), (key1539, 2)]

def rawRow8609 : Integer.Sparse Key := [(key1615, -2), (key1917, -2), (key1680, -2), (key1566, -2), (key1902, -2), (key1417, -2), (key1917, -2), (key1471, -2), (key1680, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1615, 2), (key1917, 2), (key1680, 2), (key1539, 2), (key1895, 2), (key1309, 2), (key1917, 2), (key1350, 2), (key1680, 2), (key1539, 2), (key1309, 2), (key1615, 2)]

def rawRow8610 : Integer.Sparse Key := [(key1917, -2), (key1615, -2), (key1680, -2), (key1902, -2), (key1566, -2), (key1917, -2), (key1417, -2), (key1680, -2), (key1471, -2), (key1566, -2), (key1615, -2), (key1417, -2), (key1917, 2), (key1615, 2), (key1680, 2), (key1895, 2), (key1539, 2), (key1917, 2), (key1309, 2), (key1680, 2), (key1350, 2), (key1539, 2), (key1615, 2), (key1309, 2)]

def rawRow8611 : Integer.Sparse Key := [(key1680, -2), (key1917, -2), (key1615, -2), (key1680, -2), (key1917, -2), (key1471, -2), (key1902, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1417, -2), (key1566, -2), (key1680, 2), (key1917, 2), (key1615, 2), (key1680, 2), (key1917, 2), (key1350, 2), (key1895, 2), (key1309, 2), (key1539, 2), (key1615, 2), (key1309, 2), (key1539, 2)]

def rawRow8612 : Integer.Sparse Key := [(key1917, -2), (key1680, -2), (key1615, -2), (key1917, -2), (key1680, -2), (key1902, -2), (key1471, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1566, -2), (key1417, -2), (key1917, 2), (key1680, 2), (key1615, 2), (key1917, 2), (key1680, 2), (key1895, 2), (key1350, 2), (key1539, 2), (key1309, 2), (key1615, 2), (key1539, 2), (key1309, 2)]

def rawRow8613 : Integer.Sparse Key := [(key238, -2), (key238, -2), (key238, -2), (key408, -2), (key408, -2), (key408, -2), (key408, -2), (key408, -2), (key408, -2), (key417, -2), (key417, -2), (key417, -2), (key250, 1), (key250, 1), (key250, 1), (key250, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key387, 1), (key387, 1), (key387, 1), (key387, 1), (key437, 1), (key437, 1), (key437, 1), (key437, 1), (key437, 1), (key437, 1), (key449, 1), (key449, 1), (key449, 1), (key449, 1), (key449, 1), (key449, 1)]

def rawRow8614 : Integer.Sparse Key := [(key408, -2), (key408, -2), (key417, -2), (key238, -2), (key238, -2), (key408, -2), (key408, -2), (key417, -2), (key417, -2), (key238, -2), (key408, -2), (key408, -2), (key387, 1), (key387, 1), (key437, 1), (key437, 1), (key449, 1), (key449, 1), (key250, 1), (key250, 1), (key437, 1), (key437, 1), (key449, 1), (key449, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key449, 1), (key449, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key437, 1), (key437, 1)]

def rawRow8615 : Integer.Sparse Key := [(key408, -2), (key417, -2), (key408, -2), (key408, -2), (key417, -2), (key238, -2), (key417, -2), (key238, -2), (key408, -2), (key408, -2), (key238, -2), (key408, -2), (key437, 1), (key449, 1), (key387, 1), (key449, 1), (key387, 1), (key437, 1), (key437, 1), (key449, 1), (key250, 1), (key449, 1), (key250, 1), (key437, 1), (key387, 1), (key449, 1), (key250, 1), (key449, 1), (key250, 1), (key387, 1), (key387, 1), (key437, 1), (key250, 1), (key437, 1), (key250, 1), (key387, 1)]

def rawRow8616 : Integer.Sparse Key := [(key417, -2), (key408, -2), (key408, -2), (key417, -2), (key408, -2), (key417, -2), (key238, -2), (key408, -2), (key238, -2), (key408, -2), (key408, -2), (key238, -2), (key449, 1), (key437, 1), (key449, 1), (key387, 1), (key437, 1), (key387, 1), (key449, 1), (key437, 1), (key449, 1), (key250, 1), (key437, 1), (key250, 1), (key449, 1), (key387, 1), (key449, 1), (key250, 1), (key387, 1), (key250, 1), (key437, 1), (key387, 1), (key437, 1), (key250, 1), (key387, 1), (key250, 1)]

def rawRow8617 : Integer.Sparse Key := [(key250, -2), (key250, -2), (key259, -2), (key318, -2), (key318, -2), (key437, -2), (key437, -2), (key441, -2), (key441, -2), (key327, -2), (key449, -2), (key449, -2), (key238, 1), (key238, 1), (key250, 1), (key250, 1), (key259, 1), (key259, 1), (key304, 1), (key304, 1), (key387, 1), (key387, 1), (key396, 1), (key396, 1), (key318, 1), (key318, 1), (key408, 1), (key408, 1), (key441, 1), (key441, 1), (key327, 1), (key327, 1), (key417, 1), (key417, 1), (key449, 1), (key449, 1)]

def rawRow8618 : Integer.Sparse Key := [(key250, -2), (key259, -2), (key250, -2), (key437, -2), (key441, -2), (key318, -2), (key441, -2), (key318, -2), (key437, -2), (key449, -2), (key327, -2), (key449, -2), (key250, 1), (key259, 1), (key238, 1), (key259, 1), (key238, 1), (key250, 1), (key387, 1), (key396, 1), (key304, 1), (key396, 1), (key304, 1), (key387, 1), (key408, 1), (key441, 1), (key318, 1), (key441, 1), (key318, 1), (key408, 1), (key417, 1), (key449, 1), (key327, 1), (key449, 1), (key327, 1), (key417, 1)]

def rawRow8619 : Integer.Sparse Key := [(key259, -2), (key250, -2), (key250, -2), (key441, -2), (key437, -2), (key441, -2), (key318, -2), (key437, -2), (key318, -2), (key449, -2), (key449, -2), (key327, -2), (key259, 1), (key250, 1), (key259, 1), (key238, 1), (key250, 1), (key238, 1), (key396, 1), (key387, 1), (key396, 1), (key304, 1), (key387, 1), (key304, 1), (key441, 1), (key408, 1), (key441, 1), (key318, 1), (key408, 1), (key318, 1), (key449, 1), (key417, 1), (key449, 1), (key327, 1), (key417, 1), (key327, 1)]

def rawRow8620 : Integer.Sparse Key := [(key318, -2), (key318, -2), (key327, -2), (key250, -2), (key250, -2), (key437, -2), (key437, -2), (key449, -2), (key449, -2), (key259, -2), (key441, -2), (key441, -2), (key304, 1), (key304, 1), (key318, 1), (key318, 1), (key327, 1), (key327, 1), (key238, 1), (key238, 1), (key408, 1), (key408, 1), (key417, 1), (key417, 1), (key250, 1), (key250, 1), (key387, 1), (key387, 1), (key449, 1), (key449, 1), (key259, 1), (key259, 1), (key396, 1), (key396, 1), (key441, 1), (key441, 1)]

def rawRow8621 : Integer.Sparse Key := [(key318, -2), (key327, -2), (key318, -2), (key437, -2), (key449, -2), (key250, -2), (key449, -2), (key250, -2), (key437, -2), (key441, -2), (key259, -2), (key441, -2), (key318, 1), (key327, 1), (key304, 1), (key327, 1), (key304, 1), (key318, 1), (key408, 1), (key417, 1), (key238, 1), (key417, 1), (key238, 1), (key408, 1), (key387, 1), (key449, 1), (key250, 1), (key449, 1), (key250, 1), (key387, 1), (key396, 1), (key441, 1), (key259, 1), (key441, 1), (key259, 1), (key396, 1)]

def rawRow8622 : Integer.Sparse Key := [(key327, -2), (key318, -2), (key318, -2), (key449, -2), (key437, -2), (key449, -2), (key250, -2), (key437, -2), (key250, -2), (key441, -2), (key441, -2), (key259, -2), (key327, 1), (key318, 1), (key327, 1), (key304, 1), (key318, 1), (key304, 1), (key417, 1), (key408, 1), (key417, 1), (key238, 1), (key408, 1), (key238, 1), (key449, 1), (key387, 1), (key449, 1), (key250, 1), (key387, 1), (key250, 1), (key441, 1), (key396, 1), (key441, 1), (key259, 1), (key396, 1), (key259, 1)]

def rawRow8623 : Integer.Sparse Key := [(key437, -2), (key441, -2), (key449, -2), (key250, -2), (key259, -2), (key318, -2), (key441, -2), (key327, -2), (key449, -2), (key250, -2), (key318, -2), (key437, -2), (key387, 1), (key396, 1), (key408, 1), (key441, 1), (key417, 1), (key449, 1), (key250, 1), (key259, 1), (key318, 1), (key441, 1), (key327, 1), (key449, 1), (key238, 1), (key259, 1), (key304, 1), (key396, 1), (key327, 1), (key417, 1), (key238, 1), (key250, 1), (key304, 1), (key387, 1), (key318, 1), (key408, 1)]

def rawRow8624 : Integer.Sparse Key := [(key441, -2), (key437, -2), (key449, -2), (key259, -2), (key250, -2), (key441, -2), (key318, -2), (key449, -2), (key327, -2), (key250, -2), (key437, -2), (key318, -2), (key396, 1), (key387, 1), (key441, 1), (key408, 1), (key449, 1), (key417, 1), (key259, 1), (key250, 1), (key441, 1), (key318, 1), (key449, 1), (key327, 1), (key259, 1), (key238, 1), (key396, 1), (key304, 1), (key417, 1), (key327, 1), (key250, 1), (key238, 1), (key387, 1), (key304, 1), (key408, 1), (key318, 1)]

def rawRow8625 : Integer.Sparse Key := [(key437, -2), (key449, -2), (key441, -2), (key318, -2), (key327, -2), (key250, -2), (key449, -2), (key259, -2), (key441, -2), (key318, -2), (key250, -2), (key437, -2), (key408, 1), (key417, 1), (key387, 1), (key449, 1), (key396, 1), (key441, 1), (key318, 1), (key327, 1), (key250, 1), (key449, 1), (key259, 1), (key441, 1), (key304, 1), (key327, 1), (key238, 1), (key417, 1), (key259, 1), (key396, 1), (key304, 1), (key318, 1), (key238, 1), (key408, 1), (key250, 1), (key387, 1)]

def rawRow8626 : Integer.Sparse Key := [(key449, -2), (key437, -2), (key441, -2), (key327, -2), (key318, -2), (key449, -2), (key250, -2), (key441, -2), (key259, -2), (key318, -2), (key437, -2), (key250, -2), (key417, 1), (key408, 1), (key449, 1), (key387, 1), (key441, 1), (key396, 1), (key327, 1), (key318, 1), (key449, 1), (key250, 1), (key441, 1), (key259, 1), (key327, 1), (key304, 1), (key417, 1), (key238, 1), (key396, 1), (key259, 1), (key318, 1), (key304, 1), (key408, 1), (key238, 1), (key387, 1), (key250, 1)]

def rawRow8627 : Integer.Sparse Key := [(key441, -2), (key449, -2), (key437, -2), (key441, -2), (key449, -2), (key259, -2), (key327, -2), (key250, -2), (key318, -2), (key437, -2), (key250, -2), (key318, -2), (key441, 1), (key449, 1), (key396, 1), (key417, 1), (key387, 1), (key408, 1), (key441, 1), (key449, 1), (key259, 1), (key327, 1), (key250, 1), (key318, 1), (key396, 1), (key417, 1), (key259, 1), (key327, 1), (key238, 1), (key304, 1), (key387, 1), (key408, 1), (key250, 1), (key318, 1), (key238, 1), (key304, 1)]

def rawRow8628 : Integer.Sparse Key := [(key449, -2), (key441, -2), (key437, -2), (key449, -2), (key441, -2), (key327, -2), (key259, -2), (key318, -2), (key250, -2), (key437, -2), (key318, -2), (key250, -2), (key449, 1), (key441, 1), (key417, 1), (key396, 1), (key408, 1), (key387, 1), (key449, 1), (key441, 1), (key327, 1), (key259, 1), (key318, 1), (key250, 1), (key417, 1), (key396, 1), (key327, 1), (key259, 1), (key304, 1), (key238, 1), (key408, 1), (key387, 1), (key318, 1), (key250, 1), (key304, 1), (key238, 1)]

def rawRow8629 : Integer.Sparse Key := [(key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1917, 1), (key1350, -2), (key1350, -2), (key1350, -2), (key1471, -2), (key1471, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1680, -2), (key1680, -2), (key1680, -2), (key1680, -2)]

def rawRow8630 : Integer.Sparse Key := [(key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1471, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1350, -2), (key1471, -2), (key1471, -2), (key1680, -2), (key1680, -2)]

def rawRow8631 : Integer.Sparse Key := [(key1615, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1417, 1), (key1680, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1350, -2), (key1471, -2)]

def rawRow8632 : Integer.Sparse Key := [(key1917, 1), (key1615, 1), (key1917, 1), (key1417, 1), (key1615, 1), (key1417, 1), (key1917, 1), (key1615, 1), (key1917, 1), (key1309, 1), (key1615, 1), (key1309, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1615, 1), (key1417, 1), (key1615, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1680, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1680, -2), (key1350, -2), (key1680, -2), (key1471, -2), (key1680, -2), (key1350, -2), (key1471, -2), (key1350, -2)]

def rawRow8633 : Integer.Sparse Key := [(key1289, 1), (key1289, 1), (key1309, 1), (key1309, 1), (key1350, 1), (key1350, 1), (key1384, 1), (key1384, 1), (key1417, 1), (key1417, 1), (key1471, 1), (key1471, 1), (key1539, 1), (key1539, 1), (key1566, 1), (key1566, 1), (key1680, 1), (key1680, 1), (key1895, 1), (key1895, 1), (key1902, 1), (key1902, 1), (key1917, 1), (key1917, 1), (key1289, -2), (key1309, -2), (key1309, -2), (key1384, -2), (key1417, -2), (key1417, -2), (key1539, -2), (key1539, -2), (key1566, -2), (key1566, -2), (key1615, -2), (key1615, -2)]

def rawRow8634 : Integer.Sparse Key := [(key1309, 1), (key1350, 1), (key1289, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1917, 1), (key1895, 1), (key1902, 1), (key1309, -2), (key1289, -2), (key1309, -2), (key1417, -2), (key1384, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1539, -2), (key1615, -2), (key1539, -2), (key1566, -2)]

def rawRow8635 : Integer.Sparse Key := [(key1350, 1), (key1309, 1), (key1350, 1), (key1289, 1), (key1309, 1), (key1289, 1), (key1471, 1), (key1417, 1), (key1471, 1), (key1384, 1), (key1417, 1), (key1384, 1), (key1680, 1), (key1566, 1), (key1680, 1), (key1539, 1), (key1566, 1), (key1539, 1), (key1917, 1), (key1902, 1), (key1917, 1), (key1895, 1), (key1902, 1), (key1895, 1), (key1309, -2), (key1309, -2), (key1289, -2), (key1417, -2), (key1417, -2), (key1384, -2), (key1615, -2), (key1566, -2), (key1615, -2), (key1539, -2), (key1566, -2), (key1539, -2)]

def rawRow8636 : Integer.Sparse Key := [(key1384, 1), (key1384, 1), (key1539, 1), (key1539, 1), (key1895, 1), (key1895, 1), (key1289, 1), (key1289, 1), (key1566, 1), (key1566, 1), (key1902, 1), (key1902, 1), (key1309, 1), (key1309, 1), (key1417, 1), (key1417, 1), (key1917, 1), (key1917, 1), (key1350, 1), (key1350, 1), (key1471, 1), (key1471, 1), (key1680, 1), (key1680, 1), (key1384, -2), (key1539, -2), (key1539, -2), (key1289, -2), (key1566, -2), (key1566, -2), (key1309, -2), (key1309, -2), (key1417, -2), (key1417, -2), (key1615, -2), (key1615, -2)]

def rawRow8637 : Integer.Sparse Key := [(key1539, 1), (key1895, 1), (key1384, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1680, 1), (key1350, 1), (key1471, 1), (key1539, -2), (key1384, -2), (key1539, -2), (key1566, -2), (key1289, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1309, -2), (key1615, -2), (key1309, -2), (key1417, -2)]

def rawRow8638 : Integer.Sparse Key := [(key1895, 1), (key1539, 1), (key1895, 1), (key1384, 1), (key1539, 1), (key1384, 1), (key1902, 1), (key1566, 1), (key1902, 1), (key1289, 1), (key1566, 1), (key1289, 1), (key1917, 1), (key1417, 1), (key1917, 1), (key1309, 1), (key1417, 1), (key1309, 1), (key1680, 1), (key1471, 1), (key1680, 1), (key1350, 1), (key1471, 1), (key1350, 1), (key1539, -2), (key1539, -2), (key1384, -2), (key1566, -2), (key1566, -2), (key1289, -2), (key1615, -2), (key1417, -2), (key1615, -2), (key1309, -2), (key1417, -2), (key1309, -2)]

def rawRow8639 : Integer.Sparse Key := [(key1417, 1), (key1471, 1), (key1566, 1), (key1680, 1), (key1902, 1), (key1917, 1), (key1309, 1), (key1350, 1), (key1539, 1), (key1680, 1), (key1895, 1), (key1917, 1), (key1289, 1), (key1350, 1), (key1384, 1), (key1471, 1), (key1895, 1), (key1902, 1), (key1289, 1), (key1309, 1), (key1384, 1), (key1417, 1), (key1539, 1), (key1566, 1), (key1417, -2), (key1566, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1615, -2), (key1289, -2), (key1309, -2), (key1384, -2), (key1417, -2), (key1539, -2), (key1566, -2)]

def rawRow8640 : Integer.Sparse Key := [(key1471, 1), (key1417, 1), (key1680, 1), (key1566, 1), (key1917, 1), (key1902, 1), (key1350, 1), (key1309, 1), (key1680, 1), (key1539, 1), (key1917, 1), (key1895, 1), (key1350, 1), (key1289, 1), (key1471, 1), (key1384, 1), (key1902, 1), (key1895, 1), (key1309, 1), (key1289, 1), (key1417, 1), (key1384, 1), (key1566, 1), (key1539, 1), (key1417, -2), (key1615, -2), (key1566, -2), (key1309, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1289, -2), (key1417, -2), (key1384, -2), (key1566, -2), (key1539, -2)]

def rawRow8641 : Integer.Sparse Key := [(key1566, 1), (key1902, 1), (key1417, 1), (key1917, 1), (key1471, 1), (key1680, 1), (key1539, 1), (key1895, 1), (key1309, 1), (key1917, 1), (key1350, 1), (key1680, 1), (key1384, 1), (key1895, 1), (key1289, 1), (key1902, 1), (key1350, 1), (key1471, 1), (key1384, 1), (key1539, 1), (key1289, 1), (key1566, 1), (key1309, 1), (key1417, 1), (key1566, -2), (key1417, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1615, -2), (key1384, -2), (key1539, -2), (key1289, -2), (key1566, -2), (key1309, -2), (key1417, -2)]

def rawRow8642 : Integer.Sparse Key := [(key1902, 1), (key1566, 1), (key1917, 1), (key1417, 1), (key1680, 1), (key1471, 1), (key1895, 1), (key1539, 1), (key1917, 1), (key1309, 1), (key1680, 1), (key1350, 1), (key1895, 1), (key1384, 1), (key1902, 1), (key1289, 1), (key1471, 1), (key1350, 1), (key1539, 1), (key1384, 1), (key1566, 1), (key1289, 1), (key1417, 1), (key1309, 1), (key1566, -2), (key1615, -2), (key1417, -2), (key1539, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1384, -2), (key1566, -2), (key1289, -2), (key1417, -2), (key1309, -2)]

def rawRow8643 : Integer.Sparse Key := [(key1680, 1), (key1917, 1), (key1471, 1), (key1902, 1), (key1417, 1), (key1566, 1), (key1680, 1), (key1917, 1), (key1350, 1), (key1895, 1), (key1309, 1), (key1539, 1), (key1471, 1), (key1902, 1), (key1350, 1), (key1895, 1), (key1289, 1), (key1384, 1), (key1417, 1), (key1566, 1), (key1309, 1), (key1539, 1), (key1289, 1), (key1384, 1), (key1615, -2), (key1417, -2), (key1566, -2), (key1615, -2), (key1309, -2), (key1539, -2), (key1417, -2), (key1566, -2), (key1309, -2), (key1539, -2), (key1289, -2), (key1384, -2)]

def rawRow8644 : Integer.Sparse Key := [(key1917, 1), (key1680, 1), (key1902, 1), (key1471, 1), (key1566, 1), (key1417, 1), (key1917, 1), (key1680, 1), (key1895, 1), (key1350, 1), (key1539, 1), (key1309, 1), (key1902, 1), (key1471, 1), (key1895, 1), (key1350, 1), (key1384, 1), (key1289, 1), (key1566, 1), (key1417, 1), (key1539, 1), (key1309, 1), (key1384, 1), (key1289, 1), (key1615, -2), (key1566, -2), (key1417, -2), (key1615, -2), (key1539, -2), (key1309, -2), (key1566, -2), (key1417, -2), (key1539, -2), (key1309, -2), (key1384, -2), (key1289, -2)]

def rawRow8645 : Integer.Sparse Key := [(key234, -6), (key404, -6), (key404, -6), (key404, -6), (key246, 2), (key246, 2), (key246, 2), (key314, 2), (key314, 2), (key314, 2), (key433, 2), (key433, 2), (key433, 2), (key433, 2), (key433, 2), (key433, 2)]

def rawRow8646 : Integer.Sparse Key := [(key404, -6), (key234, -6), (key404, -6), (key404, -6), (key314, 2), (key433, 2), (key433, 2), (key246, 2), (key433, 2), (key433, 2), (key246, 2), (key246, 2), (key314, 2), (key314, 2), (key433, 2), (key433, 2)]

def rawRow8647 : Integer.Sparse Key := [(key404, -6), (key404, -6), (key234, -6), (key404, -6), (key433, 2), (key314, 2), (key433, 2), (key433, 2), (key246, 2), (key433, 2), (key314, 2), (key433, 2), (key246, 2), (key433, 2), (key246, 2), (key314, 2)]

def rawRow8648 : Integer.Sparse Key := [(key404, -6), (key404, -6), (key404, -6), (key234, -6), (key433, 2), (key433, 2), (key314, 2), (key433, 2), (key433, 2), (key246, 2), (key433, 2), (key314, 2), (key433, 2), (key246, 2), (key314, 2), (key246, 2)]

def rawRow8649 : Integer.Sparse Key := [(key246, -6), (key314, -6), (key433, -6), (key433, -6), (key234, 2), (key246, 2), (key246, 2), (key300, 2), (key314, 2), (key314, 2), (key383, 2), (key383, 2), (key404, 2), (key404, 2), (key433, 2), (key433, 2)]

def rawRow8650 : Integer.Sparse Key := [(key246, -6), (key433, -6), (key314, -6), (key433, -6), (key246, 2), (key234, 2), (key246, 2), (key314, 2), (key300, 2), (key314, 2), (key404, 2), (key433, 2), (key383, 2), (key433, 2), (key383, 2), (key404, 2)]

def rawRow8651 : Integer.Sparse Key := [(key246, -6), (key433, -6), (key433, -6), (key314, -6), (key246, 2), (key246, 2), (key234, 2), (key314, 2), (key314, 2), (key300, 2), (key433, 2), (key404, 2), (key433, 2), (key383, 2), (key404, 2), (key383, 2)]

def rawRow8652 : Integer.Sparse Key := [(key314, -6), (key246, -6), (key433, -6), (key433, -6), (key300, 2), (key314, 2), (key314, 2), (key234, 2), (key404, 2), (key404, 2), (key246, 2), (key246, 2), (key314, 2), (key314, 2), (key433, 2), (key433, 2)]

def rawRow8653 : Integer.Sparse Key := [(key314, -6), (key433, -6), (key246, -6), (key433, -6), (key314, 2), (key300, 2), (key314, 2), (key404, 2), (key234, 2), (key404, 2), (key314, 2), (key433, 2), (key246, 2), (key433, 2), (key246, 2), (key314, 2)]

def rawRow8654 : Integer.Sparse Key := [(key314, -6), (key433, -6), (key433, -6), (key246, -6), (key314, 2), (key314, 2), (key300, 2), (key404, 2), (key404, 2), (key234, 2), (key433, 2), (key314, 2), (key433, 2), (key246, 2), (key314, 2), (key246, 2)]

def rawRow8655 : Integer.Sparse Key := [(key433, -6), (key246, -6), (key314, -6), (key433, -6), (key383, 2), (key404, 2), (key433, 2), (key246, 2), (key314, 2), (key433, 2), (key234, 2), (key246, 2), (key300, 2), (key314, 2), (key383, 2), (key404, 2)]

def rawRow8656 : Integer.Sparse Key := [(key433, -6), (key246, -6), (key433, -6), (key314, -6), (key383, 2), (key433, 2), (key404, 2), (key246, 2), (key433, 2), (key314, 2), (key246, 2), (key234, 2), (key314, 2), (key300, 2), (key404, 2), (key383, 2)]

def rawRow8657 : Integer.Sparse Key := [(key433, -6), (key314, -6), (key246, -6), (key433, -6), (key404, 2), (key383, 2), (key433, 2), (key314, 2), (key246, 2), (key433, 2), (key300, 2), (key314, 2), (key234, 2), (key404, 2), (key246, 2), (key314, 2)]

def rawRow8658 : Integer.Sparse Key := [(key433, -6), (key314, -6), (key433, -6), (key246, -6), (key404, 2), (key433, 2), (key383, 2), (key314, 2), (key433, 2), (key246, 2), (key314, 2), (key300, 2), (key404, 2), (key234, 2), (key314, 2), (key246, 2)]

def rawRow8659 : Integer.Sparse Key := [(key433, -6), (key433, -6), (key246, -6), (key314, -6), (key433, 2), (key383, 2), (key404, 2), (key433, 2), (key246, 2), (key314, 2), (key383, 2), (key404, 2), (key246, 2), (key314, 2), (key234, 2), (key300, 2)]

def rawRow8660 : Integer.Sparse Key := [(key433, -6), (key433, -6), (key314, -6), (key246, -6), (key433, 2), (key404, 2), (key383, 2), (key433, 2), (key314, 2), (key246, 2), (key404, 2), (key383, 2), (key314, 2), (key246, 2), (key300, 2), (key234, 2)]

def rawRow8661 : Integer.Sparse Key := [(key2456, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2531, 2), (key2459, 2), (key2531, 2), (key2517, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2561, -2)]

def rawRow8662 : Integer.Sparse Key := [(key2456, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2531, 2), (key2459, 2), (key2520, -2), (key2517, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2561, -2), (key2520, -2)]

def rawRow8663 : Integer.Sparse Key := [(key2459, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2531, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2520, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2520, -2)]

def rawRow8664 : Integer.Sparse Key := [(key2531, 2), (key2531, 2), (key2531, 2), (key2459, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2561, -2), (key2561, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2517, -2), (key2517, -2)]

def rawRow8665 : Integer.Sparse Key := [(key2364, 2), (key2364, 2), (key2364, 2), (key2459, 2), (key2459, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2361, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2517, -2)]

def rawRow8666 : Integer.Sparse Key := [(key2459, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2364, 2), (key2459, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2)]

def rawRow8667 : Integer.Sparse Key := [(key2520, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2364, 2), (key2459, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2), (key2456, -2)]

def rawRow8668 : Integer.Sparse Key := [(key2520, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2364, 2), (key2459, 2), (key2364, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2)]

def rawRow8669 : Integer.Sparse Key := [(key969, -24), (key1083, 6), (key1083, 6), (key1083, 6), (key1177, 6)]

def rawRow8670 : Integer.Sparse Key := [(key969, -24), (key1083, 6), (key1083, 6), (key1177, 6), (key1083, 6)]

def rawRow8671 : Integer.Sparse Key := [(key969, -24), (key1083, 6), (key1177, 6), (key1083, 6), (key1083, 6)]

def rawRow8672 : Integer.Sparse Key := [(key969, -24), (key1177, 6), (key1083, 6), (key1083, 6), (key1083, 6)]

def rawRow8673 : Integer.Sparse Key := [(key1177, -24), (key969, 6), (key1083, 6), (key1083, 6), (key1083, 6)]

def rawRow8674 : Integer.Sparse Key := [(key1177, -24), (key1083, 6), (key969, 6), (key1083, 6), (key1083, 6)]

def rawRow8675 : Integer.Sparse Key := [(key1177, -24), (key1083, 6), (key1083, 6), (key969, 6), (key1083, 6)]

def rawRow8676 : Integer.Sparse Key := [(key1177, -24), (key1083, 6), (key1083, 6), (key1083, 6), (key969, 6)]

def rawRow8677 : Integer.Sparse Key := [(key972, -6), (key977, -6), (key977, -6), (key977, -6), (key1086, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1181, 2)]

def rawRow8678 : Integer.Sparse Key := [(key977, -6), (key972, -6), (key977, -6), (key977, -6), (key1091, 2), (key1086, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1181, 2), (key1091, 2)]

def rawRow8679 : Integer.Sparse Key := [(key977, -6), (key977, -6), (key972, -6), (key977, -6), (key1091, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1091, 2)]

def rawRow8680 : Integer.Sparse Key := [(key977, -6), (key977, -6), (key977, -6), (key972, -6), (key1181, 2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1086, 2)]

def rawRow8681 : Integer.Sparse Key := [(key1181, -6), (key1181, -6), (key1181, -6), (key1218, -6), (key977, 2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key1162, 2)]

def rawRow8682 : Integer.Sparse Key := [(key1181, -6), (key1181, -6), (key1218, -6), (key1181, -6), (key1091, 2), (key1091, 2), (key1162, 2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1091, 2)]

def rawRow8683 : Integer.Sparse Key := [(key1181, -6), (key1218, -6), (key1181, -6), (key1181, -6), (key1091, 2), (key1162, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1091, 2), (key977, 2), (key1091, 2)]

def rawRow8684 : Integer.Sparse Key := [(key1218, -6), (key1181, -6), (key1181, -6), (key1181, -6), (key1162, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1091, 2), (key977, 2), (key1091, 2), (key1091, 2), (key977, 2)]

def rawRow8685 : Integer.Sparse Key := [(key2397, -6), (key2397, -6), (key2397, -6), (key2431, -6), (key2463, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2474, 2), (key2497, 2)]

def rawRow8686 : Integer.Sparse Key := [(key2397, -6), (key2397, -6), (key2431, -6), (key2397, -6), (key2463, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2474, 2)]

def rawRow8687 : Integer.Sparse Key := [(key2397, -6), (key2431, -6), (key2397, -6), (key2397, -6), (key2474, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2)]

def rawRow8688 : Integer.Sparse Key := [(key2431, -6), (key2397, -6), (key2397, -6), (key2397, -6), (key2497, 2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2)]

def rawRow8689 : Integer.Sparse Key := [(key2384, -6), (key2474, -6), (key2474, -6), (key2474, -6), (key2369, 2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2)]

def rawRow8690 : Integer.Sparse Key := [(key2474, -6), (key2384, -6), (key2474, -6), (key2474, -6), (key2397, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

def rawRow8691 : Integer.Sparse Key := [(key2474, -6), (key2474, -6), (key2384, -6), (key2474, -6), (key2463, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2397, 2)]

def rawRow8692 : Integer.Sparse Key := [(key2474, -6), (key2474, -6), (key2474, -6), (key2384, -6), (key2463, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2397, 2), (key2369, 2)]

def rawRow8693 : Integer.Sparse Key := [(key2354, -6), (key2358, -6), (key2358, -6), (key2358, -6), (key2449, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2529, 2)]

def rawRow8694 : Integer.Sparse Key := [(key2358, -6), (key2354, -6), (key2358, -6), (key2358, -6), (key2453, 2), (key2449, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2529, 2), (key2453, 2)]

def rawRow8695 : Integer.Sparse Key := [(key2358, -6), (key2358, -6), (key2354, -6), (key2358, -6), (key2453, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2453, 2)]

def rawRow8696 : Integer.Sparse Key := [(key2358, -6), (key2358, -6), (key2358, -6), (key2354, -6), (key2529, 2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2449, 2)]

def rawRow8697 : Integer.Sparse Key := [(key2529, -6), (key2529, -6), (key2529, -6), (key2559, -6), (key2358, 2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2514, 2)]

def rawRow8698 : Integer.Sparse Key := [(key2529, -6), (key2529, -6), (key2559, -6), (key2529, -6), (key2453, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2453, 2)]

def rawRow8699 : Integer.Sparse Key := [(key2529, -6), (key2559, -6), (key2529, -6), (key2529, -6), (key2453, 2), (key2514, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2358, 2), (key2453, 2)]

def rawRow8700 : Integer.Sparse Key := [(key2559, -6), (key2529, -6), (key2529, -6), (key2529, -6), (key2514, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2358, 2)]

def rawRow8701 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2767, -2), (key2763, -2), (key2930, -2), (key2767, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2930, -2), (key2840, 1), (key2844, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2888, 1), (key2967, 1)]

def rawRow8702 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2930, -2), (key2763, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2930, -2), (key2767, -2), (key2844, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2888, 1)]

def rawRow8703 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2930, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2763, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8704 : Integer.Sparse Key := [(key2930, -2), (key2930, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2763, -2), (key2763, -2), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1)]

def rawRow8705 : Integer.Sparse Key := [(key2599, -2), (key2599, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2909, -2), (key2909, -2), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1)]

def rawRow8706 : Integer.Sparse Key := [(key2888, -2), (key2888, -2), (key2909, -2), (key2599, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2909, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1)]

def rawRow8707 : Integer.Sparse Key := [(key2888, -2), (key2909, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2599, -2), (key2909, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2599, -2), (key2888, -2), (key2844, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2767, 1)]

def rawRow8708 : Integer.Sparse Key := [(key2909, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2888, -2), (key2909, -2), (key2599, -2), (key2888, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2599, -2), (key2875, 1), (key2844, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2767, 1), (key2588, 1)]

def rawRow8709 : Integer.Sparse Key := [(key2352, -24), (key2447, 6), (key2447, 6), (key2447, 6), (key2511, 6)]

def rawRow8710 : Integer.Sparse Key := [(key2352, -24), (key2447, 6), (key2447, 6), (key2511, 6), (key2447, 6)]

def rawRow8711 : Integer.Sparse Key := [(key2352, -24), (key2447, 6), (key2511, 6), (key2447, 6), (key2447, 6)]

def rawRow8712 : Integer.Sparse Key := [(key2352, -24), (key2511, 6), (key2447, 6), (key2447, 6), (key2447, 6)]

def rawRow8713 : Integer.Sparse Key := [(key2511, -24), (key2352, 6), (key2447, 6), (key2447, 6), (key2447, 6)]

def rawRow8714 : Integer.Sparse Key := [(key2511, -24), (key2447, 6), (key2352, 6), (key2447, 6), (key2447, 6)]

def rawRow8715 : Integer.Sparse Key := [(key2511, -24), (key2447, 6), (key2447, 6), (key2352, 6), (key2447, 6)]

def rawRow8716 : Integer.Sparse Key := [(key2511, -24), (key2447, 6), (key2447, 6), (key2447, 6), (key2352, 6)]

def rawRow8717 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2588, -2), (key2584, -2), (key2599, -2), (key2588, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2599, -2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2)]

def rawRow8718 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2599, -2), (key2584, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2599, -2), (key2588, -2), (key2767, 2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2767, 2)]

def rawRow8719 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2599, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2584, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2)]

def rawRow8720 : Integer.Sparse Key := [(key2599, -2), (key2599, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2584, -2), (key2584, -2), (key2930, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2763, 2)]

def rawRow8721 : Integer.Sparse Key := [(key2930, -2), (key2930, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2988, -2), (key2988, -2), (key2599, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2909, 2)]

def rawRow8722 : Integer.Sparse Key := [(key2967, -2), (key2967, -2), (key2988, -2), (key2930, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2988, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2)]

def rawRow8723 : Integer.Sparse Key := [(key2967, -2), (key2988, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2930, -2), (key2988, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2930, -2), (key2967, -2), (key2888, 2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2888, 2)]

def rawRow8724 : Integer.Sparse Key := [(key2988, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2967, -2), (key2988, -2), (key2930, -2), (key2967, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2930, -2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2)]

def rawRow8725 : Integer.Sparse Key := [(key1527, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1532, -2), (key1527, -2), (key1766, -2), (key1532, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1766, -2), (key1605, 1), (key1610, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1649, 1), (key1605, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1807, 1), (key1649, 1), (key1807, 1), (key1610, 1), (key1649, 1), (key1610, 1), (key1807, 1), (key1649, 1), (key1807, 1)]

def rawRow8726 : Integer.Sparse Key := [(key1532, -2), (key1527, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1766, -2), (key1527, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1766, -2), (key1532, -2), (key1610, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1649, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1649, 1)]

def rawRow8727 : Integer.Sparse Key := [(key1532, -2), (key1532, -2), (key1527, -2), (key1766, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1527, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1807, 1), (key1807, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1605, 1), (key1605, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1)]

def rawRow8728 : Integer.Sparse Key := [(key1766, -2), (key1766, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1527, -2), (key1527, -2), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1)]

def rawRow8729 : Integer.Sparse Key := [(key1266, -2), (key1266, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1672, -2), (key1672, -2), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1)]

def rawRow8730 : Integer.Sparse Key := [(key1649, -2), (key1649, -2), (key1672, -2), (key1266, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1672, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1257, 1), (key1257, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1638, 1), (key1638, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1)]

def rawRow8731 : Integer.Sparse Key := [(key1649, -2), (key1672, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1266, -2), (key1672, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1266, -2), (key1649, -2), (key1610, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1532, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1532, 1)]

def rawRow8732 : Integer.Sparse Key := [(key1672, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1649, -2), (key1672, -2), (key1266, -2), (key1649, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1266, -2), (key1638, 1), (key1610, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1532, 1), (key1638, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1257, 1), (key1532, 1), (key1257, 1), (key1610, 1), (key1532, 1), (key1610, 1), (key1257, 1), (key1532, 1), (key1257, 1)]

def rawRow8733 : Integer.Sparse Key := [(key2840, 1), (key2844, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2875, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2988, -2), (key2909, -2), (key2988, -2)]

def rawRow8734 : Integer.Sparse Key := [(key2844, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2888, 1), (key2875, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2988, -2), (key2909, -2)]

def rawRow8735 : Integer.Sparse Key := [(key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2909, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2988, -2), (key2909, -2), (key2909, -2), (key2875, -2), (key2875, -2)]

def rawRow8736 : Integer.Sparse Key := [(key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2988, -2), (key2988, -2), (key2988, -2), (key2909, -2), (key2909, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2875, -2), (key2875, -2), (key2875, -2), (key2875, -2)]

def rawRow8737 : Integer.Sparse Key := [(key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2584, -2), (key2584, -2), (key2584, -2), (key2763, -2), (key2763, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2840, -2), (key2840, -2), (key2840, -2), (key2840, -2)]

def rawRow8738 : Integer.Sparse Key := [(key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2763, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2584, -2), (key2763, -2), (key2763, -2), (key2840, -2), (key2840, -2)]

def rawRow8739 : Integer.Sparse Key := [(key2844, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2767, 1), (key2840, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2584, -2), (key2763, -2)]

def rawRow8740 : Integer.Sparse Key := [(key2875, 1), (key2844, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2840, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2584, -2), (key2763, -2), (key2584, -2)]

def rawRow8741 : Integer.Sparse Key := [(key1524, -6), (key1524, -6), (key1524, -6), (key1762, -6), (key1602, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1803, 2), (key1645, 2), (key1803, 2)]

def rawRow8742 : Integer.Sparse Key := [(key1524, -6), (key1524, -6), (key1762, -6), (key1524, -6), (key1602, 2), (key1645, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1803, 2), (key1645, 2)]

def rawRow8743 : Integer.Sparse Key := [(key1524, -6), (key1762, -6), (key1524, -6), (key1524, -6), (key1645, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1803, 2), (key1645, 2), (key1645, 2), (key1602, 2), (key1602, 2)]

def rawRow8744 : Integer.Sparse Key := [(key1762, -6), (key1524, -6), (key1524, -6), (key1524, -6), (key1803, 2), (key1803, 2), (key1803, 2), (key1645, 2), (key1645, 2), (key1645, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2)]

def rawRow8745 : Integer.Sparse Key := [(key1262, -6), (key1645, -6), (key1645, -6), (key1645, -6), (key1249, 2), (key1249, 2), (key1249, 2), (key1524, 2), (key1524, 2), (key1524, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2)]

def rawRow8746 : Integer.Sparse Key := [(key1645, -6), (key1262, -6), (key1645, -6), (key1645, -6), (key1524, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1249, 2), (key1524, 2), (key1524, 2), (key1602, 2), (key1602, 2)]

def rawRow8747 : Integer.Sparse Key := [(key1645, -6), (key1645, -6), (key1262, -6), (key1645, -6), (key1602, 2), (key1524, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1249, 2), (key1524, 2)]

def rawRow8748 : Integer.Sparse Key := [(key1645, -6), (key1645, -6), (key1645, -6), (key1262, -6), (key1602, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1249, 2), (key1524, 2), (key1249, 2)]

def rawRow8749 : Integer.Sparse Key := [(key2353, 6), (key2356, 6), (key2356, 6), (key2356, 6), (key2527, -6), (key2527, -6), (key2527, -6), (key2558, -6)]

def rawRow8750 : Integer.Sparse Key := [(key2356, 6), (key2353, 6), (key2356, 6), (key2356, 6), (key2527, -6), (key2527, -6), (key2558, -6), (key2527, -6)]

def rawRow8751 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2353, 6), (key2356, 6), (key2527, -6), (key2558, -6), (key2527, -6), (key2527, -6)]

def rawRow8752 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2356, 6), (key2353, 6), (key2558, -6), (key2527, -6), (key2527, -6), (key2527, -6)]

def rawRow8753 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2353, -6), (key2448, -6), (key2448, -6), (key2448, -6)]

def rawRow8754 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2448, -6), (key2353, -6), (key2448, -6), (key2448, -6)]

def rawRow8755 : Integer.Sparse Key := [(key2527, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2448, -6), (key2448, -6), (key2353, -6), (key2448, -6)]

def rawRow8756 : Integer.Sparse Key := [(key2558, 6), (key2527, 6), (key2527, 6), (key2527, 6), (key2448, -6), (key2448, -6), (key2448, -6), (key2353, -6)]

def rawRow8757 : Integer.Sparse Key := [(key2366, 2), (key2366, 2), (key2366, 2), (key2461, 2), (key2461, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2361, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2517, -2)]

def rawRow8758 : Integer.Sparse Key := [(key2461, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2366, 2), (key2461, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2)]

def rawRow8759 : Integer.Sparse Key := [(key2523, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2366, 2), (key2461, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2), (key2456, -2)]

def rawRow8760 : Integer.Sparse Key := [(key2523, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2366, 2), (key2461, 2), (key2366, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2)]

def rawRow8761 : Integer.Sparse Key := [(key1226, -24), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6)]

def rawRow8762 : Integer.Sparse Key := [(key1226, -24), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6)]

def rawRow8763 : Integer.Sparse Key := [(key1226, -24), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6)]

def rawRow8764 : Integer.Sparse Key := [(key1226, -24), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6)]

def rawRow8765 : Integer.Sparse Key := [(key1228, -6), (key1228, -6), (key1228, -6), (key1245, -6), (key979, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key1164, 2)]

def rawRow8766 : Integer.Sparse Key := [(key1228, -6), (key1228, -6), (key1245, -6), (key1228, -6), (key1093, 2), (key1093, 2), (key1164, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1093, 2)]

def rawRow8767 : Integer.Sparse Key := [(key1228, -6), (key1245, -6), (key1228, -6), (key1228, -6), (key1093, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1093, 2), (key979, 2), (key1093, 2)]

def rawRow8768 : Integer.Sparse Key := [(key1245, -6), (key1228, -6), (key1228, -6), (key1228, -6), (key1164, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1093, 2), (key979, 2), (key1093, 2), (key1093, 2), (key979, 2)]

def rawRow8769 : Integer.Sparse Key := [(key2385, -6), (key2475, -6), (key2475, -6), (key2475, -6), (key2372, 2), (key2372, 2), (key2372, 2), (key2400, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2)]

def rawRow8770 : Integer.Sparse Key := [(key2475, -6), (key2385, -6), (key2475, -6), (key2475, -6), (key2400, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2372, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2)]

def rawRow8771 : Integer.Sparse Key := [(key2475, -6), (key2475, -6), (key2385, -6), (key2475, -6), (key2466, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2400, 2)]

def rawRow8772 : Integer.Sparse Key := [(key2475, -6), (key2475, -6), (key2475, -6), (key2385, -6), (key2466, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2400, 2), (key2372, 2)]

def rawRow8773 : Integer.Sparse Key := [(key2566, -6), (key2566, -6), (key2566, -6), (key2578, -6), (key2359, 2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2515, 2)]

def rawRow8774 : Integer.Sparse Key := [(key2566, -6), (key2566, -6), (key2578, -6), (key2566, -6), (key2454, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2454, 2)]

def rawRow8775 : Integer.Sparse Key := [(key2566, -6), (key2578, -6), (key2566, -6), (key2566, -6), (key2454, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2359, 2), (key2454, 2)]

def rawRow8776 : Integer.Sparse Key := [(key2578, -6), (key2566, -6), (key2566, -6), (key2566, -6), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2359, 2)]

def rawRow8777 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2404, -2), (key2398, -2), (key2435, -2), (key2404, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2435, -2), (key2464, 1), (key2470, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2478, 1), (key2501, 1)]

def rawRow8778 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2435, -2), (key2398, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2435, -2), (key2404, -2), (key2470, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2478, 1)]

def rawRow8779 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2398, -2), (key2435, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2398, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1)]

def rawRow8780 : Integer.Sparse Key := [(key2435, -2), (key2435, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2398, -2), (key2398, -2), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1)]

def rawRow8781 : Integer.Sparse Key := [(key2604, -2), (key2604, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2925, -2), (key2925, -2), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1)]

def rawRow8782 : Integer.Sparse Key := [(key2916, -2), (key2916, -2), (key2925, -2), (key2604, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2925, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1)]

def rawRow8783 : Integer.Sparse Key := [(key2916, -2), (key2925, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2604, -2), (key2925, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2604, -2), (key2916, -2), (key2845, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2768, 1)]

def rawRow8784 : Integer.Sparse Key := [(key2925, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2916, -2), (key2925, -2), (key2604, -2), (key2916, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2604, -2), (key2876, 1), (key2845, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2768, 1), (key2589, 1)]

def rawRow8785 : Integer.Sparse Key := [(key2355, -24), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6)]

def rawRow8786 : Integer.Sparse Key := [(key2355, -24), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6)]

def rawRow8787 : Integer.Sparse Key := [(key2355, -24), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6)]

def rawRow8788 : Integer.Sparse Key := [(key2355, -24), (key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6)]

def rawRow8789 : Integer.Sparse Key := [(key2512, -24), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6)]

def rawRow8790 : Integer.Sparse Key := [(key2512, -24), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6)]

def rawRow8791 : Integer.Sparse Key := [(key2512, -24), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6)]

def rawRow8792 : Integer.Sparse Key := [(key2512, -24), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6)]

def rawRow8793 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2376, -2), (key2370, -2), (key2388, -2), (key2376, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2404, 2), (key2398, 2), (key2435, 2), (key2404, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2435, 2)]

def rawRow8794 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2388, -2), (key2370, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2388, -2), (key2376, -2), (key2404, 2), (key2398, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2435, 2), (key2398, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2435, 2), (key2404, 2)]

def rawRow8795 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2370, -2), (key2388, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2370, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2404, 2), (key2404, 2), (key2398, 2), (key2435, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2398, 2), (key2435, 2), (key2404, 2), (key2404, 2)]

def rawRow8796 : Integer.Sparse Key := [(key2388, -2), (key2388, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2370, -2), (key2370, -2), (key2435, 2), (key2435, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2398, 2), (key2398, 2)]

def rawRow8797 : Integer.Sparse Key := [(key3005, -2), (key3005, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3028, -2), (key3028, -2), (key2604, 2), (key2604, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2925, 2), (key2925, 2)]

def rawRow8798 : Integer.Sparse Key := [(key3019, -2), (key3019, -2), (key3028, -2), (key3005, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3028, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key2916, 2), (key2916, 2), (key2925, 2), (key2604, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2925, 2), (key2604, 2), (key2916, 2), (key2916, 2)]

def rawRow8799 : Integer.Sparse Key := [(key3019, -2), (key3028, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3005, -2), (key3028, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3005, -2), (key3019, -2), (key2916, 2), (key2925, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2604, 2), (key2925, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2604, 2), (key2916, 2)]

def rawRow8800 : Integer.Sparse Key := [(key3028, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3019, -2), (key3028, -2), (key3005, -2), (key3019, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3005, -2), (key2925, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2916, 2), (key2925, 2), (key2604, 2), (key2916, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2604, 2)]

def rawRow8801 : Integer.Sparse Key := [(key1526, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1534, -2), (key1526, -2), (key1894, -2), (key1534, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1894, -2), (key1604, 1), (key1612, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1679, 1), (key1604, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1604, 1), (key1679, 1), (key1604, 1), (key1916, 1), (key1679, 1), (key1916, 1), (key1612, 1), (key1679, 1), (key1612, 1), (key1916, 1), (key1679, 1), (key1916, 1)]

def rawRow8802 : Integer.Sparse Key := [(key1534, -2), (key1526, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1894, -2), (key1526, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1894, -2), (key1534, -2), (key1612, 1), (key1604, 1), (key1679, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1679, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1679, 1)]

def rawRow8803 : Integer.Sparse Key := [(key1534, -2), (key1534, -2), (key1526, -2), (key1894, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1526, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1916, 1), (key1916, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1604, 1), (key1604, 1), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1)]

def rawRow8804 : Integer.Sparse Key := [(key1894, -2), (key1894, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1526, -2), (key1526, -2), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1)]

def rawRow8805 : Integer.Sparse Key := [(key1271, -2), (key1271, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1693, -2), (key1693, -2), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1)]

def rawRow8806 : Integer.Sparse Key := [(key1679, -2), (key1679, -2), (key1693, -2), (key1271, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1693, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1259, 1), (key1259, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1640, 1), (key1640, 1), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1)]

def rawRow8807 : Integer.Sparse Key := [(key1679, -2), (key1693, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1271, -2), (key1693, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1271, -2), (key1679, -2), (key1612, 1), (key1640, 1), (key1534, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1534, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1534, 1)]

def rawRow8808 : Integer.Sparse Key := [(key1693, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1679, -2), (key1693, -2), (key1271, -2), (key1679, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1271, -2), (key1640, 1), (key1612, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1534, 1), (key1640, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1640, 1), (key1534, 1), (key1640, 1), (key1259, 1), (key1534, 1), (key1259, 1), (key1612, 1), (key1534, 1), (key1612, 1), (key1259, 1), (key1534, 1), (key1259, 1)]

def rawRow8809 : Integer.Sparse Key := [(key2464, 1), (key2470, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2478, 1), (key2501, 1), (key2568, -2), (key2568, -2), (key2570, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2570, -2), (key2568, -2), (key2575, -2), (key2570, -2), (key2575, -2)]

def rawRow8810 : Integer.Sparse Key := [(key2470, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2478, 1), (key2568, -2), (key2570, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2570, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2575, -2), (key2570, -2)]

def rawRow8811 : Integer.Sparse Key := [(key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2570, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2575, -2), (key2570, -2), (key2570, -2), (key2568, -2), (key2568, -2)]

def rawRow8812 : Integer.Sparse Key := [(key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2575, -2), (key2575, -2), (key2575, -2), (key2570, -2), (key2570, -2), (key2570, -2), (key2568, -2), (key2568, -2), (key2568, -2), (key2568, -2), (key2568, -2), (key2568, -2)]

def rawRow8813 : Integer.Sparse Key := [(key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2370, -2), (key2370, -2), (key2370, -2), (key2398, -2), (key2398, -2), (key2398, -2), (key2464, -2), (key2464, -2), (key2464, -2), (key2464, -2), (key2464, -2), (key2464, -2)]

def rawRow8814 : Integer.Sparse Key := [(key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2762, -2), (key2839, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2839, -2), (key2370, -2), (key2370, -2), (key2398, -2), (key2398, -2), (key2464, -2), (key2464, -2)]

def rawRow8815 : Integer.Sparse Key := [(key2845, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2768, 1), (key2839, -2), (key2762, -2), (key2839, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2762, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2370, -2), (key2398, -2)]

def rawRow8816 : Integer.Sparse Key := [(key2876, 1), (key2845, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2768, 1), (key2589, 1), (key2839, -2), (key2839, -2), (key2762, -2), (key2839, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2762, -2), (key2839, -2), (key2583, -2), (key2762, -2), (key2583, -2)]

def rawRow8817 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1525, -6), (key1892, -6), (key1603, 2), (key1603, 2), (key1677, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1677, 2), (key1603, 2), (key1914, 2), (key1677, 2), (key1914, 2)]

def rawRow8818 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1892, -6), (key1525, -6), (key1603, 2), (key1677, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1677, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1914, 2), (key1677, 2)]

def rawRow8819 : Integer.Sparse Key := [(key1525, -6), (key1892, -6), (key1525, -6), (key1525, -6), (key1677, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1677, 2), (key1677, 2), (key1603, 2), (key1603, 2)]

def rawRow8820 : Integer.Sparse Key := [(key1892, -6), (key1525, -6), (key1525, -6), (key1525, -6), (key1914, 2), (key1914, 2), (key1914, 2), (key1677, 2), (key1677, 2), (key1677, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2)]

def rawRow8821 : Integer.Sparse Key := [(key1269, -6), (key1677, -6), (key1677, -6), (key1677, -6), (key1250, 2), (key1250, 2), (key1250, 2), (key1525, 2), (key1525, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2)]

def rawRow8822 : Integer.Sparse Key := [(key1677, -6), (key1269, -6), (key1677, -6), (key1677, -6), (key1525, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1250, 2), (key1525, 2), (key1525, 2), (key1603, 2), (key1603, 2)]

def rawRow8823 : Integer.Sparse Key := [(key1677, -6), (key1677, -6), (key1269, -6), (key1677, -6), (key1603, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1525, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1250, 2), (key1525, 2)]

def rawRow8824 : Integer.Sparse Key := [(key1677, -6), (key1677, -6), (key1677, -6), (key1269, -6), (key1603, 2), (key1603, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1525, 2), (key1603, 2), (key1250, 2), (key1525, 2), (key1250, 2)]

def rawRow8825 : Integer.Sparse Key := [(key2354, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2529, -6), (key2529, -6), (key2529, -6), (key2559, -6)]

def rawRow8826 : Integer.Sparse Key := [(key2358, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2529, -6), (key2529, -6), (key2559, -6), (key2529, -6)]

def rawRow8827 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2529, -6), (key2559, -6), (key2529, -6), (key2529, -6)]

def rawRow8828 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2559, -6), (key2529, -6), (key2529, -6), (key2529, -6)]

def rawRow8829 : Integer.Sparse Key := [(key2514, 6), (key2514, 6), (key2514, 6), (key2559, 6), (key2354, -6), (key2449, -6), (key2449, -6), (key2449, -6)]

def rawRow8830 : Integer.Sparse Key := [(key2514, 6), (key2514, 6), (key2559, 6), (key2514, 6), (key2449, -6), (key2354, -6), (key2449, -6), (key2449, -6)]

def rawRow8831 : Integer.Sparse Key := [(key2514, 6), (key2559, 6), (key2514, 6), (key2514, 6), (key2449, -6), (key2449, -6), (key2354, -6), (key2449, -6)]

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

def rawRow8832 : Integer.Sparse Key := [(key2559, 6), (key2514, 6), (key2514, 6), (key2514, 6), (key2449, -6), (key2449, -6), (key2449, -6), (key2354, -6)]

def rawRow8833 : Integer.Sparse Key := [(key2353, 6), (key2359, 6), (key2359, 6), (key2359, 6), (key2566, -6), (key2566, -6), (key2566, -6), (key2578, -6)]

def rawRow8834 : Integer.Sparse Key := [(key2359, 6), (key2353, 6), (key2359, 6), (key2359, 6), (key2566, -6), (key2566, -6), (key2578, -6), (key2566, -6)]

def rawRow8835 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2353, 6), (key2359, 6), (key2566, -6), (key2578, -6), (key2566, -6), (key2566, -6)]

def rawRow8836 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2359, 6), (key2353, 6), (key2578, -6), (key2566, -6), (key2566, -6), (key2566, -6)]

def rawRow8837 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2353, -6), (key2448, -6), (key2448, -6), (key2448, -6)]

def rawRow8838 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2448, -6), (key2353, -6), (key2448, -6), (key2448, -6)]

def rawRow8839 : Integer.Sparse Key := [(key2566, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2448, -6), (key2448, -6), (key2353, -6), (key2448, -6)]

def rawRow8840 : Integer.Sparse Key := [(key2578, 6), (key2566, 6), (key2566, 6), (key2566, 6), (key2448, -6), (key2448, -6), (key2448, -6), (key2353, -6)]

def rawRow8841 : Integer.Sparse Key := [(key2268, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2294, 2), (key2272, 2), (key2294, 2), (key2323, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2324, -2), (key2323, -2), (key2336, -2), (key2324, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2336, -2)]

def rawRow8842 : Integer.Sparse Key := [(key2268, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2294, 2), (key2272, 2), (key2324, -2), (key2323, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2336, -2), (key2323, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2336, -2), (key2324, -2)]

def rawRow8843 : Integer.Sparse Key := [(key2272, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2294, 2), (key2272, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2324, -2), (key2324, -2), (key2323, -2), (key2336, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2323, -2), (key2336, -2), (key2324, -2), (key2324, -2)]

def rawRow8844 : Integer.Sparse Key := [(key2294, 2), (key2294, 2), (key2294, 2), (key2272, 2), (key2272, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2336, -2), (key2336, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2323, -2), (key2323, -2)]

def rawRow8845 : Integer.Sparse Key := [(key1999, 2), (key1999, 2), (key2003, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2323, 2), (key2324, 2), (key2323, 2), (key2336, 2), (key2324, 2), (key2336, 2), (key1999, -2), (key2003, -2), (key2003, -2), (key2268, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2294, -2), (key2324, -2), (key2324, -2), (key2336, -2)]

def rawRow8846 : Integer.Sparse Key := [(key1999, 2), (key2003, 2), (key1999, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2324, 2), (key2323, 2), (key2336, 2), (key2323, 2), (key2336, 2), (key2324, 2), (key2003, -2), (key1999, -2), (key2003, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2324, -2), (key2336, -2), (key2324, -2)]

def rawRow8847 : Integer.Sparse Key := [(key2003, 2), (key1999, 2), (key1999, 2), (key2294, 2), (key2268, 2), (key2268, 2), (key2336, 2), (key2336, 2), (key2324, 2), (key2324, 2), (key2323, 2), (key2323, 2), (key2003, -2), (key2003, -2), (key1999, -2), (key2294, -2), (key2294, -2), (key2272, -2), (key2272, -2), (key2268, -2), (key2268, -2), (key2336, -2), (key2324, -2), (key2324, -2)]

def rawRow8848 : Integer.Sparse Key := [(key2268, 2), (key2323, 2), (key2324, 2), (key1999, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2003, 2), (key2268, 2), (key2294, 2), (key2324, 2), (key2336, 2), (key2268, -2), (key2272, -2), (key2324, -2), (key1999, -2), (key2003, -2), (key2268, -2), (key2294, -2), (key2324, -2), (key2336, -2), (key2003, -2), (key2272, -2), (key2294, -2)]

def rawRow8849 : Integer.Sparse Key := [(key2268, 2), (key2324, 2), (key2323, 2), (key1999, 2), (key2336, 2), (key2323, 2), (key2003, 2), (key1999, 2), (key2294, 2), (key2268, 2), (key2336, 2), (key2324, 2), (key2272, -2), (key2268, -2), (key2324, -2), (key2003, -2), (key1999, -2), (key2294, -2), (key2268, -2), (key2336, -2), (key2324, -2), (key2003, -2), (key2294, -2), (key2272, -2)]

def rawRow8850 : Integer.Sparse Key := [(key2323, 2), (key2268, 2), (key2324, 2), (key2323, 2), (key1999, 2), (key2336, 2), (key2268, 2), (key2324, 2), (key1999, 2), (key2336, 2), (key2003, 2), (key2294, 2), (key2268, -2), (key2324, -2), (key2272, -2), (key2268, -2), (key2324, -2), (key1999, -2), (key2336, -2), (key2003, -2), (key2294, -2), (key2272, -2), (key2003, -2), (key2294, -2)]

def rawRow8851 : Integer.Sparse Key := [(key2323, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2324, 2), (key2268, 2), (key2336, 2), (key1999, 2), (key2294, 2), (key2003, 2), (key2324, -2), (key2268, -2), (key2272, -2), (key2324, -2), (key2268, -2), (key2336, -2), (key1999, -2), (key2294, -2), (key2003, -2), (key2272, -2), (key2294, -2), (key2003, -2)]

def rawRow8852 : Integer.Sparse Key := [(key2324, 2), (key2268, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2323, 2), (key2294, 2), (key2336, 2), (key2003, 2), (key2324, 2), (key1999, 2), (key2268, 2), (key2272, -2), (key2324, -2), (key2268, -2), (key2294, -2), (key2336, -2), (key2003, -2), (key2324, -2), (key1999, -2), (key2268, -2), (key2294, -2), (key2003, -2), (key2272, -2)]

def rawRow8853 : Integer.Sparse Key := [(key2324, 2), (key2323, 2), (key2268, 2), (key2336, 2), (key2323, 2), (key1999, 2), (key2336, 2), (key2294, 2), (key2324, 2), (key2003, 2), (key2268, 2), (key1999, 2), (key2324, -2), (key2272, -2), (key2268, -2), (key2336, -2), (key2294, -2), (key2324, -2), (key2003, -2), (key2268, -2), (key1999, -2), (key2294, -2), (key2272, -2), (key2003, -2)]

def rawRow8854 : Integer.Sparse Key := [(key2294, 2), (key2336, 2), (key2336, 2), (key2003, 2), (key2324, 2), (key2324, 2), (key1999, 2), (key1999, 2), (key2268, 2), (key2268, 2), (key2323, 2), (key2323, 2), (key2294, -2), (key2294, -2), (key2336, -2), (key2003, -2), (key2003, -2), (key2272, -2), (key2272, -2), (key2324, -2), (key2324, -2), (key1999, -2), (key2268, -2), (key2268, -2)]

def rawRow8855 : Integer.Sparse Key := [(key2336, 2), (key2294, 2), (key2336, 2), (key2324, 2), (key2003, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key1999, 2), (key2323, 2), (key1999, 2), (key2268, 2), (key2294, -2), (key2336, -2), (key2294, -2), (key2272, -2), (key2324, -2), (key2003, -2), (key2324, -2), (key2003, -2), (key2272, -2), (key2268, -2), (key1999, -2), (key2268, -2)]

def rawRow8856 : Integer.Sparse Key := [(key2336, 2), (key2336, 2), (key2294, 2), (key2324, 2), (key2324, 2), (key2003, 2), (key2323, 2), (key2268, 2), (key2323, 2), (key1999, 2), (key2268, 2), (key1999, 2), (key2336, -2), (key2294, -2), (key2294, -2), (key2324, -2), (key2272, -2), (key2324, -2), (key2003, -2), (key2272, -2), (key2003, -2), (key2268, -2), (key2268, -2), (key1999, -2)]

def rawRow8857 : Integer.Sparse Key := [(key724, -24), (key942, 6), (key942, 6), (key942, 6), (key946, 6)]

def rawRow8858 : Integer.Sparse Key := [(key724, -24), (key942, 6), (key942, 6), (key946, 6), (key942, 6)]

def rawRow8859 : Integer.Sparse Key := [(key724, -24), (key942, 6), (key946, 6), (key942, 6), (key942, 6)]

def rawRow8860 : Integer.Sparse Key := [(key724, -24), (key946, 6), (key942, 6), (key942, 6), (key942, 6)]

def rawRow8861 : Integer.Sparse Key := [(key942, -24), (key724, 6), (key942, 6), (key942, 6), (key946, 6)]

def rawRow8862 : Integer.Sparse Key := [(key942, -24), (key724, 6), (key942, 6), (key946, 6), (key942, 6)]

def rawRow8863 : Integer.Sparse Key := [(key942, -24), (key724, 6), (key946, 6), (key942, 6), (key942, 6)]

def rawRow8864 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key724, 6), (key942, 6), (key946, 6)]

def rawRow8865 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key724, 6), (key946, 6), (key942, 6)]

def rawRow8866 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key942, 6), (key724, 6), (key946, 6)]

def rawRow8867 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key942, 6), (key946, 6), (key724, 6)]

def rawRow8868 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key946, 6), (key724, 6), (key942, 6)]

def rawRow8869 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key946, 6), (key942, 6), (key724, 6)]

def rawRow8870 : Integer.Sparse Key := [(key942, -24), (key946, 6), (key724, 6), (key942, 6), (key942, 6)]

def rawRow8871 : Integer.Sparse Key := [(key942, -24), (key946, 6), (key942, 6), (key724, 6), (key942, 6)]

def rawRow8872 : Integer.Sparse Key := [(key942, -24), (key946, 6), (key942, 6), (key942, 6), (key724, 6)]

def rawRow8873 : Integer.Sparse Key := [(key713, -6), (key715, -6), (key715, -6), (key715, -6), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key892, 2), (key890, 2), (key914, 2), (key892, 2), (key914, 2), (key892, 2), (key892, 2), (key914, 2)]

def rawRow8874 : Integer.Sparse Key := [(key715, -6), (key713, -6), (key715, -6), (key715, -6), (key892, 2), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key914, 2), (key890, 2), (key914, 2), (key892, 2), (key892, 2), (key914, 2), (key892, 2)]

def rawRow8875 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key713, -6), (key715, -6), (key892, 2), (key892, 2), (key890, 2), (key914, 2), (key914, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key914, 2), (key892, 2), (key892, 2)]

def rawRow8876 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key715, -6), (key713, -6), (key914, 2), (key914, 2), (key914, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key890, 2)]

def rawRow8877 : Integer.Sparse Key := [(key890, -6), (key892, -6), (key892, -6), (key959, -6), (key713, 2), (key715, 2), (key715, 2), (key890, 2), (key892, 2), (key890, 2), (key914, 2), (key892, 2), (key914, 2), (key959, 2), (key959, 2), (key966, 2)]

def rawRow8878 : Integer.Sparse Key := [(key892, -6), (key890, -6), (key892, -6), (key959, -6), (key715, 2), (key713, 2), (key715, 2), (key892, 2), (key890, 2), (key914, 2), (key890, 2), (key914, 2), (key892, 2), (key959, 2), (key966, 2), (key959, 2)]

def rawRow8879 : Integer.Sparse Key := [(key892, -6), (key892, -6), (key890, -6), (key959, -6), (key715, 2), (key715, 2), (key713, 2), (key914, 2), (key914, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key966, 2), (key959, 2), (key959, 2)]

def rawRow8880 : Integer.Sparse Key := [(key890, -6), (key892, -6), (key959, -6), (key892, -6), (key890, 2), (key892, 2), (key959, 2), (key713, 2), (key715, 2), (key890, 2), (key914, 2), (key959, 2), (key966, 2), (key715, 2), (key892, 2), (key914, 2)]

def rawRow8881 : Integer.Sparse Key := [(key892, -6), (key890, -6), (key959, -6), (key892, -6), (key892, 2), (key890, 2), (key959, 2), (key715, 2), (key713, 2), (key914, 2), (key890, 2), (key966, 2), (key959, 2), (key715, 2), (key914, 2), (key892, 2)]

def rawRow8882 : Integer.Sparse Key := [(key890, -6), (key959, -6), (key892, -6), (key892, -6), (key890, 2), (key959, 2), (key892, 2), (key890, 2), (key959, 2), (key713, 2), (key966, 2), (key715, 2), (key914, 2), (key892, 2), (key715, 2), (key914, 2)]

def rawRow8883 : Integer.Sparse Key := [(key959, -6), (key890, -6), (key892, -6), (key892, -6), (key959, 2), (key890, 2), (key892, 2), (key959, 2), (key890, 2), (key966, 2), (key713, 2), (key914, 2), (key715, 2), (key892, 2), (key914, 2), (key715, 2)]

def rawRow8884 : Integer.Sparse Key := [(key892, -6), (key959, -6), (key890, -6), (key892, -6), (key892, 2), (key959, 2), (key890, 2), (key914, 2), (key966, 2), (key715, 2), (key959, 2), (key713, 2), (key890, 2), (key914, 2), (key715, 2), (key892, 2)]

def rawRow8885 : Integer.Sparse Key := [(key959, -6), (key892, -6), (key890, -6), (key892, -6), (key959, 2), (key892, 2), (key890, 2), (key966, 2), (key914, 2), (key959, 2), (key715, 2), (key890, 2), (key713, 2), (key914, 2), (key892, 2), (key715, 2)]

def rawRow8886 : Integer.Sparse Key := [(key892, -6), (key892, -6), (key959, -6), (key890, -6), (key914, 2), (key914, 2), (key966, 2), (key715, 2), (key715, 2), (key892, 2), (key892, 2), (key959, 2), (key959, 2), (key713, 2), (key890, 2), (key890, 2)]

def rawRow8887 : Integer.Sparse Key := [(key892, -6), (key959, -6), (key892, -6), (key890, -6), (key914, 2), (key966, 2), (key914, 2), (key892, 2), (key959, 2), (key715, 2), (key959, 2), (key715, 2), (key892, 2), (key890, 2), (key713, 2), (key890, 2)]

def rawRow8888 : Integer.Sparse Key := [(key959, -6), (key892, -6), (key892, -6), (key890, -6), (key966, 2), (key914, 2), (key914, 2), (key959, 2), (key892, 2), (key959, 2), (key715, 2), (key892, 2), (key715, 2), (key890, 2), (key890, 2), (key713, 2)]

def rawRow8889 : Integer.Sparse Key := [(key2203, -6), (key2203, -6), (key2203, -6), (key2206, -6), (key2317, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2318, 2), (key2321, 2)]

def rawRow8890 : Integer.Sparse Key := [(key2203, -6), (key2203, -6), (key2206, -6), (key2203, -6), (key2317, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2321, 2), (key2318, 2)]

def rawRow8891 : Integer.Sparse Key := [(key2203, -6), (key2206, -6), (key2203, -6), (key2203, -6), (key2318, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2321, 2), (key2318, 2), (key2318, 2), (key2317, 2), (key2317, 2)]

def rawRow8892 : Integer.Sparse Key := [(key2206, -6), (key2203, -6), (key2203, -6), (key2203, -6), (key2321, 2), (key2321, 2), (key2321, 2), (key2318, 2), (key2318, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2)]

def rawRow8893 : Integer.Sparse Key := [(key2098, -6), (key2317, -6), (key2317, -6), (key2321, -6), (key2098, 2), (key2098, 2), (key2099, 2), (key2203, 2), (key2203, 2), (key2206, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2318, 2), (key2321, 2)]

def rawRow8894 : Integer.Sparse Key := [(key2098, -6), (key2317, -6), (key2321, -6), (key2317, -6), (key2098, 2), (key2099, 2), (key2098, 2), (key2203, 2), (key2206, 2), (key2203, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2321, 2), (key2318, 2)]

def rawRow8895 : Integer.Sparse Key := [(key2098, -6), (key2321, -6), (key2317, -6), (key2317, -6), (key2099, 2), (key2098, 2), (key2098, 2), (key2206, 2), (key2203, 2), (key2203, 2), (key2321, 2), (key2321, 2), (key2318, 2), (key2318, 2), (key2317, 2), (key2317, 2)]

def rawRow8896 : Integer.Sparse Key := [(key2317, -6), (key2098, -6), (key2317, -6), (key2321, -6), (key2203, 2), (key2317, 2), (key2318, 2), (key2098, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2099, 2), (key2203, 2), (key2206, 2), (key2318, 2), (key2321, 2)]

def rawRow8897 : Integer.Sparse Key := [(key2317, -6), (key2098, -6), (key2321, -6), (key2317, -6), (key2203, 2), (key2318, 2), (key2317, 2), (key2098, 2), (key2321, 2), (key2317, 2), (key2099, 2), (key2098, 2), (key2206, 2), (key2203, 2), (key2321, 2), (key2318, 2)]

def rawRow8898 : Integer.Sparse Key := [(key2317, -6), (key2317, -6), (key2098, -6), (key2321, -6), (key2317, 2), (key2203, 2), (key2318, 2), (key2317, 2), (key2098, 2), (key2321, 2), (key2203, 2), (key2318, 2), (key2098, 2), (key2321, 2), (key2099, 2), (key2206, 2)]

def rawRow8899 : Integer.Sparse Key := [(key2317, -6), (key2317, -6), (key2321, -6), (key2098, -6), (key2317, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2318, 2), (key2203, 2), (key2321, 2), (key2098, 2), (key2206, 2), (key2099, 2)]

def rawRow8900 : Integer.Sparse Key := [(key2317, -6), (key2321, -6), (key2098, -6), (key2317, -6), (key2318, 2), (key2203, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2317, 2), (key2206, 2), (key2321, 2), (key2099, 2), (key2318, 2), (key2098, 2), (key2203, 2)]

def rawRow8901 : Integer.Sparse Key := [(key2317, -6), (key2321, -6), (key2317, -6), (key2098, -6), (key2318, 2), (key2317, 2), (key2203, 2), (key2321, 2), (key2317, 2), (key2098, 2), (key2321, 2), (key2206, 2), (key2318, 2), (key2099, 2), (key2203, 2), (key2098, 2)]

def rawRow8902 : Integer.Sparse Key := [(key2321, -6), (key2098, -6), (key2317, -6), (key2317, -6), (key2206, 2), (key2321, 2), (key2321, 2), (key2099, 2), (key2318, 2), (key2318, 2), (key2098, 2), (key2098, 2), (key2203, 2), (key2203, 2), (key2317, 2), (key2317, 2)]

def rawRow8903 : Integer.Sparse Key := [(key2321, -6), (key2317, -6), (key2098, -6), (key2317, -6), (key2321, 2), (key2206, 2), (key2321, 2), (key2318, 2), (key2099, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2098, 2), (key2317, 2), (key2098, 2), (key2203, 2)]

def rawRow8904 : Integer.Sparse Key := [(key2321, -6), (key2317, -6), (key2317, -6), (key2098, -6), (key2321, 2), (key2321, 2), (key2206, 2), (key2318, 2), (key2318, 2), (key2099, 2), (key2317, 2), (key2203, 2), (key2317, 2), (key2098, 2), (key2203, 2), (key2098, 2)]

def rawRow8905 : Integer.Sparse Key := [(key1998, -6), (key2000, -6), (key2000, -6), (key2000, -6), (key2267, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2292, 2)]

def rawRow8906 : Integer.Sparse Key := [(key2000, -6), (key1998, -6), (key2000, -6), (key2000, -6), (key2269, 2), (key2267, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2292, 2), (key2269, 2)]

def rawRow8907 : Integer.Sparse Key := [(key2000, -6), (key2000, -6), (key1998, -6), (key2000, -6), (key2269, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2269, 2)]

def rawRow8908 : Integer.Sparse Key := [(key2000, -6), (key2000, -6), (key2000, -6), (key1998, -6), (key2292, 2), (key2292, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2267, 2), (key2267, 2)]

def rawRow8909 : Integer.Sparse Key := [(key2267, -6), (key2269, -6), (key2269, -6), (key2340, -6), (key1998, 2), (key2000, 2), (key2000, 2), (key2267, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2292, 2), (key2340, 2), (key2340, 2), (key2349, 2)]

def rawRow8910 : Integer.Sparse Key := [(key2269, -6), (key2267, -6), (key2269, -6), (key2340, -6), (key2000, 2), (key1998, 2), (key2000, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2340, 2), (key2349, 2), (key2340, 2)]

def rawRow8911 : Integer.Sparse Key := [(key2269, -6), (key2269, -6), (key2267, -6), (key2340, -6), (key2000, 2), (key2000, 2), (key1998, 2), (key2292, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2267, 2), (key2349, 2), (key2340, 2), (key2340, 2)]

def rawRow8912 : Integer.Sparse Key := [(key2267, -6), (key2269, -6), (key2340, -6), (key2269, -6), (key2267, 2), (key2269, 2), (key2340, 2), (key1998, 2), (key2000, 2), (key2267, 2), (key2292, 2), (key2340, 2), (key2349, 2), (key2000, 2), (key2269, 2), (key2292, 2)]

def rawRow8913 : Integer.Sparse Key := [(key2269, -6), (key2267, -6), (key2340, -6), (key2269, -6), (key2269, 2), (key2267, 2), (key2340, 2), (key2000, 2), (key1998, 2), (key2292, 2), (key2267, 2), (key2349, 2), (key2340, 2), (key2000, 2), (key2292, 2), (key2269, 2)]

def rawRow8914 : Integer.Sparse Key := [(key2267, -6), (key2340, -6), (key2269, -6), (key2269, -6), (key2267, 2), (key2340, 2), (key2269, 2), (key2267, 2), (key2340, 2), (key1998, 2), (key2349, 2), (key2000, 2), (key2292, 2), (key2269, 2), (key2000, 2), (key2292, 2)]

def rawRow8915 : Integer.Sparse Key := [(key2340, -6), (key2267, -6), (key2269, -6), (key2269, -6), (key2340, 2), (key2267, 2), (key2269, 2), (key2340, 2), (key2267, 2), (key2349, 2), (key1998, 2), (key2292, 2), (key2000, 2), (key2269, 2), (key2292, 2), (key2000, 2)]

def rawRow8916 : Integer.Sparse Key := [(key2269, -6), (key2340, -6), (key2267, -6), (key2269, -6), (key2269, 2), (key2340, 2), (key2267, 2), (key2292, 2), (key2349, 2), (key2000, 2), (key2340, 2), (key1998, 2), (key2267, 2), (key2292, 2), (key2000, 2), (key2269, 2)]

def rawRow8917 : Integer.Sparse Key := [(key2340, -6), (key2269, -6), (key2267, -6), (key2269, -6), (key2340, 2), (key2269, 2), (key2267, 2), (key2349, 2), (key2292, 2), (key2340, 2), (key2000, 2), (key2267, 2), (key1998, 2), (key2292, 2), (key2269, 2), (key2000, 2)]

def rawRow8918 : Integer.Sparse Key := [(key2269, -6), (key2269, -6), (key2340, -6), (key2267, -6), (key2292, 2), (key2292, 2), (key2349, 2), (key2000, 2), (key2000, 2), (key2269, 2), (key2269, 2), (key2340, 2), (key2340, 2), (key1998, 2), (key2267, 2), (key2267, 2)]

def rawRow8919 : Integer.Sparse Key := [(key2269, -6), (key2340, -6), (key2269, -6), (key2267, -6), (key2292, 2), (key2349, 2), (key2292, 2), (key2269, 2), (key2340, 2), (key2000, 2), (key2340, 2), (key2000, 2), (key2269, 2), (key2267, 2), (key1998, 2), (key2267, 2)]

def rawRow8920 : Integer.Sparse Key := [(key2340, -6), (key2269, -6), (key2269, -6), (key2267, -6), (key2349, 2), (key2292, 2), (key2292, 2), (key2340, 2), (key2269, 2), (key2340, 2), (key2000, 2), (key2269, 2), (key2000, 2), (key2267, 2), (key2267, 2), (key1998, 2)]

def rawRow8921 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2176, -2), (key2174, -2), (key2187, -2), (key2176, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2187, -2), (key2274, 1), (key2276, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2279, 1), (key2287, 1)]

def rawRow8922 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2187, -2), (key2174, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2187, -2), (key2176, -2), (key2276, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2279, 1)]

def rawRow8923 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2174, -2), (key2187, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2174, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1)]

def rawRow8924 : Integer.Sparse Key := [(key2187, -2), (key2187, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2174, -2), (key2174, -2), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1)]

def rawRow8925 : Integer.Sparse Key := [(key2077, -2), (key2079, -2), (key2079, -2), (key2274, -2), (key2276, -2), (key2274, -2), (key2287, -2), (key2276, -2), (key2287, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2077, 1), (key2079, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2085, 1), (key2174, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2187, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2341, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2343, 1), (key2347, 1)]

def rawRow8926 : Integer.Sparse Key := [(key2079, -2), (key2077, -2), (key2079, -2), (key2276, -2), (key2274, -2), (key2287, -2), (key2274, -2), (key2287, -2), (key2276, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2079, 1), (key2077, 1), (key2085, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2341, 1), (key2347, 1), (key2343, 1)]

def rawRow8927 : Integer.Sparse Key := [(key2079, -2), (key2079, -2), (key2077, -2), (key2287, -2), (key2287, -2), (key2276, -2), (key2276, -2), (key2274, -2), (key2274, -2), (key2347, -2), (key2341, -2), (key2341, -2), (key2085, 1), (key2085, 1), (key2079, 1), (key2079, 1), (key2077, 1), (key2077, 1), (key2187, 1), (key2187, 1), (key2176, 1), (key2176, 1), (key2174, 1), (key2174, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2347, 1), (key2347, 1), (key2343, 1), (key2343, 1), (key2341, 1), (key2341, 1)]

def rawRow8928 : Integer.Sparse Key := [(key2274, -2), (key2276, -2), (key2341, -2), (key2077, -2), (key2079, -2), (key2274, -2), (key2287, -2), (key2341, -2), (key2347, -2), (key2079, -2), (key2276, -2), (key2287, -2), (key2174, 1), (key2176, 1), (key2274, 1), (key2279, 1), (key2341, 1), (key2343, 1), (key2077, 1), (key2079, 1), (key2274, 1), (key2287, 1), (key2341, 1), (key2347, 1), (key2077, 1), (key2085, 1), (key2174, 1), (key2187, 1), (key2343, 1), (key2347, 1), (key2079, 1), (key2085, 1), (key2176, 1), (key2187, 1), (key2279, 1), (key2287, 1)]

def rawRow8929 : Integer.Sparse Key := [(key2276, -2), (key2274, -2), (key2341, -2), (key2079, -2), (key2077, -2), (key2287, -2), (key2274, -2), (key2347, -2), (key2341, -2), (key2079, -2), (key2287, -2), (key2276, -2), (key2176, 1), (key2174, 1), (key2279, 1), (key2274, 1), (key2343, 1), (key2341, 1), (key2079, 1), (key2077, 1), (key2287, 1), (key2274, 1), (key2347, 1), (key2341, 1), (key2085, 1), (key2077, 1), (key2187, 1), (key2174, 1), (key2347, 1), (key2343, 1), (key2085, 1), (key2079, 1), (key2187, 1), (key2176, 1), (key2287, 1), (key2279, 1)]

def rawRow8930 : Integer.Sparse Key := [(key2274, -2), (key2341, -2), (key2276, -2), (key2274, -2), (key2341, -2), (key2077, -2), (key2347, -2), (key2079, -2), (key2287, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2274, 1), (key2341, 1), (key2174, 1), (key2343, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2341, 1), (key2077, 1), (key2347, 1), (key2079, 1), (key2287, 1), (key2174, 1), (key2343, 1), (key2077, 1), (key2347, 1), (key2085, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2079, 1), (key2287, 1), (key2085, 1), (key2187, 1)]

def rawRow8931 : Integer.Sparse Key := [(key2341, -2), (key2274, -2), (key2276, -2), (key2341, -2), (key2274, -2), (key2347, -2), (key2077, -2), (key2287, -2), (key2079, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2341, 1), (key2274, 1), (key2343, 1), (key2174, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2274, 1), (key2347, 1), (key2077, 1), (key2287, 1), (key2079, 1), (key2343, 1), (key2174, 1), (key2347, 1), (key2077, 1), (key2187, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2287, 1), (key2079, 1), (key2187, 1), (key2085, 1)]

def rawRow8932 : Integer.Sparse Key := [(key2276, -2), (key2341, -2), (key2274, -2), (key2287, -2), (key2347, -2), (key2079, -2), (key2341, -2), (key2077, -2), (key2274, -2), (key2287, -2), (key2079, -2), (key2276, -2), (key2279, 1), (key2343, 1), (key2176, 1), (key2341, 1), (key2174, 1), (key2274, 1), (key2287, 1), (key2347, 1), (key2079, 1), (key2341, 1), (key2077, 1), (key2274, 1), (key2187, 1), (key2347, 1), (key2085, 1), (key2343, 1), (key2077, 1), (key2174, 1), (key2187, 1), (key2287, 1), (key2085, 1), (key2279, 1), (key2079, 1), (key2176, 1)]

def rawRow8933 : Integer.Sparse Key := [(key2341, -2), (key2276, -2), (key2274, -2), (key2347, -2), (key2287, -2), (key2341, -2), (key2079, -2), (key2274, -2), (key2077, -2), (key2287, -2), (key2276, -2), (key2079, -2), (key2343, 1), (key2279, 1), (key2341, 1), (key2176, 1), (key2274, 1), (key2174, 1), (key2347, 1), (key2287, 1), (key2341, 1), (key2079, 1), (key2274, 1), (key2077, 1), (key2347, 1), (key2187, 1), (key2343, 1), (key2085, 1), (key2174, 1), (key2077, 1), (key2287, 1), (key2187, 1), (key2279, 1), (key2085, 1), (key2176, 1), (key2079, 1)]

def rawRow8934 : Integer.Sparse Key := [(key2287, -2), (key2287, -2), (key2347, -2), (key2079, -2), (key2079, -2), (key2276, -2), (key2276, -2), (key2341, -2), (key2341, -2), (key2077, -2), (key2274, -2), (key2274, -2), (key2187, 1), (key2187, 1), (key2287, 1), (key2287, 1), (key2347, 1), (key2347, 1), (key2085, 1), (key2085, 1), (key2279, 1), (key2279, 1), (key2343, 1), (key2343, 1), (key2079, 1), (key2079, 1), (key2176, 1), (key2176, 1), (key2341, 1), (key2341, 1), (key2077, 1), (key2077, 1), (key2174, 1), (key2174, 1), (key2274, 1), (key2274, 1)]

def rawRow8935 : Integer.Sparse Key := [(key2287, -2), (key2347, -2), (key2287, -2), (key2276, -2), (key2341, -2), (key2079, -2), (key2341, -2), (key2079, -2), (key2276, -2), (key2274, -2), (key2077, -2), (key2274, -2), (key2287, 1), (key2347, 1), (key2187, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2274, 1), (key2077, 1), (key2174, 1)]

def rawRow8936 : Integer.Sparse Key := [(key2347, -2), (key2287, -2), (key2287, -2), (key2341, -2), (key2276, -2), (key2341, -2), (key2079, -2), (key2276, -2), (key2079, -2), (key2274, -2), (key2274, -2), (key2077, -2), (key2347, 1), (key2287, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2187, 1), (key2343, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2085, 1), (key2341, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2079, 1), (key2274, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2174, 1), (key2077, 1)]

def rawRow8937 : Integer.Sparse Key := [(key2009, -24), (key2316, 6), (key2316, 6), (key2316, 6), (key2322, 6)]

def rawRow8938 : Integer.Sparse Key := [(key2009, -24), (key2316, 6), (key2316, 6), (key2322, 6), (key2316, 6)]

def rawRow8939 : Integer.Sparse Key := [(key2009, -24), (key2316, 6), (key2322, 6), (key2316, 6), (key2316, 6)]

def rawRow8940 : Integer.Sparse Key := [(key2009, -24), (key2322, 6), (key2316, 6), (key2316, 6), (key2316, 6)]

def rawRow8941 : Integer.Sparse Key := [(key2316, -24), (key2009, 6), (key2316, 6), (key2316, 6), (key2322, 6)]

def rawRow8942 : Integer.Sparse Key := [(key2316, -24), (key2009, 6), (key2316, 6), (key2322, 6), (key2316, 6)]

def rawRow8943 : Integer.Sparse Key := [(key2316, -24), (key2009, 6), (key2322, 6), (key2316, 6), (key2316, 6)]

def rawRow8944 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2009, 6), (key2316, 6), (key2322, 6)]

def rawRow8945 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2009, 6), (key2322, 6), (key2316, 6)]

def rawRow8946 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2316, 6), (key2009, 6), (key2322, 6)]

def rawRow8947 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2316, 6), (key2322, 6), (key2009, 6)]

def rawRow8948 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2322, 6), (key2009, 6), (key2316, 6)]

def rawRow8949 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2322, 6), (key2316, 6), (key2009, 6)]

def rawRow8950 : Integer.Sparse Key := [(key2316, -24), (key2322, 6), (key2009, 6), (key2316, 6), (key2316, 6)]

def rawRow8951 : Integer.Sparse Key := [(key2316, -24), (key2322, 6), (key2316, 6), (key2009, 6), (key2316, 6)]

def rawRow8952 : Integer.Sparse Key := [(key2316, -24), (key2322, 6), (key2316, 6), (key2316, 6), (key2009, 6)]

def rawRow8953 : Integer.Sparse Key := [(key2077, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2079, -2), (key2077, -2), (key2085, -2), (key2079, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2085, -2), (key2174, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2176, 2), (key2174, 2), (key2187, 2), (key2176, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2187, 2)]

def rawRow8954 : Integer.Sparse Key := [(key2079, -2), (key2077, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2085, -2), (key2077, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2085, -2), (key2079, -2), (key2176, 2), (key2174, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2187, 2), (key2174, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2187, 2), (key2176, 2)]

def rawRow8955 : Integer.Sparse Key := [(key2079, -2), (key2079, -2), (key2077, -2), (key2085, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2077, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2176, 2), (key2176, 2), (key2174, 2), (key2187, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2174, 2), (key2187, 2), (key2176, 2), (key2176, 2)]

def rawRow8956 : Integer.Sparse Key := [(key2085, -2), (key2085, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2077, -2), (key2077, -2), (key2187, 2), (key2187, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2174, 2), (key2174, 2)]

def rawRow8957 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2176, -2), (key2274, -2), (key2276, -2), (key2274, -2), (key2279, -2), (key2276, -2), (key2279, -2), (key2341, -2), (key2341, -2), (key2343, -2), (key2077, 2), (key2079, 2), (key2079, 2), (key2274, 2), (key2276, 2), (key2274, 2), (key2287, 2), (key2276, 2), (key2287, 2), (key2341, 2), (key2341, 2), (key2347, 2)]

def rawRow8958 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2176, -2), (key2276, -2), (key2274, -2), (key2279, -2), (key2274, -2), (key2279, -2), (key2276, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2079, 2), (key2077, 2), (key2079, 2), (key2276, 2), (key2274, 2), (key2287, 2), (key2274, 2), (key2287, 2), (key2276, 2), (key2341, 2), (key2347, 2), (key2341, 2)]

def rawRow8959 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2174, -2), (key2279, -2), (key2279, -2), (key2276, -2), (key2276, -2), (key2274, -2), (key2274, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2079, 2), (key2079, 2), (key2077, 2), (key2287, 2), (key2287, 2), (key2276, 2), (key2276, 2), (key2274, 2), (key2274, 2), (key2347, 2), (key2341, 2), (key2341, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8960 : Integer.Sparse Key := [(key2274, -2), (key2276, -2), (key2341, -2), (key2174, -2), (key2176, -2), (key2274, -2), (key2279, -2), (key2341, -2), (key2343, -2), (key2176, -2), (key2276, -2), (key2279, -2), (key2274, 2), (key2276, 2), (key2341, 2), (key2077, 2), (key2079, 2), (key2274, 2), (key2287, 2), (key2341, 2), (key2347, 2), (key2079, 2), (key2276, 2), (key2287, 2)]

def rawRow8961 : Integer.Sparse Key := [(key2276, -2), (key2274, -2), (key2341, -2), (key2176, -2), (key2174, -2), (key2279, -2), (key2274, -2), (key2343, -2), (key2341, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2276, 2), (key2274, 2), (key2341, 2), (key2079, 2), (key2077, 2), (key2287, 2), (key2274, 2), (key2347, 2), (key2341, 2), (key2079, 2), (key2287, 2), (key2276, 2)]

def rawRow8962 : Integer.Sparse Key := [(key2274, -2), (key2341, -2), (key2276, -2), (key2274, -2), (key2341, -2), (key2174, -2), (key2343, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2176, -2), (key2279, -2), (key2274, 2), (key2341, 2), (key2276, 2), (key2274, 2), (key2341, 2), (key2077, 2), (key2347, 2), (key2079, 2), (key2287, 2), (key2276, 2), (key2079, 2), (key2287, 2)]

def rawRow8963 : Integer.Sparse Key := [(key2341, -2), (key2274, -2), (key2276, -2), (key2341, -2), (key2274, -2), (key2343, -2), (key2174, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2279, -2), (key2176, -2), (key2341, 2), (key2274, 2), (key2276, 2), (key2341, 2), (key2274, 2), (key2347, 2), (key2077, 2), (key2287, 2), (key2079, 2), (key2276, 2), (key2287, 2), (key2079, 2)]

def rawRow8964 : Integer.Sparse Key := [(key2276, -2), (key2341, -2), (key2274, -2), (key2279, -2), (key2343, -2), (key2176, -2), (key2341, -2), (key2174, -2), (key2274, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2276, 2), (key2341, 2), (key2274, 2), (key2287, 2), (key2347, 2), (key2079, 2), (key2341, 2), (key2077, 2), (key2274, 2), (key2287, 2), (key2079, 2), (key2276, 2)]

def rawRow8965 : Integer.Sparse Key := [(key2341, -2), (key2276, -2), (key2274, -2), (key2343, -2), (key2279, -2), (key2341, -2), (key2176, -2), (key2274, -2), (key2174, -2), (key2279, -2), (key2276, -2), (key2176, -2), (key2341, 2), (key2276, 2), (key2274, 2), (key2347, 2), (key2287, 2), (key2341, 2), (key2079, 2), (key2274, 2), (key2077, 2), (key2287, 2), (key2276, 2), (key2079, 2)]

def rawRow8966 : Integer.Sparse Key := [(key2279, -2), (key2279, -2), (key2343, -2), (key2176, -2), (key2176, -2), (key2276, -2), (key2276, -2), (key2341, -2), (key2341, -2), (key2174, -2), (key2274, -2), (key2274, -2), (key2287, 2), (key2287, 2), (key2347, 2), (key2079, 2), (key2079, 2), (key2276, 2), (key2276, 2), (key2341, 2), (key2341, 2), (key2077, 2), (key2274, 2), (key2274, 2)]

def rawRow8967 : Integer.Sparse Key := [(key2279, -2), (key2343, -2), (key2279, -2), (key2276, -2), (key2341, -2), (key2176, -2), (key2341, -2), (key2176, -2), (key2276, -2), (key2274, -2), (key2174, -2), (key2274, -2), (key2287, 2), (key2347, 2), (key2287, 2), (key2276, 2), (key2341, 2), (key2079, 2), (key2341, 2), (key2079, 2), (key2276, 2), (key2274, 2), (key2077, 2), (key2274, 2)]

def rawRow8968 : Integer.Sparse Key := [(key2343, -2), (key2279, -2), (key2279, -2), (key2341, -2), (key2276, -2), (key2341, -2), (key2176, -2), (key2276, -2), (key2176, -2), (key2274, -2), (key2274, -2), (key2174, -2), (key2347, 2), (key2287, 2), (key2287, 2), (key2341, 2), (key2276, 2), (key2341, 2), (key2079, 2), (key2276, 2), (key2079, 2), (key2274, 2), (key2274, 2), (key2077, 2)]

def rawRow8969 : Integer.Sparse Key := [(key817, -2), (key818, -2), (key818, -2), (key817, -2), (key818, -2), (key817, -2), (key825, -2), (key818, -2), (key825, -2), (key818, -2), (key818, -2), (key825, -2), (key897, 1), (key898, 1), (key897, 1), (key902, 1), (key898, 1), (key902, 1), (key897, 1), (key898, 1), (key897, 1), (key908, 1), (key898, 1), (key908, 1), (key897, 1), (key902, 1), (key897, 1), (key908, 1), (key902, 1), (key908, 1), (key898, 1), (key902, 1), (key898, 1), (key908, 1), (key902, 1), (key908, 1)]

def rawRow8970 : Integer.Sparse Key := [(key818, -2), (key817, -2), (key818, -2), (key818, -2), (key817, -2), (key825, -2), (key817, -2), (key825, -2), (key818, -2), (key818, -2), (key825, -2), (key818, -2), (key898, 1), (key897, 1), (key902, 1), (key897, 1), (key902, 1), (key898, 1), (key898, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key898, 1), (key902, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key902, 1), (key902, 1), (key898, 1), (key908, 1), (key898, 1), (key908, 1), (key902, 1)]

def rawRow8971 : Integer.Sparse Key := [(key818, -2), (key818, -2), (key817, -2), (key825, -2), (key825, -2), (key818, -2), (key818, -2), (key817, -2), (key817, -2), (key825, -2), (key818, -2), (key818, -2), (key902, 1), (key902, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key908, 1), (key908, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key897, 1), (key897, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key898, 1), (key898, 1)]

def rawRow8972 : Integer.Sparse Key := [(key825, -2), (key825, -2), (key825, -2), (key818, -2), (key818, -2), (key818, -2), (key818, -2), (key818, -2), (key818, -2), (key817, -2), (key817, -2), (key817, -2), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key898, 1), (key898, 1), (key898, 1), (key898, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1)]

def rawRow8973 : Integer.Sparse Key := [(key737, -2), (key738, -2), (key738, -2), (key897, -2), (key898, -2), (key897, -2), (key908, -2), (key898, -2), (key908, -2), (key960, -2), (key960, -2), (key964, -2), (key737, 1), (key738, 1), (key737, 1), (key743, 1), (key738, 1), (key743, 1), (key817, 1), (key818, 1), (key817, 1), (key825, 1), (key818, 1), (key825, 1), (key897, 1), (key902, 1), (key897, 1), (key908, 1), (key902, 1), (key908, 1), (key960, 1), (key962, 1), (key960, 1), (key964, 1), (key962, 1), (key964, 1)]

def rawRow8974 : Integer.Sparse Key := [(key738, -2), (key737, -2), (key738, -2), (key898, -2), (key897, -2), (key908, -2), (key897, -2), (key908, -2), (key898, -2), (key960, -2), (key964, -2), (key960, -2), (key738, 1), (key737, 1), (key743, 1), (key737, 1), (key743, 1), (key738, 1), (key818, 1), (key817, 1), (key825, 1), (key817, 1), (key825, 1), (key818, 1), (key902, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key902, 1), (key962, 1), (key960, 1), (key964, 1), (key960, 1), (key964, 1), (key962, 1)]

def rawRow8975 : Integer.Sparse Key := [(key738, -2), (key738, -2), (key737, -2), (key908, -2), (key908, -2), (key898, -2), (key898, -2), (key897, -2), (key897, -2), (key964, -2), (key960, -2), (key960, -2), (key743, 1), (key743, 1), (key738, 1), (key738, 1), (key737, 1), (key737, 1), (key825, 1), (key825, 1), (key818, 1), (key818, 1), (key817, 1), (key817, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key897, 1), (key897, 1), (key964, 1), (key964, 1), (key962, 1), (key962, 1), (key960, 1), (key960, 1)]

def rawRow8976 : Integer.Sparse Key := [(key897, -2), (key898, -2), (key960, -2), (key737, -2), (key738, -2), (key897, -2), (key908, -2), (key960, -2), (key964, -2), (key738, -2), (key898, -2), (key908, -2), (key817, 1), (key818, 1), (key897, 1), (key902, 1), (key960, 1), (key962, 1), (key737, 1), (key738, 1), (key897, 1), (key908, 1), (key960, 1), (key964, 1), (key737, 1), (key743, 1), (key817, 1), (key825, 1), (key962, 1), (key964, 1), (key738, 1), (key743, 1), (key818, 1), (key825, 1), (key902, 1), (key908, 1)]

def rawRow8977 : Integer.Sparse Key := [(key898, -2), (key897, -2), (key960, -2), (key738, -2), (key737, -2), (key908, -2), (key897, -2), (key964, -2), (key960, -2), (key738, -2), (key908, -2), (key898, -2), (key818, 1), (key817, 1), (key902, 1), (key897, 1), (key962, 1), (key960, 1), (key738, 1), (key737, 1), (key908, 1), (key897, 1), (key964, 1), (key960, 1), (key743, 1), (key737, 1), (key825, 1), (key817, 1), (key964, 1), (key962, 1), (key743, 1), (key738, 1), (key825, 1), (key818, 1), (key908, 1), (key902, 1)]

def rawRow8978 : Integer.Sparse Key := [(key897, -2), (key960, -2), (key898, -2), (key897, -2), (key960, -2), (key737, -2), (key964, -2), (key738, -2), (key908, -2), (key898, -2), (key738, -2), (key908, -2), (key897, 1), (key960, 1), (key817, 1), (key962, 1), (key818, 1), (key902, 1), (key897, 1), (key960, 1), (key737, 1), (key964, 1), (key738, 1), (key908, 1), (key817, 1), (key962, 1), (key737, 1), (key964, 1), (key743, 1), (key825, 1), (key818, 1), (key902, 1), (key738, 1), (key908, 1), (key743, 1), (key825, 1)]

def rawRow8979 : Integer.Sparse Key := [(key960, -2), (key897, -2), (key898, -2), (key960, -2), (key897, -2), (key964, -2), (key737, -2), (key908, -2), (key738, -2), (key898, -2), (key908, -2), (key738, -2), (key960, 1), (key897, 1), (key962, 1), (key817, 1), (key902, 1), (key818, 1), (key960, 1), (key897, 1), (key964, 1), (key737, 1), (key908, 1), (key738, 1), (key962, 1), (key817, 1), (key964, 1), (key737, 1), (key825, 1), (key743, 1), (key902, 1), (key818, 1), (key908, 1), (key738, 1), (key825, 1), (key743, 1)]

def rawRow8980 : Integer.Sparse Key := [(key898, -2), (key960, -2), (key897, -2), (key908, -2), (key964, -2), (key738, -2), (key960, -2), (key737, -2), (key897, -2), (key908, -2), (key738, -2), (key898, -2), (key902, 1), (key962, 1), (key818, 1), (key960, 1), (key817, 1), (key897, 1), (key908, 1), (key964, 1), (key738, 1), (key960, 1), (key737, 1), (key897, 1), (key825, 1), (key964, 1), (key743, 1), (key962, 1), (key737, 1), (key817, 1), (key825, 1), (key908, 1), (key743, 1), (key902, 1), (key738, 1), (key818, 1)]

def rawRow8981 : Integer.Sparse Key := [(key960, -2), (key898, -2), (key897, -2), (key964, -2), (key908, -2), (key960, -2), (key738, -2), (key897, -2), (key737, -2), (key908, -2), (key898, -2), (key738, -2), (key962, 1), (key902, 1), (key960, 1), (key818, 1), (key897, 1), (key817, 1), (key964, 1), (key908, 1), (key960, 1), (key738, 1), (key897, 1), (key737, 1), (key964, 1), (key825, 1), (key962, 1), (key743, 1), (key817, 1), (key737, 1), (key908, 1), (key825, 1), (key902, 1), (key743, 1), (key818, 1), (key738, 1)]

def rawRow8982 : Integer.Sparse Key := [(key908, -2), (key908, -2), (key964, -2), (key738, -2), (key738, -2), (key898, -2), (key898, -2), (key960, -2), (key960, -2), (key737, -2), (key897, -2), (key897, -2), (key825, 1), (key825, 1), (key908, 1), (key908, 1), (key964, 1), (key964, 1), (key743, 1), (key743, 1), (key902, 1), (key902, 1), (key962, 1), (key962, 1), (key738, 1), (key738, 1), (key818, 1), (key818, 1), (key960, 1), (key960, 1), (key737, 1), (key737, 1), (key817, 1), (key817, 1), (key897, 1), (key897, 1)]

def rawRow8983 : Integer.Sparse Key := [(key908, -2), (key964, -2), (key908, -2), (key898, -2), (key960, -2), (key738, -2), (key960, -2), (key738, -2), (key898, -2), (key897, -2), (key737, -2), (key897, -2), (key908, 1), (key964, 1), (key825, 1), (key964, 1), (key825, 1), (key908, 1), (key902, 1), (key962, 1), (key743, 1), (key962, 1), (key743, 1), (key902, 1), (key818, 1), (key960, 1), (key738, 1), (key960, 1), (key738, 1), (key818, 1), (key817, 1), (key897, 1), (key737, 1), (key897, 1), (key737, 1), (key817, 1)]

def rawRow8984 : Integer.Sparse Key := [(key964, -2), (key908, -2), (key908, -2), (key960, -2), (key898, -2), (key960, -2), (key738, -2), (key898, -2), (key738, -2), (key897, -2), (key897, -2), (key737, -2), (key964, 1), (key908, 1), (key964, 1), (key825, 1), (key908, 1), (key825, 1), (key962, 1), (key902, 1), (key962, 1), (key743, 1), (key902, 1), (key743, 1), (key960, 1), (key818, 1), (key960, 1), (key738, 1), (key818, 1), (key738, 1), (key897, 1), (key817, 1), (key897, 1), (key737, 1), (key817, 1), (key737, 1)]

def rawRow8985 : Integer.Sparse Key := [(key2274, 1), (key2276, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2341, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2347, -2), (key2343, -2), (key2347, -2)]

def rawRow8986 : Integer.Sparse Key := [(key2276, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2279, 1), (key2341, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2347, -2), (key2343, -2)]

def rawRow8987 : Integer.Sparse Key := [(key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2343, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2347, -2), (key2343, -2), (key2343, -2), (key2341, -2), (key2341, -2)]

def rawRow8988 : Integer.Sparse Key := [(key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2347, -2), (key2347, -2), (key2347, -2), (key2343, -2), (key2343, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2341, -2), (key2341, -2), (key2341, -2), (key2341, -2)]

def rawRow8989 : Integer.Sparse Key := [(key2077, 1), (key2079, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2085, 1), (key2174, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2187, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2341, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2343, 1), (key2347, 1), (key2079, -2), (key2079, -2), (key2085, -2), (key2176, -2), (key2176, -2), (key2187, -2), (key2276, -2), (key2279, -2), (key2276, -2), (key2287, -2), (key2279, -2), (key2287, -2)]

def rawRow8990 : Integer.Sparse Key := [(key2079, 1), (key2077, 1), (key2085, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2341, 1), (key2347, 1), (key2343, 1), (key2079, -2), (key2085, -2), (key2079, -2), (key2176, -2), (key2187, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2287, -2), (key2276, -2), (key2287, -2), (key2279, -2)]

def rawRow8991 : Integer.Sparse Key := [(key2085, 1), (key2085, 1), (key2079, 1), (key2079, 1), (key2077, 1), (key2077, 1), (key2187, 1), (key2187, 1), (key2176, 1), (key2176, 1), (key2174, 1), (key2174, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2347, 1), (key2347, 1), (key2343, 1), (key2343, 1), (key2341, 1), (key2341, 1), (key2085, -2), (key2079, -2), (key2079, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2287, -2), (key2287, -2), (key2279, -2), (key2279, -2), (key2276, -2), (key2276, -2)]

def rawRow8992 : Integer.Sparse Key := [(key2174, 1), (key2176, 1), (key2274, 1), (key2279, 1), (key2341, 1), (key2343, 1), (key2077, 1), (key2079, 1), (key2274, 1), (key2287, 1), (key2341, 1), (key2347, 1), (key2077, 1), (key2085, 1), (key2174, 1), (key2187, 1), (key2343, 1), (key2347, 1), (key2079, 1), (key2085, 1), (key2176, 1), (key2187, 1), (key2279, 1), (key2287, 1), (key2176, -2), (key2276, -2), (key2279, -2), (key2079, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2085, -2), (key2176, -2), (key2187, -2), (key2279, -2), (key2287, -2)]

def rawRow8993 : Integer.Sparse Key := [(key2176, 1), (key2174, 1), (key2279, 1), (key2274, 1), (key2343, 1), (key2341, 1), (key2079, 1), (key2077, 1), (key2287, 1), (key2274, 1), (key2347, 1), (key2341, 1), (key2085, 1), (key2077, 1), (key2187, 1), (key2174, 1), (key2347, 1), (key2343, 1), (key2085, 1), (key2079, 1), (key2187, 1), (key2176, 1), (key2287, 1), (key2279, 1), (key2176, -2), (key2279, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2276, -2), (key2085, -2), (key2079, -2), (key2187, -2), (key2176, -2), (key2287, -2), (key2279, -2)]

def rawRow8994 : Integer.Sparse Key := [(key2274, 1), (key2341, 1), (key2174, 1), (key2343, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2341, 1), (key2077, 1), (key2347, 1), (key2079, 1), (key2287, 1), (key2174, 1), (key2343, 1), (key2077, 1), (key2347, 1), (key2085, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2079, 1), (key2287, 1), (key2085, 1), (key2187, 1), (key2276, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2176, -2), (key2279, -2), (key2079, -2), (key2287, -2), (key2085, -2), (key2187, -2)]

def rawRow8995 : Integer.Sparse Key := [(key2341, 1), (key2274, 1), (key2343, 1), (key2174, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2274, 1), (key2347, 1), (key2077, 1), (key2287, 1), (key2079, 1), (key2343, 1), (key2174, 1), (key2347, 1), (key2077, 1), (key2187, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2287, 1), (key2079, 1), (key2187, 1), (key2085, 1), (key2276, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2279, -2), (key2176, -2), (key2287, -2), (key2079, -2), (key2187, -2), (key2085, -2)]

def rawRow8996 : Integer.Sparse Key := [(key2279, 1), (key2343, 1), (key2176, 1), (key2341, 1), (key2174, 1), (key2274, 1), (key2287, 1), (key2347, 1), (key2079, 1), (key2341, 1), (key2077, 1), (key2274, 1), (key2187, 1), (key2347, 1), (key2085, 1), (key2343, 1), (key2077, 1), (key2174, 1), (key2187, 1), (key2287, 1), (key2085, 1), (key2279, 1), (key2079, 1), (key2176, 1), (key2279, -2), (key2176, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2276, -2), (key2187, -2), (key2287, -2), (key2085, -2), (key2279, -2), (key2079, -2), (key2176, -2)]

def rawRow8997 : Integer.Sparse Key := [(key2343, 1), (key2279, 1), (key2341, 1), (key2176, 1), (key2274, 1), (key2174, 1), (key2347, 1), (key2287, 1), (key2341, 1), (key2079, 1), (key2274, 1), (key2077, 1), (key2347, 1), (key2187, 1), (key2343, 1), (key2085, 1), (key2174, 1), (key2077, 1), (key2287, 1), (key2187, 1), (key2279, 1), (key2085, 1), (key2176, 1), (key2079, 1), (key2279, -2), (key2276, -2), (key2176, -2), (key2287, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2187, -2), (key2279, -2), (key2085, -2), (key2176, -2), (key2079, -2)]

def rawRow8998 : Integer.Sparse Key := [(key2187, 1), (key2187, 1), (key2287, 1), (key2287, 1), (key2347, 1), (key2347, 1), (key2085, 1), (key2085, 1), (key2279, 1), (key2279, 1), (key2343, 1), (key2343, 1), (key2079, 1), (key2079, 1), (key2176, 1), (key2176, 1), (key2341, 1), (key2341, 1), (key2077, 1), (key2077, 1), (key2174, 1), (key2174, 1), (key2274, 1), (key2274, 1), (key2187, -2), (key2287, -2), (key2287, -2), (key2085, -2), (key2279, -2), (key2279, -2), (key2079, -2), (key2079, -2), (key2176, -2), (key2176, -2), (key2276, -2), (key2276, -2)]

def rawRow8999 : Integer.Sparse Key := [(key2287, 1), (key2347, 1), (key2187, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2274, 1), (key2077, 1), (key2174, 1), (key2287, -2), (key2187, -2), (key2287, -2), (key2279, -2), (key2085, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2079, -2), (key2276, -2), (key2079, -2), (key2176, -2)]

def rawRow9000 : Integer.Sparse Key := [(key2347, 1), (key2287, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2187, 1), (key2343, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2085, 1), (key2341, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2079, 1), (key2274, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2174, 1), (key2077, 1), (key2287, -2), (key2287, -2), (key2187, -2), (key2279, -2), (key2279, -2), (key2085, -2), (key2276, -2), (key2176, -2), (key2276, -2), (key2079, -2), (key2176, -2), (key2079, -2)]

def rawRow9001 : Integer.Sparse Key := [(key843, -6), (key843, -6), (key843, -6), (key844, -6), (key943, 2), (key943, 2), (key944, 2), (key943, 2), (key943, 2), (key945, 2), (key943, 2), (key944, 2), (key943, 2), (key945, 2), (key944, 2), (key945, 2)]

def rawRow9002 : Integer.Sparse Key := [(key843, -6), (key843, -6), (key844, -6), (key843, -6), (key943, 2), (key944, 2), (key943, 2), (key943, 2), (key945, 2), (key943, 2), (key944, 2), (key943, 2), (key945, 2), (key943, 2), (key945, 2), (key944, 2)]

def rawRow9003 : Integer.Sparse Key := [(key843, -6), (key844, -6), (key843, -6), (key843, -6), (key944, 2), (key943, 2), (key943, 2), (key945, 2), (key943, 2), (key943, 2), (key945, 2), (key945, 2), (key944, 2), (key944, 2), (key943, 2), (key943, 2)]

def rawRow9004 : Integer.Sparse Key := [(key844, -6), (key843, -6), (key843, -6), (key843, -6), (key945, 2), (key945, 2), (key945, 2), (key944, 2), (key944, 2), (key944, 2), (key943, 2), (key943, 2), (key943, 2), (key943, 2), (key943, 2), (key943, 2)]

def rawRow9005 : Integer.Sparse Key := [(key754, -6), (key943, -6), (key943, -6), (key945, -6), (key754, 2), (key754, 2), (key755, 2), (key843, 2), (key843, 2), (key844, 2), (key943, 2), (key944, 2), (key943, 2), (key945, 2), (key944, 2), (key945, 2)]

def rawRow9006 : Integer.Sparse Key := [(key754, -6), (key943, -6), (key945, -6), (key943, -6), (key754, 2), (key755, 2), (key754, 2), (key843, 2), (key844, 2), (key843, 2), (key944, 2), (key943, 2), (key945, 2), (key943, 2), (key945, 2), (key944, 2)]

def rawRow9007 : Integer.Sparse Key := [(key754, -6), (key945, -6), (key943, -6), (key943, -6), (key755, 2), (key754, 2), (key754, 2), (key844, 2), (key843, 2), (key843, 2), (key945, 2), (key945, 2), (key944, 2), (key944, 2), (key943, 2), (key943, 2)]

def rawRow9008 : Integer.Sparse Key := [(key943, -6), (key754, -6), (key943, -6), (key945, -6), (key843, 2), (key943, 2), (key944, 2), (key754, 2), (key943, 2), (key945, 2), (key754, 2), (key755, 2), (key843, 2), (key844, 2), (key944, 2), (key945, 2)]

def rawRow9009 : Integer.Sparse Key := [(key943, -6), (key754, -6), (key945, -6), (key943, -6), (key843, 2), (key944, 2), (key943, 2), (key754, 2), (key945, 2), (key943, 2), (key755, 2), (key754, 2), (key844, 2), (key843, 2), (key945, 2), (key944, 2)]

def rawRow9010 : Integer.Sparse Key := [(key943, -6), (key943, -6), (key754, -6), (key945, -6), (key943, 2), (key843, 2), (key944, 2), (key943, 2), (key754, 2), (key945, 2), (key843, 2), (key944, 2), (key754, 2), (key945, 2), (key755, 2), (key844, 2)]

def rawRow9011 : Integer.Sparse Key := [(key943, -6), (key943, -6), (key945, -6), (key754, -6), (key943, 2), (key944, 2), (key843, 2), (key943, 2), (key945, 2), (key754, 2), (key944, 2), (key843, 2), (key945, 2), (key754, 2), (key844, 2), (key755, 2)]

def rawRow9012 : Integer.Sparse Key := [(key943, -6), (key945, -6), (key754, -6), (key943, -6), (key944, 2), (key843, 2), (key943, 2), (key945, 2), (key754, 2), (key943, 2), (key844, 2), (key945, 2), (key755, 2), (key944, 2), (key754, 2), (key843, 2)]

def rawRow9013 : Integer.Sparse Key := [(key943, -6), (key945, -6), (key943, -6), (key754, -6), (key944, 2), (key943, 2), (key843, 2), (key945, 2), (key943, 2), (key754, 2), (key945, 2), (key844, 2), (key944, 2), (key755, 2), (key843, 2), (key754, 2)]

def rawRow9014 : Integer.Sparse Key := [(key945, -6), (key754, -6), (key943, -6), (key943, -6), (key844, 2), (key945, 2), (key945, 2), (key755, 2), (key944, 2), (key944, 2), (key754, 2), (key754, 2), (key843, 2), (key843, 2), (key943, 2), (key943, 2)]

def rawRow9015 : Integer.Sparse Key := [(key945, -6), (key943, -6), (key754, -6), (key943, -6), (key945, 2), (key844, 2), (key945, 2), (key944, 2), (key755, 2), (key944, 2), (key843, 2), (key943, 2), (key754, 2), (key943, 2), (key754, 2), (key843, 2)]

def rawRow9016 : Integer.Sparse Key := [(key945, -6), (key943, -6), (key943, -6), (key754, -6), (key945, 2), (key945, 2), (key844, 2), (key944, 2), (key944, 2), (key755, 2), (key943, 2), (key843, 2), (key943, 2), (key754, 2), (key843, 2), (key754, 2)]

def rawRow9017 : Integer.Sparse Key := [(key2006, 6), (key2007, 6), (key2007, 6), (key2007, 6), (key2340, -6), (key2340, -6), (key2340, -6), (key2349, -6)]

def rawRow9018 : Integer.Sparse Key := [(key2007, 6), (key2006, 6), (key2007, 6), (key2007, 6), (key2340, -6), (key2340, -6), (key2349, -6), (key2340, -6)]

end MUB6.Certificate.GramRows

end OAI
end


