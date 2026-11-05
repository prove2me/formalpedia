-- Prove2me | Definitions.Def_OAIQ106E049
-- name    : OAIQ106E049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:02:35.159287+00:00
-- url     : https://prove2.me/theorems/a88fc9d6-0eb4-4eee-9f4a-7ca995180c0a
-- title:
--   Definitions bundle OAIQ106E049 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1556 declarations of OpenAI's Lean: 1556 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow17525`, `OAI.MUB6.Certificate.GramRows.rawRow17526`, `OAI.MUB6.Certificate.GramRows.rawRow17527`, `OAI.MUB6.Certificate.GramRows.rawRow17528`, `OAI.MUB6.Certificate.GramRows.rawRow17529`, `OAI.MUB6.Certificate.GramRows.rawRow1753`, `OAI.MUB6.Certificate.GramRows.rawRow17530`, `OAI.MUB6.Certificate.GramRows.rawRow17531`, `OAI.MUB6.Certificate.GramRows.rawRow17532`, `OAI.MUB6.Certificate.GramRows.rawRow17533`, `OAI.MUB6.Certificate.GramRows.rawRow17534`, `OAI.MUB6.Certificate.GramRows.rawRow17535`, `OAI.MUB6.Certificate.GramRows.rawRow17536`, `OAI.MUB6.Certificate.GramRows.rawRow17537`, `OAI.MUB6.Certificate.GramRows.rawRow17538`, `OAI.MUB6.Certificate.GramRows.rawRow17539`, `OAI.MUB6.Certificate.GramRows.rawRow1754`, `OAI.MUB6.Certificate.GramRows.rawRow17540`, `OAI.MUB6.Certificate.GramRows.rawRow17541`, `OAI.MUB6.Certificate.GramRows.rawRow17542`, `OAI.MUB6.Certificate.GramRows.rawRow17543`, `OAI.MUB6.Certificate.GramRows.rawRow17544`, `OAI.MUB6.Certificate.GramRows.rawRow17545`, `OAI.MUB6.Certificate.GramRows.rawRow17546`, `OAI.MUB6.Certificate.GramRows.rawRow17547`, `OAI.MUB6.Certificate.GramRows.rawRow17548`, `OAI.MUB6.Certificate.GramRows.rawRow17549`, `OAI.MUB6.Certificate.GramRows.rawRow1755`, `OAI.MUB6.Certificate.GramRows.rawRow17550`, `OAI.MUB6.Certificate.GramRows.rawRow17551`, `OAI.MUB6.Certificate.GramRows.rawRow17552`, `OAI.MUB6.Certificate.GramRows.rawRow17553`, `OAI.MUB6.Certificate.GramRows.rawRow17554`, `OAI.MUB6.Certificate.GramRows.rawRow17555`, `OAI.MUB6.Certificate.GramRows.rawRow17556`, `OAI.MUB6.Certificate.GramRows.rawRow17557`, `OAI.MUB6.Certificate.GramRows.rawRow17558`, `OAI.MUB6.Certificate.GramRows.rawRow17559`, `OAI.MUB6.Certificate.GramRows.rawRow1756`, `OAI.MUB6.Certificate.GramRows.rawRow17560` and 1516 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block160`, `MutuallyUnbiased_GramRows_Block161`, `MutuallyUnbiased_GramRows_Block162`, `MutuallyUnbiased_GramRows_Block163`, `MutuallyUnbiased_GramRows_Block164`, `MutuallyUnbiased_GramRows_Block165`, `MutuallyUnbiased_GramRows_Block166`, `MutuallyUnbiased_GramRows_Block167`, `MutuallyUnbiased_GramRows_Block168`, `MutuallyUnbiased_GramRows_Block169`, `MutuallyUnbiased_GramRows_Block170`, `MutuallyUnbiased_GramRows_Block171`, `MutuallyUnbiased_GramRows_Block2`, `MutuallyUnbiased_GramRows_Block37`, `MutuallyUnbiased_GramRows_Block38`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow21_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval2_2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6_e`.
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

def rawRow18 : Integer.Sparse Key := [(key335, -1), (key340, -1), (key335, 2), (key319, 1), (key328, 1), (key305, -1), (key319, -1), (key316, -2), (key302, 1), (key316, 1), (key578, 1), (key583, 1), (key578, -2), (key409, -1), (key418, -1), (key239, 1), (key409, 1), (key406, 2), (key236, -1), (key406, -1), (key450, -1), (key601, -1), (key328, 1), (key450, 1), (key442, 1), (key595, 1), (key260, -1), (key442, -1), (key316, -1), (key435, -1), (key248, 1), (key435, 1), (key475, 2), (key340, -1), (key475, -1), (key469, -2), (key271, 1), (key469, 1), (key335, 1), (key467, 1), (key267, -1), (key467, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17525 : Integer.Sparse Key := [(key524, -2), (key517, -2), (key524, -2), (key517, 6), (key555, -2), (key549, -2), (key555, -2), (key524, 2), (key517, 2), (key555, 2), (key517, 2), (key555, 2), (key524, 2), (key517, -2), (key549, -2), (key517, -2), (key555, 6), (key524, -2), (key555, -2), (key524, -2)]

def rawRow17526 : Integer.Sparse Key := [(key524, -2), (key524, -2), (key517, -2), (key517, 6), (key555, -2), (key555, -2), (key549, -2), (key555, 2), (key555, 2), (key524, 2), (key524, 2), (key517, 2), (key517, 2), (key549, -2), (key517, -2), (key517, -2), (key555, 6), (key555, -2), (key524, -2), (key524, -2)]

def rawRow17527 : Integer.Sparse Key := [(key549, -2), (key555, -2), (key555, -2), (key555, 6), (key517, -2), (key524, -2), (key524, -2), (key517, 2), (key524, 2), (key517, 2), (key555, 2), (key524, 2), (key555, 2), (key524, -2), (key524, -2), (key555, -2), (key517, 6), (key517, -2), (key517, -2), (key549, -2)]

def rawRow17528 : Integer.Sparse Key := [(key555, -2), (key549, -2), (key555, -2), (key555, 6), (key524, -2), (key517, -2), (key524, -2), (key524, 2), (key517, 2), (key555, 2), (key517, 2), (key555, 2), (key524, 2), (key524, -2), (key555, -2), (key524, -2), (key517, 6), (key517, -2), (key549, -2), (key517, -2)]

def rawRow17529 : Integer.Sparse Key := [(key555, -2), (key555, -2), (key549, -2), (key555, 6), (key524, -2), (key524, -2), (key517, -2), (key555, 2), (key555, 2), (key524, 2), (key524, 2), (key517, 2), (key517, 2), (key555, -2), (key524, -2), (key524, -2), (key517, 6), (key549, -2), (key517, -2), (key517, -2)]

def rawRow17530 : Integer.Sparse Key := [(key555, -2), (key555, -2), (key555, -2), (key549, 6), (key555, -2), (key555, -2), (key555, -2), (key524, 2), (key524, 2), (key524, 2), (key524, 2), (key524, 2), (key524, 2), (key517, -2), (key517, -2), (key517, -2), (key549, 6), (key517, -2), (key517, -2), (key517, -2)]

def rawRow17531 : Integer.Sparse Key := [(key1854, 2), (key1856, 2), (key1856, 2), (key1856, -2), (key1856, -2), (key1858, -2), (key1854, 2), (key1856, 2), (key1856, 2), (key1856, -1), (key1856, -1), (key1887, -1), (key1887, -1), (key1890, -1), (key1890, -1), (key1856, -2), (key1856, -2), (key1858, -2), (key1856, -1), (key1856, -1), (key1887, -1), (key1887, -1), (key1890, -1), (key1890, -1), (key1858, 4), (key1890, 4), (key1890, 4)]

def rawRow17532 : Integer.Sparse Key := [(key1856, 2), (key1854, 2), (key1856, 2), (key1856, -2), (key1858, -2), (key1856, -2), (key1856, 2), (key1854, 2), (key1856, 2), (key1887, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1856, -2), (key1858, -2), (key1856, -2), (key1887, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1890, 4), (key1858, 4), (key1890, 4)]

def rawRow17533 : Integer.Sparse Key := [(key1856, 2), (key1856, 2), (key1854, 2), (key1858, -2), (key1856, -2), (key1856, -2), (key1856, 2), (key1856, 2), (key1854, 2), (key1890, -1), (key1887, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1856, -1), (key1858, -2), (key1856, -2), (key1856, -2), (key1890, -1), (key1887, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1856, -1), (key1890, 4), (key1890, 4), (key1858, 4)]

def rawRow17534 : Integer.Sparse Key := [(key1856, 2), (key1856, 2), (key1858, 2), (key1854, -2), (key1856, -2), (key1856, -2), (key1887, 2), (key1887, 2), (key1890, 2), (key1854, -1), (key1856, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1887, -1), (key1887, -2), (key1890, -2), (key1890, -2), (key1856, -1), (key1858, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1890, -1), (key1856, 4), (key1856, 4), (key1887, 4)]

def rawRow17535 : Integer.Sparse Key := [(key1856, 2), (key1858, 2), (key1856, 2), (key1856, -2), (key1854, -2), (key1856, -2), (key1887, 2), (key1890, 2), (key1887, 2), (key1856, -1), (key1854, -1), (key1887, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1890, -2), (key1887, -2), (key1890, -2), (key1858, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1856, 4), (key1887, 4), (key1856, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17536 : Integer.Sparse Key := [(key1858, 2), (key1856, 2), (key1856, 2), (key1856, -2), (key1856, -2), (key1854, -2), (key1890, 2), (key1887, 2), (key1887, 2), (key1887, -1), (key1887, -1), (key1856, -1), (key1856, -1), (key1854, -1), (key1854, -1), (key1890, -2), (key1890, -2), (key1887, -2), (key1890, -1), (key1890, -1), (key1858, -1), (key1858, -1), (key1856, -1), (key1856, -1), (key1887, 4), (key1856, 4), (key1856, 4)]

def rawRow17537 : Integer.Sparse Key := [(key1887, 2), (key1887, 2), (key1890, 2), (key1887, -2), (key1890, -2), (key1890, -2), (key1856, 2), (key1856, 2), (key1858, 2), (key1856, -1), (key1858, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1890, -1), (key1854, -2), (key1856, -2), (key1856, -2), (key1854, -1), (key1856, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1887, -1), (key1856, 4), (key1856, 4), (key1887, 4)]

def rawRow17538 : Integer.Sparse Key := [(key1887, 2), (key1890, 2), (key1887, 2), (key1890, -2), (key1887, -2), (key1890, -2), (key1856, 2), (key1858, 2), (key1856, 2), (key1858, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1856, -2), (key1854, -2), (key1856, -2), (key1856, -1), (key1854, -1), (key1887, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1856, 4), (key1887, 4), (key1856, 4)]

def rawRow17539 : Integer.Sparse Key := [(key1890, 2), (key1887, 2), (key1887, 2), (key1890, -2), (key1890, -2), (key1887, -2), (key1858, 2), (key1856, 2), (key1856, 2), (key1890, -1), (key1890, -1), (key1858, -1), (key1858, -1), (key1856, -1), (key1856, -1), (key1856, -2), (key1856, -2), (key1854, -2), (key1887, -1), (key1887, -1), (key1856, -1), (key1856, -1), (key1854, -1), (key1854, -1), (key1887, 4), (key1856, 4), (key1856, 4)]

def rawRow17540 : Integer.Sparse Key := [(key1890, 2), (key1890, 2), (key1890, 2), (key1887, -2), (key1887, -2), (key1887, -2), (key1890, 2), (key1890, 2), (key1890, 2), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1887, -2), (key1887, -2), (key1887, -2), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1854, 4), (key1854, 4), (key1854, 4)]

def rawRow17541 : Integer.Sparse Key := [(key1862, 2), (key1862, 2), (key1866, 2), (key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1862, 2), (key1862, 2), (key1866, 2), (key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1868, 2), (key1868, 2), (key1878, 2), (key1878, 2), (key1889, 2), (key1889, 2)]

def rawRow17542 : Integer.Sparse Key := [(key1862, 2), (key1866, 2), (key1862, 2), (key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, 2), (key1866, 2), (key1862, 2), (key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1878, 2), (key1889, 2), (key1868, 2), (key1889, 2), (key1868, 2), (key1878, 2)]

def rawRow17543 : Integer.Sparse Key := [(key1866, 2), (key1862, 2), (key1862, 2), (key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1866, 2), (key1862, 2), (key1862, 2), (key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1889, 2), (key1878, 2), (key1889, 2), (key1868, 2), (key1878, 2), (key1868, 2)]

def rawRow17544 : Integer.Sparse Key := [(key1868, 2), (key1871, 2), (key1871, 2), (key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1878, 2), (key1881, 2), (key1881, 2), (key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2)]

def rawRow17545 : Integer.Sparse Key := [(key1871, 2), (key1868, 2), (key1871, 2), (key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1881, 2), (key1878, 2), (key1881, 2), (key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2)]

def rawRow17546 : Integer.Sparse Key := [(key1871, 2), (key1871, 2), (key1868, 2), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1878, 2), (key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2)]

def rawRow17547 : Integer.Sparse Key := [(key1878, 2), (key1881, 2), (key1881, 2), (key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1868, 2), (key1871, 2), (key1871, 2), (key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2)]

def rawRow17548 : Integer.Sparse Key := [(key1881, 2), (key1878, 2), (key1881, 2), (key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1871, 2), (key1868, 2), (key1871, 2), (key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2)]

def rawRow17549 : Integer.Sparse Key := [(key1881, 2), (key1881, 2), (key1878, 2), (key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1871, 2), (key1871, 2), (key1868, 2), (key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2)]

def rawRow17550 : Integer.Sparse Key := [(key1889, 2), (key1889, 2), (key1889, 2), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1889, 2), (key1889, 2), (key1889, 2), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2)]

def rawRow17551 : Integer.Sparse Key := [(key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1866, 2), (key1871, 2), (key1871, 2), (key1862, 1), (key1862, 1), (key1878, 1), (key1878, 1), (key1881, 1), (key1881, 1), (key1866, -2), (key1881, -2), (key1881, -2), (key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1862, 1), (key1862, 1), (key1878, 1), (key1878, 1), (key1881, 1), (key1881, 1), (key1866, 2), (key1871, 2), (key1871, 2), (key1866, -2), (key1881, -2), (key1881, -2)]

def rawRow17552 : Integer.Sparse Key := [(key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1871, 2), (key1866, 2), (key1871, 2), (key1878, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1881, -2), (key1866, -2), (key1881, -2), (key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1878, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1871, 2), (key1866, 2), (key1871, 2), (key1881, -2), (key1866, -2), (key1881, -2)]

def rawRow17553 : Integer.Sparse Key := [(key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1871, 2), (key1871, 2), (key1866, 2), (key1881, 1), (key1878, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1862, 1), (key1881, -2), (key1881, -2), (key1866, -2), (key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1881, 1), (key1878, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1862, 1), (key1871, 2), (key1871, 2), (key1866, 2), (key1881, -2), (key1881, -2), (key1866, -2)]

def rawRow17554 : Integer.Sparse Key := [(key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1862, 2), (key1862, 2), (key1868, 2), (key1862, 1), (key1866, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1881, 1), (key1862, -2), (key1862, -2), (key1878, -2), (key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1868, 1), (key1871, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1889, 1), (key1881, 2), (key1881, 2), (key1889, 2), (key1871, -2), (key1871, -2), (key1889, -2)]

def rawRow17555 : Integer.Sparse Key := [(key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1862, 2), (key1868, 2), (key1862, 2), (key1866, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1862, -2), (key1878, -2), (key1862, -2), (key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1871, 1), (key1868, 1), (key1889, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1881, 2), (key1889, 2), (key1881, 2), (key1871, -2), (key1889, -2), (key1871, -2)]

def rawRow17556 : Integer.Sparse Key := [(key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1868, 2), (key1862, 2), (key1862, 2), (key1881, 1), (key1881, 1), (key1866, 1), (key1866, 1), (key1862, 1), (key1862, 1), (key1878, -2), (key1862, -2), (key1862, -2), (key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1889, 1), (key1889, 1), (key1871, 1), (key1871, 1), (key1868, 1), (key1868, 1), (key1889, 2), (key1881, 2), (key1881, 2), (key1889, -2), (key1871, -2), (key1871, -2)]

def rawRow17557 : Integer.Sparse Key := [(key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1881, 2), (key1881, 2), (key1889, 2), (key1868, 1), (key1871, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1889, 1), (key1871, -2), (key1871, -2), (key1889, -2), (key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1862, 1), (key1866, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1881, 1), (key1862, 2), (key1862, 2), (key1868, 2), (key1862, -2), (key1862, -2), (key1878, -2)]

def rawRow17558 : Integer.Sparse Key := [(key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1881, 2), (key1889, 2), (key1881, 2), (key1871, 1), (key1868, 1), (key1889, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1871, -2), (key1889, -2), (key1871, -2), (key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1866, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1862, 2), (key1868, 2), (key1862, 2), (key1862, -2), (key1878, -2), (key1862, -2)]

def rawRow17559 : Integer.Sparse Key := [(key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1889, 2), (key1881, 2), (key1881, 2), (key1889, 1), (key1889, 1), (key1871, 1), (key1871, 1), (key1868, 1), (key1868, 1), (key1889, -2), (key1871, -2), (key1871, -2), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 1), (key1881, 1), (key1866, 1), (key1866, 1), (key1862, 1), (key1862, 1), (key1868, 2), (key1862, 2), (key1862, 2), (key1878, -2), (key1862, -2), (key1862, -2)]

def rawRow17560 : Integer.Sparse Key := [(key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1878, 2), (key1878, 2), (key1878, 2), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1868, -2), (key1868, -2), (key1868, -2), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1878, 2), (key1878, 2), (key1878, 2), (key1868, -2), (key1868, -2), (key1868, -2)]

def rawRow17561 : Integer.Sparse Key := [(key1938, -1), (key1938, -1), (key1941, -1), (key1941, -1), (key1942, -1), (key1942, -1), (key1939, 2), (key1942, 2), (key1942, 2), (key1938, 1), (key1938, 1), (key1950, 1), (key1950, 1), (key1951, 1), (key1951, 1), (key1939, -2), (key1951, -2), (key1951, -2), (key1938, -1), (key1938, -1), (key1941, -1), (key1941, -1), (key1942, -1), (key1942, -1), (key1938, 1), (key1938, 1), (key1950, 1), (key1950, 1), (key1951, 1), (key1951, 1), (key1939, 2), (key1942, 2), (key1942, 2), (key1939, -2), (key1951, -2), (key1951, -2)]

def rawRow17562 : Integer.Sparse Key := [(key1941, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1942, 2), (key1939, 2), (key1942, 2), (key1950, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1951, -2), (key1939, -2), (key1951, -2), (key1941, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1950, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1942, 2), (key1939, 2), (key1942, 2), (key1951, -2), (key1939, -2), (key1951, -2)]

def rawRow17563 : Integer.Sparse Key := [(key1942, -1), (key1941, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1938, -1), (key1942, 2), (key1942, 2), (key1939, 2), (key1951, 1), (key1950, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1938, 1), (key1951, -2), (key1951, -2), (key1939, -2), (key1942, -1), (key1941, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1938, -1), (key1951, 1), (key1950, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1938, 1), (key1942, 2), (key1942, 2), (key1939, 2), (key1951, -2), (key1951, -2), (key1939, -2)]

def rawRow17564 : Integer.Sparse Key := [(key1938, -1), (key1939, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1942, -1), (key1938, 2), (key1938, 2), (key1941, 2), (key1938, 1), (key1939, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1951, 1), (key1938, -2), (key1938, -2), (key1950, -2), (key1950, -1), (key1951, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1956, -1), (key1941, 1), (key1942, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1956, 1), (key1951, 2), (key1951, 2), (key1956, 2), (key1942, -2), (key1942, -2), (key1956, -2)]

def rawRow17565 : Integer.Sparse Key := [(key1939, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1938, 2), (key1941, 2), (key1938, 2), (key1939, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1938, -2), (key1950, -2), (key1938, -2), (key1951, -1), (key1950, -1), (key1956, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1942, 1), (key1941, 1), (key1956, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1951, 2), (key1956, 2), (key1951, 2), (key1942, -2), (key1956, -2), (key1942, -2)]

def rawRow17566 : Integer.Sparse Key := [(key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1941, 2), (key1938, 2), (key1938, 2), (key1951, 1), (key1951, 1), (key1939, 1), (key1939, 1), (key1938, 1), (key1938, 1), (key1950, -2), (key1938, -2), (key1938, -2), (key1956, -1), (key1956, -1), (key1951, -1), (key1951, -1), (key1950, -1), (key1950, -1), (key1956, 1), (key1956, 1), (key1942, 1), (key1942, 1), (key1941, 1), (key1941, 1), (key1956, 2), (key1951, 2), (key1951, 2), (key1956, -2), (key1942, -2), (key1942, -2)]

def rawRow17567 : Integer.Sparse Key := [(key1950, -1), (key1951, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1956, -1), (key1951, 2), (key1951, 2), (key1956, 2), (key1941, 1), (key1942, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1956, 1), (key1942, -2), (key1942, -2), (key1956, -2), (key1938, -1), (key1939, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1942, -1), (key1938, 1), (key1939, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1951, 1), (key1938, 2), (key1938, 2), (key1941, 2), (key1938, -2), (key1938, -2), (key1950, -2)]

def rawRow17568 : Integer.Sparse Key := [(key1951, -1), (key1950, -1), (key1956, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1951, 2), (key1956, 2), (key1951, 2), (key1942, 1), (key1941, 1), (key1956, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1942, -2), (key1956, -2), (key1942, -2), (key1939, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1939, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1938, 2), (key1941, 2), (key1938, 2), (key1938, -2), (key1950, -2), (key1938, -2)]

def rawRow17569 : Integer.Sparse Key := [(key1956, -1), (key1956, -1), (key1951, -1), (key1951, -1), (key1950, -1), (key1950, -1), (key1956, 2), (key1951, 2), (key1951, 2), (key1956, 1), (key1956, 1), (key1942, 1), (key1942, 1), (key1941, 1), (key1941, 1), (key1956, -2), (key1942, -2), (key1942, -2), (key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1951, 1), (key1951, 1), (key1939, 1), (key1939, 1), (key1938, 1), (key1938, 1), (key1941, 2), (key1938, 2), (key1938, 2), (key1950, -2), (key1938, -2), (key1938, -2)]

def rawRow17570 : Integer.Sparse Key := [(key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1950, 2), (key1950, 2), (key1950, 2), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1941, -2), (key1941, -2), (key1941, -2), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1950, 2), (key1950, 2), (key1950, 2), (key1941, -2), (key1941, -2), (key1941, -2)]

def rawRow17571 : Integer.Sparse Key := [(key1863, 2), (key1880, 2), (key1880, 2), (key1865, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1883, -1), (key1883, -1), (key1863, 2), (key1880, 2), (key1880, 2), (key1870, -1), (key1870, -1), (key1880, -1), (key1880, -1), (key1891, -1), (key1891, -1), (key1865, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1883, -1), (key1883, -1), (key1870, -1), (key1870, -1), (key1880, -1), (key1880, -1), (key1891, -1), (key1891, -1), (key1872, 2), (key1872, 2), (key1883, 2), (key1883, 2), (key1891, 2), (key1891, 2)]

def rawRow17572 : Integer.Sparse Key := [(key1880, 2), (key1863, 2), (key1880, 2), (key1880, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1880, 2), (key1863, 2), (key1880, 2), (key1880, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1880, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1883, 2), (key1891, 2), (key1872, 2), (key1891, 2), (key1872, 2), (key1883, 2)]

def rawRow17573 : Integer.Sparse Key := [(key1880, 2), (key1880, 2), (key1863, 2), (key1883, -1), (key1880, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1865, -1), (key1880, 2), (key1880, 2), (key1863, 2), (key1891, -1), (key1880, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1870, -1), (key1883, -1), (key1880, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1865, -1), (key1891, -1), (key1880, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1870, -1), (key1891, 2), (key1883, 2), (key1891, 2), (key1872, 2), (key1883, 2), (key1872, 2)]

def rawRow17574 : Integer.Sparse Key := [(key1865, 2), (key1865, 2), (key1883, 2), (key1863, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1880, -1), (key1870, 2), (key1870, 2), (key1891, 2), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1870, -1), (key1872, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1891, -1), (key1865, -1), (key1872, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1883, -1), (key1865, 2), (key1870, 2), (key1865, 2), (key1880, 2), (key1870, 2), (key1880, 2)]

def rawRow17575 : Integer.Sparse Key := [(key1865, 2), (key1883, 2), (key1865, 2), (key1865, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1870, 2), (key1891, 2), (key1870, 2), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1872, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1872, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1870, 2), (key1865, 2), (key1880, 2), (key1865, 2), (key1880, 2), (key1870, 2)]

def rawRow17576 : Integer.Sparse Key := [(key1883, 2), (key1865, 2), (key1865, 2), (key1880, -1), (key1880, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1891, 2), (key1870, 2), (key1870, 2), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1891, -1), (key1891, -1), (key1872, -1), (key1872, -1), (key1870, -1), (key1870, -1), (key1883, -1), (key1883, -1), (key1872, -1), (key1872, -1), (key1865, -1), (key1865, -1), (key1880, 2), (key1880, 2), (key1870, 2), (key1870, 2), (key1865, 2), (key1865, 2)]

def rawRow17577 : Integer.Sparse Key := [(key1870, 2), (key1870, 2), (key1891, 2), (key1870, -1), (key1872, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1891, -1), (key1865, 2), (key1865, 2), (key1883, 2), (key1865, -1), (key1872, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1883, -1), (key1863, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1880, -1), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1865, 2), (key1870, 2), (key1865, 2), (key1880, 2), (key1870, 2), (key1880, 2)]

def rawRow17578 : Integer.Sparse Key := [(key1870, 2), (key1891, 2), (key1870, 2), (key1872, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1865, 2), (key1883, 2), (key1865, 2), (key1872, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1870, 2), (key1865, 2), (key1880, 2), (key1865, 2), (key1880, 2), (key1870, 2)]

def rawRow17579 : Integer.Sparse Key := [(key1891, 2), (key1870, 2), (key1870, 2), (key1891, -1), (key1891, -1), (key1872, -1), (key1872, -1), (key1870, -1), (key1870, -1), (key1883, 2), (key1865, 2), (key1865, 2), (key1883, -1), (key1883, -1), (key1872, -1), (key1872, -1), (key1865, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1880, 2), (key1880, 2), (key1870, 2), (key1870, 2), (key1865, 2), (key1865, 2)]

def rawRow17580 : Integer.Sparse Key := [(key1872, 2), (key1872, 2), (key1872, 2), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1872, 2), (key1872, 2), (key1872, 2), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1863, 2), (key1863, 2), (key1863, 2), (key1863, 2), (key1863, 2), (key1863, 2)]

def rawRow17581 : Integer.Sparse Key := [(key533, 4), (key533, 4), (key536, 4), (key533, -2), (key533, -2), (key539, -2), (key539, -2), (key544, -2), (key544, -2), (key533, -2), (key533, -2), (key539, -2), (key539, -2), (key544, -2), (key544, -2), (key539, 4), (key539, 4), (key556, 4)]

def rawRow17582 : Integer.Sparse Key := [(key533, 4), (key536, 4), (key533, 4), (key539, -2), (key544, -2), (key533, -2), (key544, -2), (key533, -2), (key539, -2), (key539, -2), (key544, -2), (key533, -2), (key544, -2), (key533, -2), (key539, -2), (key539, 4), (key556, 4), (key539, 4)]

def rawRow17583 : Integer.Sparse Key := [(key536, 4), (key533, 4), (key533, 4), (key544, -2), (key539, -2), (key544, -2), (key533, -2), (key539, -2), (key533, -2), (key544, -2), (key539, -2), (key544, -2), (key533, -2), (key539, -2), (key533, -2), (key556, 4), (key539, 4), (key539, 4)]

def rawRow17584 : Integer.Sparse Key := [(key539, 4), (key544, 4), (key544, 4), (key533, -2), (key536, -2), (key533, -2), (key544, -2), (key536, -2), (key544, -2), (key539, -2), (key544, -2), (key539, -2), (key556, -2), (key544, -2), (key556, -2), (key533, 4), (key544, 4), (key544, 4)]

def rawRow17585 : Integer.Sparse Key := [(key544, 4), (key539, 4), (key544, 4), (key536, -2), (key533, -2), (key544, -2), (key533, -2), (key544, -2), (key536, -2), (key544, -2), (key539, -2), (key556, -2), (key539, -2), (key556, -2), (key544, -2), (key544, 4), (key533, 4), (key544, 4)]

def rawRow17586 : Integer.Sparse Key := [(key544, 4), (key544, 4), (key539, 4), (key544, -2), (key544, -2), (key536, -2), (key536, -2), (key533, -2), (key533, -2), (key556, -2), (key556, -2), (key544, -2), (key544, -2), (key539, -2), (key539, -2), (key544, 4), (key544, 4), (key533, 4)]

def rawRow17587 : Integer.Sparse Key := [(key539, 4), (key544, 4), (key544, 4), (key539, -2), (key544, -2), (key539, -2), (key556, -2), (key544, -2), (key556, -2), (key533, -2), (key536, -2), (key533, -2), (key544, -2), (key536, -2), (key544, -2), (key533, 4), (key544, 4), (key544, 4)]

def rawRow17588 : Integer.Sparse Key := [(key544, 4), (key539, 4), (key544, 4), (key544, -2), (key539, -2), (key556, -2), (key539, -2), (key556, -2), (key544, -2), (key536, -2), (key533, -2), (key544, -2), (key533, -2), (key544, -2), (key536, -2), (key544, 4), (key533, 4), (key544, 4)]

def rawRow17589 : Integer.Sparse Key := [(key544, 4), (key544, 4), (key539, 4), (key556, -2), (key556, -2), (key544, -2), (key544, -2), (key539, -2), (key539, -2), (key544, -2), (key544, -2), (key536, -2), (key536, -2), (key533, -2), (key533, -2), (key544, 4), (key544, 4), (key533, 4)]

def rawRow17590 : Integer.Sparse Key := [(key556, 4), (key556, 4), (key556, 4), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key536, 4), (key536, 4), (key536, 4)]

def rawRow17591 : Integer.Sparse Key := [(key633, -2), (key633, -2), (key635, -2), (key635, -2), (key638, -2), (key638, -2), (key635, 2), (key635, 2), (key644, 2), (key638, 2), (key638, 2), (key644, 2), (key635, 2), (key635, 2), (key644, 2), (key644, -6), (key638, 2), (key638, 2), (key644, 2), (key644, -6)]

def rawRow17592 : Integer.Sparse Key := [(key635, -2), (key638, -2), (key633, -2), (key638, -2), (key633, -2), (key635, -2), (key635, 2), (key644, 2), (key635, 2), (key638, 2), (key644, 2), (key638, 2), (key635, 2), (key644, 2), (key635, 2), (key644, -6), (key638, 2), (key644, 2), (key638, 2), (key644, -6)]

def rawRow17593 : Integer.Sparse Key := [(key638, -2), (key635, -2), (key638, -2), (key633, -2), (key635, -2), (key633, -2), (key644, 2), (key635, 2), (key635, 2), (key644, 2), (key638, 2), (key638, 2), (key644, 2), (key635, 2), (key635, 2), (key644, -6), (key644, 2), (key638, 2), (key638, 2), (key644, -6)]

def rawRow17594 : Integer.Sparse Key := [(key635, -2), (key638, -2), (key635, -2), (key644, -2), (key638, -2), (key644, -2), (key633, 2), (key638, 2), (key638, 2), (key633, 2), (key635, 2), (key635, 2), (key635, 2), (key644, 2), (key644, 2), (key635, -6), (key638, 2), (key644, 2), (key644, 2), (key638, -6)]

def rawRow17595 : Integer.Sparse Key := [(key638, -2), (key635, -2), (key644, -2), (key635, -2), (key644, -2), (key638, -2), (key638, 2), (key633, 2), (key638, 2), (key635, 2), (key633, 2), (key635, 2), (key644, 2), (key635, 2), (key644, 2), (key635, -6), (key644, 2), (key638, 2), (key644, 2), (key638, -6)]

def rawRow17596 : Integer.Sparse Key := [(key644, -2), (key644, -2), (key638, -2), (key638, -2), (key635, -2), (key635, -2), (key638, 2), (key638, 2), (key633, 2), (key635, 2), (key635, 2), (key633, 2), (key644, 2), (key644, 2), (key635, 2), (key635, -6), (key644, 2), (key644, 2), (key638, 2), (key638, -6)]

def rawRow17597 : Integer.Sparse Key := [(key635, -2), (key638, -2), (key635, -2), (key644, -2), (key638, -2), (key644, -2), (key635, 2), (key644, 2), (key644, 2), (key638, 2), (key644, 2), (key644, 2), (key633, 2), (key638, 2), (key638, 2), (key638, -6), (key633, 2), (key635, 2), (key635, 2), (key635, -6)]

def rawRow17598 : Integer.Sparse Key := [(key638, -2), (key635, -2), (key644, -2), (key635, -2), (key644, -2), (key638, -2), (key644, 2), (key635, 2), (key644, 2), (key644, 2), (key638, 2), (key644, 2), (key638, 2), (key633, 2), (key638, 2), (key638, -6), (key635, 2), (key633, 2), (key635, 2), (key635, -6)]

def rawRow17599 : Integer.Sparse Key := [(key644, -2), (key644, -2), (key638, -2), (key638, -2), (key635, -2), (key635, -2), (key644, 2), (key644, 2), (key635, 2), (key644, 2), (key644, 2), (key638, 2), (key638, 2), (key638, 2), (key633, 2), (key638, -6), (key635, 2), (key635, 2), (key633, 2), (key635, -6)]

def rawRow17600 : Integer.Sparse Key := [(key644, -2), (key644, -2), (key644, -2), (key644, -2), (key644, -2), (key644, -2), (key638, 2), (key638, 2), (key638, 2), (key635, 2), (key635, 2), (key635, 2), (key638, 2), (key638, 2), (key638, 2), (key633, -6), (key635, 2), (key635, 2), (key635, 2), (key633, -6)]

def rawRow17601 : Integer.Sparse Key := [(key291, 4), (key294, 4), (key294, 4), (key294, -4), (key294, -4), (key298, -4), (key294, -4), (key294, -4), (key298, -4), (key298, 12)]

def rawRow17602 : Integer.Sparse Key := [(key294, 4), (key291, 4), (key294, 4), (key294, -4), (key298, -4), (key294, -4), (key294, -4), (key298, -4), (key294, -4), (key298, 12)]

def rawRow17603 : Integer.Sparse Key := [(key294, 4), (key294, 4), (key291, 4), (key298, -4), (key294, -4), (key294, -4), (key298, -4), (key294, -4), (key294, -4), (key298, 12)]

def rawRow17604 : Integer.Sparse Key := [(key294, 4), (key294, 4), (key298, 4), (key291, -4), (key294, -4), (key294, -4), (key294, -4), (key298, -4), (key298, -4), (key294, 12)]

def rawRow17605 : Integer.Sparse Key := [(key294, 4), (key298, 4), (key294, 4), (key294, -4), (key291, -4), (key294, -4), (key298, -4), (key294, -4), (key298, -4), (key294, 12)]

def rawRow17606 : Integer.Sparse Key := [(key298, 4), (key294, 4), (key294, 4), (key294, -4), (key294, -4), (key291, -4), (key298, -4), (key298, -4), (key294, -4), (key294, 12)]

def rawRow17607 : Integer.Sparse Key := [(key294, 4), (key294, 4), (key298, 4), (key294, -4), (key298, -4), (key298, -4), (key291, -4), (key294, -4), (key294, -4), (key294, 12)]

def rawRow17608 : Integer.Sparse Key := [(key294, 4), (key298, 4), (key294, 4), (key298, -4), (key294, -4), (key298, -4), (key294, -4), (key291, -4), (key294, -4), (key294, 12)]

def rawRow17609 : Integer.Sparse Key := [(key298, 4), (key294, 4), (key294, 4), (key298, -4), (key298, -4), (key294, -4), (key294, -4), (key294, -4), (key291, -4), (key294, 12)]

def rawRow17610 : Integer.Sparse Key := [(key298, 4), (key298, 4), (key298, 4), (key294, -4), (key294, -4), (key294, -4), (key294, -4), (key294, -4), (key294, -4), (key291, 12)]

def rawRow17611 : Integer.Sparse Key := [(key2237, 4), (key2237, 4), (key2260, 4), (key2271, -2), (key2273, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2295, -2), (key2271, -2), (key2273, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2295, -2), (key2325, 4), (key2325, 4), (key2337, 4)]

def rawRow17612 : Integer.Sparse Key := [(key2237, 4), (key2260, 4), (key2237, 4), (key2273, -2), (key2271, -2), (key2295, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2273, -2), (key2271, -2), (key2295, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2325, 4), (key2337, 4), (key2325, 4)]

def rawRow17613 : Integer.Sparse Key := [(key2260, 4), (key2237, 4), (key2237, 4), (key2295, -2), (key2295, -2), (key2273, -2), (key2273, -2), (key2271, -2), (key2271, -2), (key2295, -2), (key2295, -2), (key2273, -2), (key2273, -2), (key2271, -2), (key2271, -2), (key2337, 4), (key2325, 4), (key2325, 4)]

def rawRow17614 : Integer.Sparse Key := [(key1992, 4), (key2271, 4), (key2295, 4), (key1992, -2), (key1995, -2), (key2237, -2), (key2260, -2), (key2273, -2), (key2295, -2), (key2002, -2), (key2004, -2), (key2271, -2), (key2295, -2), (key2325, -2), (key2337, -2), (key2004, 4), (key2273, 4), (key2295, 4)]

def rawRow17615 : Integer.Sparse Key := [(key1992, 4), (key2295, 4), (key2271, 4), (key1995, -2), (key1992, -2), (key2260, -2), (key2237, -2), (key2295, -2), (key2273, -2), (key2004, -2), (key2002, -2), (key2295, -2), (key2271, -2), (key2337, -2), (key2325, -2), (key2004, 4), (key2295, 4), (key2273, 4)]

def rawRow17616 : Integer.Sparse Key := [(key2271, 4), (key1992, 4), (key2295, 4), (key2237, -2), (key2273, -2), (key1992, -2), (key2295, -2), (key1995, -2), (key2260, -2), (key2271, -2), (key2325, -2), (key2002, -2), (key2337, -2), (key2004, -2), (key2295, -2), (key2273, 4), (key2004, 4), (key2295, 4)]

def rawRow17617 : Integer.Sparse Key := [(key2271, 4), (key2295, 4), (key1992, 4), (key2273, -2), (key2237, -2), (key2295, -2), (key1992, -2), (key2260, -2), (key1995, -2), (key2325, -2), (key2271, -2), (key2337, -2), (key2002, -2), (key2295, -2), (key2004, -2), (key2273, 4), (key2295, 4), (key2004, 4)]

def rawRow17618 : Integer.Sparse Key := [(key2295, 4), (key1992, 4), (key2271, 4), (key2260, -2), (key2295, -2), (key1995, -2), (key2273, -2), (key1992, -2), (key2237, -2), (key2295, -2), (key2337, -2), (key2004, -2), (key2325, -2), (key2002, -2), (key2271, -2), (key2295, 4), (key2004, 4), (key2273, 4)]

def rawRow17619 : Integer.Sparse Key := [(key2295, 4), (key2271, 4), (key1992, 4), (key2295, -2), (key2260, -2), (key2273, -2), (key1995, -2), (key2237, -2), (key1992, -2), (key2337, -2), (key2295, -2), (key2325, -2), (key2004, -2), (key2271, -2), (key2002, -2), (key2295, 4), (key2273, 4), (key2004, 4)]

def rawRow17620 : Integer.Sparse Key := [(key1992, 4), (key2271, 4), (key2295, 4), (key2002, -2), (key2004, -2), (key2271, -2), (key2295, -2), (key2325, -2), (key2337, -2), (key1992, -2), (key1995, -2), (key2237, -2), (key2260, -2), (key2273, -2), (key2295, -2), (key2004, 4), (key2273, 4), (key2295, 4)]

def rawRow17621 : Integer.Sparse Key := [(key1992, 4), (key2295, 4), (key2271, 4), (key2004, -2), (key2002, -2), (key2295, -2), (key2271, -2), (key2337, -2), (key2325, -2), (key1995, -2), (key1992, -2), (key2260, -2), (key2237, -2), (key2295, -2), (key2273, -2), (key2004, 4), (key2295, 4), (key2273, 4)]

def rawRow17622 : Integer.Sparse Key := [(key2271, 4), (key1992, 4), (key2295, 4), (key2271, -2), (key2325, -2), (key2002, -2), (key2337, -2), (key2004, -2), (key2295, -2), (key2237, -2), (key2273, -2), (key1992, -2), (key2295, -2), (key1995, -2), (key2260, -2), (key2273, 4), (key2004, 4), (key2295, 4)]

def rawRow17623 : Integer.Sparse Key := [(key2271, 4), (key2295, 4), (key1992, 4), (key2325, -2), (key2271, -2), (key2337, -2), (key2002, -2), (key2295, -2), (key2004, -2), (key2273, -2), (key2237, -2), (key2295, -2), (key1992, -2), (key2260, -2), (key1995, -2), (key2273, 4), (key2295, 4), (key2004, 4)]

def rawRow17624 : Integer.Sparse Key := [(key2295, 4), (key1992, 4), (key2271, 4), (key2295, -2), (key2337, -2), (key2004, -2), (key2325, -2), (key2002, -2), (key2271, -2), (key2260, -2), (key2295, -2), (key1995, -2), (key2273, -2), (key1992, -2), (key2237, -2), (key2295, 4), (key2004, 4), (key2273, 4)]

def rawRow17625 : Integer.Sparse Key := [(key2295, 4), (key2271, 4), (key1992, 4), (key2337, -2), (key2295, -2), (key2325, -2), (key2004, -2), (key2271, -2), (key2002, -2), (key2295, -2), (key2260, -2), (key2273, -2), (key1995, -2), (key2237, -2), (key1992, -2), (key2295, 4), (key2273, 4), (key2004, 4)]

def rawRow17626 : Integer.Sparse Key := [(key2002, 4), (key2002, 4), (key2337, 4), (key1992, -2), (key2004, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key2295, -2), (key1992, -2), (key2004, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key2295, -2), (key1995, 4), (key1995, 4), (key2260, 4)]

def rawRow17627 : Integer.Sparse Key := [(key2002, 4), (key2337, 4), (key2002, 4), (key2004, -2), (key1992, -2), (key2295, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key2004, -2), (key1992, -2), (key2295, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key1995, 4), (key2260, 4), (key1995, 4)]

def rawRow17628 : Integer.Sparse Key := [(key2337, 4), (key2002, 4), (key2002, 4), (key2295, -2), (key2295, -2), (key2004, -2), (key2004, -2), (key1992, -2), (key1992, -2), (key2295, -2), (key2295, -2), (key2004, -2), (key2004, -2), (key1992, -2), (key1992, -2), (key2260, 4), (key1995, 4), (key1995, 4)]

def rawRow17629 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key62, -2), (key72, 6), (key704, -2), (key709, -2), (key709, -2), (key858, 2), (key863, 2), (key858, 2), (key885, 2), (key863, 2), (key885, 2), (key923, -2), (key923, -2), (key940, -2), (key723, 6), (key923, -2), (key923, -2), (key940, -2)]

def rawRow17630 : Integer.Sparse Key := [(key62, -2), (key60, -2), (key62, -2), (key72, 6), (key709, -2), (key704, -2), (key709, -2), (key863, 2), (key858, 2), (key885, 2), (key858, 2), (key885, 2), (key863, 2), (key923, -2), (key940, -2), (key923, -2), (key723, 6), (key923, -2), (key940, -2), (key923, -2)]

def rawRow17631 : Integer.Sparse Key := [(key62, -2), (key62, -2), (key60, -2), (key72, 6), (key709, -2), (key709, -2), (key704, -2), (key885, 2), (key885, 2), (key863, 2), (key863, 2), (key858, 2), (key858, 2), (key940, -2), (key923, -2), (key923, -2), (key723, 6), (key940, -2), (key923, -2), (key923, -2)]

def rawRow17632 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key62, 6), (key858, -2), (key863, -2), (key923, -2), (key704, 2), (key709, 2), (key858, 2), (key885, 2), (key923, 2), (key940, 2), (key709, -2), (key863, -2), (key885, -2), (key923, 6), (key723, -2), (key923, -2), (key940, -2)]

def rawRow17633 : Integer.Sparse Key := [(key62, -2), (key60, -2), (key72, -2), (key62, 6), (key863, -2), (key858, -2), (key923, -2), (key709, 2), (key704, 2), (key885, 2), (key858, 2), (key940, 2), (key923, 2), (key709, -2), (key885, -2), (key863, -2), (key923, 6), (key723, -2), (key940, -2), (key923, -2)]

def rawRow17634 : Integer.Sparse Key := [(key60, -2), (key72, -2), (key62, -2), (key62, 6), (key858, -2), (key923, -2), (key863, -2), (key858, 2), (key923, 2), (key704, 2), (key940, 2), (key709, 2), (key885, 2), (key863, -2), (key709, -2), (key885, -2), (key923, 6), (key923, -2), (key723, -2), (key940, -2)]

def rawRow17635 : Integer.Sparse Key := [(key72, -2), (key60, -2), (key62, -2), (key62, 6), (key923, -2), (key858, -2), (key863, -2), (key923, 2), (key858, 2), (key940, 2), (key704, 2), (key885, 2), (key709, 2), (key863, -2), (key885, -2), (key709, -2), (key923, 6), (key923, -2), (key940, -2), (key723, -2)]

def rawRow17636 : Integer.Sparse Key := [(key62, -2), (key72, -2), (key60, -2), (key62, 6), (key863, -2), (key923, -2), (key858, -2), (key885, 2), (key940, 2), (key709, 2), (key923, 2), (key704, 2), (key858, 2), (key885, -2), (key709, -2), (key863, -2), (key923, 6), (key940, -2), (key723, -2), (key923, -2)]

def rawRow17637 : Integer.Sparse Key := [(key72, -2), (key62, -2), (key60, -2), (key62, 6), (key923, -2), (key863, -2), (key858, -2), (key940, 2), (key885, 2), (key923, 2), (key709, 2), (key858, 2), (key704, 2), (key885, -2), (key863, -2), (key709, -2), (key923, 6), (key940, -2), (key923, -2), (key723, -2)]

def rawRow17638 : Integer.Sparse Key := [(key125, -2), (key127, -2), (key135, -2), (key135, 6), (key60, -2), (key62, -2), (key72, -2), (key704, 2), (key709, 2), (key858, 2), (key885, 2), (key923, 2), (key940, 2), (key723, -2), (key923, -2), (key940, -2), (key709, 6), (key709, -2), (key863, -2), (key885, -2)]

def rawRow17639 : Integer.Sparse Key := [(key127, -2), (key125, -2), (key135, -2), (key135, 6), (key62, -2), (key60, -2), (key72, -2), (key709, 2), (key704, 2), (key885, 2), (key858, 2), (key940, 2), (key923, 2), (key723, -2), (key940, -2), (key923, -2), (key709, 6), (key709, -2), (key885, -2), (key863, -2)]

def rawRow17640 : Integer.Sparse Key := [(key125, -2), (key135, -2), (key127, -2), (key135, 6), (key60, -2), (key72, -2), (key62, -2), (key858, 2), (key923, 2), (key704, 2), (key940, 2), (key709, 2), (key885, 2), (key923, -2), (key723, -2), (key940, -2), (key709, 6), (key863, -2), (key709, -2), (key885, -2)]

def rawRow17641 : Integer.Sparse Key := [(key135, -2), (key125, -2), (key127, -2), (key135, 6), (key72, -2), (key60, -2), (key62, -2), (key923, 2), (key858, 2), (key940, 2), (key704, 2), (key885, 2), (key709, 2), (key923, -2), (key940, -2), (key723, -2), (key709, 6), (key863, -2), (key885, -2), (key709, -2)]

def rawRow17642 : Integer.Sparse Key := [(key127, -2), (key135, -2), (key125, -2), (key135, 6), (key62, -2), (key72, -2), (key60, -2), (key885, 2), (key940, 2), (key709, 2), (key923, 2), (key704, 2), (key858, 2), (key940, -2), (key723, -2), (key923, -2), (key709, 6), (key885, -2), (key709, -2), (key863, -2)]

def rawRow17643 : Integer.Sparse Key := [(key135, -2), (key127, -2), (key125, -2), (key135, 6), (key72, -2), (key62, -2), (key60, -2), (key940, 2), (key885, 2), (key923, 2), (key709, 2), (key858, 2), (key704, 2), (key940, -2), (key923, -2), (key723, -2), (key709, 6), (key885, -2), (key863, -2), (key709, -2)]

def rawRow17644 : Integer.Sparse Key := [(key125, -2), (key135, -2), (key135, -2), (key127, 6), (key125, -2), (key135, -2), (key135, -2), (key60, 2), (key72, 2), (key704, 2), (key940, 2), (key723, 2), (key940, 2), (key709, -2), (key709, -2), (key885, -2), (key863, 6), (key709, -2), (key709, -2), (key885, -2)]

def rawRow17645 : Integer.Sparse Key := [(key135, -2), (key125, -2), (key135, -2), (key127, 6), (key135, -2), (key125, -2), (key135, -2), (key72, 2), (key60, 2), (key940, 2), (key704, 2), (key940, 2), (key723, 2), (key709, -2), (key885, -2), (key709, -2), (key863, 6), (key709, -2), (key885, -2), (key709, -2)]

def rawRow17646 : Integer.Sparse Key := [(key135, -2), (key135, -2), (key125, -2), (key127, 6), (key135, -2), (key135, -2), (key125, -2), (key180, 2), (key180, 2), (key72, 2), (key72, 2), (key704, 2), (key704, 2), (key885, -2), (key709, -2), (key709, -2), (key863, 6), (key885, -2), (key709, -2), (key709, -2)]

def rawRow17647 : Integer.Sparse Key := [(key1988, -2), (key1993, -2), (key1993, -2), (key2008, 6), (key1988, -2), (key1993, -2), (key1993, -2), (key2233, 2), (key2238, 2), (key2233, 2), (key2258, 2), (key2238, 2), (key2258, 2), (key2301, -2), (key2301, -2), (key2314, -2), (key2008, 6), (key2301, -2), (key2301, -2), (key2314, -2)]

def rawRow17648 : Integer.Sparse Key := [(key1993, -2), (key1988, -2), (key1993, -2), (key2008, 6), (key1993, -2), (key1988, -2), (key1993, -2), (key2238, 2), (key2233, 2), (key2258, 2), (key2233, 2), (key2258, 2), (key2238, 2), (key2301, -2), (key2314, -2), (key2301, -2), (key2008, 6), (key2301, -2), (key2314, -2), (key2301, -2)]

def rawRow17649 : Integer.Sparse Key := [(key1993, -2), (key1993, -2), (key1988, -2), (key2008, 6), (key1993, -2), (key1993, -2), (key1988, -2), (key2258, 2), (key2258, 2), (key2238, 2), (key2238, 2), (key2233, 2), (key2233, 2), (key2314, -2), (key2301, -2), (key2301, -2), (key2008, 6), (key2314, -2), (key2301, -2), (key2301, -2)]

def rawRow17650 : Integer.Sparse Key := [(key1988, -2), (key1993, -2), (key2008, -2), (key1993, 6), (key2233, -2), (key2238, -2), (key2301, -2), (key1988, 2), (key1993, 2), (key2233, 2), (key2258, 2), (key2301, 2), (key2314, 2), (key1993, -2), (key2238, -2), (key2258, -2), (key2301, 6), (key2008, -2), (key2301, -2), (key2314, -2)]

def rawRow17651 : Integer.Sparse Key := [(key1993, -2), (key1988, -2), (key2008, -2), (key1993, 6), (key2238, -2), (key2233, -2), (key2301, -2), (key1993, 2), (key1988, 2), (key2258, 2), (key2233, 2), (key2314, 2), (key2301, 2), (key1993, -2), (key2258, -2), (key2238, -2), (key2301, 6), (key2008, -2), (key2314, -2), (key2301, -2)]

def rawRow17652 : Integer.Sparse Key := [(key1988, -2), (key2008, -2), (key1993, -2), (key1993, 6), (key2233, -2), (key2301, -2), (key2238, -2), (key2233, 2), (key2301, 2), (key1988, 2), (key2314, 2), (key1993, 2), (key2258, 2), (key2238, -2), (key1993, -2), (key2258, -2), (key2301, 6), (key2301, -2), (key2008, -2), (key2314, -2)]

def rawRow17653 : Integer.Sparse Key := [(key2008, -2), (key1988, -2), (key1993, -2), (key1993, 6), (key2301, -2), (key2233, -2), (key2238, -2), (key2301, 2), (key2233, 2), (key2314, 2), (key1988, 2), (key2258, 2), (key1993, 2), (key2238, -2), (key2258, -2), (key1993, -2), (key2301, 6), (key2301, -2), (key2314, -2), (key2008, -2)]

def rawRow17654 : Integer.Sparse Key := [(key1993, -2), (key2008, -2), (key1988, -2), (key1993, 6), (key2238, -2), (key2301, -2), (key2233, -2), (key2258, 2), (key2314, 2), (key1993, 2), (key2301, 2), (key1988, 2), (key2233, 2), (key2258, -2), (key1993, -2), (key2238, -2), (key2301, 6), (key2314, -2), (key2008, -2), (key2301, -2)]

def rawRow17655 : Integer.Sparse Key := [(key2008, -2), (key1993, -2), (key1988, -2), (key1993, 6), (key2301, -2), (key2238, -2), (key2233, -2), (key2314, 2), (key2258, 2), (key2301, 2), (key1993, 2), (key2233, 2), (key1988, 2), (key2258, -2), (key2238, -2), (key1993, -2), (key2301, 6), (key2314, -2), (key2301, -2), (key2008, -2)]

def rawRow17656 : Integer.Sparse Key := [(key2233, -2), (key2238, -2), (key2301, -2), (key2301, 6), (key1988, -2), (key1993, -2), (key2008, -2), (key1988, 2), (key1993, 2), (key2233, 2), (key2258, 2), (key2301, 2), (key2314, 2), (key2008, -2), (key2301, -2), (key2314, -2), (key1993, 6), (key1993, -2), (key2238, -2), (key2258, -2)]

def rawRow17657 : Integer.Sparse Key := [(key2238, -2), (key2233, -2), (key2301, -2), (key2301, 6), (key1993, -2), (key1988, -2), (key2008, -2), (key1993, 2), (key1988, 2), (key2258, 2), (key2233, 2), (key2314, 2), (key2301, 2), (key2008, -2), (key2314, -2), (key2301, -2), (key1993, 6), (key1993, -2), (key2258, -2), (key2238, -2)]

def rawRow17658 : Integer.Sparse Key := [(key2233, -2), (key2301, -2), (key2238, -2), (key2301, 6), (key1988, -2), (key2008, -2), (key1993, -2), (key2233, 2), (key2301, 2), (key1988, 2), (key2314, 2), (key1993, 2), (key2258, 2), (key2301, -2), (key2008, -2), (key2314, -2), (key1993, 6), (key2238, -2), (key1993, -2), (key2258, -2)]

def rawRow17659 : Integer.Sparse Key := [(key2301, -2), (key2233, -2), (key2238, -2), (key2301, 6), (key2008, -2), (key1988, -2), (key1993, -2), (key2301, 2), (key2233, 2), (key2314, 2), (key1988, 2), (key2258, 2), (key1993, 2), (key2301, -2), (key2314, -2), (key2008, -2), (key1993, 6), (key2238, -2), (key2258, -2), (key1993, -2)]

def rawRow17660 : Integer.Sparse Key := [(key2238, -2), (key2301, -2), (key2233, -2), (key2301, 6), (key1993, -2), (key2008, -2), (key1988, -2), (key2258, 2), (key2314, 2), (key1993, 2), (key2301, 2), (key1988, 2), (key2233, 2), (key2314, -2), (key2008, -2), (key2301, -2), (key1993, 6), (key2258, -2), (key1993, -2), (key2238, -2)]

def rawRow17661 : Integer.Sparse Key := [(key2301, -2), (key2238, -2), (key2233, -2), (key2301, 6), (key2008, -2), (key1993, -2), (key1988, -2), (key2314, 2), (key2258, 2), (key2301, 2), (key1993, 2), (key2233, 2), (key1988, 2), (key2314, -2), (key2301, -2), (key2008, -2), (key1993, 6), (key2258, -2), (key2238, -2), (key1993, -2)]

def rawRow17662 : Integer.Sparse Key := [(key2233, -2), (key2301, -2), (key2301, -2), (key2238, 6), (key2233, -2), (key2301, -2), (key2301, -2), (key1988, 2), (key2008, 2), (key1988, 2), (key2314, 2), (key2008, 2), (key2314, 2), (key1993, -2), (key1993, -2), (key2258, -2), (key2238, 6), (key1993, -2), (key1993, -2), (key2258, -2)]

def rawRow17663 : Integer.Sparse Key := [(key2301, -2), (key2233, -2), (key2301, -2), (key2238, 6), (key2301, -2), (key2233, -2), (key2301, -2), (key2008, 2), (key1988, 2), (key2314, 2), (key1988, 2), (key2314, 2), (key2008, 2), (key1993, -2), (key2258, -2), (key1993, -2), (key2238, 6), (key1993, -2), (key2258, -2), (key1993, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17664 : Integer.Sparse Key := [(key2301, -2), (key2301, -2), (key2233, -2), (key2238, 6), (key2301, -2), (key2301, -2), (key2233, -2), (key2314, 2), (key2314, 2), (key2008, 2), (key2008, 2), (key1988, 2), (key1988, 2), (key2258, -2), (key1993, -2), (key1993, -2), (key2238, 6), (key2258, -2), (key1993, -2), (key1993, -2)]

def rawRow17665 : Integer.Sparse Key := [(key2030, 6), (key2060, -2), (key2060, -2), (key2068, -2), (key2030, 6), (key2149, -2), (key2149, -2), (key2165, -2), (key2060, -2), (key2060, -2), (key2068, -2), (key2149, -2), (key2149, -2), (key2165, -2), (key2242, 2), (key2245, 2), (key2242, 2), (key2252, 2), (key2245, 2), (key2252, 2)]

def rawRow17666 : Integer.Sparse Key := [(key2030, 6), (key2060, -2), (key2068, -2), (key2060, -2), (key2030, 6), (key2149, -2), (key2165, -2), (key2149, -2), (key2060, -2), (key2068, -2), (key2060, -2), (key2149, -2), (key2165, -2), (key2149, -2), (key2245, 2), (key2242, 2), (key2252, 2), (key2242, 2), (key2252, 2), (key2245, 2)]

def rawRow17667 : Integer.Sparse Key := [(key2030, 6), (key2068, -2), (key2060, -2), (key2060, -2), (key2030, 6), (key2165, -2), (key2149, -2), (key2149, -2), (key2068, -2), (key2060, -2), (key2060, -2), (key2165, -2), (key2149, -2), (key2149, -2), (key2252, 2), (key2252, 2), (key2245, 2), (key2245, 2), (key2242, 2), (key2242, 2)]

def rawRow17668 : Integer.Sparse Key := [(key2060, 6), (key2030, -2), (key2060, -2), (key2068, -2), (key2149, 6), (key2030, -2), (key2149, -2), (key2165, -2), (key2149, -2), (key2242, -2), (key2245, -2), (key2060, -2), (key2242, -2), (key2252, -2), (key2060, 2), (key2068, 2), (key2149, 2), (key2165, 2), (key2245, 2), (key2252, 2)]

def rawRow17669 : Integer.Sparse Key := [(key2060, 6), (key2030, -2), (key2068, -2), (key2060, -2), (key2149, 6), (key2030, -2), (key2165, -2), (key2149, -2), (key2149, -2), (key2245, -2), (key2242, -2), (key2060, -2), (key2252, -2), (key2242, -2), (key2068, 2), (key2060, 2), (key2165, 2), (key2149, 2), (key2252, 2), (key2245, 2)]

def rawRow17670 : Integer.Sparse Key := [(key2060, 6), (key2060, -2), (key2030, -2), (key2068, -2), (key2149, 6), (key2149, -2), (key2030, -2), (key2165, -2), (key2242, -2), (key2149, -2), (key2245, -2), (key2242, -2), (key2060, -2), (key2252, -2), (key2149, 2), (key2245, 2), (key2060, 2), (key2252, 2), (key2068, 2), (key2165, 2)]

def rawRow17671 : Integer.Sparse Key := [(key2060, 6), (key2060, -2), (key2068, -2), (key2030, -2), (key2149, 6), (key2149, -2), (key2165, -2), (key2030, -2), (key2242, -2), (key2245, -2), (key2149, -2), (key2242, -2), (key2252, -2), (key2060, -2), (key2245, 2), (key2149, 2), (key2252, 2), (key2060, 2), (key2165, 2), (key2068, 2)]

def rawRow17672 : Integer.Sparse Key := [(key2060, 6), (key2068, -2), (key2030, -2), (key2060, -2), (key2149, 6), (key2165, -2), (key2030, -2), (key2149, -2), (key2245, -2), (key2149, -2), (key2242, -2), (key2252, -2), (key2060, -2), (key2242, -2), (key2165, 2), (key2252, 2), (key2068, 2), (key2245, 2), (key2060, 2), (key2149, 2)]

def rawRow17673 : Integer.Sparse Key := [(key2060, 6), (key2068, -2), (key2060, -2), (key2030, -2), (key2149, 6), (key2165, -2), (key2149, -2), (key2030, -2), (key2245, -2), (key2242, -2), (key2149, -2), (key2252, -2), (key2242, -2), (key2060, -2), (key2252, 2), (key2165, 2), (key2245, 2), (key2068, 2), (key2149, 2), (key2060, 2)]

def rawRow17674 : Integer.Sparse Key := [(key2149, 6), (key2149, -2), (key2242, -2), (key2245, -2), (key2060, 6), (key2060, -2), (key2242, -2), (key2252, -2), (key2030, -2), (key2060, -2), (key2068, -2), (key2030, -2), (key2149, -2), (key2165, -2), (key2060, 2), (key2068, 2), (key2149, 2), (key2165, 2), (key2245, 2), (key2252, 2)]

def rawRow17675 : Integer.Sparse Key := [(key2149, 6), (key2149, -2), (key2245, -2), (key2242, -2), (key2060, 6), (key2060, -2), (key2252, -2), (key2242, -2), (key2030, -2), (key2068, -2), (key2060, -2), (key2030, -2), (key2165, -2), (key2149, -2), (key2068, 2), (key2060, 2), (key2165, 2), (key2149, 2), (key2252, 2), (key2245, 2)]

def rawRow17676 : Integer.Sparse Key := [(key2149, 6), (key2242, -2), (key2149, -2), (key2245, -2), (key2060, 6), (key2242, -2), (key2060, -2), (key2252, -2), (key2060, -2), (key2030, -2), (key2068, -2), (key2149, -2), (key2030, -2), (key2165, -2), (key2149, 2), (key2245, 2), (key2060, 2), (key2252, 2), (key2068, 2), (key2165, 2)]

def rawRow17677 : Integer.Sparse Key := [(key2149, 6), (key2242, -2), (key2245, -2), (key2149, -2), (key2060, 6), (key2242, -2), (key2252, -2), (key2060, -2), (key2060, -2), (key2068, -2), (key2030, -2), (key2149, -2), (key2165, -2), (key2030, -2), (key2245, 2), (key2149, 2), (key2252, 2), (key2060, 2), (key2165, 2), (key2068, 2)]

def rawRow17678 : Integer.Sparse Key := [(key2149, 6), (key2245, -2), (key2149, -2), (key2242, -2), (key2060, 6), (key2252, -2), (key2060, -2), (key2242, -2), (key2068, -2), (key2030, -2), (key2060, -2), (key2165, -2), (key2030, -2), (key2149, -2), (key2165, 2), (key2252, 2), (key2068, 2), (key2245, 2), (key2060, 2), (key2149, 2)]

def rawRow17679 : Integer.Sparse Key := [(key2149, 6), (key2245, -2), (key2242, -2), (key2149, -2), (key2060, 6), (key2252, -2), (key2242, -2), (key2060, -2), (key2068, -2), (key2060, -2), (key2030, -2), (key2165, -2), (key2149, -2), (key2030, -2), (key2252, 2), (key2165, 2), (key2245, 2), (key2068, 2), (key2149, 2), (key2060, 2)]

def rawRow17680 : Integer.Sparse Key := [(key2242, 6), (key2149, -2), (key2149, -2), (key2245, -2), (key2242, 6), (key2060, -2), (key2060, -2), (key2252, -2), (key2149, -2), (key2149, -2), (key2245, -2), (key2060, -2), (key2060, -2), (key2252, -2), (key2030, 2), (key2068, 2), (key2030, 2), (key2165, 2), (key2068, 2), (key2165, 2)]

def rawRow17681 : Integer.Sparse Key := [(key2242, 6), (key2149, -2), (key2245, -2), (key2149, -2), (key2242, 6), (key2060, -2), (key2252, -2), (key2060, -2), (key2149, -2), (key2245, -2), (key2149, -2), (key2060, -2), (key2252, -2), (key2060, -2), (key2068, 2), (key2030, 2), (key2165, 2), (key2030, 2), (key2165, 2), (key2068, 2)]

def rawRow17682 : Integer.Sparse Key := [(key2242, 6), (key2245, -2), (key2149, -2), (key2149, -2), (key2242, 6), (key2252, -2), (key2060, -2), (key2060, -2), (key2245, -2), (key2149, -2), (key2149, -2), (key2252, -2), (key2060, -2), (key2060, -2), (key2165, 2), (key2165, 2), (key2068, 2), (key2068, 2), (key2030, 2), (key2030, 2)]

def rawRow17683 : Integer.Sparse Key := [(key704, -2), (key707, -2), (key707, -2), (key716, 6), (key704, -2), (key707, -2), (key707, -2), (key858, 2), (key861, 2), (key858, 2), (key884, 2), (key861, 2), (key884, 2), (key893, -2), (key893, -2), (key915, -2), (key716, 6), (key893, -2), (key893, -2), (key915, -2)]

def rawRow17684 : Integer.Sparse Key := [(key707, -2), (key704, -2), (key707, -2), (key716, 6), (key707, -2), (key704, -2), (key707, -2), (key861, 2), (key858, 2), (key884, 2), (key858, 2), (key884, 2), (key861, 2), (key893, -2), (key915, -2), (key893, -2), (key716, 6), (key893, -2), (key915, -2), (key893, -2)]

def rawRow17685 : Integer.Sparse Key := [(key707, -2), (key707, -2), (key704, -2), (key716, 6), (key707, -2), (key707, -2), (key704, -2), (key884, 2), (key884, 2), (key861, 2), (key861, 2), (key858, 2), (key858, 2), (key915, -2), (key893, -2), (key893, -2), (key716, 6), (key915, -2), (key893, -2), (key893, -2)]

def rawRow17686 : Integer.Sparse Key := [(key704, -2), (key707, -2), (key716, -2), (key707, 6), (key858, -2), (key861, -2), (key893, -2), (key704, 2), (key707, 2), (key858, 2), (key884, 2), (key893, 2), (key915, 2), (key707, -2), (key861, -2), (key884, -2), (key893, 6), (key716, -2), (key893, -2), (key915, -2)]

def rawRow17687 : Integer.Sparse Key := [(key707, -2), (key704, -2), (key716, -2), (key707, 6), (key861, -2), (key858, -2), (key893, -2), (key707, 2), (key704, 2), (key884, 2), (key858, 2), (key915, 2), (key893, 2), (key707, -2), (key884, -2), (key861, -2), (key893, 6), (key716, -2), (key915, -2), (key893, -2)]

def rawRow17688 : Integer.Sparse Key := [(key704, -2), (key716, -2), (key707, -2), (key707, 6), (key858, -2), (key893, -2), (key861, -2), (key858, 2), (key893, 2), (key704, 2), (key915, 2), (key707, 2), (key884, 2), (key861, -2), (key707, -2), (key884, -2), (key893, 6), (key893, -2), (key716, -2), (key915, -2)]

def rawRow17689 : Integer.Sparse Key := [(key716, -2), (key704, -2), (key707, -2), (key707, 6), (key893, -2), (key858, -2), (key861, -2), (key893, 2), (key858, 2), (key915, 2), (key704, 2), (key884, 2), (key707, 2), (key861, -2), (key884, -2), (key707, -2), (key893, 6), (key893, -2), (key915, -2), (key716, -2)]

def rawRow17690 : Integer.Sparse Key := [(key707, -2), (key716, -2), (key704, -2), (key707, 6), (key861, -2), (key893, -2), (key858, -2), (key884, 2), (key915, 2), (key707, 2), (key893, 2), (key704, 2), (key858, 2), (key884, -2), (key707, -2), (key861, -2), (key893, 6), (key915, -2), (key716, -2), (key893, -2)]

def rawRow17691 : Integer.Sparse Key := [(key716, -2), (key707, -2), (key704, -2), (key707, 6), (key893, -2), (key861, -2), (key858, -2), (key915, 2), (key884, 2), (key893, 2), (key707, 2), (key858, 2), (key704, 2), (key884, -2), (key861, -2), (key707, -2), (key893, 6), (key915, -2), (key893, -2), (key716, -2)]

def rawRow17692 : Integer.Sparse Key := [(key858, -2), (key861, -2), (key893, -2), (key893, 6), (key704, -2), (key707, -2), (key716, -2), (key704, 2), (key707, 2), (key858, 2), (key884, 2), (key893, 2), (key915, 2), (key716, -2), (key893, -2), (key915, -2), (key707, 6), (key707, -2), (key861, -2), (key884, -2)]

def rawRow17693 : Integer.Sparse Key := [(key861, -2), (key858, -2), (key893, -2), (key893, 6), (key707, -2), (key704, -2), (key716, -2), (key707, 2), (key704, 2), (key884, 2), (key858, 2), (key915, 2), (key893, 2), (key716, -2), (key915, -2), (key893, -2), (key707, 6), (key707, -2), (key884, -2), (key861, -2)]

def rawRow17694 : Integer.Sparse Key := [(key858, -2), (key893, -2), (key861, -2), (key893, 6), (key704, -2), (key716, -2), (key707, -2), (key858, 2), (key893, 2), (key704, 2), (key915, 2), (key707, 2), (key884, 2), (key893, -2), (key716, -2), (key915, -2), (key707, 6), (key861, -2), (key707, -2), (key884, -2)]

def rawRow17695 : Integer.Sparse Key := [(key893, -2), (key858, -2), (key861, -2), (key893, 6), (key716, -2), (key704, -2), (key707, -2), (key893, 2), (key858, 2), (key915, 2), (key704, 2), (key884, 2), (key707, 2), (key893, -2), (key915, -2), (key716, -2), (key707, 6), (key861, -2), (key884, -2), (key707, -2)]

def rawRow17696 : Integer.Sparse Key := [(key861, -2), (key893, -2), (key858, -2), (key893, 6), (key707, -2), (key716, -2), (key704, -2), (key884, 2), (key915, 2), (key707, 2), (key893, 2), (key704, 2), (key858, 2), (key915, -2), (key716, -2), (key893, -2), (key707, 6), (key884, -2), (key707, -2), (key861, -2)]

def rawRow17697 : Integer.Sparse Key := [(key893, -2), (key861, -2), (key858, -2), (key893, 6), (key716, -2), (key707, -2), (key704, -2), (key915, 2), (key884, 2), (key893, 2), (key707, 2), (key858, 2), (key704, 2), (key915, -2), (key893, -2), (key716, -2), (key707, 6), (key884, -2), (key861, -2), (key707, -2)]

def rawRow17698 : Integer.Sparse Key := [(key858, -2), (key893, -2), (key893, -2), (key861, 6), (key858, -2), (key893, -2), (key893, -2), (key704, 2), (key716, 2), (key704, 2), (key915, 2), (key716, 2), (key915, 2), (key707, -2), (key707, -2), (key884, -2), (key861, 6), (key707, -2), (key707, -2), (key884, -2)]

def rawRow17699 : Integer.Sparse Key := [(key893, -2), (key858, -2), (key893, -2), (key861, 6), (key893, -2), (key858, -2), (key893, -2), (key716, 2), (key704, 2), (key915, 2), (key704, 2), (key915, 2), (key716, 2), (key707, -2), (key884, -2), (key707, -2), (key861, 6), (key707, -2), (key884, -2), (key707, -2)]

def rawRow17700 : Integer.Sparse Key := [(key893, -2), (key893, -2), (key858, -2), (key861, 6), (key893, -2), (key893, -2), (key858, -2), (key915, 2), (key915, 2), (key716, 2), (key716, 2), (key704, 2), (key704, 2), (key884, -2), (key707, -2), (key707, -2), (key861, 6), (key884, -2), (key707, -2), (key707, -2)]

def rawRow17701 : Integer.Sparse Key := [(key862, 4), (key862, 4), (key887, 4), (key894, -2), (key896, -2), (key894, -2), (key917, -2), (key896, -2), (key917, -2), (key894, -2), (key896, -2), (key894, -2), (key917, -2), (key896, -2), (key917, -2), (key949, 4), (key949, 4), (key956, 4)]

def rawRow17702 : Integer.Sparse Key := [(key862, 4), (key887, 4), (key862, 4), (key896, -2), (key894, -2), (key917, -2), (key894, -2), (key917, -2), (key896, -2), (key896, -2), (key894, -2), (key917, -2), (key894, -2), (key917, -2), (key896, -2), (key949, 4), (key956, 4), (key949, 4)]

def rawRow17703 : Integer.Sparse Key := [(key887, 4), (key862, 4), (key862, 4), (key917, -2), (key917, -2), (key896, -2), (key896, -2), (key894, -2), (key894, -2), (key917, -2), (key917, -2), (key896, -2), (key896, -2), (key894, -2), (key894, -2), (key956, 4), (key949, 4), (key949, 4)]

def rawRow17704 : Integer.Sparse Key := [(key708, 4), (key894, 4), (key917, 4), (key708, -2), (key711, -2), (key862, -2), (key887, -2), (key896, -2), (key917, -2), (key717, -2), (key719, -2), (key894, -2), (key917, -2), (key949, -2), (key956, -2), (key719, 4), (key896, 4), (key917, 4)]

def rawRow17705 : Integer.Sparse Key := [(key708, 4), (key917, 4), (key894, 4), (key711, -2), (key708, -2), (key887, -2), (key862, -2), (key917, -2), (key896, -2), (key719, -2), (key717, -2), (key917, -2), (key894, -2), (key956, -2), (key949, -2), (key719, 4), (key917, 4), (key896, 4)]

def rawRow17706 : Integer.Sparse Key := [(key894, 4), (key708, 4), (key917, 4), (key862, -2), (key896, -2), (key708, -2), (key917, -2), (key711, -2), (key887, -2), (key894, -2), (key949, -2), (key717, -2), (key956, -2), (key719, -2), (key917, -2), (key896, 4), (key719, 4), (key917, 4)]

def rawRow17707 : Integer.Sparse Key := [(key894, 4), (key917, 4), (key708, 4), (key896, -2), (key862, -2), (key917, -2), (key708, -2), (key887, -2), (key711, -2), (key949, -2), (key894, -2), (key956, -2), (key717, -2), (key917, -2), (key719, -2), (key896, 4), (key917, 4), (key719, 4)]

def rawRow17708 : Integer.Sparse Key := [(key917, 4), (key708, 4), (key894, 4), (key887, -2), (key917, -2), (key711, -2), (key896, -2), (key708, -2), (key862, -2), (key917, -2), (key956, -2), (key719, -2), (key949, -2), (key717, -2), (key894, -2), (key917, 4), (key719, 4), (key896, 4)]

def rawRow17709 : Integer.Sparse Key := [(key917, 4), (key894, 4), (key708, 4), (key917, -2), (key887, -2), (key896, -2), (key711, -2), (key862, -2), (key708, -2), (key956, -2), (key917, -2), (key949, -2), (key719, -2), (key894, -2), (key717, -2), (key917, 4), (key896, 4), (key719, 4)]

def rawRow17710 : Integer.Sparse Key := [(key708, 4), (key894, 4), (key917, 4), (key717, -2), (key719, -2), (key894, -2), (key917, -2), (key949, -2), (key956, -2), (key708, -2), (key711, -2), (key862, -2), (key887, -2), (key896, -2), (key917, -2), (key719, 4), (key896, 4), (key917, 4)]

def rawRow17711 : Integer.Sparse Key := [(key708, 4), (key917, 4), (key894, 4), (key719, -2), (key717, -2), (key917, -2), (key894, -2), (key956, -2), (key949, -2), (key711, -2), (key708, -2), (key887, -2), (key862, -2), (key917, -2), (key896, -2), (key719, 4), (key917, 4), (key896, 4)]

def rawRow17712 : Integer.Sparse Key := [(key894, 4), (key708, 4), (key917, 4), (key894, -2), (key949, -2), (key717, -2), (key956, -2), (key719, -2), (key917, -2), (key862, -2), (key896, -2), (key708, -2), (key917, -2), (key711, -2), (key887, -2), (key896, 4), (key719, 4), (key917, 4)]

def rawRow17713 : Integer.Sparse Key := [(key894, 4), (key917, 4), (key708, 4), (key949, -2), (key894, -2), (key956, -2), (key717, -2), (key917, -2), (key719, -2), (key896, -2), (key862, -2), (key917, -2), (key708, -2), (key887, -2), (key711, -2), (key896, 4), (key917, 4), (key719, 4)]

def rawRow17714 : Integer.Sparse Key := [(key917, 4), (key708, 4), (key894, 4), (key917, -2), (key956, -2), (key719, -2), (key949, -2), (key717, -2), (key894, -2), (key887, -2), (key917, -2), (key711, -2), (key896, -2), (key708, -2), (key862, -2), (key917, 4), (key719, 4), (key896, 4)]

def rawRow17715 : Integer.Sparse Key := [(key917, 4), (key894, 4), (key708, 4), (key956, -2), (key917, -2), (key949, -2), (key719, -2), (key894, -2), (key717, -2), (key917, -2), (key887, -2), (key896, -2), (key711, -2), (key862, -2), (key708, -2), (key917, 4), (key896, 4), (key719, 4)]

def rawRow17716 : Integer.Sparse Key := [(key78, 4), (key717, 4), (key956, 4), (key708, -2), (key719, -2), (key708, -2), (key917, -2), (key719, -2), (key917, -2), (key708, -2), (key719, -2), (key708, -2), (key917, -2), (key719, -2), (key917, -2), (key711, 4), (key711, 4), (key887, 4)]

def rawRow17717 : Integer.Sparse Key := [(key78, 4), (key956, 4), (key717, 4), (key719, -2), (key708, -2), (key917, -2), (key708, -2), (key917, -2), (key719, -2), (key719, -2), (key708, -2), (key917, -2), (key708, -2), (key917, -2), (key719, -2), (key711, 4), (key887, 4), (key711, 4)]

def rawRow17718 : Integer.Sparse Key := [(key191, 4), (key78, 4), (key717, 4), (key917, -2), (key917, -2), (key719, -2), (key719, -2), (key708, -2), (key708, -2), (key917, -2), (key917, -2), (key719, -2), (key719, -2), (key708, -2), (key708, -2), (key887, 4), (key711, 4), (key711, 4)]

def rawRow17719 : Integer.Sparse Key := [(key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2195, 2), (key2195, 2), (key2201, 2), (key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2243, 2), (key2248, 2), (key2243, 2), (key2255, 2), (key2248, 2), (key2255, 2), (key2304, -1), (key2306, -1), (key2304, -1), (key2311, -1), (key2306, -1), (key2311, -1), (key2195, 2), (key2195, 2), (key2201, 2), (key2304, -1), (key2306, -1), (key2304, -1), (key2311, -1), (key2306, -1), (key2311, -1)]

def rawRow17720 : Integer.Sparse Key := [(key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2195, 2), (key2201, 2), (key2195, 2), (key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2248, 2), (key2243, 2), (key2255, 2), (key2243, 2), (key2255, 2), (key2248, 2), (key2306, -1), (key2304, -1), (key2311, -1), (key2304, -1), (key2311, -1), (key2306, -1), (key2195, 2), (key2201, 2), (key2195, 2), (key2306, -1), (key2304, -1), (key2311, -1), (key2304, -1), (key2311, -1), (key2306, -1)]

def rawRow17721 : Integer.Sparse Key := [(key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2201, 2), (key2195, 2), (key2195, 2), (key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2255, 2), (key2255, 2), (key2248, 2), (key2248, 2), (key2243, 2), (key2243, 2), (key2311, -1), (key2311, -1), (key2306, -1), (key2306, -1), (key2304, -1), (key2304, -1), (key2201, 2), (key2195, 2), (key2195, 2), (key2311, -1), (key2311, -1), (key2306, -1), (key2306, -1), (key2304, -1), (key2304, -1)]

def rawRow17722 : Integer.Sparse Key := [(key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2036, 2), (key2155, 2), (key2168, 2), (key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2), (key2066, -1), (key2071, -1), (key2155, -1), (key2168, -1), (key2248, -1), (key2255, -1), (key2093, 2), (key2304, 2), (key2311, 2), (key2093, -1), (key2096, -1), (key2195, -1), (key2201, -1), (key2306, -1), (key2311, -1)]

def rawRow17723 : Integer.Sparse Key := [(key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2036, 2), (key2168, 2), (key2155, 2), (key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2), (key2071, -1), (key2066, -1), (key2168, -1), (key2155, -1), (key2255, -1), (key2248, -1), (key2093, 2), (key2311, 2), (key2304, 2), (key2096, -1), (key2093, -1), (key2201, -1), (key2195, -1), (key2311, -1), (key2306, -1)]

def rawRow17724 : Integer.Sparse Key := [(key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2155, 2), (key2036, 2), (key2168, 2), (key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2), (key2155, -1), (key2248, -1), (key2066, -1), (key2255, -1), (key2071, -1), (key2168, -1), (key2304, 2), (key2093, 2), (key2311, 2), (key2195, -1), (key2306, -1), (key2093, -1), (key2311, -1), (key2096, -1), (key2201, -1)]

def rawRow17725 : Integer.Sparse Key := [(key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2155, 2), (key2168, 2), (key2036, 2), (key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2), (key2248, -1), (key2155, -1), (key2255, -1), (key2066, -1), (key2168, -1), (key2071, -1), (key2304, 2), (key2311, 2), (key2093, 2), (key2306, -1), (key2195, -1), (key2311, -1), (key2093, -1), (key2201, -1), (key2096, -1)]

def rawRow17726 : Integer.Sparse Key := [(key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2168, 2), (key2036, 2), (key2155, 2), (key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2), (key2168, -1), (key2255, -1), (key2071, -1), (key2248, -1), (key2066, -1), (key2155, -1), (key2311, 2), (key2093, 2), (key2304, 2), (key2201, -1), (key2311, -1), (key2096, -1), (key2306, -1), (key2093, -1), (key2195, -1)]

def rawRow17727 : Integer.Sparse Key := [(key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2168, 2), (key2155, 2), (key2036, 2), (key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2), (key2255, -1), (key2168, -1), (key2248, -1), (key2071, -1), (key2155, -1), (key2066, -1), (key2311, 2), (key2304, 2), (key2093, 2), (key2311, -1), (key2201, -1), (key2306, -1), (key2096, -1), (key2195, -1), (key2093, -1)]

def rawRow17728 : Integer.Sparse Key := [(key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2093, 2), (key2304, 2), (key2311, 2), (key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2), (key2093, -1), (key2096, -1), (key2195, -1), (key2201, -1), (key2306, -1), (key2311, -1), (key2036, 2), (key2155, 2), (key2168, 2), (key2066, -1), (key2071, -1), (key2155, -1), (key2168, -1), (key2248, -1), (key2255, -1)]

def rawRow17729 : Integer.Sparse Key := [(key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2093, 2), (key2311, 2), (key2304, 2), (key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2), (key2096, -1), (key2093, -1), (key2201, -1), (key2195, -1), (key2311, -1), (key2306, -1), (key2036, 2), (key2168, 2), (key2155, 2), (key2071, -1), (key2066, -1), (key2168, -1), (key2155, -1), (key2255, -1), (key2248, -1)]

def rawRow17730 : Integer.Sparse Key := [(key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2304, 2), (key2093, 2), (key2311, 2), (key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2), (key2195, -1), (key2306, -1), (key2093, -1), (key2311, -1), (key2096, -1), (key2201, -1), (key2155, 2), (key2036, 2), (key2168, 2), (key2155, -1), (key2248, -1), (key2066, -1), (key2255, -1), (key2071, -1), (key2168, -1)]

def rawRow17731 : Integer.Sparse Key := [(key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2304, 2), (key2311, 2), (key2093, 2), (key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2), (key2306, -1), (key2195, -1), (key2311, -1), (key2093, -1), (key2201, -1), (key2096, -1), (key2155, 2), (key2168, 2), (key2036, 2), (key2248, -1), (key2155, -1), (key2255, -1), (key2066, -1), (key2168, -1), (key2071, -1)]

def rawRow17732 : Integer.Sparse Key := [(key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2311, 2), (key2093, 2), (key2304, 2), (key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2), (key2201, -1), (key2311, -1), (key2096, -1), (key2306, -1), (key2093, -1), (key2195, -1), (key2168, 2), (key2036, 2), (key2155, 2), (key2168, -1), (key2255, -1), (key2071, -1), (key2248, -1), (key2066, -1), (key2155, -1)]

def rawRow17733 : Integer.Sparse Key := [(key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2311, 2), (key2304, 2), (key2093, 2), (key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2), (key2311, -1), (key2201, -1), (key2306, -1), (key2096, -1), (key2195, -1), (key2093, -1), (key2168, 2), (key2155, 2), (key2036, 2), (key2255, -1), (key2168, -1), (key2248, -1), (key2071, -1), (key2155, -1), (key2066, -1)]

def rawRow17734 : Integer.Sparse Key := [(key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2066, 2), (key2066, 2), (key2255, 2), (key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2031, 2), (key2096, 2), (key2031, 2), (key2201, 2), (key2096, 2), (key2201, 2), (key2036, -1), (key2071, -1), (key2036, -1), (key2168, -1), (key2071, -1), (key2168, -1), (key2066, 2), (key2066, 2), (key2255, 2), (key2036, -1), (key2071, -1), (key2036, -1), (key2168, -1), (key2071, -1), (key2168, -1)]

def rawRow17735 : Integer.Sparse Key := [(key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2066, 2), (key2255, 2), (key2066, 2), (key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2096, 2), (key2031, 2), (key2201, 2), (key2031, 2), (key2201, 2), (key2096, 2), (key2071, -1), (key2036, -1), (key2168, -1), (key2036, -1), (key2168, -1), (key2071, -1), (key2066, 2), (key2255, 2), (key2066, 2), (key2071, -1), (key2036, -1), (key2168, -1), (key2036, -1), (key2168, -1), (key2071, -1)]

def rawRow17736 : Integer.Sparse Key := [(key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2255, 2), (key2066, 2), (key2066, 2), (key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2201, 2), (key2201, 2), (key2096, 2), (key2096, 2), (key2031, 2), (key2031, 2), (key2168, -1), (key2168, -1), (key2071, -1), (key2071, -1), (key2036, -1), (key2036, -1), (key2255, 2), (key2066, 2), (key2066, 2), (key2168, -1), (key2168, -1), (key2071, -1), (key2071, -1), (key2036, -1), (key2036, -1)]

def rawRow17737 : Integer.Sparse Key := [(key2116, 4), (key2116, 4), (key2121, 4), (key2158, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2250, 12)]

def rawRow17738 : Integer.Sparse Key := [(key2116, 4), (key2121, 4), (key2116, 4), (key2161, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2250, 12)]

def rawRow17739 : Integer.Sparse Key := [(key2121, 4), (key2116, 4), (key2116, 4), (key2161, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2250, 12)]

def rawRow17740 : Integer.Sparse Key := [(key2116, 4), (key2158, 4), (key2161, 4), (key2116, -4), (key2121, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2250, -4), (key2161, 12)]

def rawRow17741 : Integer.Sparse Key := [(key2116, 4), (key2161, 4), (key2158, 4), (key2121, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2250, -4), (key2161, 12)]

def rawRow17742 : Integer.Sparse Key := [(key2158, 4), (key2116, 4), (key2161, 4), (key2116, -4), (key2161, -4), (key2121, -4), (key2158, -4), (key2250, -4), (key2161, -4), (key2161, 12)]

def rawRow17743 : Integer.Sparse Key := [(key2158, 4), (key2161, 4), (key2116, 4), (key2161, -4), (key2116, -4), (key2121, -4), (key2250, -4), (key2158, -4), (key2161, -4), (key2161, 12)]

def rawRow17744 : Integer.Sparse Key := [(key2161, 4), (key2116, 4), (key2158, 4), (key2121, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2250, -4), (key2158, -4), (key2161, 12)]

def rawRow17745 : Integer.Sparse Key := [(key2161, 4), (key2158, 4), (key2116, 4), (key2161, -4), (key2121, -4), (key2116, -4), (key2250, -4), (key2161, -4), (key2158, -4), (key2161, 12)]

def rawRow17746 : Integer.Sparse Key := [(key2116, 4), (key2158, 4), (key2161, 4), (key2158, -4), (key2161, -4), (key2250, -4), (key2116, -4), (key2121, -4), (key2161, -4), (key2161, 12)]

def rawRow17747 : Integer.Sparse Key := [(key2116, 4), (key2161, 4), (key2158, 4), (key2161, -4), (key2158, -4), (key2250, -4), (key2121, -4), (key2116, -4), (key2161, -4), (key2161, 12)]

def rawRow17748 : Integer.Sparse Key := [(key2158, 4), (key2116, 4), (key2161, 4), (key2158, -4), (key2250, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2121, -4), (key2161, 12)]

def rawRow17749 : Integer.Sparse Key := [(key2158, 4), (key2161, 4), (key2116, 4), (key2250, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2121, -4), (key2161, 12)]

def rawRow17750 : Integer.Sparse Key := [(key2161, 4), (key2116, 4), (key2158, 4), (key2161, -4), (key2250, -4), (key2158, -4), (key2121, -4), (key2161, -4), (key2116, -4), (key2161, 12)]

def rawRow17751 : Integer.Sparse Key := [(key2161, 4), (key2158, 4), (key2116, 4), (key2250, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2121, -4), (key2116, -4), (key2161, 12)]

def rawRow17752 : Integer.Sparse Key := [(key2158, 4), (key2158, 4), (key2250, 4), (key2116, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2121, 12)]

def rawRow17753 : Integer.Sparse Key := [(key2158, 4), (key2250, 4), (key2158, 4), (key2161, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2121, 12)]

def rawRow17754 : Integer.Sparse Key := [(key2250, 4), (key2158, 4), (key2158, 4), (key2161, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2121, 12)]

def rawRow17755 : Integer.Sparse Key := [(key1988, -2), (key1991, -2), (key1991, -2), (key2001, 6), (key1988, -2), (key1991, -2), (key1991, -2), (key2233, 2), (key2236, 2), (key2233, 2), (key2257, 2), (key2236, 2), (key2257, 2), (key2270, -2), (key2270, -2), (key2293, -2), (key2001, 6), (key2270, -2), (key2270, -2), (key2293, -2)]

def rawRow17756 : Integer.Sparse Key := [(key1991, -2), (key1988, -2), (key1991, -2), (key2001, 6), (key1991, -2), (key1988, -2), (key1991, -2), (key2236, 2), (key2233, 2), (key2257, 2), (key2233, 2), (key2257, 2), (key2236, 2), (key2270, -2), (key2293, -2), (key2270, -2), (key2001, 6), (key2270, -2), (key2293, -2), (key2270, -2)]

def rawRow17757 : Integer.Sparse Key := [(key1991, -2), (key1991, -2), (key1988, -2), (key2001, 6), (key1991, -2), (key1991, -2), (key1988, -2), (key2257, 2), (key2257, 2), (key2236, 2), (key2236, 2), (key2233, 2), (key2233, 2), (key2293, -2), (key2270, -2), (key2270, -2), (key2001, 6), (key2293, -2), (key2270, -2), (key2270, -2)]

def rawRow17758 : Integer.Sparse Key := [(key1988, -2), (key1991, -2), (key2001, -2), (key1991, 6), (key2233, -2), (key2236, -2), (key2270, -2), (key1988, 2), (key1991, 2), (key2233, 2), (key2257, 2), (key2270, 2), (key2293, 2), (key1991, -2), (key2236, -2), (key2257, -2), (key2270, 6), (key2001, -2), (key2270, -2), (key2293, -2)]

def rawRow17759 : Integer.Sparse Key := [(key1991, -2), (key1988, -2), (key2001, -2), (key1991, 6), (key2236, -2), (key2233, -2), (key2270, -2), (key1991, 2), (key1988, 2), (key2257, 2), (key2233, 2), (key2293, 2), (key2270, 2), (key1991, -2), (key2257, -2), (key2236, -2), (key2270, 6), (key2001, -2), (key2293, -2), (key2270, -2)]

def rawRow17760 : Integer.Sparse Key := [(key1988, -2), (key2001, -2), (key1991, -2), (key1991, 6), (key2233, -2), (key2270, -2), (key2236, -2), (key2233, 2), (key2270, 2), (key1988, 2), (key2293, 2), (key1991, 2), (key2257, 2), (key2236, -2), (key1991, -2), (key2257, -2), (key2270, 6), (key2270, -2), (key2001, -2), (key2293, -2)]

def rawRow17761 : Integer.Sparse Key := [(key2001, -2), (key1988, -2), (key1991, -2), (key1991, 6), (key2270, -2), (key2233, -2), (key2236, -2), (key2270, 2), (key2233, 2), (key2293, 2), (key1988, 2), (key2257, 2), (key1991, 2), (key2236, -2), (key2257, -2), (key1991, -2), (key2270, 6), (key2270, -2), (key2293, -2), (key2001, -2)]

def rawRow17762 : Integer.Sparse Key := [(key1991, -2), (key2001, -2), (key1988, -2), (key1991, 6), (key2236, -2), (key2270, -2), (key2233, -2), (key2257, 2), (key2293, 2), (key1991, 2), (key2270, 2), (key1988, 2), (key2233, 2), (key2257, -2), (key1991, -2), (key2236, -2), (key2270, 6), (key2293, -2), (key2001, -2), (key2270, -2)]

def rawRow17763 : Integer.Sparse Key := [(key2001, -2), (key1991, -2), (key1988, -2), (key1991, 6), (key2270, -2), (key2236, -2), (key2233, -2), (key2293, 2), (key2257, 2), (key2270, 2), (key1991, 2), (key2233, 2), (key1988, 2), (key2257, -2), (key2236, -2), (key1991, -2), (key2270, 6), (key2293, -2), (key2270, -2), (key2001, -2)]

def rawRow17764 : Integer.Sparse Key := [(key2233, -2), (key2236, -2), (key2270, -2), (key2270, 6), (key1988, -2), (key1991, -2), (key2001, -2), (key1988, 2), (key1991, 2), (key2233, 2), (key2257, 2), (key2270, 2), (key2293, 2), (key2001, -2), (key2270, -2), (key2293, -2), (key1991, 6), (key1991, -2), (key2236, -2), (key2257, -2)]

def rawRow17765 : Integer.Sparse Key := [(key2236, -2), (key2233, -2), (key2270, -2), (key2270, 6), (key1991, -2), (key1988, -2), (key2001, -2), (key1991, 2), (key1988, 2), (key2257, 2), (key2233, 2), (key2293, 2), (key2270, 2), (key2001, -2), (key2293, -2), (key2270, -2), (key1991, 6), (key1991, -2), (key2257, -2), (key2236, -2)]

def rawRow17766 : Integer.Sparse Key := [(key2233, -2), (key2270, -2), (key2236, -2), (key2270, 6), (key1988, -2), (key2001, -2), (key1991, -2), (key2233, 2), (key2270, 2), (key1988, 2), (key2293, 2), (key1991, 2), (key2257, 2), (key2270, -2), (key2001, -2), (key2293, -2), (key1991, 6), (key2236, -2), (key1991, -2), (key2257, -2)]

def rawRow17767 : Integer.Sparse Key := [(key2270, -2), (key2233, -2), (key2236, -2), (key2270, 6), (key2001, -2), (key1988, -2), (key1991, -2), (key2270, 2), (key2233, 2), (key2293, 2), (key1988, 2), (key2257, 2), (key1991, 2), (key2270, -2), (key2293, -2), (key2001, -2), (key1991, 6), (key2236, -2), (key2257, -2), (key1991, -2)]

def rawRow17768 : Integer.Sparse Key := [(key2236, -2), (key2270, -2), (key2233, -2), (key2270, 6), (key1991, -2), (key2001, -2), (key1988, -2), (key2257, 2), (key2293, 2), (key1991, 2), (key2270, 2), (key1988, 2), (key2233, 2), (key2293, -2), (key2001, -2), (key2270, -2), (key1991, 6), (key2257, -2), (key1991, -2), (key2236, -2)]

def rawRow17769 : Integer.Sparse Key := [(key2270, -2), (key2236, -2), (key2233, -2), (key2270, 6), (key2001, -2), (key1991, -2), (key1988, -2), (key2293, 2), (key2257, 2), (key2270, 2), (key1991, 2), (key2233, 2), (key1988, 2), (key2293, -2), (key2270, -2), (key2001, -2), (key1991, 6), (key2257, -2), (key2236, -2), (key1991, -2)]

def rawRow17770 : Integer.Sparse Key := [(key2233, -2), (key2270, -2), (key2270, -2), (key2236, 6), (key2233, -2), (key2270, -2), (key2270, -2), (key1988, 2), (key2001, 2), (key1988, 2), (key2293, 2), (key2001, 2), (key2293, 2), (key1991, -2), (key1991, -2), (key2257, -2), (key2236, 6), (key1991, -2), (key1991, -2), (key2257, -2)]

def rawRow17771 : Integer.Sparse Key := [(key2270, -2), (key2233, -2), (key2270, -2), (key2236, 6), (key2270, -2), (key2233, -2), (key2270, -2), (key2001, 2), (key1988, 2), (key2293, 2), (key1988, 2), (key2293, 2), (key2001, 2), (key1991, -2), (key2257, -2), (key1991, -2), (key2236, 6), (key1991, -2), (key2257, -2), (key1991, -2)]

def rawRow17772 : Integer.Sparse Key := [(key2270, -2), (key2270, -2), (key2233, -2), (key2236, 6), (key2270, -2), (key2270, -2), (key2233, -2), (key2293, 2), (key2293, 2), (key2001, 2), (key2001, 2), (key1988, 2), (key1988, 2), (key2257, -2), (key1991, -2), (key1991, -2), (key2236, 6), (key2257, -2), (key1991, -2), (key1991, -2)]

def rawRow17773 : Integer.Sparse Key := [(key772, 4), (key772, 4), (key780, 4), (key799, -4), (key805, -4), (key805, -4), (key799, -4), (key805, -4), (key805, -4), (key874, 12)]

def rawRow17774 : Integer.Sparse Key := [(key772, 4), (key780, 4), (key772, 4), (key805, -4), (key799, -4), (key805, -4), (key805, -4), (key799, -4), (key805, -4), (key874, 12)]

def rawRow17775 : Integer.Sparse Key := [(key780, 4), (key772, 4), (key772, 4), (key805, -4), (key805, -4), (key799, -4), (key805, -4), (key805, -4), (key799, -4), (key874, 12)]

def rawRow17776 : Integer.Sparse Key := [(key772, 4), (key799, 4), (key805, 4), (key772, -4), (key780, -4), (key805, -4), (key799, -4), (key805, -4), (key874, -4), (key805, 12)]

def rawRow17777 : Integer.Sparse Key := [(key772, 4), (key805, 4), (key799, 4), (key780, -4), (key772, -4), (key805, -4), (key805, -4), (key799, -4), (key874, -4), (key805, 12)]

def rawRow17778 : Integer.Sparse Key := [(key799, 4), (key772, 4), (key805, 4), (key772, -4), (key805, -4), (key780, -4), (key799, -4), (key874, -4), (key805, -4), (key805, 12)]

def rawRow17779 : Integer.Sparse Key := [(key799, 4), (key805, 4), (key772, 4), (key805, -4), (key772, -4), (key780, -4), (key874, -4), (key799, -4), (key805, -4), (key805, 12)]

def rawRow17780 : Integer.Sparse Key := [(key805, 4), (key772, 4), (key799, 4), (key780, -4), (key805, -4), (key772, -4), (key805, -4), (key874, -4), (key799, -4), (key805, 12)]

def rawRow17781 : Integer.Sparse Key := [(key805, 4), (key799, 4), (key772, 4), (key805, -4), (key780, -4), (key772, -4), (key874, -4), (key805, -4), (key799, -4), (key805, 12)]

def rawRow17782 : Integer.Sparse Key := [(key772, 4), (key799, 4), (key805, 4), (key799, -4), (key805, -4), (key874, -4), (key772, -4), (key780, -4), (key805, -4), (key805, 12)]

def rawRow17783 : Integer.Sparse Key := [(key772, 4), (key805, 4), (key799, 4), (key805, -4), (key799, -4), (key874, -4), (key780, -4), (key772, -4), (key805, -4), (key805, 12)]

def rawRow17784 : Integer.Sparse Key := [(key799, 4), (key772, 4), (key805, 4), (key799, -4), (key874, -4), (key805, -4), (key772, -4), (key805, -4), (key780, -4), (key805, 12)]

def rawRow17785 : Integer.Sparse Key := [(key799, 4), (key805, 4), (key772, 4), (key874, -4), (key799, -4), (key805, -4), (key805, -4), (key772, -4), (key780, -4), (key805, 12)]

def rawRow17786 : Integer.Sparse Key := [(key805, 4), (key772, 4), (key799, 4), (key805, -4), (key874, -4), (key799, -4), (key780, -4), (key805, -4), (key772, -4), (key805, 12)]

def rawRow17787 : Integer.Sparse Key := [(key805, 4), (key799, 4), (key772, 4), (key874, -4), (key805, -4), (key799, -4), (key805, -4), (key780, -4), (key772, -4), (key805, 12)]

def rawRow17788 : Integer.Sparse Key := [(key799, 4), (key799, 4), (key874, 4), (key772, -4), (key805, -4), (key805, -4), (key772, -4), (key805, -4), (key805, -4), (key780, 12)]

def rawRow17789 : Integer.Sparse Key := [(key799, 4), (key874, 4), (key799, 4), (key805, -4), (key772, -4), (key805, -4), (key805, -4), (key772, -4), (key805, -4), (key780, 12)]

def rawRow17790 : Integer.Sparse Key := [(key874, 4), (key799, 4), (key799, 4), (key805, -4), (key805, -4), (key772, -4), (key805, -4), (key805, -4), (key772, -4), (key780, 12)]

def rawRow17791 : Integer.Sparse Key := [(key2150, -1), (key2153, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2167, -1), (key2177, 2), (key2177, 2), (key2188, 2), (key2150, -1), (key2153, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2167, -1), (key2243, 2), (key2247, 2), (key2243, 2), (key2254, 2), (key2247, 2), (key2254, 2), (key2277, -1), (key2280, -1), (key2277, -1), (key2288, -1), (key2280, -1), (key2288, -1), (key2177, 2), (key2177, 2), (key2188, 2), (key2277, -1), (key2280, -1), (key2277, -1), (key2288, -1), (key2280, -1), (key2288, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17792 : Integer.Sparse Key := [(key2153, -1), (key2150, -1), (key2167, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2177, 2), (key2188, 2), (key2177, 2), (key2153, -1), (key2150, -1), (key2167, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2247, 2), (key2243, 2), (key2254, 2), (key2243, 2), (key2254, 2), (key2247, 2), (key2280, -1), (key2277, -1), (key2288, -1), (key2277, -1), (key2288, -1), (key2280, -1), (key2177, 2), (key2188, 2), (key2177, 2), (key2280, -1), (key2277, -1), (key2288, -1), (key2277, -1), (key2288, -1), (key2280, -1)]

def rawRow17793 : Integer.Sparse Key := [(key2167, -1), (key2167, -1), (key2153, -1), (key2153, -1), (key2150, -1), (key2150, -1), (key2188, 2), (key2177, 2), (key2177, 2), (key2167, -1), (key2167, -1), (key2153, -1), (key2153, -1), (key2150, -1), (key2150, -1), (key2254, 2), (key2254, 2), (key2247, 2), (key2247, 2), (key2243, 2), (key2243, 2), (key2288, -1), (key2288, -1), (key2280, -1), (key2280, -1), (key2277, -1), (key2277, -1), (key2188, 2), (key2177, 2), (key2177, 2), (key2288, -1), (key2288, -1), (key2280, -1), (key2280, -1), (key2277, -1), (key2277, -1)]

def rawRow17794 : Integer.Sparse Key := [(key2031, -1), (key2034, -1), (key2150, -1), (key2167, -1), (key2177, -1), (key2188, -1), (key2034, 2), (key2153, 2), (key2167, 2), (key2061, -1), (key2064, -1), (key2243, -1), (key2254, -1), (key2277, -1), (key2288, -1), (key2061, 2), (key2070, 2), (key2150, 2), (key2167, 2), (key2280, 2), (key2288, 2), (key2064, -1), (key2070, -1), (key2153, -1), (key2167, -1), (key2247, -1), (key2254, -1), (key2080, 2), (key2277, 2), (key2288, 2), (key2080, -1), (key2086, -1), (key2177, -1), (key2188, -1), (key2280, -1), (key2288, -1)]

def rawRow17795 : Integer.Sparse Key := [(key2034, -1), (key2031, -1), (key2167, -1), (key2150, -1), (key2188, -1), (key2177, -1), (key2034, 2), (key2167, 2), (key2153, 2), (key2064, -1), (key2061, -1), (key2254, -1), (key2243, -1), (key2288, -1), (key2277, -1), (key2070, 2), (key2061, 2), (key2167, 2), (key2150, 2), (key2288, 2), (key2280, 2), (key2070, -1), (key2064, -1), (key2167, -1), (key2153, -1), (key2254, -1), (key2247, -1), (key2080, 2), (key2288, 2), (key2277, 2), (key2086, -1), (key2080, -1), (key2188, -1), (key2177, -1), (key2288, -1), (key2280, -1)]

def rawRow17796 : Integer.Sparse Key := [(key2150, -1), (key2177, -1), (key2031, -1), (key2188, -1), (key2034, -1), (key2167, -1), (key2153, 2), (key2034, 2), (key2167, 2), (key2243, -1), (key2277, -1), (key2061, -1), (key2288, -1), (key2064, -1), (key2254, -1), (key2150, 2), (key2280, 2), (key2061, 2), (key2288, 2), (key2070, 2), (key2167, 2), (key2153, -1), (key2247, -1), (key2064, -1), (key2254, -1), (key2070, -1), (key2167, -1), (key2277, 2), (key2080, 2), (key2288, 2), (key2177, -1), (key2280, -1), (key2080, -1), (key2288, -1), (key2086, -1), (key2188, -1)]

def rawRow17797 : Integer.Sparse Key := [(key2177, -1), (key2150, -1), (key2188, -1), (key2031, -1), (key2167, -1), (key2034, -1), (key2153, 2), (key2167, 2), (key2034, 2), (key2277, -1), (key2243, -1), (key2288, -1), (key2061, -1), (key2254, -1), (key2064, -1), (key2280, 2), (key2150, 2), (key2288, 2), (key2061, 2), (key2167, 2), (key2070, 2), (key2247, -1), (key2153, -1), (key2254, -1), (key2064, -1), (key2167, -1), (key2070, -1), (key2277, 2), (key2288, 2), (key2080, 2), (key2280, -1), (key2177, -1), (key2288, -1), (key2080, -1), (key2188, -1), (key2086, -1)]

def rawRow17798 : Integer.Sparse Key := [(key2167, -1), (key2188, -1), (key2034, -1), (key2177, -1), (key2031, -1), (key2150, -1), (key2167, 2), (key2034, 2), (key2153, 2), (key2254, -1), (key2288, -1), (key2064, -1), (key2277, -1), (key2061, -1), (key2243, -1), (key2167, 2), (key2288, 2), (key2070, 2), (key2280, 2), (key2061, 2), (key2150, 2), (key2167, -1), (key2254, -1), (key2070, -1), (key2247, -1), (key2064, -1), (key2153, -1), (key2288, 2), (key2080, 2), (key2277, 2), (key2188, -1), (key2288, -1), (key2086, -1), (key2280, -1), (key2080, -1), (key2177, -1)]

def rawRow17799 : Integer.Sparse Key := [(key2188, -1), (key2167, -1), (key2177, -1), (key2034, -1), (key2150, -1), (key2031, -1), (key2167, 2), (key2153, 2), (key2034, 2), (key2288, -1), (key2254, -1), (key2277, -1), (key2064, -1), (key2243, -1), (key2061, -1), (key2288, 2), (key2167, 2), (key2280, 2), (key2070, 2), (key2150, 2), (key2061, 2), (key2254, -1), (key2167, -1), (key2247, -1), (key2070, -1), (key2153, -1), (key2064, -1), (key2288, 2), (key2277, 2), (key2080, 2), (key2288, -1), (key2188, -1), (key2280, -1), (key2086, -1), (key2177, -1), (key2080, -1)]

def rawRow17800 : Integer.Sparse Key := [(key2061, -1), (key2064, -1), (key2243, -1), (key2254, -1), (key2277, -1), (key2288, -1), (key2080, 2), (key2277, 2), (key2288, 2), (key2031, -1), (key2034, -1), (key2150, -1), (key2167, -1), (key2177, -1), (key2188, -1), (key2061, 2), (key2070, 2), (key2150, 2), (key2167, 2), (key2280, 2), (key2288, 2), (key2080, -1), (key2086, -1), (key2177, -1), (key2188, -1), (key2280, -1), (key2288, -1), (key2034, 2), (key2153, 2), (key2167, 2), (key2064, -1), (key2070, -1), (key2153, -1), (key2167, -1), (key2247, -1), (key2254, -1)]

def rawRow17801 : Integer.Sparse Key := [(key2064, -1), (key2061, -1), (key2254, -1), (key2243, -1), (key2288, -1), (key2277, -1), (key2080, 2), (key2288, 2), (key2277, 2), (key2034, -1), (key2031, -1), (key2167, -1), (key2150, -1), (key2188, -1), (key2177, -1), (key2070, 2), (key2061, 2), (key2167, 2), (key2150, 2), (key2288, 2), (key2280, 2), (key2086, -1), (key2080, -1), (key2188, -1), (key2177, -1), (key2288, -1), (key2280, -1), (key2034, 2), (key2167, 2), (key2153, 2), (key2070, -1), (key2064, -1), (key2167, -1), (key2153, -1), (key2254, -1), (key2247, -1)]

def rawRow17802 : Integer.Sparse Key := [(key2243, -1), (key2277, -1), (key2061, -1), (key2288, -1), (key2064, -1), (key2254, -1), (key2277, 2), (key2080, 2), (key2288, 2), (key2150, -1), (key2177, -1), (key2031, -1), (key2188, -1), (key2034, -1), (key2167, -1), (key2150, 2), (key2280, 2), (key2061, 2), (key2288, 2), (key2070, 2), (key2167, 2), (key2177, -1), (key2280, -1), (key2080, -1), (key2288, -1), (key2086, -1), (key2188, -1), (key2153, 2), (key2034, 2), (key2167, 2), (key2153, -1), (key2247, -1), (key2064, -1), (key2254, -1), (key2070, -1), (key2167, -1)]

def rawRow17803 : Integer.Sparse Key := [(key2277, -1), (key2243, -1), (key2288, -1), (key2061, -1), (key2254, -1), (key2064, -1), (key2277, 2), (key2288, 2), (key2080, 2), (key2177, -1), (key2150, -1), (key2188, -1), (key2031, -1), (key2167, -1), (key2034, -1), (key2280, 2), (key2150, 2), (key2288, 2), (key2061, 2), (key2167, 2), (key2070, 2), (key2280, -1), (key2177, -1), (key2288, -1), (key2080, -1), (key2188, -1), (key2086, -1), (key2153, 2), (key2167, 2), (key2034, 2), (key2247, -1), (key2153, -1), (key2254, -1), (key2064, -1), (key2167, -1), (key2070, -1)]

def rawRow17804 : Integer.Sparse Key := [(key2254, -1), (key2288, -1), (key2064, -1), (key2277, -1), (key2061, -1), (key2243, -1), (key2288, 2), (key2080, 2), (key2277, 2), (key2167, -1), (key2188, -1), (key2034, -1), (key2177, -1), (key2031, -1), (key2150, -1), (key2167, 2), (key2288, 2), (key2070, 2), (key2280, 2), (key2061, 2), (key2150, 2), (key2188, -1), (key2288, -1), (key2086, -1), (key2280, -1), (key2080, -1), (key2177, -1), (key2167, 2), (key2034, 2), (key2153, 2), (key2167, -1), (key2254, -1), (key2070, -1), (key2247, -1), (key2064, -1), (key2153, -1)]

def rawRow17805 : Integer.Sparse Key := [(key2288, -1), (key2254, -1), (key2277, -1), (key2064, -1), (key2243, -1), (key2061, -1), (key2288, 2), (key2277, 2), (key2080, 2), (key2188, -1), (key2167, -1), (key2177, -1), (key2034, -1), (key2150, -1), (key2031, -1), (key2288, 2), (key2167, 2), (key2280, 2), (key2070, 2), (key2150, 2), (key2061, 2), (key2288, -1), (key2188, -1), (key2280, -1), (key2086, -1), (key2177, -1), (key2080, -1), (key2167, 2), (key2153, 2), (key2034, 2), (key2254, -1), (key2167, -1), (key2247, -1), (key2070, -1), (key2153, -1), (key2064, -1)]

def rawRow17806 : Integer.Sparse Key := [(key2061, -1), (key2080, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2288, -1), (key2064, 2), (key2064, 2), (key2254, 2), (key2061, -1), (key2080, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2288, -1), (key2031, 2), (key2086, 2), (key2031, 2), (key2188, 2), (key2086, 2), (key2188, 2), (key2034, -1), (key2070, -1), (key2034, -1), (key2167, -1), (key2070, -1), (key2167, -1), (key2064, 2), (key2064, 2), (key2254, 2), (key2034, -1), (key2070, -1), (key2034, -1), (key2167, -1), (key2070, -1), (key2167, -1)]

def rawRow17807 : Integer.Sparse Key := [(key2080, -1), (key2061, -1), (key2288, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2064, 2), (key2254, 2), (key2064, 2), (key2080, -1), (key2061, -1), (key2288, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2086, 2), (key2031, 2), (key2188, 2), (key2031, 2), (key2188, 2), (key2086, 2), (key2070, -1), (key2034, -1), (key2167, -1), (key2034, -1), (key2167, -1), (key2070, -1), (key2064, 2), (key2254, 2), (key2064, 2), (key2070, -1), (key2034, -1), (key2167, -1), (key2034, -1), (key2167, -1), (key2070, -1)]

def rawRow17808 : Integer.Sparse Key := [(key2288, -1), (key2288, -1), (key2080, -1), (key2080, -1), (key2061, -1), (key2061, -1), (key2254, 2), (key2064, 2), (key2064, 2), (key2288, -1), (key2288, -1), (key2080, -1), (key2080, -1), (key2061, -1), (key2061, -1), (key2188, 2), (key2188, 2), (key2086, 2), (key2086, 2), (key2031, 2), (key2031, 2), (key2167, -1), (key2167, -1), (key2070, -1), (key2070, -1), (key2034, -1), (key2034, -1), (key2254, 2), (key2064, 2), (key2064, 2), (key2167, -1), (key2167, -1), (key2070, -1), (key2070, -1), (key2034, -1), (key2034, -1)]

def rawRow17809 : Integer.Sparse Key := [(key361, -2), (key364, -2), (key364, -2), (key368, 6), (key361, -2), (key364, -2), (key364, -2), (key530, 2), (key534, 2), (key530, 2), (key634, 2), (key534, 2), (key634, 2), (key540, -2), (key540, -2), (key639, -2), (key368, 6), (key540, -2), (key540, -2), (key639, -2)]

def rawRow17810 : Integer.Sparse Key := [(key364, -2), (key361, -2), (key364, -2), (key368, 6), (key364, -2), (key361, -2), (key364, -2), (key534, 2), (key530, 2), (key634, 2), (key530, 2), (key634, 2), (key534, 2), (key540, -2), (key639, -2), (key540, -2), (key368, 6), (key540, -2), (key639, -2), (key540, -2)]

def rawRow17811 : Integer.Sparse Key := [(key364, -2), (key364, -2), (key361, -2), (key368, 6), (key364, -2), (key364, -2), (key361, -2), (key634, 2), (key634, 2), (key534, 2), (key534, 2), (key530, 2), (key530, 2), (key639, -2), (key540, -2), (key540, -2), (key368, 6), (key639, -2), (key540, -2), (key540, -2)]

def rawRow17812 : Integer.Sparse Key := [(key361, -2), (key364, -2), (key368, -2), (key364, 6), (key530, -2), (key534, -2), (key540, -2), (key361, 2), (key364, 2), (key530, 2), (key634, 2), (key540, 2), (key639, 2), (key364, -2), (key534, -2), (key634, -2), (key540, 6), (key368, -2), (key540, -2), (key639, -2)]

def rawRow17813 : Integer.Sparse Key := [(key364, -2), (key361, -2), (key368, -2), (key364, 6), (key534, -2), (key530, -2), (key540, -2), (key364, 2), (key361, 2), (key634, 2), (key530, 2), (key639, 2), (key540, 2), (key364, -2), (key634, -2), (key534, -2), (key540, 6), (key368, -2), (key639, -2), (key540, -2)]

def rawRow17814 : Integer.Sparse Key := [(key361, -2), (key368, -2), (key364, -2), (key364, 6), (key530, -2), (key540, -2), (key534, -2), (key530, 2), (key540, 2), (key361, 2), (key639, 2), (key364, 2), (key634, 2), (key534, -2), (key364, -2), (key634, -2), (key540, 6), (key540, -2), (key368, -2), (key639, -2)]

def rawRow17815 : Integer.Sparse Key := [(key368, -2), (key361, -2), (key364, -2), (key364, 6), (key540, -2), (key530, -2), (key534, -2), (key540, 2), (key530, 2), (key639, 2), (key361, 2), (key634, 2), (key364, 2), (key534, -2), (key634, -2), (key364, -2), (key540, 6), (key540, -2), (key639, -2), (key368, -2)]

def rawRow17816 : Integer.Sparse Key := [(key364, -2), (key368, -2), (key361, -2), (key364, 6), (key534, -2), (key540, -2), (key530, -2), (key634, 2), (key639, 2), (key364, 2), (key540, 2), (key361, 2), (key530, 2), (key634, -2), (key364, -2), (key534, -2), (key540, 6), (key639, -2), (key368, -2), (key540, -2)]

def rawRow17817 : Integer.Sparse Key := [(key368, -2), (key364, -2), (key361, -2), (key364, 6), (key540, -2), (key534, -2), (key530, -2), (key639, 2), (key634, 2), (key540, 2), (key364, 2), (key530, 2), (key361, 2), (key634, -2), (key534, -2), (key364, -2), (key540, 6), (key639, -2), (key540, -2), (key368, -2)]

def rawRow17818 : Integer.Sparse Key := [(key530, -2), (key534, -2), (key540, -2), (key540, 6), (key361, -2), (key364, -2), (key368, -2), (key361, 2), (key364, 2), (key530, 2), (key634, 2), (key540, 2), (key639, 2), (key368, -2), (key540, -2), (key639, -2), (key364, 6), (key364, -2), (key534, -2), (key634, -2)]

def rawRow17819 : Integer.Sparse Key := [(key534, -2), (key530, -2), (key540, -2), (key540, 6), (key364, -2), (key361, -2), (key368, -2), (key364, 2), (key361, 2), (key634, 2), (key530, 2), (key639, 2), (key540, 2), (key368, -2), (key639, -2), (key540, -2), (key364, 6), (key364, -2), (key634, -2), (key534, -2)]

def rawRow17820 : Integer.Sparse Key := [(key530, -2), (key540, -2), (key534, -2), (key540, 6), (key361, -2), (key368, -2), (key364, -2), (key530, 2), (key540, 2), (key361, 2), (key639, 2), (key364, 2), (key634, 2), (key540, -2), (key368, -2), (key639, -2), (key364, 6), (key534, -2), (key364, -2), (key634, -2)]

def rawRow17821 : Integer.Sparse Key := [(key540, -2), (key530, -2), (key534, -2), (key540, 6), (key368, -2), (key361, -2), (key364, -2), (key540, 2), (key530, 2), (key639, 2), (key361, 2), (key634, 2), (key364, 2), (key540, -2), (key639, -2), (key368, -2), (key364, 6), (key534, -2), (key634, -2), (key364, -2)]

def rawRow17822 : Integer.Sparse Key := [(key534, -2), (key540, -2), (key530, -2), (key540, 6), (key364, -2), (key368, -2), (key361, -2), (key634, 2), (key639, 2), (key364, 2), (key540, 2), (key361, 2), (key530, 2), (key639, -2), (key368, -2), (key540, -2), (key364, 6), (key634, -2), (key364, -2), (key534, -2)]

def rawRow17823 : Integer.Sparse Key := [(key540, -2), (key534, -2), (key530, -2), (key540, 6), (key368, -2), (key364, -2), (key361, -2), (key639, 2), (key634, 2), (key540, 2), (key364, 2), (key530, 2), (key361, 2), (key639, -2), (key540, -2), (key368, -2), (key364, 6), (key634, -2), (key534, -2), (key364, -2)]

def rawRow17824 : Integer.Sparse Key := [(key530, -2), (key540, -2), (key540, -2), (key534, 6), (key530, -2), (key540, -2), (key540, -2), (key361, 2), (key368, 2), (key361, 2), (key639, 2), (key368, 2), (key639, 2), (key364, -2), (key364, -2), (key634, -2), (key534, 6), (key364, -2), (key364, -2), (key634, -2)]

def rawRow17825 : Integer.Sparse Key := [(key540, -2), (key530, -2), (key540, -2), (key534, 6), (key540, -2), (key530, -2), (key540, -2), (key368, 2), (key361, 2), (key639, 2), (key361, 2), (key639, 2), (key368, 2), (key364, -2), (key634, -2), (key364, -2), (key534, 6), (key364, -2), (key634, -2), (key364, -2)]

def rawRow17826 : Integer.Sparse Key := [(key540, -2), (key540, -2), (key530, -2), (key534, 6), (key540, -2), (key540, -2), (key530, -2), (key639, 2), (key639, 2), (key368, 2), (key368, 2), (key361, 2), (key361, 2), (key634, -2), (key364, -2), (key364, -2), (key534, 6), (key634, -2), (key364, -2), (key364, -2)]

def rawRow17827 : Integer.Sparse Key := [(key1992, 2), (key1992, 2), (key1995, 2), (key2002, -2), (key2004, -2), (key2004, -2), (key1992, 2), (key1992, 2), (key1995, 2), (key2271, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2295, -1), (key2002, -2), (key2004, -2), (key2004, -2), (key2271, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2295, -1), (key2325, 4), (key2325, 4), (key2337, 4)]

def rawRow17828 : Integer.Sparse Key := [(key1992, 2), (key1995, 2), (key1992, 2), (key2004, -2), (key2002, -2), (key2004, -2), (key1992, 2), (key1995, 2), (key1992, 2), (key2273, -1), (key2271, -1), (key2295, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2004, -2), (key2002, -2), (key2004, -2), (key2273, -1), (key2271, -1), (key2295, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2325, 4), (key2337, 4), (key2325, 4)]

def rawRow17829 : Integer.Sparse Key := [(key1995, 2), (key1992, 2), (key1992, 2), (key2004, -2), (key2004, -2), (key2002, -2), (key1995, 2), (key1992, 2), (key1992, 2), (key2295, -1), (key2295, -1), (key2273, -1), (key2273, -1), (key2271, -1), (key2271, -1), (key2004, -2), (key2004, -2), (key2002, -2), (key2295, -1), (key2295, -1), (key2273, -1), (key2273, -1), (key2271, -1), (key2271, -1), (key2337, 4), (key2325, 4), (key2325, 4)]

def rawRow17830 : Integer.Sparse Key := [(key1992, 2), (key2002, 2), (key2004, 2), (key1992, -2), (key1995, -2), (key2004, -2), (key2237, 2), (key2271, 2), (key2273, 2), (key1992, -1), (key1995, -1), (key2237, -1), (key2260, -1), (key2273, -1), (key2295, -1), (key2271, -2), (key2273, -2), (key2325, -2), (key2002, -1), (key2004, -1), (key2271, -1), (key2295, -1), (key2325, -1), (key2337, -1), (key2004, 4), (key2273, 4), (key2295, 4)]

def rawRow17831 : Integer.Sparse Key := [(key1992, 2), (key2004, 2), (key2002, 2), (key1995, -2), (key1992, -2), (key2004, -2), (key2237, 2), (key2273, 2), (key2271, 2), (key1995, -1), (key1992, -1), (key2260, -1), (key2237, -1), (key2295, -1), (key2273, -1), (key2273, -2), (key2271, -2), (key2325, -2), (key2004, -1), (key2002, -1), (key2295, -1), (key2271, -1), (key2337, -1), (key2325, -1), (key2004, 4), (key2295, 4), (key2273, 4)]

def rawRow17832 : Integer.Sparse Key := [(key2002, 2), (key1992, 2), (key2004, 2), (key1992, -2), (key2004, -2), (key1995, -2), (key2271, 2), (key2237, 2), (key2273, 2), (key2237, -1), (key2273, -1), (key1992, -1), (key2295, -1), (key1995, -1), (key2260, -1), (key2271, -2), (key2325, -2), (key2273, -2), (key2271, -1), (key2325, -1), (key2002, -1), (key2337, -1), (key2004, -1), (key2295, -1), (key2273, 4), (key2004, 4), (key2295, 4)]

def rawRow17833 : Integer.Sparse Key := [(key2002, 2), (key2004, 2), (key1992, 2), (key2004, -2), (key1992, -2), (key1995, -2), (key2271, 2), (key2273, 2), (key2237, 2), (key2273, -1), (key2237, -1), (key2295, -1), (key1992, -1), (key2260, -1), (key1995, -1), (key2325, -2), (key2271, -2), (key2273, -2), (key2325, -1), (key2271, -1), (key2337, -1), (key2002, -1), (key2295, -1), (key2004, -1), (key2273, 4), (key2295, 4), (key2004, 4)]

def rawRow17834 : Integer.Sparse Key := [(key2004, 2), (key1992, 2), (key2002, 2), (key1995, -2), (key2004, -2), (key1992, -2), (key2273, 2), (key2237, 2), (key2271, 2), (key2260, -1), (key2295, -1), (key1995, -1), (key2273, -1), (key1992, -1), (key2237, -1), (key2273, -2), (key2325, -2), (key2271, -2), (key2295, -1), (key2337, -1), (key2004, -1), (key2325, -1), (key2002, -1), (key2271, -1), (key2295, 4), (key2004, 4), (key2273, 4)]

def rawRow17835 : Integer.Sparse Key := [(key2004, 2), (key2002, 2), (key1992, 2), (key2004, -2), (key1995, -2), (key1992, -2), (key2273, 2), (key2271, 2), (key2237, 2), (key2295, -1), (key2260, -1), (key2273, -1), (key1995, -1), (key2237, -1), (key1992, -1), (key2325, -2), (key2273, -2), (key2271, -2), (key2337, -1), (key2295, -1), (key2325, -1), (key2004, -1), (key2271, -1), (key2002, -1), (key2295, 4), (key2273, 4), (key2004, 4)]

def rawRow17836 : Integer.Sparse Key := [(key2237, 2), (key2271, 2), (key2273, 2), (key2271, -2), (key2273, -2), (key2325, -2), (key1992, 2), (key2002, 2), (key2004, 2), (key2002, -1), (key2004, -1), (key2271, -1), (key2295, -1), (key2325, -1), (key2337, -1), (key1992, -2), (key1995, -2), (key2004, -2), (key1992, -1), (key1995, -1), (key2237, -1), (key2260, -1), (key2273, -1), (key2295, -1), (key2004, 4), (key2273, 4), (key2295, 4)]

def rawRow17837 : Integer.Sparse Key := [(key2237, 2), (key2273, 2), (key2271, 2), (key2273, -2), (key2271, -2), (key2325, -2), (key1992, 2), (key2004, 2), (key2002, 2), (key2004, -1), (key2002, -1), (key2295, -1), (key2271, -1), (key2337, -1), (key2325, -1), (key1995, -2), (key1992, -2), (key2004, -2), (key1995, -1), (key1992, -1), (key2260, -1), (key2237, -1), (key2295, -1), (key2273, -1), (key2004, 4), (key2295, 4), (key2273, 4)]

def rawRow17838 : Integer.Sparse Key := [(key2271, 2), (key2237, 2), (key2273, 2), (key2271, -2), (key2325, -2), (key2273, -2), (key2002, 2), (key1992, 2), (key2004, 2), (key2271, -1), (key2325, -1), (key2002, -1), (key2337, -1), (key2004, -1), (key2295, -1), (key1992, -2), (key2004, -2), (key1995, -2), (key2237, -1), (key2273, -1), (key1992, -1), (key2295, -1), (key1995, -1), (key2260, -1), (key2273, 4), (key2004, 4), (key2295, 4)]

def rawRow17839 : Integer.Sparse Key := [(key2271, 2), (key2273, 2), (key2237, 2), (key2325, -2), (key2271, -2), (key2273, -2), (key2002, 2), (key2004, 2), (key1992, 2), (key2325, -1), (key2271, -1), (key2337, -1), (key2002, -1), (key2295, -1), (key2004, -1), (key2004, -2), (key1992, -2), (key1995, -2), (key2273, -1), (key2237, -1), (key2295, -1), (key1992, -1), (key2260, -1), (key1995, -1), (key2273, 4), (key2295, 4), (key2004, 4)]

def rawRow17840 : Integer.Sparse Key := [(key2273, 2), (key2237, 2), (key2271, 2), (key2273, -2), (key2325, -2), (key2271, -2), (key2004, 2), (key1992, 2), (key2002, 2), (key2295, -1), (key2337, -1), (key2004, -1), (key2325, -1), (key2002, -1), (key2271, -1), (key1995, -2), (key2004, -2), (key1992, -2), (key2260, -1), (key2295, -1), (key1995, -1), (key2273, -1), (key1992, -1), (key2237, -1), (key2295, 4), (key2004, 4), (key2273, 4)]

def rawRow17841 : Integer.Sparse Key := [(key2273, 2), (key2271, 2), (key2237, 2), (key2325, -2), (key2273, -2), (key2271, -2), (key2004, 2), (key2002, 2), (key1992, 2), (key2337, -1), (key2295, -1), (key2325, -1), (key2004, -1), (key2271, -1), (key2002, -1), (key2004, -2), (key1995, -2), (key1992, -2), (key2295, -1), (key2260, -1), (key2273, -1), (key1995, -1), (key2237, -1), (key1992, -1), (key2295, 4), (key2273, 4), (key2004, 4)]

def rawRow17842 : Integer.Sparse Key := [(key2271, 2), (key2271, 2), (key2325, 2), (key2237, -2), (key2273, -2), (key2273, -2), (key2271, 2), (key2271, 2), (key2325, 2), (key1992, -1), (key2004, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key2295, -1), (key2237, -2), (key2273, -2), (key2273, -2), (key1992, -1), (key2004, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key2295, -1), (key1995, 4), (key1995, 4), (key2260, 4)]

def rawRow17843 : Integer.Sparse Key := [(key2271, 2), (key2325, 2), (key2271, 2), (key2273, -2), (key2237, -2), (key2273, -2), (key2271, 2), (key2325, 2), (key2271, 2), (key2004, -1), (key1992, -1), (key2295, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key2273, -2), (key2237, -2), (key2273, -2), (key2004, -1), (key1992, -1), (key2295, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key1995, 4), (key2260, 4), (key1995, 4)]

def rawRow17844 : Integer.Sparse Key := [(key2325, 2), (key2271, 2), (key2271, 2), (key2273, -2), (key2273, -2), (key2237, -2), (key2325, 2), (key2271, 2), (key2271, 2), (key2295, -1), (key2295, -1), (key2004, -1), (key2004, -1), (key1992, -1), (key1992, -1), (key2273, -2), (key2273, -2), (key2237, -2), (key2295, -1), (key2295, -1), (key2004, -1), (key2004, -1), (key1992, -1), (key1992, -1), (key2260, 4), (key1995, 4), (key1995, 4)]

def rawRow17845 : Integer.Sparse Key := [(key2031, 2), (key2036, 2), (key2036, 2), (key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2031, 2), (key2036, 2), (key2036, 2), (key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2243, 2), (key2248, 2), (key2243, 2), (key2255, 2), (key2248, 2), (key2255, 2)]

def rawRow17846 : Integer.Sparse Key := [(key2036, 2), (key2031, 2), (key2036, 2), (key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2036, 2), (key2031, 2), (key2036, 2), (key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2248, 2), (key2243, 2), (key2255, 2), (key2243, 2), (key2255, 2), (key2248, 2)]

def rawRow17847 : Integer.Sparse Key := [(key2036, 2), (key2036, 2), (key2031, 2), (key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2036, 2), (key2036, 2), (key2031, 2), (key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2255, 2), (key2255, 2), (key2248, 2), (key2248, 2), (key2243, 2), (key2243, 2)]

def rawRow17848 : Integer.Sparse Key := [(key2061, 2), (key2066, 2), (key2093, 2), (key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2150, 2), (key2155, 2), (key2195, 2), (key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2)]

def rawRow17849 : Integer.Sparse Key := [(key2066, 2), (key2061, 2), (key2093, 2), (key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2155, 2), (key2150, 2), (key2195, 2), (key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2)]

def rawRow17850 : Integer.Sparse Key := [(key2061, 2), (key2093, 2), (key2066, 2), (key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2150, 2), (key2195, 2), (key2155, 2), (key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2)]

def rawRow17851 : Integer.Sparse Key := [(key2093, 2), (key2061, 2), (key2066, 2), (key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2195, 2), (key2150, 2), (key2155, 2), (key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2)]

def rawRow17852 : Integer.Sparse Key := [(key2066, 2), (key2093, 2), (key2061, 2), (key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2155, 2), (key2195, 2), (key2150, 2), (key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2)]

def rawRow17853 : Integer.Sparse Key := [(key2093, 2), (key2066, 2), (key2061, 2), (key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2195, 2), (key2155, 2), (key2150, 2), (key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2)]

def rawRow17854 : Integer.Sparse Key := [(key2150, 2), (key2155, 2), (key2195, 2), (key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2061, 2), (key2066, 2), (key2093, 2), (key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2)]

def rawRow17855 : Integer.Sparse Key := [(key2155, 2), (key2150, 2), (key2195, 2), (key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2066, 2), (key2061, 2), (key2093, 2), (key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2)]

def rawRow17856 : Integer.Sparse Key := [(key2150, 2), (key2195, 2), (key2155, 2), (key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2061, 2), (key2093, 2), (key2066, 2), (key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2)]

def rawRow17857 : Integer.Sparse Key := [(key2195, 2), (key2150, 2), (key2155, 2), (key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2093, 2), (key2061, 2), (key2066, 2), (key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2)]

def rawRow17858 : Integer.Sparse Key := [(key2155, 2), (key2195, 2), (key2150, 2), (key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2066, 2), (key2093, 2), (key2061, 2), (key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2)]

def rawRow17859 : Integer.Sparse Key := [(key2195, 2), (key2155, 2), (key2150, 2), (key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2093, 2), (key2066, 2), (key2061, 2), (key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2)]

def rawRow17860 : Integer.Sparse Key := [(key2243, 2), (key2304, 2), (key2304, 2), (key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2243, 2), (key2304, 2), (key2304, 2), (key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2031, 2), (key2096, 2), (key2031, 2), (key2201, 2), (key2096, 2), (key2201, 2)]

def rawRow17861 : Integer.Sparse Key := [(key2304, 2), (key2243, 2), (key2304, 2), (key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2304, 2), (key2243, 2), (key2304, 2), (key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2096, 2), (key2031, 2), (key2201, 2), (key2031, 2), (key2201, 2), (key2096, 2)]

def rawRow17862 : Integer.Sparse Key := [(key2304, 2), (key2304, 2), (key2243, 2), (key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2304, 2), (key2304, 2), (key2243, 2), (key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2201, 2), (key2201, 2), (key2096, 2), (key2096, 2), (key2031, 2), (key2031, 2)]

def rawRow17863 : Integer.Sparse Key := [(key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2093, 2), (key2093, 2), (key2096, 2), (key2150, 1), (key2155, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2168, 1), (key2195, -2), (key2195, -2), (key2201, -2), (key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2150, 1), (key2155, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2168, 1), (key2093, 2), (key2093, 2), (key2096, 2), (key2195, -2), (key2195, -2), (key2201, -2)]

def rawRow17864 : Integer.Sparse Key := [(key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2093, 2), (key2096, 2), (key2093, 2), (key2155, 1), (key2150, 1), (key2168, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2195, -2), (key2201, -2), (key2195, -2), (key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2155, 1), (key2150, 1), (key2168, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2093, 2), (key2096, 2), (key2093, 2), (key2195, -2), (key2201, -2), (key2195, -2)]

def rawRow17865 : Integer.Sparse Key := [(key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2096, 2), (key2093, 2), (key2093, 2), (key2168, 1), (key2168, 1), (key2155, 1), (key2155, 1), (key2150, 1), (key2150, 1), (key2201, -2), (key2195, -2), (key2195, -2), (key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2168, 1), (key2168, 1), (key2155, 1), (key2155, 1), (key2150, 1), (key2150, 1), (key2096, 2), (key2093, 2), (key2093, 2), (key2201, -2), (key2195, -2), (key2195, -2)]

def rawRow17866 : Integer.Sparse Key := [(key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2036, 2), (key2066, 2), (key2071, 2), (key2031, 1), (key2036, 1), (key2150, 1), (key2168, 1), (key2195, 1), (key2201, 1), (key2036, -2), (key2155, -2), (key2168, -2), (key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2061, 1), (key2066, 1), (key2243, 1), (key2255, 1), (key2304, 1), (key2311, 1), (key2195, 2), (key2304, 2), (key2306, 2), (key2093, -2), (key2304, -2), (key2311, -2)]

def rawRow17867 : Integer.Sparse Key := [(key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2036, 2), (key2071, 2), (key2066, 2), (key2036, 1), (key2031, 1), (key2168, 1), (key2150, 1), (key2201, 1), (key2195, 1), (key2036, -2), (key2168, -2), (key2155, -2), (key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2066, 1), (key2061, 1), (key2255, 1), (key2243, 1), (key2311, 1), (key2304, 1), (key2195, 2), (key2306, 2), (key2304, 2), (key2093, -2), (key2311, -2), (key2304, -2)]

def rawRow17868 : Integer.Sparse Key := [(key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2066, 2), (key2036, 2), (key2071, 2), (key2150, 1), (key2195, 1), (key2031, 1), (key2201, 1), (key2036, 1), (key2168, 1), (key2155, -2), (key2036, -2), (key2168, -2), (key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2243, 1), (key2304, 1), (key2061, 1), (key2311, 1), (key2066, 1), (key2255, 1), (key2304, 2), (key2195, 2), (key2306, 2), (key2304, -2), (key2093, -2), (key2311, -2)]

def rawRow17869 : Integer.Sparse Key := [(key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2066, 2), (key2071, 2), (key2036, 2), (key2195, 1), (key2150, 1), (key2201, 1), (key2031, 1), (key2168, 1), (key2036, 1), (key2155, -2), (key2168, -2), (key2036, -2), (key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2304, 1), (key2243, 1), (key2311, 1), (key2061, 1), (key2255, 1), (key2066, 1), (key2304, 2), (key2306, 2), (key2195, 2), (key2304, -2), (key2311, -2), (key2093, -2)]

def rawRow17870 : Integer.Sparse Key := [(key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2071, 2), (key2036, 2), (key2066, 2), (key2168, 1), (key2201, 1), (key2036, 1), (key2195, 1), (key2031, 1), (key2150, 1), (key2168, -2), (key2036, -2), (key2155, -2), (key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2255, 1), (key2311, 1), (key2066, 1), (key2304, 1), (key2061, 1), (key2243, 1), (key2306, 2), (key2195, 2), (key2304, 2), (key2311, -2), (key2093, -2), (key2304, -2)]

def rawRow17871 : Integer.Sparse Key := [(key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2071, 2), (key2066, 2), (key2036, 2), (key2201, 1), (key2168, 1), (key2195, 1), (key2036, 1), (key2150, 1), (key2031, 1), (key2168, -2), (key2155, -2), (key2036, -2), (key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2311, 1), (key2255, 1), (key2304, 1), (key2066, 1), (key2243, 1), (key2061, 1), (key2306, 2), (key2304, 2), (key2195, 2), (key2311, -2), (key2304, -2), (key2093, -2)]

def rawRow17872 : Integer.Sparse Key := [(key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2195, 2), (key2304, 2), (key2306, 2), (key2061, 1), (key2066, 1), (key2243, 1), (key2255, 1), (key2304, 1), (key2311, 1), (key2093, -2), (key2304, -2), (key2311, -2), (key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2031, 1), (key2036, 1), (key2150, 1), (key2168, 1), (key2195, 1), (key2201, 1), (key2036, 2), (key2066, 2), (key2071, 2), (key2036, -2), (key2155, -2), (key2168, -2)]

def rawRow17873 : Integer.Sparse Key := [(key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2195, 2), (key2306, 2), (key2304, 2), (key2066, 1), (key2061, 1), (key2255, 1), (key2243, 1), (key2311, 1), (key2304, 1), (key2093, -2), (key2311, -2), (key2304, -2), (key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2036, 1), (key2031, 1), (key2168, 1), (key2150, 1), (key2201, 1), (key2195, 1), (key2036, 2), (key2071, 2), (key2066, 2), (key2036, -2), (key2168, -2), (key2155, -2)]

def rawRow17874 : Integer.Sparse Key := [(key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2304, 2), (key2195, 2), (key2306, 2), (key2243, 1), (key2304, 1), (key2061, 1), (key2311, 1), (key2066, 1), (key2255, 1), (key2304, -2), (key2093, -2), (key2311, -2), (key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2150, 1), (key2195, 1), (key2031, 1), (key2201, 1), (key2036, 1), (key2168, 1), (key2066, 2), (key2036, 2), (key2071, 2), (key2155, -2), (key2036, -2), (key2168, -2)]

def rawRow17875 : Integer.Sparse Key := [(key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2304, 2), (key2306, 2), (key2195, 2), (key2304, 1), (key2243, 1), (key2311, 1), (key2061, 1), (key2255, 1), (key2066, 1), (key2304, -2), (key2311, -2), (key2093, -2), (key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2195, 1), (key2150, 1), (key2201, 1), (key2031, 1), (key2168, 1), (key2036, 1), (key2066, 2), (key2071, 2), (key2036, 2), (key2155, -2), (key2168, -2), (key2036, -2)]

def rawRow17876 : Integer.Sparse Key := [(key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2306, 2), (key2195, 2), (key2304, 2), (key2255, 1), (key2311, 1), (key2066, 1), (key2304, 1), (key2061, 1), (key2243, 1), (key2311, -2), (key2093, -2), (key2304, -2), (key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2168, 1), (key2201, 1), (key2036, 1), (key2195, 1), (key2031, 1), (key2150, 1), (key2071, 2), (key2036, 2), (key2066, 2), (key2168, -2), (key2036, -2), (key2155, -2)]

def rawRow17877 : Integer.Sparse Key := [(key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2306, 2), (key2304, 2), (key2195, 2), (key2311, 1), (key2255, 1), (key2304, 1), (key2066, 1), (key2243, 1), (key2061, 1), (key2311, -2), (key2304, -2), (key2093, -2), (key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2201, 1), (key2168, 1), (key2195, 1), (key2036, 1), (key2150, 1), (key2031, 1), (key2071, 2), (key2066, 2), (key2036, 2), (key2168, -2), (key2155, -2), (key2036, -2)]

def rawRow17878 : Integer.Sparse Key := [(key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2155, 2), (key2155, 2), (key2248, 2), (key2061, 1), (key2093, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2311, 1), (key2066, -2), (key2066, -2), (key2255, -2), (key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2061, 1), (key2093, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2311, 1), (key2155, 2), (key2155, 2), (key2248, 2), (key2066, -2), (key2066, -2), (key2255, -2)]

def rawRow17879 : Integer.Sparse Key := [(key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2155, 2), (key2248, 2), (key2155, 2), (key2093, 1), (key2061, 1), (key2311, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2066, -2), (key2255, -2), (key2066, -2), (key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2093, 1), (key2061, 1), (key2311, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2155, 2), (key2248, 2), (key2155, 2), (key2066, -2), (key2255, -2), (key2066, -2)]

def rawRow17880 : Integer.Sparse Key := [(key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2248, 2), (key2155, 2), (key2155, 2), (key2311, 1), (key2311, 1), (key2093, 1), (key2093, 1), (key2061, 1), (key2061, 1), (key2255, -2), (key2066, -2), (key2066, -2), (key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2311, 1), (key2311, 1), (key2093, 1), (key2093, 1), (key2061, 1), (key2061, 1), (key2248, 2), (key2155, 2), (key2155, 2), (key2255, -2), (key2066, -2), (key2066, -2)]

def rawRow17881 : Integer.Sparse Key := [(key2061, -1), (key2064, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2070, -1), (key2080, 2), (key2080, 2), (key2086, 2), (key2150, 1), (key2153, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2167, 1), (key2177, -2), (key2177, -2), (key2188, -2), (key2061, -1), (key2064, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2070, -1), (key2150, 1), (key2153, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2167, 1), (key2080, 2), (key2080, 2), (key2086, 2), (key2177, -2), (key2177, -2), (key2188, -2)]

def rawRow17882 : Integer.Sparse Key := [(key2064, -1), (key2061, -1), (key2070, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2080, 2), (key2086, 2), (key2080, 2), (key2153, 1), (key2150, 1), (key2167, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2177, -2), (key2188, -2), (key2177, -2), (key2064, -1), (key2061, -1), (key2070, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2153, 1), (key2150, 1), (key2167, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2080, 2), (key2086, 2), (key2080, 2), (key2177, -2), (key2188, -2), (key2177, -2)]

def rawRow17883 : Integer.Sparse Key := [(key2070, -1), (key2070, -1), (key2064, -1), (key2064, -1), (key2061, -1), (key2061, -1), (key2086, 2), (key2080, 2), (key2080, 2), (key2167, 1), (key2167, 1), (key2153, 1), (key2153, 1), (key2150, 1), (key2150, 1), (key2188, -2), (key2177, -2), (key2177, -2), (key2070, -1), (key2070, -1), (key2064, -1), (key2064, -1), (key2061, -1), (key2061, -1), (key2167, 1), (key2167, 1), (key2153, 1), (key2153, 1), (key2150, 1), (key2150, 1), (key2086, 2), (key2080, 2), (key2080, 2), (key2188, -2), (key2177, -2), (key2177, -2)]

def rawRow17884 : Integer.Sparse Key := [(key2031, -1), (key2034, -1), (key2061, -1), (key2070, -1), (key2080, -1), (key2086, -1), (key2034, 2), (key2064, 2), (key2070, 2), (key2031, 1), (key2034, 1), (key2150, 1), (key2167, 1), (key2177, 1), (key2188, 1), (key2034, -2), (key2153, -2), (key2167, -2), (key2150, -1), (key2153, -1), (key2243, -1), (key2247, -1), (key2277, -1), (key2280, -1), (key2061, 1), (key2064, 1), (key2243, 1), (key2254, 1), (key2277, 1), (key2288, 1), (key2177, 2), (key2277, 2), (key2280, 2), (key2080, -2), (key2277, -2), (key2288, -2)]

def rawRow17885 : Integer.Sparse Key := [(key2034, -1), (key2031, -1), (key2070, -1), (key2061, -1), (key2086, -1), (key2080, -1), (key2034, 2), (key2070, 2), (key2064, 2), (key2034, 1), (key2031, 1), (key2167, 1), (key2150, 1), (key2188, 1), (key2177, 1), (key2034, -2), (key2167, -2), (key2153, -2), (key2153, -1), (key2150, -1), (key2247, -1), (key2243, -1), (key2280, -1), (key2277, -1), (key2064, 1), (key2061, 1), (key2254, 1), (key2243, 1), (key2288, 1), (key2277, 1), (key2177, 2), (key2280, 2), (key2277, 2), (key2080, -2), (key2288, -2), (key2277, -2)]

def rawRow17886 : Integer.Sparse Key := [(key2061, -1), (key2080, -1), (key2031, -1), (key2086, -1), (key2034, -1), (key2070, -1), (key2064, 2), (key2034, 2), (key2070, 2), (key2150, 1), (key2177, 1), (key2031, 1), (key2188, 1), (key2034, 1), (key2167, 1), (key2153, -2), (key2034, -2), (key2167, -2), (key2243, -1), (key2277, -1), (key2150, -1), (key2280, -1), (key2153, -1), (key2247, -1), (key2243, 1), (key2277, 1), (key2061, 1), (key2288, 1), (key2064, 1), (key2254, 1), (key2277, 2), (key2177, 2), (key2280, 2), (key2277, -2), (key2080, -2), (key2288, -2)]

def rawRow17887 : Integer.Sparse Key := [(key2080, -1), (key2061, -1), (key2086, -1), (key2031, -1), (key2070, -1), (key2034, -1), (key2064, 2), (key2070, 2), (key2034, 2), (key2177, 1), (key2150, 1), (key2188, 1), (key2031, 1), (key2167, 1), (key2034, 1), (key2153, -2), (key2167, -2), (key2034, -2), (key2277, -1), (key2243, -1), (key2280, -1), (key2150, -1), (key2247, -1), (key2153, -1), (key2277, 1), (key2243, 1), (key2288, 1), (key2061, 1), (key2254, 1), (key2064, 1), (key2277, 2), (key2280, 2), (key2177, 2), (key2277, -2), (key2288, -2), (key2080, -2)]

def rawRow17888 : Integer.Sparse Key := [(key2070, -1), (key2086, -1), (key2034, -1), (key2080, -1), (key2031, -1), (key2061, -1), (key2070, 2), (key2034, 2), (key2064, 2), (key2167, 1), (key2188, 1), (key2034, 1), (key2177, 1), (key2031, 1), (key2150, 1), (key2167, -2), (key2034, -2), (key2153, -2), (key2247, -1), (key2280, -1), (key2153, -1), (key2277, -1), (key2150, -1), (key2243, -1), (key2254, 1), (key2288, 1), (key2064, 1), (key2277, 1), (key2061, 1), (key2243, 1), (key2280, 2), (key2177, 2), (key2277, 2), (key2288, -2), (key2080, -2), (key2277, -2)]

def rawRow17889 : Integer.Sparse Key := [(key2086, -1), (key2070, -1), (key2080, -1), (key2034, -1), (key2061, -1), (key2031, -1), (key2070, 2), (key2064, 2), (key2034, 2), (key2188, 1), (key2167, 1), (key2177, 1), (key2034, 1), (key2150, 1), (key2031, 1), (key2167, -2), (key2153, -2), (key2034, -2), (key2280, -1), (key2247, -1), (key2277, -1), (key2153, -1), (key2243, -1), (key2150, -1), (key2288, 1), (key2254, 1), (key2277, 1), (key2064, 1), (key2243, 1), (key2061, 1), (key2280, 2), (key2277, 2), (key2177, 2), (key2288, -2), (key2277, -2), (key2080, -2)]

def rawRow17890 : Integer.Sparse Key := [(key2150, -1), (key2153, -1), (key2243, -1), (key2247, -1), (key2277, -1), (key2280, -1), (key2177, 2), (key2277, 2), (key2280, 2), (key2061, 1), (key2064, 1), (key2243, 1), (key2254, 1), (key2277, 1), (key2288, 1), (key2080, -2), (key2277, -2), (key2288, -2), (key2031, -1), (key2034, -1), (key2061, -1), (key2070, -1), (key2080, -1), (key2086, -1), (key2031, 1), (key2034, 1), (key2150, 1), (key2167, 1), (key2177, 1), (key2188, 1), (key2034, 2), (key2064, 2), (key2070, 2), (key2034, -2), (key2153, -2), (key2167, -2)]

def rawRow17891 : Integer.Sparse Key := [(key2153, -1), (key2150, -1), (key2247, -1), (key2243, -1), (key2280, -1), (key2277, -1), (key2177, 2), (key2280, 2), (key2277, 2), (key2064, 1), (key2061, 1), (key2254, 1), (key2243, 1), (key2288, 1), (key2277, 1), (key2080, -2), (key2288, -2), (key2277, -2), (key2034, -1), (key2031, -1), (key2070, -1), (key2061, -1), (key2086, -1), (key2080, -1), (key2034, 1), (key2031, 1), (key2167, 1), (key2150, 1), (key2188, 1), (key2177, 1), (key2034, 2), (key2070, 2), (key2064, 2), (key2034, -2), (key2167, -2), (key2153, -2)]

def rawRow17892 : Integer.Sparse Key := [(key2243, -1), (key2277, -1), (key2150, -1), (key2280, -1), (key2153, -1), (key2247, -1), (key2277, 2), (key2177, 2), (key2280, 2), (key2243, 1), (key2277, 1), (key2061, 1), (key2288, 1), (key2064, 1), (key2254, 1), (key2277, -2), (key2080, -2), (key2288, -2), (key2061, -1), (key2080, -1), (key2031, -1), (key2086, -1), (key2034, -1), (key2070, -1), (key2150, 1), (key2177, 1), (key2031, 1), (key2188, 1), (key2034, 1), (key2167, 1), (key2064, 2), (key2034, 2), (key2070, 2), (key2153, -2), (key2034, -2), (key2167, -2)]

def rawRow17893 : Integer.Sparse Key := [(key2277, -1), (key2243, -1), (key2280, -1), (key2150, -1), (key2247, -1), (key2153, -1), (key2277, 2), (key2280, 2), (key2177, 2), (key2277, 1), (key2243, 1), (key2288, 1), (key2061, 1), (key2254, 1), (key2064, 1), (key2277, -2), (key2288, -2), (key2080, -2), (key2080, -1), (key2061, -1), (key2086, -1), (key2031, -1), (key2070, -1), (key2034, -1), (key2177, 1), (key2150, 1), (key2188, 1), (key2031, 1), (key2167, 1), (key2034, 1), (key2064, 2), (key2070, 2), (key2034, 2), (key2153, -2), (key2167, -2), (key2034, -2)]

def rawRow17894 : Integer.Sparse Key := [(key2247, -1), (key2280, -1), (key2153, -1), (key2277, -1), (key2150, -1), (key2243, -1), (key2280, 2), (key2177, 2), (key2277, 2), (key2254, 1), (key2288, 1), (key2064, 1), (key2277, 1), (key2061, 1), (key2243, 1), (key2288, -2), (key2080, -2), (key2277, -2), (key2070, -1), (key2086, -1), (key2034, -1), (key2080, -1), (key2031, -1), (key2061, -1), (key2167, 1), (key2188, 1), (key2034, 1), (key2177, 1), (key2031, 1), (key2150, 1), (key2070, 2), (key2034, 2), (key2064, 2), (key2167, -2), (key2034, -2), (key2153, -2)]

def rawRow17895 : Integer.Sparse Key := [(key2280, -1), (key2247, -1), (key2277, -1), (key2153, -1), (key2243, -1), (key2150, -1), (key2280, 2), (key2277, 2), (key2177, 2), (key2288, 1), (key2254, 1), (key2277, 1), (key2064, 1), (key2243, 1), (key2061, 1), (key2288, -2), (key2277, -2), (key2080, -2), (key2086, -1), (key2070, -1), (key2080, -1), (key2034, -1), (key2061, -1), (key2031, -1), (key2188, 1), (key2167, 1), (key2177, 1), (key2034, 1), (key2150, 1), (key2031, 1), (key2070, 2), (key2064, 2), (key2034, 2), (key2167, -2), (key2153, -2), (key2034, -2)]

def rawRow17896 : Integer.Sparse Key := [(key2150, -1), (key2177, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2280, -1), (key2153, 2), (key2153, 2), (key2247, 2), (key2061, 1), (key2080, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2288, 1), (key2064, -2), (key2064, -2), (key2254, -2), (key2150, -1), (key2177, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2280, -1), (key2061, 1), (key2080, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2288, 1), (key2153, 2), (key2153, 2), (key2247, 2), (key2064, -2), (key2064, -2), (key2254, -2)]

def rawRow17897 : Integer.Sparse Key := [(key2177, -1), (key2150, -1), (key2280, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2153, 2), (key2247, 2), (key2153, 2), (key2080, 1), (key2061, 1), (key2288, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2064, -2), (key2254, -2), (key2064, -2), (key2177, -1), (key2150, -1), (key2280, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2080, 1), (key2061, 1), (key2288, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2153, 2), (key2247, 2), (key2153, 2), (key2064, -2), (key2254, -2), (key2064, -2)]

def rawRow17898 : Integer.Sparse Key := [(key2280, -1), (key2280, -1), (key2177, -1), (key2177, -1), (key2150, -1), (key2150, -1), (key2247, 2), (key2153, 2), (key2153, 2), (key2288, 1), (key2288, 1), (key2080, 1), (key2080, 1), (key2061, 1), (key2061, 1), (key2254, -2), (key2064, -2), (key2064, -2), (key2280, -1), (key2280, -1), (key2177, -1), (key2177, -1), (key2150, -1), (key2150, -1), (key2288, 1), (key2288, 1), (key2080, 1), (key2080, 1), (key2061, 1), (key2061, 1), (key2247, 2), (key2153, 2), (key2153, 2), (key2254, -2), (key2064, -2), (key2064, -2)]

def rawRow17899 : Integer.Sparse Key := [(key2154, 2), (key2154, 2), (key2170, 2), (key2178, -1), (key2180, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2190, -1), (key2154, 2), (key2154, 2), (key2170, 2), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2290, -1), (key2178, -1), (key2180, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2190, -1), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2290, -1), (key2329, 2), (key2331, 2), (key2329, 2), (key2334, 2), (key2331, 2), (key2334, 2)]

def rawRow17900 : Integer.Sparse Key := [(key2154, 2), (key2170, 2), (key2154, 2), (key2180, -1), (key2178, -1), (key2190, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2154, 2), (key2170, 2), (key2154, 2), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2180, -1), (key2178, -1), (key2190, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2331, 2), (key2329, 2), (key2334, 2), (key2329, 2), (key2334, 2), (key2331, 2)]

def rawRow17901 : Integer.Sparse Key := [(key2170, 2), (key2154, 2), (key2154, 2), (key2190, -1), (key2190, -1), (key2180, -1), (key2180, -1), (key2178, -1), (key2178, -1), (key2170, 2), (key2154, 2), (key2154, 2), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, -1), (key2278, -1), (key2190, -1), (key2190, -1), (key2180, -1), (key2180, -1), (key2178, -1), (key2178, -1), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, -1), (key2278, -1), (key2334, 2), (key2334, 2), (key2331, 2), (key2331, 2), (key2329, 2), (key2329, 2)]

def rawRow17902 : Integer.Sparse Key := [(key2035, 2), (key2178, 2), (key2190, 2), (key2035, -1), (key2038, -1), (key2154, -1), (key2170, -1), (key2180, -1), (key2190, -1), (key2065, 2), (key2278, 2), (key2290, 2), (key2065, -1), (key2073, -1), (key2154, -1), (key2170, -1), (key2282, -1), (key2290, -1), (key2081, -1), (key2083, -1), (key2278, -1), (key2290, -1), (key2329, -1), (key2334, -1), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, -1), (key2334, -1), (key2083, 2), (key2088, 2), (key2180, 2), (key2190, 2), (key2282, 2), (key2290, 2)]

def rawRow17903 : Integer.Sparse Key := [(key2035, 2), (key2190, 2), (key2178, 2), (key2038, -1), (key2035, -1), (key2170, -1), (key2154, -1), (key2190, -1), (key2180, -1), (key2065, 2), (key2290, 2), (key2278, 2), (key2073, -1), (key2065, -1), (key2170, -1), (key2154, -1), (key2290, -1), (key2282, -1), (key2083, -1), (key2081, -1), (key2290, -1), (key2278, -1), (key2334, -1), (key2329, -1), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, -1), (key2331, -1), (key2088, 2), (key2083, 2), (key2190, 2), (key2180, 2), (key2290, 2), (key2282, 2)]

def rawRow17904 : Integer.Sparse Key := [(key2178, 2), (key2035, 2), (key2190, 2), (key2154, -1), (key2180, -1), (key2035, -1), (key2190, -1), (key2038, -1), (key2170, -1), (key2278, 2), (key2065, 2), (key2290, 2), (key2154, -1), (key2282, -1), (key2065, -1), (key2290, -1), (key2073, -1), (key2170, -1), (key2278, -1), (key2329, -1), (key2081, -1), (key2334, -1), (key2083, -1), (key2290, -1), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, -1), (key2190, -1), (key2180, 2), (key2282, 2), (key2083, 2), (key2290, 2), (key2088, 2), (key2190, 2)]

def rawRow17905 : Integer.Sparse Key := [(key2178, 2), (key2190, 2), (key2035, 2), (key2180, -1), (key2154, -1), (key2190, -1), (key2035, -1), (key2170, -1), (key2038, -1), (key2278, 2), (key2290, 2), (key2065, 2), (key2282, -1), (key2154, -1), (key2290, -1), (key2065, -1), (key2170, -1), (key2073, -1), (key2329, -1), (key2278, -1), (key2334, -1), (key2081, -1), (key2290, -1), (key2083, -1), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, -1), (key2088, -1), (key2282, 2), (key2180, 2), (key2290, 2), (key2083, 2), (key2190, 2), (key2088, 2)]

def rawRow17906 : Integer.Sparse Key := [(key2190, 2), (key2035, 2), (key2178, 2), (key2170, -1), (key2190, -1), (key2038, -1), (key2180, -1), (key2035, -1), (key2154, -1), (key2290, 2), (key2065, 2), (key2278, 2), (key2170, -1), (key2290, -1), (key2073, -1), (key2282, -1), (key2065, -1), (key2154, -1), (key2290, -1), (key2334, -1), (key2083, -1), (key2329, -1), (key2081, -1), (key2278, -1), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, -1), (key2178, -1), (key2190, 2), (key2290, 2), (key2088, 2), (key2282, 2), (key2083, 2), (key2180, 2)]

def rawRow17907 : Integer.Sparse Key := [(key2190, 2), (key2178, 2), (key2035, 2), (key2190, -1), (key2170, -1), (key2180, -1), (key2038, -1), (key2154, -1), (key2035, -1), (key2290, 2), (key2278, 2), (key2065, 2), (key2290, -1), (key2170, -1), (key2282, -1), (key2073, -1), (key2154, -1), (key2065, -1), (key2334, -1), (key2290, -1), (key2329, -1), (key2083, -1), (key2278, -1), (key2081, -1), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, -1), (key2081, -1), (key2290, 2), (key2190, 2), (key2282, 2), (key2088, 2), (key2180, 2), (key2083, 2)]

def rawRow17908 : Integer.Sparse Key := [(key2065, 2), (key2278, 2), (key2290, 2), (key2081, -1), (key2083, -1), (key2278, -1), (key2290, -1), (key2329, -1), (key2334, -1), (key2035, 2), (key2178, 2), (key2190, 2), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, -1), (key2334, -1), (key2035, -1), (key2038, -1), (key2154, -1), (key2170, -1), (key2180, -1), (key2190, -1), (key2065, -1), (key2073, -1), (key2154, -1), (key2170, -1), (key2282, -1), (key2290, -1), (key2083, 2), (key2088, 2), (key2180, 2), (key2190, 2), (key2282, 2), (key2290, 2)]

def rawRow17909 : Integer.Sparse Key := [(key2065, 2), (key2290, 2), (key2278, 2), (key2083, -1), (key2081, -1), (key2290, -1), (key2278, -1), (key2334, -1), (key2329, -1), (key2035, 2), (key2190, 2), (key2178, 2), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, -1), (key2331, -1), (key2038, -1), (key2035, -1), (key2170, -1), (key2154, -1), (key2190, -1), (key2180, -1), (key2073, -1), (key2065, -1), (key2170, -1), (key2154, -1), (key2290, -1), (key2282, -1), (key2088, 2), (key2083, 2), (key2190, 2), (key2180, 2), (key2290, 2), (key2282, 2)]

def rawRow17910 : Integer.Sparse Key := [(key2278, 2), (key2065, 2), (key2290, 2), (key2278, -1), (key2329, -1), (key2081, -1), (key2334, -1), (key2083, -1), (key2290, -1), (key2178, 2), (key2035, 2), (key2190, 2), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, -1), (key2190, -1), (key2154, -1), (key2180, -1), (key2035, -1), (key2190, -1), (key2038, -1), (key2170, -1), (key2154, -1), (key2282, -1), (key2065, -1), (key2290, -1), (key2073, -1), (key2170, -1), (key2180, 2), (key2282, 2), (key2083, 2), (key2290, 2), (key2088, 2), (key2190, 2)]

def rawRow17911 : Integer.Sparse Key := [(key2278, 2), (key2290, 2), (key2065, 2), (key2329, -1), (key2278, -1), (key2334, -1), (key2081, -1), (key2290, -1), (key2083, -1), (key2178, 2), (key2190, 2), (key2035, 2), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, -1), (key2088, -1), (key2180, -1), (key2154, -1), (key2190, -1), (key2035, -1), (key2170, -1), (key2038, -1), (key2282, -1), (key2154, -1), (key2290, -1), (key2065, -1), (key2170, -1), (key2073, -1), (key2282, 2), (key2180, 2), (key2290, 2), (key2083, 2), (key2190, 2), (key2088, 2)]

def rawRow17912 : Integer.Sparse Key := [(key2290, 2), (key2065, 2), (key2278, 2), (key2290, -1), (key2334, -1), (key2083, -1), (key2329, -1), (key2081, -1), (key2278, -1), (key2190, 2), (key2035, 2), (key2178, 2), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, -1), (key2178, -1), (key2170, -1), (key2190, -1), (key2038, -1), (key2180, -1), (key2035, -1), (key2154, -1), (key2170, -1), (key2290, -1), (key2073, -1), (key2282, -1), (key2065, -1), (key2154, -1), (key2190, 2), (key2290, 2), (key2088, 2), (key2282, 2), (key2083, 2), (key2180, 2)]

def rawRow17913 : Integer.Sparse Key := [(key2290, 2), (key2278, 2), (key2065, 2), (key2334, -1), (key2290, -1), (key2329, -1), (key2083, -1), (key2278, -1), (key2081, -1), (key2190, 2), (key2178, 2), (key2035, 2), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, -1), (key2081, -1), (key2190, -1), (key2170, -1), (key2180, -1), (key2038, -1), (key2154, -1), (key2035, -1), (key2290, -1), (key2170, -1), (key2282, -1), (key2073, -1), (key2154, -1), (key2065, -1), (key2290, 2), (key2190, 2), (key2282, 2), (key2088, 2), (key2180, 2), (key2083, 2)]

def rawRow17914 : Integer.Sparse Key := [(key2081, 2), (key2081, 2), (key2334, 2), (key2065, -1), (key2083, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2290, -1), (key2081, 2), (key2081, 2), (key2334, 2), (key2035, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2190, -1), (key2065, -1), (key2083, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2290, -1), (key2035, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2190, -1), (key2038, 2), (key2073, 2), (key2038, 2), (key2170, 2), (key2073, 2), (key2170, 2)]

def rawRow17915 : Integer.Sparse Key := [(key2081, 2), (key2334, 2), (key2081, 2), (key2083, -1), (key2065, -1), (key2290, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2081, 2), (key2334, 2), (key2081, 2), (key2088, -1), (key2035, -1), (key2190, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2083, -1), (key2065, -1), (key2290, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2073, 2), (key2038, 2), (key2170, 2), (key2038, 2), (key2170, 2), (key2073, 2)]

def rawRow17916 : Integer.Sparse Key := [(key2334, 2), (key2081, 2), (key2081, 2), (key2290, -1), (key2290, -1), (key2083, -1), (key2083, -1), (key2065, -1), (key2065, -1), (key2334, 2), (key2081, 2), (key2081, 2), (key2190, -1), (key2190, -1), (key2088, -1), (key2088, -1), (key2035, -1), (key2035, -1), (key2290, -1), (key2290, -1), (key2083, -1), (key2083, -1), (key2065, -1), (key2065, -1), (key2190, -1), (key2190, -1), (key2088, -1), (key2088, -1), (key2035, -1), (key2035, -1), (key2170, 2), (key2170, 2), (key2073, 2), (key2073, 2), (key2038, 2), (key2038, 2)]

def rawRow17917 : Integer.Sparse Key := [(key777, 4), (key782, 4), (key782, 4), (key802, -2), (key807, -2), (key802, -2), (key821, -2), (key807, -2), (key821, -2), (key802, -2), (key807, -2), (key802, -2), (key821, -2), (key807, -2), (key821, -2), (key872, 4), (key905, 4), (key905, 4)]

def rawRow17918 : Integer.Sparse Key := [(key782, 4), (key777, 4), (key782, 4), (key807, -2), (key802, -2), (key821, -2), (key802, -2), (key821, -2), (key807, -2), (key807, -2), (key802, -2), (key821, -2), (key802, -2), (key821, -2), (key807, -2), (key905, 4), (key872, 4), (key905, 4)]

def rawRow17919 : Integer.Sparse Key := [(key782, 4), (key782, 4), (key777, 4), (key821, -2), (key821, -2), (key807, -2), (key807, -2), (key802, -2), (key802, -2), (key821, -2), (key821, -2), (key807, -2), (key807, -2), (key802, -2), (key802, -2), (key905, 4), (key905, 4), (key872, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17920 : Integer.Sparse Key := [(key802, 4), (key807, 4), (key812, 4), (key777, -2), (key782, -2), (key802, -2), (key821, -2), (key812, -2), (key824, -2), (key802, -2), (key807, -2), (key872, -2), (key905, -2), (key877, -2), (key907, -2), (key802, 4), (key821, 4), (key907, 4)]

def rawRow17921 : Integer.Sparse Key := [(key807, 4), (key802, 4), (key812, 4), (key782, -2), (key777, -2), (key821, -2), (key802, -2), (key824, -2), (key812, -2), (key807, -2), (key802, -2), (key905, -2), (key872, -2), (key907, -2), (key877, -2), (key821, 4), (key802, 4), (key907, 4)]

def rawRow17922 : Integer.Sparse Key := [(key802, 4), (key812, 4), (key807, 4), (key802, -2), (key812, -2), (key777, -2), (key824, -2), (key782, -2), (key821, -2), (key872, -2), (key877, -2), (key802, -2), (key907, -2), (key807, -2), (key905, -2), (key802, 4), (key907, 4), (key821, 4)]

def rawRow17923 : Integer.Sparse Key := [(key812, 4), (key802, 4), (key807, 4), (key812, -2), (key802, -2), (key824, -2), (key777, -2), (key821, -2), (key782, -2), (key877, -2), (key872, -2), (key907, -2), (key802, -2), (key905, -2), (key807, -2), (key907, 4), (key802, 4), (key821, 4)]

def rawRow17924 : Integer.Sparse Key := [(key807, 4), (key812, 4), (key802, 4), (key821, -2), (key824, -2), (key782, -2), (key812, -2), (key777, -2), (key802, -2), (key905, -2), (key907, -2), (key807, -2), (key877, -2), (key802, -2), (key872, -2), (key821, 4), (key907, 4), (key802, 4)]

def rawRow17925 : Integer.Sparse Key := [(key812, 4), (key807, 4), (key802, 4), (key824, -2), (key821, -2), (key812, -2), (key782, -2), (key802, -2), (key777, -2), (key907, -2), (key905, -2), (key877, -2), (key807, -2), (key872, -2), (key802, -2), (key907, 4), (key821, 4), (key802, 4)]

def rawRow17926 : Integer.Sparse Key := [(key802, 4), (key807, 4), (key812, 4), (key802, -2), (key807, -2), (key872, -2), (key905, -2), (key877, -2), (key907, -2), (key777, -2), (key782, -2), (key802, -2), (key821, -2), (key812, -2), (key824, -2), (key802, 4), (key821, 4), (key907, 4)]

def rawRow17927 : Integer.Sparse Key := [(key807, 4), (key802, 4), (key812, 4), (key807, -2), (key802, -2), (key905, -2), (key872, -2), (key907, -2), (key877, -2), (key782, -2), (key777, -2), (key821, -2), (key802, -2), (key824, -2), (key812, -2), (key821, 4), (key802, 4), (key907, 4)]

def rawRow17928 : Integer.Sparse Key := [(key802, 4), (key812, 4), (key807, 4), (key872, -2), (key877, -2), (key802, -2), (key907, -2), (key807, -2), (key905, -2), (key802, -2), (key812, -2), (key777, -2), (key824, -2), (key782, -2), (key821, -2), (key802, 4), (key907, 4), (key821, 4)]

def rawRow17929 : Integer.Sparse Key := [(key812, 4), (key802, 4), (key807, 4), (key877, -2), (key872, -2), (key907, -2), (key802, -2), (key905, -2), (key807, -2), (key812, -2), (key802, -2), (key824, -2), (key777, -2), (key821, -2), (key782, -2), (key907, 4), (key802, 4), (key821, 4)]

def rawRow17930 : Integer.Sparse Key := [(key807, 4), (key812, 4), (key802, 4), (key905, -2), (key907, -2), (key807, -2), (key877, -2), (key802, -2), (key872, -2), (key821, -2), (key824, -2), (key782, -2), (key812, -2), (key777, -2), (key802, -2), (key821, 4), (key907, 4), (key802, 4)]

def rawRow17931 : Integer.Sparse Key := [(key812, 4), (key807, 4), (key802, 4), (key907, -2), (key905, -2), (key877, -2), (key807, -2), (key872, -2), (key802, -2), (key824, -2), (key821, -2), (key812, -2), (key782, -2), (key802, -2), (key777, -2), (key907, 4), (key821, 4), (key802, 4)]

def rawRow17932 : Integer.Sparse Key := [(key872, 4), (key877, 4), (key877, 4), (key802, -2), (key812, -2), (key802, -2), (key907, -2), (key812, -2), (key907, -2), (key802, -2), (key812, -2), (key802, -2), (key907, -2), (key812, -2), (key907, -2), (key777, 4), (key824, 4), (key824, 4)]

def rawRow17933 : Integer.Sparse Key := [(key877, 4), (key872, 4), (key877, 4), (key812, -2), (key802, -2), (key907, -2), (key802, -2), (key907, -2), (key812, -2), (key812, -2), (key802, -2), (key907, -2), (key802, -2), (key907, -2), (key812, -2), (key824, 4), (key777, 4), (key824, 4)]

def rawRow17934 : Integer.Sparse Key := [(key877, 4), (key877, 4), (key872, 4), (key907, -2), (key907, -2), (key812, -2), (key812, -2), (key802, -2), (key802, -2), (key907, -2), (key907, -2), (key812, -2), (key812, -2), (key802, -2), (key802, -2), (key824, 4), (key824, 4), (key777, 4)]

def rawRow17935 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key763, -2), (key785, -2), (key775, -2), (key785, -2), (key800, 2), (key810, 2), (key810, 2), (key835, 2), (key838, 2), (key838, 2), (key800, 2), (key810, 2), (key810, 2), (key933, -6), (key835, 2), (key838, 2), (key838, 2), (key933, -6)]

def rawRow17936 : Integer.Sparse Key := [(key765, -2), (key763, -2), (key767, -2), (key773, -2), (key785, -2), (key775, -2), (key810, 2), (key800, 2), (key810, 2), (key838, 2), (key835, 2), (key838, 2), (key810, 2), (key800, 2), (key810, 2), (key933, -6), (key838, 2), (key835, 2), (key838, 2), (key933, -6)]

def rawRow17937 : Integer.Sparse Key := [(key767, -2), (key767, -2), (key765, -2), (key765, -2), (key773, -2), (key773, -2), (key810, 2), (key810, 2), (key800, 2), (key838, 2), (key838, 2), (key835, 2), (key810, 2), (key810, 2), (key800, 2), (key933, -6), (key838, 2), (key838, 2), (key835, 2), (key933, -6)]

def rawRow17938 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key788, -2), (key791, -2), (key790, -2), (key792, -2), (key763, 2), (key785, 2), (key838, 2), (key775, 2), (key785, 2), (key810, 2), (key800, 2), (key810, 2), (key933, 2), (key810, -6), (key835, 2), (key838, 2), (key933, 2), (key838, -6)]

def rawRow17939 : Integer.Sparse Key := [(key765, -2), (key763, -2), (key791, -2), (key788, -2), (key792, -2), (key790, -2), (key767, 2), (key773, 2), (key838, 2), (key785, 2), (key775, 2), (key810, 2), (key810, 2), (key800, 2), (key933, 2), (key810, -6), (key838, 2), (key835, 2), (key933, 2), (key838, -6)]

def rawRow17940 : Integer.Sparse Key := [(key788, -2), (key790, -2), (key763, -2), (key792, -2), (key765, -2), (key791, -2), (key763, 2), (key792, 2), (key785, 2), (key775, 2), (key810, 2), (key785, 2), (key800, 2), (key933, 2), (key810, 2), (key810, -6), (key835, 2), (key933, 2), (key838, 2), (key838, -6)]

def rawRow17941 : Integer.Sparse Key := [(key790, -2), (key788, -2), (key792, -2), (key763, -2), (key791, -2), (key765, -2), (key792, 2), (key763, 2), (key785, 2), (key810, 2), (key775, 2), (key785, 2), (key933, 2), (key800, 2), (key810, 2), (key810, -6), (key933, 2), (key835, 2), (key838, 2), (key838, -6)]

def rawRow17942 : Integer.Sparse Key := [(key791, -2), (key792, -2), (key765, -2), (key790, -2), (key763, -2), (key788, -2), (key767, 2), (key792, 2), (key773, 2), (key785, 2), (key810, 2), (key775, 2), (key810, 2), (key933, 2), (key800, 2), (key810, -6), (key838, 2), (key933, 2), (key835, 2), (key838, -6)]

def rawRow17943 : Integer.Sparse Key := [(key792, -2), (key791, -2), (key790, -2), (key765, -2), (key788, -2), (key763, -2), (key792, 2), (key767, 2), (key773, 2), (key810, 2), (key785, 2), (key775, 2), (key933, 2), (key810, 2), (key800, 2), (key810, -6), (key933, 2), (key838, 2), (key835, 2), (key838, -6)]

def rawRow17944 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key788, -2), (key791, -2), (key790, -2), (key792, -2), (key788, 2), (key791, 2), (key851, 2), (key790, 2), (key792, 2), (key851, 2), (key763, 2), (key785, 2), (key838, 2), (key838, -6), (key775, 2), (key785, 2), (key810, 2), (key810, -6)]

def rawRow17945 : Integer.Sparse Key := [(key765, -2), (key763, -2), (key791, -2), (key788, -2), (key792, -2), (key790, -2), (key791, 2), (key788, 2), (key851, 2), (key792, 2), (key790, 2), (key851, 2), (key767, 2), (key773, 2), (key838, 2), (key838, -6), (key785, 2), (key775, 2), (key810, 2), (key810, -6)]

def rawRow17946 : Integer.Sparse Key := [(key788, -2), (key790, -2), (key763, -2), (key792, -2), (key765, -2), (key791, -2), (key788, 2), (key851, 2), (key791, 2), (key790, 2), (key851, 2), (key792, 2), (key763, 2), (key792, 2), (key785, 2), (key838, -6), (key775, 2), (key810, 2), (key785, 2), (key810, -6)]

def rawRow17947 : Integer.Sparse Key := [(key790, -2), (key788, -2), (key792, -2), (key763, -2), (key791, -2), (key765, -2), (key851, 2), (key788, 2), (key791, 2), (key851, 2), (key790, 2), (key792, 2), (key792, 2), (key763, 2), (key785, 2), (key838, -6), (key810, 2), (key775, 2), (key785, 2), (key810, -6)]

def rawRow17948 : Integer.Sparse Key := [(key791, -2), (key792, -2), (key765, -2), (key790, -2), (key763, -2), (key788, -2), (key791, 2), (key851, 2), (key788, 2), (key792, 2), (key851, 2), (key790, 2), (key767, 2), (key792, 2), (key773, 2), (key838, -6), (key785, 2), (key810, 2), (key775, 2), (key810, -6)]

def rawRow17949 : Integer.Sparse Key := [(key792, -2), (key791, -2), (key790, -2), (key765, -2), (key788, -2), (key763, -2), (key851, 2), (key791, 2), (key788, 2), (key851, 2), (key792, 2), (key790, 2), (key792, 2), (key767, 2), (key773, 2), (key838, -6), (key810, 2), (key785, 2), (key775, 2), (key810, -6)]

def rawRow17950 : Integer.Sparse Key := [(key788, -2), (key790, -2), (key788, -2), (key851, -2), (key790, -2), (key851, -2), (key763, 2), (key792, 2), (key792, 2), (key765, 2), (key791, 2), (key791, 2), (key763, 2), (key792, 2), (key792, 2), (key785, -6), (key775, 2), (key810, 2), (key810, 2), (key785, -6)]

def rawRow17951 : Integer.Sparse Key := [(key790, -2), (key788, -2), (key851, -2), (key788, -2), (key851, -2), (key790, -2), (key792, 2), (key763, 2), (key792, 2), (key791, 2), (key765, 2), (key791, 2), (key792, 2), (key763, 2), (key792, 2), (key785, -6), (key810, 2), (key775, 2), (key810, 2), (key785, -6)]

def rawRow17952 : Integer.Sparse Key := [(key851, -2), (key851, -2), (key790, -2), (key790, -2), (key788, -2), (key788, -2), (key792, 2), (key792, 2), (key763, 2), (key791, 2), (key791, 2), (key765, 2), (key792, 2), (key792, 2), (key763, 2), (key785, -6), (key810, 2), (key810, 2), (key775, 2), (key785, -6)]

def rawRow17953 : Integer.Sparse Key := [(key636, 4), (key636, 4), (key637, 4), (key642, -4), (key643, -4), (key643, -4), (key642, -4), (key643, -4), (key643, -4), (key651, 12)]

def rawRow17954 : Integer.Sparse Key := [(key636, 4), (key637, 4), (key636, 4), (key643, -4), (key642, -4), (key643, -4), (key643, -4), (key642, -4), (key643, -4), (key651, 12)]

def rawRow17955 : Integer.Sparse Key := [(key637, 4), (key636, 4), (key636, 4), (key643, -4), (key643, -4), (key642, -4), (key643, -4), (key643, -4), (key642, -4), (key651, 12)]

def rawRow17956 : Integer.Sparse Key := [(key636, 4), (key642, 4), (key643, 4), (key636, -4), (key637, -4), (key643, -4), (key642, -4), (key643, -4), (key651, -4), (key643, 12)]

def rawRow17957 : Integer.Sparse Key := [(key636, 4), (key643, 4), (key642, 4), (key637, -4), (key636, -4), (key643, -4), (key643, -4), (key642, -4), (key651, -4), (key643, 12)]

def rawRow17958 : Integer.Sparse Key := [(key642, 4), (key636, 4), (key643, 4), (key636, -4), (key643, -4), (key637, -4), (key642, -4), (key651, -4), (key643, -4), (key643, 12)]

def rawRow17959 : Integer.Sparse Key := [(key642, 4), (key643, 4), (key636, 4), (key643, -4), (key636, -4), (key637, -4), (key651, -4), (key642, -4), (key643, -4), (key643, 12)]

def rawRow17960 : Integer.Sparse Key := [(key643, 4), (key636, 4), (key642, 4), (key637, -4), (key643, -4), (key636, -4), (key643, -4), (key651, -4), (key642, -4), (key643, 12)]

def rawRow17961 : Integer.Sparse Key := [(key643, 4), (key642, 4), (key636, 4), (key643, -4), (key637, -4), (key636, -4), (key651, -4), (key643, -4), (key642, -4), (key643, 12)]

def rawRow17962 : Integer.Sparse Key := [(key636, 4), (key642, 4), (key643, 4), (key642, -4), (key643, -4), (key651, -4), (key636, -4), (key637, -4), (key643, -4), (key643, 12)]

def rawRow17963 : Integer.Sparse Key := [(key636, 4), (key643, 4), (key642, 4), (key643, -4), (key642, -4), (key651, -4), (key637, -4), (key636, -4), (key643, -4), (key643, 12)]

def rawRow17964 : Integer.Sparse Key := [(key642, 4), (key636, 4), (key643, 4), (key642, -4), (key651, -4), (key643, -4), (key636, -4), (key643, -4), (key637, -4), (key643, 12)]

def rawRow17965 : Integer.Sparse Key := [(key642, 4), (key643, 4), (key636, 4), (key651, -4), (key642, -4), (key643, -4), (key643, -4), (key636, -4), (key637, -4), (key643, 12)]

def rawRow17966 : Integer.Sparse Key := [(key643, 4), (key636, 4), (key642, 4), (key643, -4), (key651, -4), (key642, -4), (key637, -4), (key643, -4), (key636, -4), (key643, 12)]

def rawRow17967 : Integer.Sparse Key := [(key643, 4), (key642, 4), (key636, 4), (key651, -4), (key643, -4), (key642, -4), (key643, -4), (key637, -4), (key636, -4), (key643, 12)]

def rawRow17968 : Integer.Sparse Key := [(key642, 4), (key642, 4), (key651, 4), (key636, -4), (key643, -4), (key643, -4), (key636, -4), (key643, -4), (key643, -4), (key637, 12)]

def rawRow17969 : Integer.Sparse Key := [(key642, 4), (key651, 4), (key642, 4), (key643, -4), (key636, -4), (key643, -4), (key643, -4), (key636, -4), (key643, -4), (key637, 12)]

def rawRow17970 : Integer.Sparse Key := [(key651, 4), (key642, 4), (key642, 4), (key643, -4), (key643, -4), (key636, -4), (key643, -4), (key643, -4), (key636, -4), (key637, 12)]

def rawRow17971 : Integer.Sparse Key := [(key781, 4), (key784, 4), (key784, 4), (key806, -2), (key809, -2), (key806, -2), (key814, -2), (key809, -2), (key814, -2), (key806, -2), (key809, -2), (key806, -2), (key814, -2), (key809, -2), (key814, -2), (key875, 4), (key879, 4), (key879, 4)]

def rawRow17972 : Integer.Sparse Key := [(key784, 4), (key781, 4), (key784, 4), (key809, -2), (key806, -2), (key814, -2), (key806, -2), (key814, -2), (key809, -2), (key809, -2), (key806, -2), (key814, -2), (key806, -2), (key814, -2), (key809, -2), (key879, 4), (key875, 4), (key879, 4)]

def rawRow17973 : Integer.Sparse Key := [(key784, 4), (key784, 4), (key781, 4), (key814, -2), (key814, -2), (key809, -2), (key809, -2), (key806, -2), (key806, -2), (key814, -2), (key814, -2), (key809, -2), (key809, -2), (key806, -2), (key806, -2), (key879, 4), (key879, 4), (key875, 4)]

def rawRow17974 : Integer.Sparse Key := [(key806, 4), (key809, 4), (key814, 4), (key781, -2), (key784, -2), (key806, -2), (key814, -2), (key822, -2), (key827, -2), (key806, -2), (key809, -2), (key875, -2), (key879, -2), (key906, -2), (key910, -2), (key806, 4), (key814, 4), (key910, 4)]

def rawRow17975 : Integer.Sparse Key := [(key809, 4), (key806, 4), (key814, 4), (key784, -2), (key781, -2), (key814, -2), (key806, -2), (key827, -2), (key822, -2), (key809, -2), (key806, -2), (key879, -2), (key875, -2), (key910, -2), (key906, -2), (key814, 4), (key806, 4), (key910, 4)]

def rawRow17976 : Integer.Sparse Key := [(key806, 4), (key814, 4), (key809, 4), (key806, -2), (key814, -2), (key781, -2), (key827, -2), (key784, -2), (key814, -2), (key875, -2), (key906, -2), (key806, -2), (key910, -2), (key809, -2), (key879, -2), (key806, 4), (key910, 4), (key814, 4)]

def rawRow17977 : Integer.Sparse Key := [(key814, 4), (key806, 4), (key809, 4), (key814, -2), (key806, -2), (key827, -2), (key781, -2), (key814, -2), (key784, -2), (key906, -2), (key875, -2), (key910, -2), (key806, -2), (key879, -2), (key809, -2), (key910, 4), (key806, 4), (key814, 4)]

def rawRow17978 : Integer.Sparse Key := [(key809, 4), (key814, 4), (key806, 4), (key822, -2), (key827, -2), (key784, -2), (key814, -2), (key781, -2), (key806, -2), (key879, -2), (key910, -2), (key809, -2), (key906, -2), (key806, -2), (key875, -2), (key814, 4), (key910, 4), (key806, 4)]

def rawRow17979 : Integer.Sparse Key := [(key814, 4), (key809, 4), (key806, 4), (key827, -2), (key822, -2), (key814, -2), (key784, -2), (key806, -2), (key781, -2), (key910, -2), (key879, -2), (key906, -2), (key809, -2), (key875, -2), (key806, -2), (key910, 4), (key814, 4), (key806, 4)]

def rawRow17980 : Integer.Sparse Key := [(key806, 4), (key809, 4), (key814, 4), (key806, -2), (key809, -2), (key875, -2), (key906, -2), (key879, -2), (key910, -2), (key781, -2), (key784, -2), (key806, -2), (key814, -2), (key822, -2), (key827, -2), (key806, 4), (key814, 4), (key910, 4)]

def rawRow17981 : Integer.Sparse Key := [(key809, 4), (key806, 4), (key814, 4), (key809, -2), (key806, -2), (key906, -2), (key875, -2), (key910, -2), (key879, -2), (key784, -2), (key781, -2), (key814, -2), (key806, -2), (key827, -2), (key822, -2), (key814, 4), (key806, 4), (key910, 4)]

def rawRow17982 : Integer.Sparse Key := [(key806, 4), (key814, 4), (key809, 4), (key875, -2), (key879, -2), (key806, -2), (key910, -2), (key809, -2), (key906, -2), (key806, -2), (key814, -2), (key781, -2), (key827, -2), (key784, -2), (key814, -2), (key806, 4), (key910, 4), (key814, 4)]

def rawRow17983 : Integer.Sparse Key := [(key814, 4), (key806, 4), (key809, 4), (key879, -2), (key875, -2), (key910, -2), (key806, -2), (key906, -2), (key809, -2), (key814, -2), (key806, -2), (key827, -2), (key781, -2), (key814, -2), (key784, -2), (key910, 4), (key806, 4), (key814, 4)]

def rawRow17984 : Integer.Sparse Key := [(key809, 4), (key814, 4), (key806, 4), (key906, -2), (key910, -2), (key809, -2), (key879, -2), (key806, -2), (key875, -2), (key822, -2), (key827, -2), (key784, -2), (key814, -2), (key781, -2), (key806, -2), (key814, 4), (key910, 4), (key806, 4)]

def rawRow17985 : Integer.Sparse Key := [(key814, 4), (key809, 4), (key806, 4), (key910, -2), (key906, -2), (key879, -2), (key809, -2), (key875, -2), (key806, -2), (key827, -2), (key822, -2), (key814, -2), (key784, -2), (key806, -2), (key781, -2), (key910, 4), (key814, 4), (key806, 4)]

def rawRow17986 : Integer.Sparse Key := [(key875, 4), (key879, 4), (key879, 4), (key806, -2), (key814, -2), (key806, -2), (key910, -2), (key814, -2), (key910, -2), (key806, -2), (key814, -2), (key806, -2), (key910, -2), (key814, -2), (key910, -2), (key781, 4), (key827, 4), (key827, 4)]

def rawRow17987 : Integer.Sparse Key := [(key879, 4), (key875, 4), (key879, 4), (key814, -2), (key806, -2), (key910, -2), (key806, -2), (key910, -2), (key814, -2), (key814, -2), (key806, -2), (key910, -2), (key806, -2), (key910, -2), (key814, -2), (key827, 4), (key781, 4), (key827, 4)]

def rawRow17988 : Integer.Sparse Key := [(key879, 4), (key879, 4), (key875, 4), (key910, -2), (key910, -2), (key814, -2), (key814, -2), (key806, -2), (key806, -2), (key910, -2), (key910, -2), (key814, -2), (key814, -2), (key806, -2), (key806, -2), (key827, 4), (key827, 4), (key781, 4)]

def rawRow17989 : Integer.Sparse Key := [(key2421, 4), (key2496, 4), (key2550, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2550, -2), (key2508, -2), (key2556, -2), (key2428, -2), (key2429, -2), (key2496, -2), (key2550, -2), (key2508, -2), (key2556, -2), (key2442, 4), (key2508, 4), (key2556, 4)]

def rawRow17990 : Integer.Sparse Key := [(key2421, 4), (key2550, 4), (key2496, 4), (key2429, -2), (key2428, -2), (key2550, -2), (key2496, -2), (key2556, -2), (key2508, -2), (key2429, -2), (key2428, -2), (key2550, -2), (key2496, -2), (key2556, -2), (key2508, -2), (key2442, 4), (key2556, 4), (key2508, 4)]

def rawRow17991 : Integer.Sparse Key := [(key2496, 4), (key2421, 4), (key2550, 4), (key2496, -2), (key2508, -2), (key2428, -2), (key2556, -2), (key2429, -2), (key2550, -2), (key2496, -2), (key2508, -2), (key2428, -2), (key2556, -2), (key2429, -2), (key2550, -2), (key2508, 4), (key2442, 4), (key2556, 4)]

def rawRow17992 : Integer.Sparse Key := [(key2496, 4), (key2550, 4), (key2421, 4), (key2508, -2), (key2496, -2), (key2556, -2), (key2428, -2), (key2550, -2), (key2429, -2), (key2508, -2), (key2496, -2), (key2556, -2), (key2428, -2), (key2550, -2), (key2429, -2), (key2508, 4), (key2556, 4), (key2442, 4)]

def rawRow17993 : Integer.Sparse Key := [(key2550, 4), (key2421, 4), (key2496, 4), (key2550, -2), (key2556, -2), (key2429, -2), (key2508, -2), (key2428, -2), (key2496, -2), (key2550, -2), (key2556, -2), (key2429, -2), (key2508, -2), (key2428, -2), (key2496, -2), (key2556, 4), (key2442, 4), (key2508, 4)]

def rawRow17994 : Integer.Sparse Key := [(key2550, 4), (key2496, 4), (key2421, 4), (key2556, -2), (key2550, -2), (key2508, -2), (key2429, -2), (key2496, -2), (key2428, -2), (key2556, -2), (key2550, -2), (key2508, -2), (key2429, -2), (key2496, -2), (key2428, -2), (key2556, 4), (key2508, 4), (key2442, 4)]

def rawRow17995 : Integer.Sparse Key := [(key2428, 4), (key2428, 4), (key2556, 4), (key2421, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2550, -2), (key2428, -2), (key2442, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2556, -2), (key2429, 4), (key2429, 4), (key2550, 4)]

def rawRow17996 : Integer.Sparse Key := [(key2428, 4), (key2556, 4), (key2428, 4), (key2429, -2), (key2421, -2), (key2550, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2442, -2), (key2428, -2), (key2556, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2429, 4), (key2550, 4), (key2429, 4)]

def rawRow17997 : Integer.Sparse Key := [(key2556, 4), (key2428, 4), (key2428, 4), (key2550, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2421, -2), (key2556, -2), (key2556, -2), (key2442, -2), (key2442, -2), (key2428, -2), (key2428, -2), (key2550, 4), (key2429, 4), (key2429, 4)]

def rawRow17998 : Integer.Sparse Key := [(key2429, 4), (key2429, 4), (key2508, 4), (key2421, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2496, -2), (key2429, -2), (key2442, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2508, -2), (key2428, 4), (key2428, 4), (key2496, 4)]

def rawRow17999 : Integer.Sparse Key := [(key2429, 4), (key2508, 4), (key2429, 4), (key2428, -2), (key2421, -2), (key2496, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2442, -2), (key2429, -2), (key2508, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2428, 4), (key2496, 4), (key2428, 4)]

def rawRow18000 : Integer.Sparse Key := [(key2508, 4), (key2429, 4), (key2429, 4), (key2496, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2421, -2), (key2508, -2), (key2508, -2), (key2442, -2), (key2442, -2), (key2429, -2), (key2429, -2), (key2496, 4), (key2428, 4), (key2428, 4)]

def rawRow18001 : Integer.Sparse Key := [(key2428, 4), (key2428, 4), (key2556, 4), (key2428, -2), (key2442, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2556, -2), (key2421, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2550, -2), (key2429, 4), (key2429, 4), (key2550, 4)]

def rawRow18002 : Integer.Sparse Key := [(key2428, 4), (key2556, 4), (key2428, 4), (key2442, -2), (key2428, -2), (key2556, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2429, 4), (key2550, 4), (key2429, 4)]

def rawRow18003 : Integer.Sparse Key := [(key2556, 4), (key2428, 4), (key2428, 4), (key2556, -2), (key2556, -2), (key2442, -2), (key2442, -2), (key2428, -2), (key2428, -2), (key2550, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2421, -2), (key2550, 4), (key2429, 4), (key2429, 4)]

def rawRow18004 : Integer.Sparse Key := [(key2442, 4), (key2442, 4), (key2442, 4), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2421, 4), (key2421, 4), (key2421, 4)]

def rawRow18005 : Integer.Sparse Key := [(key2429, 4), (key2429, 4), (key2508, 4), (key2429, -2), (key2442, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2508, -2), (key2421, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2496, -2), (key2428, 4), (key2428, 4), (key2496, 4)]

def rawRow18006 : Integer.Sparse Key := [(key2429, 4), (key2508, 4), (key2429, 4), (key2442, -2), (key2429, -2), (key2508, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2428, 4), (key2496, 4), (key2428, 4)]

def rawRow18007 : Integer.Sparse Key := [(key2508, 4), (key2429, 4), (key2429, 4), (key2508, -2), (key2508, -2), (key2442, -2), (key2442, -2), (key2429, -2), (key2429, -2), (key2496, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2421, -2), (key2496, 4), (key2428, 4), (key2428, 4)]

def rawRow18008 : Integer.Sparse Key := [(key2442, 4), (key2442, 4), (key2442, 4), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2421, 4), (key2421, 4), (key2421, 4)]

def rawRow18009 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, -2), (key1060, 6), (key1049, -2), (key1052, -2), (key1060, -2), (key1049, 2), (key1052, 2), (key1135, 2), (key1205, 2), (key1140, 2), (key1207, 2), (key1060, -2), (key1140, -2), (key1207, -2), (key1060, 6), (key1060, -2), (key1140, -2), (key1207, -2)]

def rawRow18010 : Integer.Sparse Key := [(key1052, -2), (key1049, -2), (key1060, -2), (key1060, 6), (key1052, -2), (key1049, -2), (key1060, -2), (key1052, 2), (key1049, 2), (key1205, 2), (key1135, 2), (key1207, 2), (key1140, 2), (key1060, -2), (key1207, -2), (key1140, -2), (key1060, 6), (key1060, -2), (key1207, -2), (key1140, -2)]

def rawRow18011 : Integer.Sparse Key := [(key1049, -2), (key1060, -2), (key1052, -2), (key1060, 6), (key1049, -2), (key1060, -2), (key1052, -2), (key1135, 2), (key1140, 2), (key1049, 2), (key1207, 2), (key1052, 2), (key1205, 2), (key1140, -2), (key1060, -2), (key1207, -2), (key1060, 6), (key1140, -2), (key1060, -2), (key1207, -2)]

def rawRow18012 : Integer.Sparse Key := [(key1060, -2), (key1049, -2), (key1052, -2), (key1060, 6), (key1060, -2), (key1049, -2), (key1052, -2), (key1140, 2), (key1135, 2), (key1207, 2), (key1049, 2), (key1205, 2), (key1052, 2), (key1140, -2), (key1207, -2), (key1060, -2), (key1060, 6), (key1140, -2), (key1207, -2), (key1060, -2)]

def rawRow18013 : Integer.Sparse Key := [(key1052, -2), (key1060, -2), (key1049, -2), (key1060, 6), (key1052, -2), (key1060, -2), (key1049, -2), (key1205, 2), (key1207, 2), (key1052, 2), (key1140, 2), (key1049, 2), (key1135, 2), (key1207, -2), (key1060, -2), (key1140, -2), (key1060, 6), (key1207, -2), (key1060, -2), (key1140, -2)]

def rawRow18014 : Integer.Sparse Key := [(key1060, -2), (key1052, -2), (key1049, -2), (key1060, 6), (key1060, -2), (key1052, -2), (key1049, -2), (key1207, 2), (key1205, 2), (key1140, 2), (key1052, 2), (key1135, 2), (key1049, 2), (key1207, -2), (key1140, -2), (key1060, -2), (key1060, 6), (key1207, -2), (key1140, -2), (key1060, -2)]

def rawRow18015 : Integer.Sparse Key := [(key1049, -2), (key1060, -2), (key1060, -2), (key1052, 6), (key1135, -2), (key1140, -2), (key1140, -2), (key1049, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1207, 2), (key1052, -2), (key1052, -2), (key1205, -2), (key1140, 6), (key1060, -2), (key1060, -2), (key1207, -2)]

def rawRow18016 : Integer.Sparse Key := [(key1060, -2), (key1049, -2), (key1060, -2), (key1052, 6), (key1140, -2), (key1135, -2), (key1140, -2), (key1060, 2), (key1049, 2), (key1207, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1052, -2), (key1205, -2), (key1052, -2), (key1140, 6), (key1060, -2), (key1207, -2), (key1060, -2)]

def rawRow18017 : Integer.Sparse Key := [(key1060, -2), (key1060, -2), (key1049, -2), (key1052, 6), (key1140, -2), (key1140, -2), (key1135, -2), (key1207, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1049, 2), (key1205, -2), (key1052, -2), (key1052, -2), (key1140, 6), (key1207, -2), (key1060, -2), (key1060, -2)]

def rawRow18018 : Integer.Sparse Key := [(key1052, -2), (key1060, -2), (key1060, -2), (key1049, 6), (key1205, -2), (key1207, -2), (key1207, -2), (key1052, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1140, 2), (key1049, -2), (key1049, -2), (key1135, -2), (key1207, 6), (key1060, -2), (key1060, -2), (key1140, -2)]

def rawRow18019 : Integer.Sparse Key := [(key1060, -2), (key1052, -2), (key1060, -2), (key1049, 6), (key1207, -2), (key1205, -2), (key1207, -2), (key1060, 2), (key1052, 2), (key1140, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1049, -2), (key1135, -2), (key1049, -2), (key1207, 6), (key1060, -2), (key1140, -2), (key1060, -2)]

def rawRow18020 : Integer.Sparse Key := [(key1060, -2), (key1060, -2), (key1052, -2), (key1049, 6), (key1207, -2), (key1207, -2), (key1205, -2), (key1140, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1052, 2), (key1135, -2), (key1049, -2), (key1049, -2), (key1207, 6), (key1140, -2), (key1060, -2), (key1060, -2)]

def rawRow18021 : Integer.Sparse Key := [(key1135, -2), (key1140, -2), (key1140, -2), (key1140, 6), (key1049, -2), (key1060, -2), (key1060, -2), (key1049, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1207, 2), (key1060, -2), (key1060, -2), (key1207, -2), (key1052, 6), (key1052, -2), (key1052, -2), (key1205, -2)]

def rawRow18022 : Integer.Sparse Key := [(key1140, -2), (key1135, -2), (key1140, -2), (key1140, 6), (key1060, -2), (key1049, -2), (key1060, -2), (key1060, 2), (key1049, 2), (key1207, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1060, -2), (key1207, -2), (key1060, -2), (key1052, 6), (key1052, -2), (key1205, -2), (key1052, -2)]

def rawRow18023 : Integer.Sparse Key := [(key1140, -2), (key1140, -2), (key1135, -2), (key1140, 6), (key1060, -2), (key1060, -2), (key1049, -2), (key1207, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1049, 2), (key1207, -2), (key1060, -2), (key1060, -2), (key1052, 6), (key1205, -2), (key1052, -2), (key1052, -2)]

def rawRow18024 : Integer.Sparse Key := [(key1140, -2), (key1140, -2), (key1140, -2), (key1135, 6), (key1207, -2), (key1207, -2), (key1207, -2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1049, -2), (key1049, -2), (key1049, -2), (key1205, 6), (key1052, -2), (key1052, -2), (key1052, -2)]

def rawRow18025 : Integer.Sparse Key := [(key1205, -2), (key1207, -2), (key1207, -2), (key1207, 6), (key1052, -2), (key1060, -2), (key1060, -2), (key1052, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1140, 2), (key1060, -2), (key1060, -2), (key1140, -2), (key1049, 6), (key1049, -2), (key1049, -2), (key1135, -2)]

def rawRow18026 : Integer.Sparse Key := [(key1207, -2), (key1205, -2), (key1207, -2), (key1207, 6), (key1060, -2), (key1052, -2), (key1060, -2), (key1060, 2), (key1052, 2), (key1140, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1060, -2), (key1140, -2), (key1060, -2), (key1049, 6), (key1049, -2), (key1135, -2), (key1049, -2)]

def rawRow18027 : Integer.Sparse Key := [(key1207, -2), (key1207, -2), (key1205, -2), (key1207, 6), (key1060, -2), (key1060, -2), (key1052, -2), (key1140, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1052, 2), (key1140, -2), (key1060, -2), (key1060, -2), (key1049, 6), (key1135, -2), (key1049, -2), (key1049, -2)]

def rawRow18028 : Integer.Sparse Key := [(key1207, -2), (key1207, -2), (key1207, -2), (key1205, 6), (key1140, -2), (key1140, -2), (key1140, -2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1052, -2), (key1052, -2), (key1052, -2), (key1135, 6), (key1049, -2), (key1049, -2), (key1049, -2)]

def rawRow18029 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, -2), (key2425, 6), (key2415, -2), (key2418, -2), (key2425, -2), (key2415, 2), (key2418, 2), (key2488, 2), (key2547, 2), (key2493, 2), (key2549, 2), (key2425, -2), (key2493, -2), (key2549, -2), (key2425, 6), (key2425, -2), (key2493, -2), (key2549, -2)]

def rawRow18030 : Integer.Sparse Key := [(key2418, -2), (key2415, -2), (key2425, -2), (key2425, 6), (key2418, -2), (key2415, -2), (key2425, -2), (key2418, 2), (key2415, 2), (key2547, 2), (key2488, 2), (key2549, 2), (key2493, 2), (key2425, -2), (key2549, -2), (key2493, -2), (key2425, 6), (key2425, -2), (key2549, -2), (key2493, -2)]

def rawRow18031 : Integer.Sparse Key := [(key2415, -2), (key2425, -2), (key2418, -2), (key2425, 6), (key2415, -2), (key2425, -2), (key2418, -2), (key2488, 2), (key2493, 2), (key2415, 2), (key2549, 2), (key2418, 2), (key2547, 2), (key2493, -2), (key2425, -2), (key2549, -2), (key2425, 6), (key2493, -2), (key2425, -2), (key2549, -2)]

def rawRow18032 : Integer.Sparse Key := [(key2425, -2), (key2415, -2), (key2418, -2), (key2425, 6), (key2425, -2), (key2415, -2), (key2418, -2), (key2493, 2), (key2488, 2), (key2549, 2), (key2415, 2), (key2547, 2), (key2418, 2), (key2493, -2), (key2549, -2), (key2425, -2), (key2425, 6), (key2493, -2), (key2549, -2), (key2425, -2)]

def rawRow18033 : Integer.Sparse Key := [(key2418, -2), (key2425, -2), (key2415, -2), (key2425, 6), (key2418, -2), (key2425, -2), (key2415, -2), (key2547, 2), (key2549, 2), (key2418, 2), (key2493, 2), (key2415, 2), (key2488, 2), (key2549, -2), (key2425, -2), (key2493, -2), (key2425, 6), (key2549, -2), (key2425, -2), (key2493, -2)]

def rawRow18034 : Integer.Sparse Key := [(key2425, -2), (key2418, -2), (key2415, -2), (key2425, 6), (key2425, -2), (key2418, -2), (key2415, -2), (key2549, 2), (key2547, 2), (key2493, 2), (key2418, 2), (key2488, 2), (key2415, 2), (key2549, -2), (key2493, -2), (key2425, -2), (key2425, 6), (key2549, -2), (key2493, -2), (key2425, -2)]

def rawRow18035 : Integer.Sparse Key := [(key2415, -2), (key2425, -2), (key2425, -2), (key2418, 6), (key2488, -2), (key2493, -2), (key2493, -2), (key2415, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2549, 2), (key2418, -2), (key2418, -2), (key2547, -2), (key2493, 6), (key2425, -2), (key2425, -2), (key2549, -2)]

def rawRow18036 : Integer.Sparse Key := [(key2425, -2), (key2415, -2), (key2425, -2), (key2418, 6), (key2493, -2), (key2488, -2), (key2493, -2), (key2425, 2), (key2415, 2), (key2549, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2418, -2), (key2547, -2), (key2418, -2), (key2493, 6), (key2425, -2), (key2549, -2), (key2425, -2)]

def rawRow18037 : Integer.Sparse Key := [(key2425, -2), (key2425, -2), (key2415, -2), (key2418, 6), (key2493, -2), (key2493, -2), (key2488, -2), (key2549, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2415, 2), (key2547, -2), (key2418, -2), (key2418, -2), (key2493, 6), (key2549, -2), (key2425, -2), (key2425, -2)]

def rawRow18038 : Integer.Sparse Key := [(key2418, -2), (key2425, -2), (key2425, -2), (key2415, 6), (key2547, -2), (key2549, -2), (key2549, -2), (key2418, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2493, 2), (key2415, -2), (key2415, -2), (key2488, -2), (key2549, 6), (key2425, -2), (key2425, -2), (key2493, -2)]

def rawRow18039 : Integer.Sparse Key := [(key2425, -2), (key2418, -2), (key2425, -2), (key2415, 6), (key2549, -2), (key2547, -2), (key2549, -2), (key2425, 2), (key2418, 2), (key2493, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2415, -2), (key2488, -2), (key2415, -2), (key2549, 6), (key2425, -2), (key2493, -2), (key2425, -2)]

def rawRow18040 : Integer.Sparse Key := [(key2425, -2), (key2425, -2), (key2418, -2), (key2415, 6), (key2549, -2), (key2549, -2), (key2547, -2), (key2493, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2418, 2), (key2488, -2), (key2415, -2), (key2415, -2), (key2549, 6), (key2493, -2), (key2425, -2), (key2425, -2)]

def rawRow18041 : Integer.Sparse Key := [(key2488, -2), (key2493, -2), (key2493, -2), (key2493, 6), (key2415, -2), (key2425, -2), (key2425, -2), (key2415, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2549, 2), (key2425, -2), (key2425, -2), (key2549, -2), (key2418, 6), (key2418, -2), (key2418, -2), (key2547, -2)]

def rawRow18042 : Integer.Sparse Key := [(key2493, -2), (key2488, -2), (key2493, -2), (key2493, 6), (key2425, -2), (key2415, -2), (key2425, -2), (key2425, 2), (key2415, 2), (key2549, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2425, -2), (key2549, -2), (key2425, -2), (key2418, 6), (key2418, -2), (key2547, -2), (key2418, -2)]

def rawRow18043 : Integer.Sparse Key := [(key2493, -2), (key2493, -2), (key2488, -2), (key2493, 6), (key2425, -2), (key2425, -2), (key2415, -2), (key2549, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2415, 2), (key2549, -2), (key2425, -2), (key2425, -2), (key2418, 6), (key2547, -2), (key2418, -2), (key2418, -2)]

def rawRow18044 : Integer.Sparse Key := [(key2493, -2), (key2493, -2), (key2493, -2), (key2488, 6), (key2549, -2), (key2549, -2), (key2549, -2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2415, -2), (key2415, -2), (key2415, -2), (key2547, 6), (key2418, -2), (key2418, -2), (key2418, -2)]

def rawRow18045 : Integer.Sparse Key := [(key2547, -2), (key2549, -2), (key2549, -2), (key2549, 6), (key2418, -2), (key2425, -2), (key2425, -2), (key2418, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2493, 2), (key2425, -2), (key2425, -2), (key2493, -2), (key2415, 6), (key2415, -2), (key2415, -2), (key2488, -2)]

def rawRow18046 : Integer.Sparse Key := [(key2549, -2), (key2547, -2), (key2549, -2), (key2549, 6), (key2425, -2), (key2418, -2), (key2425, -2), (key2425, 2), (key2418, 2), (key2493, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2425, -2), (key2493, -2), (key2425, -2), (key2415, 6), (key2415, -2), (key2488, -2), (key2415, -2)]

def rawRow18047 : Integer.Sparse Key := [(key2549, -2), (key2549, -2), (key2547, -2), (key2549, 6), (key2425, -2), (key2425, -2), (key2418, -2), (key2493, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2418, 2), (key2493, -2), (key2425, -2), (key2425, -2), (key2415, 6), (key2488, -2), (key2415, -2), (key2415, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18048 : Integer.Sparse Key := [(key2549, -2), (key2549, -2), (key2549, -2), (key2547, 6), (key2493, -2), (key2493, -2), (key2493, -2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2418, -2), (key2418, -2), (key2418, -2), (key2488, 6), (key2415, -2), (key2415, -2), (key2415, -2)]

def rawRow18049 : Integer.Sparse Key := [(key3046, 6), (key3046, -2), (key3060, -2), (key3064, -2), (key3046, 6), (key3046, -2), (key3095, -2), (key3101, -2), (key3046, -2), (key3060, -2), (key3064, -2), (key3046, -2), (key3095, -2), (key3101, -2), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, 2), (key3125, 2)]

def rawRow18050 : Integer.Sparse Key := [(key3046, 6), (key3046, -2), (key3064, -2), (key3060, -2), (key3046, 6), (key3046, -2), (key3101, -2), (key3095, -2), (key3046, -2), (key3064, -2), (key3060, -2), (key3046, -2), (key3101, -2), (key3095, -2), (key3064, 2), (key3060, 2), (key3101, 2), (key3095, 2), (key3125, 2), (key3123, 2)]

def rawRow18051 : Integer.Sparse Key := [(key3046, 6), (key3060, -2), (key3046, -2), (key3064, -2), (key3046, 6), (key3095, -2), (key3046, -2), (key3101, -2), (key3060, -2), (key3046, -2), (key3064, -2), (key3095, -2), (key3046, -2), (key3101, -2), (key3095, 2), (key3123, 2), (key3060, 2), (key3125, 2), (key3064, 2), (key3101, 2)]

def rawRow18052 : Integer.Sparse Key := [(key3046, 6), (key3060, -2), (key3064, -2), (key3046, -2), (key3046, 6), (key3095, -2), (key3101, -2), (key3046, -2), (key3060, -2), (key3064, -2), (key3046, -2), (key3095, -2), (key3101, -2), (key3046, -2), (key3123, 2), (key3095, 2), (key3125, 2), (key3060, 2), (key3101, 2), (key3064, 2)]

def rawRow18053 : Integer.Sparse Key := [(key3046, 6), (key3064, -2), (key3046, -2), (key3060, -2), (key3046, 6), (key3101, -2), (key3046, -2), (key3095, -2), (key3064, -2), (key3046, -2), (key3060, -2), (key3101, -2), (key3046, -2), (key3095, -2), (key3101, 2), (key3125, 2), (key3064, 2), (key3123, 2), (key3060, 2), (key3095, 2)]

def rawRow18054 : Integer.Sparse Key := [(key3046, 6), (key3064, -2), (key3060, -2), (key3046, -2), (key3046, 6), (key3101, -2), (key3095, -2), (key3046, -2), (key3064, -2), (key3060, -2), (key3046, -2), (key3101, -2), (key3095, -2), (key3046, -2), (key3125, 2), (key3101, 2), (key3123, 2), (key3064, 2), (key3095, 2), (key3060, 2)]

def rawRow18055 : Integer.Sparse Key := [(key3060, 6), (key3046, -2), (key3046, -2), (key3064, -2), (key3095, 6), (key3046, -2), (key3046, -2), (key3101, -2), (key3095, -2), (key3095, -2), (key3123, -2), (key3060, -2), (key3060, -2), (key3125, -2), (key3046, 2), (key3064, 2), (key3046, 2), (key3101, 2), (key3064, 2), (key3101, 2)]

def rawRow18056 : Integer.Sparse Key := [(key3060, 6), (key3046, -2), (key3064, -2), (key3046, -2), (key3095, 6), (key3046, -2), (key3101, -2), (key3046, -2), (key3095, -2), (key3123, -2), (key3095, -2), (key3060, -2), (key3125, -2), (key3060, -2), (key3064, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3101, 2), (key3064, 2)]

def rawRow18057 : Integer.Sparse Key := [(key3060, 6), (key3064, -2), (key3046, -2), (key3046, -2), (key3095, 6), (key3101, -2), (key3046, -2), (key3046, -2), (key3123, -2), (key3095, -2), (key3095, -2), (key3125, -2), (key3060, -2), (key3060, -2), (key3101, 2), (key3101, 2), (key3064, 2), (key3064, 2), (key3046, 2), (key3046, 2)]

def rawRow18058 : Integer.Sparse Key := [(key3064, 6), (key3046, -2), (key3046, -2), (key3060, -2), (key3101, 6), (key3046, -2), (key3046, -2), (key3095, -2), (key3101, -2), (key3101, -2), (key3125, -2), (key3064, -2), (key3064, -2), (key3123, -2), (key3046, 2), (key3060, 2), (key3046, 2), (key3095, 2), (key3060, 2), (key3095, 2)]

def rawRow18059 : Integer.Sparse Key := [(key3064, 6), (key3046, -2), (key3060, -2), (key3046, -2), (key3101, 6), (key3046, -2), (key3095, -2), (key3046, -2), (key3101, -2), (key3125, -2), (key3101, -2), (key3064, -2), (key3123, -2), (key3064, -2), (key3060, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3095, 2), (key3060, 2)]

def rawRow18060 : Integer.Sparse Key := [(key3064, 6), (key3060, -2), (key3046, -2), (key3046, -2), (key3101, 6), (key3095, -2), (key3046, -2), (key3046, -2), (key3125, -2), (key3101, -2), (key3101, -2), (key3123, -2), (key3064, -2), (key3064, -2), (key3095, 2), (key3095, 2), (key3060, 2), (key3060, 2), (key3046, 2), (key3046, 2)]

def rawRow18061 : Integer.Sparse Key := [(key3095, 6), (key3095, -2), (key3095, -2), (key3123, -2), (key3060, 6), (key3060, -2), (key3060, -2), (key3125, -2), (key3046, -2), (key3046, -2), (key3064, -2), (key3046, -2), (key3046, -2), (key3101, -2), (key3046, 2), (key3064, 2), (key3046, 2), (key3101, 2), (key3064, 2), (key3101, 2)]

def rawRow18062 : Integer.Sparse Key := [(key3095, 6), (key3095, -2), (key3123, -2), (key3095, -2), (key3060, 6), (key3060, -2), (key3125, -2), (key3060, -2), (key3046, -2), (key3064, -2), (key3046, -2), (key3046, -2), (key3101, -2), (key3046, -2), (key3064, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3101, 2), (key3064, 2)]

def rawRow18063 : Integer.Sparse Key := [(key3095, 6), (key3123, -2), (key3095, -2), (key3095, -2), (key3060, 6), (key3125, -2), (key3060, -2), (key3060, -2), (key3064, -2), (key3046, -2), (key3046, -2), (key3101, -2), (key3046, -2), (key3046, -2), (key3101, 2), (key3101, 2), (key3064, 2), (key3064, 2), (key3046, 2), (key3046, 2)]

def rawRow18064 : Integer.Sparse Key := [(key3123, 6), (key3095, -2), (key3095, -2), (key3095, -2), (key3125, 6), (key3060, -2), (key3060, -2), (key3060, -2), (key3101, -2), (key3101, -2), (key3101, -2), (key3064, -2), (key3064, -2), (key3064, -2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2)]

def rawRow18065 : Integer.Sparse Key := [(key3101, 6), (key3101, -2), (key3101, -2), (key3125, -2), (key3064, 6), (key3064, -2), (key3064, -2), (key3123, -2), (key3046, -2), (key3046, -2), (key3060, -2), (key3046, -2), (key3046, -2), (key3095, -2), (key3046, 2), (key3060, 2), (key3046, 2), (key3095, 2), (key3060, 2), (key3095, 2)]

def rawRow18066 : Integer.Sparse Key := [(key3101, 6), (key3101, -2), (key3125, -2), (key3101, -2), (key3064, 6), (key3064, -2), (key3123, -2), (key3064, -2), (key3046, -2), (key3060, -2), (key3046, -2), (key3046, -2), (key3095, -2), (key3046, -2), (key3060, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3095, 2), (key3060, 2)]

def rawRow18067 : Integer.Sparse Key := [(key3101, 6), (key3125, -2), (key3101, -2), (key3101, -2), (key3064, 6), (key3123, -2), (key3064, -2), (key3064, -2), (key3060, -2), (key3046, -2), (key3046, -2), (key3095, -2), (key3046, -2), (key3046, -2), (key3095, 2), (key3095, 2), (key3060, 2), (key3060, 2), (key3046, 2), (key3046, 2)]

def rawRow18068 : Integer.Sparse Key := [(key3125, 6), (key3101, -2), (key3101, -2), (key3101, -2), (key3123, 6), (key3064, -2), (key3064, -2), (key3064, -2), (key3095, -2), (key3095, -2), (key3095, -2), (key3060, -2), (key3060, -2), (key3060, -2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2)]

def rawRow18069 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, -2), (key1059, 6), (key1048, -2), (key1051, -2), (key1059, -2), (key1048, 2), (key1051, 2), (key1134, 2), (key1204, 2), (key1139, 2), (key1206, 2), (key1059, -2), (key1139, -2), (key1206, -2), (key1059, 6), (key1059, -2), (key1139, -2), (key1206, -2)]

def rawRow18070 : Integer.Sparse Key := [(key1051, -2), (key1048, -2), (key1059, -2), (key1059, 6), (key1051, -2), (key1048, -2), (key1059, -2), (key1051, 2), (key1048, 2), (key1204, 2), (key1134, 2), (key1206, 2), (key1139, 2), (key1059, -2), (key1206, -2), (key1139, -2), (key1059, 6), (key1059, -2), (key1206, -2), (key1139, -2)]

def rawRow18071 : Integer.Sparse Key := [(key1048, -2), (key1059, -2), (key1051, -2), (key1059, 6), (key1048, -2), (key1059, -2), (key1051, -2), (key1134, 2), (key1139, 2), (key1048, 2), (key1206, 2), (key1051, 2), (key1204, 2), (key1139, -2), (key1059, -2), (key1206, -2), (key1059, 6), (key1139, -2), (key1059, -2), (key1206, -2)]

def rawRow18072 : Integer.Sparse Key := [(key1059, -2), (key1048, -2), (key1051, -2), (key1059, 6), (key1059, -2), (key1048, -2), (key1051, -2), (key1139, 2), (key1134, 2), (key1206, 2), (key1048, 2), (key1204, 2), (key1051, 2), (key1139, -2), (key1206, -2), (key1059, -2), (key1059, 6), (key1139, -2), (key1206, -2), (key1059, -2)]

def rawRow18073 : Integer.Sparse Key := [(key1051, -2), (key1059, -2), (key1048, -2), (key1059, 6), (key1051, -2), (key1059, -2), (key1048, -2), (key1204, 2), (key1206, 2), (key1051, 2), (key1139, 2), (key1048, 2), (key1134, 2), (key1206, -2), (key1059, -2), (key1139, -2), (key1059, 6), (key1206, -2), (key1059, -2), (key1139, -2)]

def rawRow18074 : Integer.Sparse Key := [(key1059, -2), (key1051, -2), (key1048, -2), (key1059, 6), (key1059, -2), (key1051, -2), (key1048, -2), (key1206, 2), (key1204, 2), (key1139, 2), (key1051, 2), (key1134, 2), (key1048, 2), (key1206, -2), (key1139, -2), (key1059, -2), (key1059, 6), (key1206, -2), (key1139, -2), (key1059, -2)]

def rawRow18075 : Integer.Sparse Key := [(key1048, -2), (key1059, -2), (key1059, -2), (key1051, 6), (key1134, -2), (key1139, -2), (key1139, -2), (key1048, 2), (key1059, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1206, 2), (key1051, -2), (key1051, -2), (key1204, -2), (key1139, 6), (key1059, -2), (key1059, -2), (key1206, -2)]

def rawRow18076 : Integer.Sparse Key := [(key1059, -2), (key1048, -2), (key1059, -2), (key1051, 6), (key1139, -2), (key1134, -2), (key1139, -2), (key1059, 2), (key1048, 2), (key1206, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1051, -2), (key1204, -2), (key1051, -2), (key1139, 6), (key1059, -2), (key1206, -2), (key1059, -2)]

def rawRow18077 : Integer.Sparse Key := [(key1059, -2), (key1059, -2), (key1048, -2), (key1051, 6), (key1139, -2), (key1139, -2), (key1134, -2), (key1206, 2), (key1206, 2), (key1059, 2), (key1059, 2), (key1048, 2), (key1048, 2), (key1204, -2), (key1051, -2), (key1051, -2), (key1139, 6), (key1206, -2), (key1059, -2), (key1059, -2)]

def rawRow18078 : Integer.Sparse Key := [(key1051, -2), (key1059, -2), (key1059, -2), (key1048, 6), (key1204, -2), (key1206, -2), (key1206, -2), (key1051, 2), (key1059, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1139, 2), (key1048, -2), (key1048, -2), (key1134, -2), (key1206, 6), (key1059, -2), (key1059, -2), (key1139, -2)]

def rawRow18079 : Integer.Sparse Key := [(key1059, -2), (key1051, -2), (key1059, -2), (key1048, 6), (key1206, -2), (key1204, -2), (key1206, -2), (key1059, 2), (key1051, 2), (key1139, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1048, -2), (key1134, -2), (key1048, -2), (key1206, 6), (key1059, -2), (key1139, -2), (key1059, -2)]

def rawRow18080 : Integer.Sparse Key := [(key1059, -2), (key1059, -2), (key1051, -2), (key1048, 6), (key1206, -2), (key1206, -2), (key1204, -2), (key1139, 2), (key1139, 2), (key1059, 2), (key1059, 2), (key1051, 2), (key1051, 2), (key1134, -2), (key1048, -2), (key1048, -2), (key1206, 6), (key1139, -2), (key1059, -2), (key1059, -2)]

def rawRow18081 : Integer.Sparse Key := [(key1134, -2), (key1139, -2), (key1139, -2), (key1139, 6), (key1048, -2), (key1059, -2), (key1059, -2), (key1048, 2), (key1059, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1206, 2), (key1059, -2), (key1059, -2), (key1206, -2), (key1051, 6), (key1051, -2), (key1051, -2), (key1204, -2)]

def rawRow18082 : Integer.Sparse Key := [(key1139, -2), (key1134, -2), (key1139, -2), (key1139, 6), (key1059, -2), (key1048, -2), (key1059, -2), (key1059, 2), (key1048, 2), (key1206, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1059, -2), (key1206, -2), (key1059, -2), (key1051, 6), (key1051, -2), (key1204, -2), (key1051, -2)]

def rawRow18083 : Integer.Sparse Key := [(key1139, -2), (key1139, -2), (key1134, -2), (key1139, 6), (key1059, -2), (key1059, -2), (key1048, -2), (key1206, 2), (key1206, 2), (key1059, 2), (key1059, 2), (key1048, 2), (key1048, 2), (key1206, -2), (key1059, -2), (key1059, -2), (key1051, 6), (key1204, -2), (key1051, -2), (key1051, -2)]

def rawRow18084 : Integer.Sparse Key := [(key1139, -2), (key1139, -2), (key1139, -2), (key1134, 6), (key1206, -2), (key1206, -2), (key1206, -2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1048, -2), (key1048, -2), (key1048, -2), (key1204, 6), (key1051, -2), (key1051, -2), (key1051, -2)]

def rawRow18085 : Integer.Sparse Key := [(key1204, -2), (key1206, -2), (key1206, -2), (key1206, 6), (key1051, -2), (key1059, -2), (key1059, -2), (key1051, 2), (key1059, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1139, 2), (key1059, -2), (key1059, -2), (key1139, -2), (key1048, 6), (key1048, -2), (key1048, -2), (key1134, -2)]

def rawRow18086 : Integer.Sparse Key := [(key1206, -2), (key1204, -2), (key1206, -2), (key1206, 6), (key1059, -2), (key1051, -2), (key1059, -2), (key1059, 2), (key1051, 2), (key1139, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1059, -2), (key1139, -2), (key1059, -2), (key1048, 6), (key1048, -2), (key1134, -2), (key1048, -2)]

def rawRow18087 : Integer.Sparse Key := [(key1206, -2), (key1206, -2), (key1204, -2), (key1206, 6), (key1059, -2), (key1059, -2), (key1051, -2), (key1139, 2), (key1139, 2), (key1059, 2), (key1059, 2), (key1051, 2), (key1051, 2), (key1139, -2), (key1059, -2), (key1059, -2), (key1048, 6), (key1134, -2), (key1048, -2), (key1048, -2)]

def rawRow18088 : Integer.Sparse Key := [(key1206, -2), (key1206, -2), (key1206, -2), (key1204, 6), (key1139, -2), (key1139, -2), (key1139, -2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1051, -2), (key1051, -2), (key1051, -2), (key1134, 6), (key1048, -2), (key1048, -2), (key1048, -2)]

def rawRow18089 : Integer.Sparse Key := [(key1056, 4), (key1144, 4), (key1208, 4), (key1064, -2), (key1065, -2), (key1144, -2), (key1208, -2), (key1158, -2), (key1215, -2), (key1064, -2), (key1065, -2), (key1144, -2), (key1208, -2), (key1158, -2), (key1215, -2), (key1079, 4), (key1158, 4), (key1215, 4)]

def rawRow18090 : Integer.Sparse Key := [(key1056, 4), (key1208, 4), (key1144, 4), (key1065, -2), (key1064, -2), (key1208, -2), (key1144, -2), (key1215, -2), (key1158, -2), (key1065, -2), (key1064, -2), (key1208, -2), (key1144, -2), (key1215, -2), (key1158, -2), (key1079, 4), (key1215, 4), (key1158, 4)]

def rawRow18091 : Integer.Sparse Key := [(key1144, 4), (key1056, 4), (key1208, 4), (key1144, -2), (key1158, -2), (key1064, -2), (key1215, -2), (key1065, -2), (key1208, -2), (key1144, -2), (key1158, -2), (key1064, -2), (key1215, -2), (key1065, -2), (key1208, -2), (key1158, 4), (key1079, 4), (key1215, 4)]

def rawRow18092 : Integer.Sparse Key := [(key1144, 4), (key1208, 4), (key1056, 4), (key1158, -2), (key1144, -2), (key1215, -2), (key1064, -2), (key1208, -2), (key1065, -2), (key1158, -2), (key1144, -2), (key1215, -2), (key1064, -2), (key1208, -2), (key1065, -2), (key1158, 4), (key1215, 4), (key1079, 4)]

def rawRow18093 : Integer.Sparse Key := [(key1208, 4), (key1056, 4), (key1144, 4), (key1208, -2), (key1215, -2), (key1065, -2), (key1158, -2), (key1064, -2), (key1144, -2), (key1208, -2), (key1215, -2), (key1065, -2), (key1158, -2), (key1064, -2), (key1144, -2), (key1215, 4), (key1079, 4), (key1158, 4)]

def rawRow18094 : Integer.Sparse Key := [(key1208, 4), (key1144, 4), (key1056, 4), (key1215, -2), (key1208, -2), (key1158, -2), (key1065, -2), (key1144, -2), (key1064, -2), (key1215, -2), (key1208, -2), (key1158, -2), (key1065, -2), (key1144, -2), (key1064, -2), (key1215, 4), (key1158, 4), (key1079, 4)]

def rawRow18095 : Integer.Sparse Key := [(key1064, 4), (key1064, 4), (key1215, 4), (key1056, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1208, -2), (key1064, -2), (key1079, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1215, -2), (key1065, 4), (key1065, 4), (key1208, 4)]

def rawRow18096 : Integer.Sparse Key := [(key1064, 4), (key1215, 4), (key1064, 4), (key1065, -2), (key1056, -2), (key1208, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1079, -2), (key1064, -2), (key1215, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1065, 4), (key1208, 4), (key1065, 4)]

def rawRow18097 : Integer.Sparse Key := [(key1215, 4), (key1064, 4), (key1064, 4), (key1208, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1056, -2), (key1215, -2), (key1215, -2), (key1079, -2), (key1079, -2), (key1064, -2), (key1064, -2), (key1208, 4), (key1065, 4), (key1065, 4)]

def rawRow18098 : Integer.Sparse Key := [(key1065, 4), (key1065, 4), (key1158, 4), (key1056, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1144, -2), (key1065, -2), (key1079, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1158, -2), (key1064, 4), (key1064, 4), (key1144, 4)]

def rawRow18099 : Integer.Sparse Key := [(key1065, 4), (key1158, 4), (key1065, 4), (key1064, -2), (key1056, -2), (key1144, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1079, -2), (key1065, -2), (key1158, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1064, 4), (key1144, 4), (key1064, 4)]

def rawRow18100 : Integer.Sparse Key := [(key1158, 4), (key1065, 4), (key1065, 4), (key1144, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1056, -2), (key1158, -2), (key1158, -2), (key1079, -2), (key1079, -2), (key1065, -2), (key1065, -2), (key1144, 4), (key1064, 4), (key1064, 4)]

def rawRow18101 : Integer.Sparse Key := [(key1064, 4), (key1064, 4), (key1215, 4), (key1064, -2), (key1079, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1215, -2), (key1056, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1208, -2), (key1065, 4), (key1065, 4), (key1208, 4)]

def rawRow18102 : Integer.Sparse Key := [(key1064, 4), (key1215, 4), (key1064, 4), (key1079, -2), (key1064, -2), (key1215, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1065, 4), (key1208, 4), (key1065, 4)]

def rawRow18103 : Integer.Sparse Key := [(key1215, 4), (key1064, 4), (key1064, 4), (key1215, -2), (key1215, -2), (key1079, -2), (key1079, -2), (key1064, -2), (key1064, -2), (key1208, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1056, -2), (key1208, 4), (key1065, 4), (key1065, 4)]

def rawRow18104 : Integer.Sparse Key := [(key1079, 4), (key1079, 4), (key1079, 4), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1056, 4), (key1056, 4), (key1056, 4)]

def rawRow18105 : Integer.Sparse Key := [(key1065, 4), (key1065, 4), (key1158, 4), (key1065, -2), (key1079, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1158, -2), (key1056, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1144, -2), (key1064, 4), (key1064, 4), (key1144, 4)]

def rawRow18106 : Integer.Sparse Key := [(key1065, 4), (key1158, 4), (key1065, 4), (key1079, -2), (key1065, -2), (key1158, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1064, 4), (key1144, 4), (key1064, 4)]

def rawRow18107 : Integer.Sparse Key := [(key1158, 4), (key1065, 4), (key1065, 4), (key1158, -2), (key1158, -2), (key1079, -2), (key1079, -2), (key1065, -2), (key1065, -2), (key1144, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1056, -2), (key1144, 4), (key1064, 4), (key1064, 4)]

def rawRow18108 : Integer.Sparse Key := [(key1079, 4), (key1079, 4), (key1079, 4), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1056, 4), (key1056, 4), (key1056, 4)]

def rawRow18109 : Integer.Sparse Key := [(key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2690, 2), (key2819, 2), (key2956, 2), (key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2711, 2), (key2741, 2), (key2814, 2), (key2954, 2), (key2901, 2), (key2980, 2), (key2716, -1), (key2743, -1), (key2819, -1), (key2956, -1), (key2901, -1), (key2980, -1), (key2690, 2), (key2819, 2), (key2956, 2), (key2716, -1), (key2743, -1), (key2819, -1), (key2956, -1), (key2901, -1), (key2980, -1)]

def rawRow18110 : Integer.Sparse Key := [(key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2690, 2), (key2956, 2), (key2819, 2), (key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2741, 2), (key2711, 2), (key2954, 2), (key2814, 2), (key2980, 2), (key2901, 2), (key2743, -1), (key2716, -1), (key2956, -1), (key2819, -1), (key2980, -1), (key2901, -1), (key2690, 2), (key2956, 2), (key2819, 2), (key2743, -1), (key2716, -1), (key2956, -1), (key2819, -1), (key2980, -1), (key2901, -1)]

def rawRow18111 : Integer.Sparse Key := [(key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2819, 2), (key2690, 2), (key2956, 2), (key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2814, 2), (key2901, 2), (key2711, 2), (key2980, 2), (key2741, 2), (key2954, 2), (key2819, -1), (key2901, -1), (key2716, -1), (key2980, -1), (key2743, -1), (key2956, -1), (key2819, 2), (key2690, 2), (key2956, 2), (key2819, -1), (key2901, -1), (key2716, -1), (key2980, -1), (key2743, -1), (key2956, -1)]

def rawRow18112 : Integer.Sparse Key := [(key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2819, 2), (key2956, 2), (key2690, 2), (key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2901, 2), (key2814, 2), (key2980, 2), (key2711, 2), (key2954, 2), (key2741, 2), (key2901, -1), (key2819, -1), (key2980, -1), (key2716, -1), (key2956, -1), (key2743, -1), (key2819, 2), (key2956, 2), (key2690, 2), (key2901, -1), (key2819, -1), (key2980, -1), (key2716, -1), (key2956, -1), (key2743, -1)]

def rawRow18113 : Integer.Sparse Key := [(key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2956, 2), (key2690, 2), (key2819, 2), (key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2954, 2), (key2980, 2), (key2741, 2), (key2901, 2), (key2711, 2), (key2814, 2), (key2956, -1), (key2980, -1), (key2743, -1), (key2901, -1), (key2716, -1), (key2819, -1), (key2956, 2), (key2690, 2), (key2819, 2), (key2956, -1), (key2980, -1), (key2743, -1), (key2901, -1), (key2716, -1), (key2819, -1)]

def rawRow18114 : Integer.Sparse Key := [(key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2956, 2), (key2819, 2), (key2690, 2), (key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2980, 2), (key2954, 2), (key2901, 2), (key2741, 2), (key2814, 2), (key2711, 2), (key2980, -1), (key2956, -1), (key2901, -1), (key2743, -1), (key2819, -1), (key2716, -1), (key2956, 2), (key2819, 2), (key2690, 2), (key2980, -1), (key2956, -1), (key2901, -1), (key2743, -1), (key2819, -1), (key2716, -1)]

def rawRow18115 : Integer.Sparse Key := [(key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2683, 2), (key2683, 2), (key2954, 2), (key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2), (key2683, -1), (key2741, -1), (key2683, -1), (key2954, -1), (key2741, -1), (key2954, -1), (key2716, 2), (key2716, 2), (key2980, 2), (key2690, -1), (key2743, -1), (key2690, -1), (key2956, -1), (key2743, -1), (key2956, -1)]

def rawRow18116 : Integer.Sparse Key := [(key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2683, 2), (key2954, 2), (key2683, 2), (key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2741, -1), (key2683, -1), (key2954, -1), (key2683, -1), (key2954, -1), (key2741, -1), (key2716, 2), (key2980, 2), (key2716, 2), (key2743, -1), (key2690, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2743, -1)]

def rawRow18117 : Integer.Sparse Key := [(key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2954, 2), (key2683, 2), (key2683, 2), (key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2), (key2954, -1), (key2954, -1), (key2741, -1), (key2741, -1), (key2683, -1), (key2683, -1), (key2980, 2), (key2716, 2), (key2716, 2), (key2956, -1), (key2956, -1), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1)]

def rawRow18118 : Integer.Sparse Key := [(key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2680, 2), (key2680, 2), (key2814, 2), (key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2), (key2680, -1), (key2711, -1), (key2680, -1), (key2814, -1), (key2711, -1), (key2814, -1), (key2743, 2), (key2743, 2), (key2901, 2), (key2690, -1), (key2716, -1), (key2690, -1), (key2819, -1), (key2716, -1), (key2819, -1)]

def rawRow18119 : Integer.Sparse Key := [(key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2680, 2), (key2814, 2), (key2680, 2), (key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2711, -1), (key2680, -1), (key2814, -1), (key2680, -1), (key2814, -1), (key2711, -1), (key2743, 2), (key2901, 2), (key2743, 2), (key2716, -1), (key2690, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2716, -1)]

def rawRow18120 : Integer.Sparse Key := [(key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2814, 2), (key2680, 2), (key2680, 2), (key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2), (key2814, -1), (key2814, -1), (key2711, -1), (key2711, -1), (key2680, -1), (key2680, -1), (key2901, 2), (key2743, 2), (key2743, 2), (key2819, -1), (key2819, -1), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1)]

def rawRow18121 : Integer.Sparse Key := [(key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2716, 2), (key2716, 2), (key2980, 2), (key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2), (key2690, -1), (key2743, -1), (key2690, -1), (key2956, -1), (key2743, -1), (key2956, -1), (key2683, 2), (key2683, 2), (key2954, 2), (key2683, -1), (key2741, -1), (key2683, -1), (key2954, -1), (key2741, -1), (key2954, -1)]

def rawRow18122 : Integer.Sparse Key := [(key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2716, 2), (key2980, 2), (key2716, 2), (key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2743, -1), (key2690, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2743, -1), (key2683, 2), (key2954, 2), (key2683, 2), (key2741, -1), (key2683, -1), (key2954, -1), (key2683, -1), (key2954, -1), (key2741, -1)]

def rawRow18123 : Integer.Sparse Key := [(key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2980, 2), (key2716, 2), (key2716, 2), (key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2), (key2956, -1), (key2956, -1), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2954, 2), (key2683, 2), (key2683, 2), (key2954, -1), (key2954, -1), (key2741, -1), (key2741, -1), (key2683, -1), (key2683, -1)]

def rawRow18124 : Integer.Sparse Key := [(key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2711, 2), (key2711, 2), (key2711, 2), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2741, 2), (key2741, 2), (key2741, 2), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1)]

def rawRow18125 : Integer.Sparse Key := [(key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2743, 2), (key2743, 2), (key2901, 2), (key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2), (key2690, -1), (key2716, -1), (key2690, -1), (key2819, -1), (key2716, -1), (key2819, -1), (key2680, 2), (key2680, 2), (key2814, 2), (key2680, -1), (key2711, -1), (key2680, -1), (key2814, -1), (key2711, -1), (key2814, -1)]

def rawRow18126 : Integer.Sparse Key := [(key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2743, 2), (key2901, 2), (key2743, 2), (key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2716, -1), (key2690, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2716, -1), (key2680, 2), (key2814, 2), (key2680, 2), (key2711, -1), (key2680, -1), (key2814, -1), (key2680, -1), (key2814, -1), (key2711, -1)]

def rawRow18127 : Integer.Sparse Key := [(key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2901, 2), (key2743, 2), (key2743, 2), (key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2), (key2819, -1), (key2819, -1), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2814, 2), (key2680, 2), (key2680, 2), (key2814, -1), (key2814, -1), (key2711, -1), (key2711, -1), (key2680, -1), (key2680, -1)]

def rawRow18128 : Integer.Sparse Key := [(key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2741, 2), (key2741, 2), (key2741, 2), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2711, 2), (key2711, 2), (key2711, 2), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1)]

def rawRow18129 : Integer.Sparse Key := [(key3080, 4), (key3085, 4), (key3087, 4), (key3085, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3100, 12)]

def rawRow18130 : Integer.Sparse Key := [(key3080, 4), (key3087, 4), (key3085, 4), (key3087, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3100, 12)]

def rawRow18131 : Integer.Sparse Key := [(key3085, 4), (key3080, 4), (key3087, 4), (key3085, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3100, 12)]

def rawRow18132 : Integer.Sparse Key := [(key3085, 4), (key3087, 4), (key3080, 4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, 12)]

def rawRow18133 : Integer.Sparse Key := [(key3087, 4), (key3080, 4), (key3085, 4), (key3087, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3100, 12)]

def rawRow18134 : Integer.Sparse Key := [(key3087, 4), (key3085, 4), (key3080, 4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, 12)]

def rawRow18135 : Integer.Sparse Key := [(key3085, 4), (key3085, 4), (key3100, 4), (key3080, -4), (key3087, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3100, -4), (key3087, 12)]

def rawRow18136 : Integer.Sparse Key := [(key3085, 4), (key3100, 4), (key3085, 4), (key3087, -4), (key3080, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3100, -4), (key3087, 12)]

def rawRow18137 : Integer.Sparse Key := [(key3100, 4), (key3085, 4), (key3085, 4), (key3087, -4), (key3087, -4), (key3080, -4), (key3100, -4), (key3100, -4), (key3085, -4), (key3087, 12)]

def rawRow18138 : Integer.Sparse Key := [(key3087, 4), (key3087, 4), (key3100, 4), (key3080, -4), (key3085, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3100, -4), (key3085, 12)]

def rawRow18139 : Integer.Sparse Key := [(key3087, 4), (key3100, 4), (key3087, 4), (key3085, -4), (key3080, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3100, -4), (key3085, 12)]

def rawRow18140 : Integer.Sparse Key := [(key3100, 4), (key3087, 4), (key3087, 4), (key3085, -4), (key3085, -4), (key3080, -4), (key3100, -4), (key3100, -4), (key3087, -4), (key3085, 12)]

def rawRow18141 : Integer.Sparse Key := [(key3085, 4), (key3085, 4), (key3100, 4), (key3085, -4), (key3100, -4), (key3100, -4), (key3080, -4), (key3087, -4), (key3087, -4), (key3087, 12)]

def rawRow18142 : Integer.Sparse Key := [(key3085, 4), (key3100, 4), (key3085, 4), (key3100, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3080, -4), (key3087, -4), (key3087, 12)]

def rawRow18143 : Integer.Sparse Key := [(key3100, 4), (key3085, 4), (key3085, 4), (key3100, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3087, -4), (key3080, -4), (key3087, 12)]

def rawRow18144 : Integer.Sparse Key := [(key3100, 4), (key3100, 4), (key3100, 4), (key3085, -4), (key3085, -4), (key3085, -4), (key3087, -4), (key3087, -4), (key3087, -4), (key3080, 12)]

def rawRow18145 : Integer.Sparse Key := [(key3087, 4), (key3087, 4), (key3100, 4), (key3087, -4), (key3100, -4), (key3100, -4), (key3080, -4), (key3085, -4), (key3085, -4), (key3085, 12)]

def rawRow18146 : Integer.Sparse Key := [(key3087, 4), (key3100, 4), (key3087, 4), (key3100, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3080, -4), (key3085, -4), (key3085, 12)]

def rawRow18147 : Integer.Sparse Key := [(key3100, 4), (key3087, 4), (key3087, 4), (key3100, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3085, -4), (key3080, -4), (key3085, 12)]

def rawRow18148 : Integer.Sparse Key := [(key3100, 4), (key3100, 4), (key3100, 4), (key3087, -4), (key3087, -4), (key3087, -4), (key3085, -4), (key3085, -4), (key3085, -4), (key3080, 12)]

def rawRow18149 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, -2), (key2424, 6), (key3033, -2), (key3035, -2), (key3039, -2), (key3033, 2), (key3035, 2), (key3120, 2), (key3128, 2), (key3131, 2), (key3138, 2), (key3039, -2), (key3131, -2), (key3138, -2), (key3039, 6), (key3039, -2), (key3131, -2), (key3138, -2)]

def rawRow18150 : Integer.Sparse Key := [(key2417, -2), (key2414, -2), (key2424, -2), (key2424, 6), (key3035, -2), (key3033, -2), (key3039, -2), (key3035, 2), (key3033, 2), (key3128, 2), (key3120, 2), (key3138, 2), (key3131, 2), (key3039, -2), (key3138, -2), (key3131, -2), (key3039, 6), (key3039, -2), (key3138, -2), (key3131, -2)]

def rawRow18151 : Integer.Sparse Key := [(key2414, -2), (key2424, -2), (key2417, -2), (key2424, 6), (key3033, -2), (key3039, -2), (key3035, -2), (key3120, 2), (key3131, 2), (key3033, 2), (key3138, 2), (key3035, 2), (key3128, 2), (key3131, -2), (key3039, -2), (key3138, -2), (key3039, 6), (key3131, -2), (key3039, -2), (key3138, -2)]

def rawRow18152 : Integer.Sparse Key := [(key2424, -2), (key2414, -2), (key2417, -2), (key2424, 6), (key3039, -2), (key3033, -2), (key3035, -2), (key3131, 2), (key3120, 2), (key3138, 2), (key3033, 2), (key3128, 2), (key3035, 2), (key3131, -2), (key3138, -2), (key3039, -2), (key3039, 6), (key3131, -2), (key3138, -2), (key3039, -2)]

def rawRow18153 : Integer.Sparse Key := [(key2417, -2), (key2424, -2), (key2414, -2), (key2424, 6), (key3035, -2), (key3039, -2), (key3033, -2), (key3128, 2), (key3138, 2), (key3035, 2), (key3131, 2), (key3033, 2), (key3120, 2), (key3138, -2), (key3039, -2), (key3131, -2), (key3039, 6), (key3138, -2), (key3039, -2), (key3131, -2)]

def rawRow18154 : Integer.Sparse Key := [(key2424, -2), (key2417, -2), (key2414, -2), (key2424, 6), (key3039, -2), (key3035, -2), (key3033, -2), (key3138, 2), (key3128, 2), (key3131, 2), (key3035, 2), (key3120, 2), (key3033, 2), (key3138, -2), (key3131, -2), (key3039, -2), (key3039, 6), (key3138, -2), (key3131, -2), (key3039, -2)]

def rawRow18155 : Integer.Sparse Key := [(key2414, -2), (key2424, -2), (key2424, -2), (key2417, 6), (key3120, -2), (key3131, -2), (key3131, -2), (key3033, 2), (key3039, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3138, 2), (key3035, -2), (key3035, -2), (key3128, -2), (key3131, 6), (key3039, -2), (key3039, -2), (key3138, -2)]

def rawRow18156 : Integer.Sparse Key := [(key2424, -2), (key2414, -2), (key2424, -2), (key2417, 6), (key3131, -2), (key3120, -2), (key3131, -2), (key3039, 2), (key3033, 2), (key3138, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3035, -2), (key3128, -2), (key3035, -2), (key3131, 6), (key3039, -2), (key3138, -2), (key3039, -2)]

def rawRow18157 : Integer.Sparse Key := [(key2424, -2), (key2424, -2), (key2414, -2), (key2417, 6), (key3131, -2), (key3131, -2), (key3120, -2), (key3138, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3033, 2), (key3033, 2), (key3128, -2), (key3035, -2), (key3035, -2), (key3131, 6), (key3138, -2), (key3039, -2), (key3039, -2)]

def rawRow18158 : Integer.Sparse Key := [(key2417, -2), (key2424, -2), (key2424, -2), (key2414, 6), (key3128, -2), (key3138, -2), (key3138, -2), (key3035, 2), (key3039, 2), (key3035, 2), (key3131, 2), (key3039, 2), (key3131, 2), (key3033, -2), (key3033, -2), (key3120, -2), (key3138, 6), (key3039, -2), (key3039, -2), (key3131, -2)]

def rawRow18159 : Integer.Sparse Key := [(key2424, -2), (key2417, -2), (key2424, -2), (key2414, 6), (key3138, -2), (key3128, -2), (key3138, -2), (key3039, 2), (key3035, 2), (key3131, 2), (key3035, 2), (key3131, 2), (key3039, 2), (key3033, -2), (key3120, -2), (key3033, -2), (key3138, 6), (key3039, -2), (key3131, -2), (key3039, -2)]

def rawRow18160 : Integer.Sparse Key := [(key2424, -2), (key2424, -2), (key2417, -2), (key2414, 6), (key3138, -2), (key3138, -2), (key3128, -2), (key3131, 2), (key3131, 2), (key3039, 2), (key3039, 2), (key3035, 2), (key3035, 2), (key3120, -2), (key3033, -2), (key3033, -2), (key3138, 6), (key3131, -2), (key3039, -2), (key3039, -2)]

def rawRow18161 : Integer.Sparse Key := [(key2487, -2), (key2492, -2), (key2492, -2), (key2492, 6), (key2414, -2), (key2424, -2), (key2424, -2), (key3033, 2), (key3039, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3138, 2), (key3039, -2), (key3039, -2), (key3138, -2), (key3035, 6), (key3035, -2), (key3035, -2), (key3128, -2)]

def rawRow18162 : Integer.Sparse Key := [(key2492, -2), (key2487, -2), (key2492, -2), (key2492, 6), (key2424, -2), (key2414, -2), (key2424, -2), (key3039, 2), (key3033, 2), (key3138, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3039, -2), (key3138, -2), (key3039, -2), (key3035, 6), (key3035, -2), (key3128, -2), (key3035, -2)]

def rawRow18163 : Integer.Sparse Key := [(key2492, -2), (key2492, -2), (key2487, -2), (key2492, 6), (key2424, -2), (key2424, -2), (key2414, -2), (key3138, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3033, 2), (key3033, 2), (key3138, -2), (key3039, -2), (key3039, -2), (key3035, 6), (key3128, -2), (key3035, -2), (key3035, -2)]

def rawRow18164 : Integer.Sparse Key := [(key2492, -2), (key2492, -2), (key2492, -2), (key2487, 6), (key2548, -2), (key2548, -2), (key2548, -2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2414, -2), (key3033, -2), (key3033, -2), (key3128, 6), (key3035, -2), (key3035, -2), (key3035, -2)]

def rawRow18165 : Integer.Sparse Key := [(key2546, -2), (key2548, -2), (key2548, -2), (key2548, 6), (key2417, -2), (key2424, -2), (key2424, -2), (key2417, 2), (key2424, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2492, 2), (key2424, -2), (key2424, -2), (key2492, -2), (key2414, 6), (key3033, -2), (key3033, -2), (key3120, -2)]

def rawRow18166 : Integer.Sparse Key := [(key2548, -2), (key2546, -2), (key2548, -2), (key2548, 6), (key2424, -2), (key2417, -2), (key2424, -2), (key2424, 2), (key2417, 2), (key2492, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2424, -2), (key2492, -2), (key2424, -2), (key2414, 6), (key3033, -2), (key3120, -2), (key3033, -2)]

def rawRow18167 : Integer.Sparse Key := [(key2548, -2), (key2548, -2), (key2546, -2), (key2548, 6), (key2424, -2), (key2424, -2), (key2417, -2), (key2492, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2417, 2), (key2492, -2), (key2424, -2), (key2424, -2), (key2414, 6), (key3120, -2), (key3033, -2), (key3033, -2)]

def rawRow18168 : Integer.Sparse Key := [(key2548, -2), (key2548, -2), (key2548, -2), (key2546, 6), (key2492, -2), (key2492, -2), (key2492, -2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2417, -2), (key2417, -2), (key2417, -2), (key2487, 6), (key2414, -2), (key3033, -2), (key3033, -2)]

def rawRow18169 : Integer.Sparse Key := [(key2101, 4), (key2106, 4), (key2111, 4), (key2106, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2139, 12)]

def rawRow18170 : Integer.Sparse Key := [(key2101, 4), (key2111, 4), (key2106, 4), (key2111, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2139, 12)]

def rawRow18171 : Integer.Sparse Key := [(key2106, 4), (key2101, 4), (key2111, 4), (key2106, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2139, 12)]

def rawRow18172 : Integer.Sparse Key := [(key2106, 4), (key2111, 4), (key2101, 4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, 12)]

def rawRow18173 : Integer.Sparse Key := [(key2111, 4), (key2101, 4), (key2106, 4), (key2111, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2139, 12)]

def rawRow18174 : Integer.Sparse Key := [(key2111, 4), (key2106, 4), (key2101, 4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, 12)]

def rawRow18175 : Integer.Sparse Key := [(key2106, 4), (key2106, 4), (key2139, 4), (key2101, -4), (key2111, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2139, -4), (key2111, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18176 : Integer.Sparse Key := [(key2106, 4), (key2139, 4), (key2106, 4), (key2111, -4), (key2101, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2139, -4), (key2111, 12)]

def rawRow18177 : Integer.Sparse Key := [(key2139, 4), (key2106, 4), (key2106, 4), (key2111, -4), (key2111, -4), (key2101, -4), (key2139, -4), (key2139, -4), (key2106, -4), (key2111, 12)]

def rawRow18178 : Integer.Sparse Key := [(key2111, 4), (key2111, 4), (key2139, 4), (key2101, -4), (key2106, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2139, -4), (key2106, 12)]

def rawRow18179 : Integer.Sparse Key := [(key2111, 4), (key2139, 4), (key2111, 4), (key2106, -4), (key2101, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2139, -4), (key2106, 12)]

def rawRow18180 : Integer.Sparse Key := [(key2139, 4), (key2111, 4), (key2111, 4), (key2106, -4), (key2106, -4), (key2101, -4), (key2139, -4), (key2139, -4), (key2111, -4), (key2106, 12)]

def rawRow18181 : Integer.Sparse Key := [(key2106, 4), (key2106, 4), (key2139, 4), (key2106, -4), (key2139, -4), (key2139, -4), (key2101, -4), (key2111, -4), (key2111, -4), (key2111, 12)]

def rawRow18182 : Integer.Sparse Key := [(key2106, 4), (key2139, 4), (key2106, 4), (key2139, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2101, -4), (key2111, -4), (key2111, 12)]

def rawRow18183 : Integer.Sparse Key := [(key2139, 4), (key2106, 4), (key2106, 4), (key2139, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2111, -4), (key2101, -4), (key2111, 12)]

def rawRow18184 : Integer.Sparse Key := [(key2139, 4), (key2139, 4), (key2139, 4), (key2106, -4), (key2106, -4), (key2106, -4), (key2111, -4), (key2111, -4), (key2111, -4), (key2101, 12)]

def rawRow18185 : Integer.Sparse Key := [(key2111, 4), (key2111, 4), (key2139, 4), (key2111, -4), (key2139, -4), (key2139, -4), (key2101, -4), (key2106, -4), (key2106, -4), (key2106, 12)]

def rawRow18186 : Integer.Sparse Key := [(key2111, 4), (key2139, 4), (key2111, 4), (key2139, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2101, -4), (key2106, -4), (key2106, 12)]

def rawRow18187 : Integer.Sparse Key := [(key2139, 4), (key2111, 4), (key2111, 4), (key2139, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2106, -4), (key2101, -4), (key2106, 12)]

def rawRow18188 : Integer.Sparse Key := [(key2139, 4), (key2139, 4), (key2139, 4), (key2111, -4), (key2111, -4), (key2111, -4), (key2106, -4), (key2106, -4), (key2106, -4), (key2101, 12)]

def rawRow18189 : Integer.Sparse Key := [(key3047, -1), (key3050, -1), (key3096, -1), (key3103, -1), (key3106, -1), (key3110, -1), (key3054, 2), (key3106, 2), (key3110, 2), (key3047, -1), (key3050, -1), (key3096, -1), (key3103, -1), (key3106, -1), (key3110, -1), (key3061, 2), (key3066, 2), (key3096, 2), (key3103, 2), (key3134, 2), (key3136, 2), (key3069, -1), (key3072, -1), (key3106, -1), (key3110, -1), (key3134, -1), (key3136, -1), (key3054, 2), (key3106, 2), (key3110, 2), (key3069, -1), (key3072, -1), (key3106, -1), (key3110, -1), (key3134, -1), (key3136, -1)]

def rawRow18190 : Integer.Sparse Key := [(key3050, -1), (key3047, -1), (key3103, -1), (key3096, -1), (key3110, -1), (key3106, -1), (key3054, 2), (key3110, 2), (key3106, 2), (key3050, -1), (key3047, -1), (key3103, -1), (key3096, -1), (key3110, -1), (key3106, -1), (key3066, 2), (key3061, 2), (key3103, 2), (key3096, 2), (key3136, 2), (key3134, 2), (key3072, -1), (key3069, -1), (key3110, -1), (key3106, -1), (key3136, -1), (key3134, -1), (key3054, 2), (key3110, 2), (key3106, 2), (key3072, -1), (key3069, -1), (key3110, -1), (key3106, -1), (key3136, -1), (key3134, -1)]

def rawRow18191 : Integer.Sparse Key := [(key3096, -1), (key3106, -1), (key3047, -1), (key3110, -1), (key3050, -1), (key3103, -1), (key3106, 2), (key3054, 2), (key3110, 2), (key3096, -1), (key3106, -1), (key3047, -1), (key3110, -1), (key3050, -1), (key3103, -1), (key3096, 2), (key3134, 2), (key3061, 2), (key3136, 2), (key3066, 2), (key3103, 2), (key3106, -1), (key3134, -1), (key3069, -1), (key3136, -1), (key3072, -1), (key3110, -1), (key3106, 2), (key3054, 2), (key3110, 2), (key3106, -1), (key3134, -1), (key3069, -1), (key3136, -1), (key3072, -1), (key3110, -1)]

def rawRow18192 : Integer.Sparse Key := [(key3106, -1), (key3096, -1), (key3110, -1), (key3047, -1), (key3103, -1), (key3050, -1), (key3106, 2), (key3110, 2), (key3054, 2), (key3106, -1), (key3096, -1), (key3110, -1), (key3047, -1), (key3103, -1), (key3050, -1), (key3134, 2), (key3096, 2), (key3136, 2), (key3061, 2), (key3103, 2), (key3066, 2), (key3134, -1), (key3106, -1), (key3136, -1), (key3069, -1), (key3110, -1), (key3072, -1), (key3106, 2), (key3110, 2), (key3054, 2), (key3134, -1), (key3106, -1), (key3136, -1), (key3069, -1), (key3110, -1), (key3072, -1)]

def rawRow18193 : Integer.Sparse Key := [(key3103, -1), (key3110, -1), (key3050, -1), (key3106, -1), (key3047, -1), (key3096, -1), (key3110, 2), (key3054, 2), (key3106, 2), (key3103, -1), (key3110, -1), (key3050, -1), (key3106, -1), (key3047, -1), (key3096, -1), (key3103, 2), (key3136, 2), (key3066, 2), (key3134, 2), (key3061, 2), (key3096, 2), (key3110, -1), (key3136, -1), (key3072, -1), (key3134, -1), (key3069, -1), (key3106, -1), (key3110, 2), (key3054, 2), (key3106, 2), (key3110, -1), (key3136, -1), (key3072, -1), (key3134, -1), (key3069, -1), (key3106, -1)]

def rawRow18194 : Integer.Sparse Key := [(key3110, -1), (key3103, -1), (key3106, -1), (key3050, -1), (key3096, -1), (key3047, -1), (key3110, 2), (key3106, 2), (key3054, 2), (key3110, -1), (key3103, -1), (key3106, -1), (key3050, -1), (key3096, -1), (key3047, -1), (key3136, 2), (key3103, 2), (key3134, 2), (key3066, 2), (key3096, 2), (key3061, 2), (key3136, -1), (key3110, -1), (key3134, -1), (key3072, -1), (key3106, -1), (key3069, -1), (key3110, 2), (key3106, 2), (key3054, 2), (key3136, -1), (key3110, -1), (key3134, -1), (key3072, -1), (key3106, -1), (key3069, -1)]

def rawRow18195 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3050, 2), (key3050, 2), (key3103, 2), (key3061, -1), (key3069, -1), (key3061, -1), (key3136, -1), (key3069, -1), (key3136, -1), (key3047, 2), (key3072, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3110, 2), (key3050, -1), (key3066, -1), (key3050, -1), (key3103, -1), (key3066, -1), (key3103, -1), (key3069, 2), (key3069, 2), (key3136, 2), (key3054, -1), (key3072, -1), (key3054, -1), (key3110, -1), (key3072, -1), (key3110, -1)]

def rawRow18196 : Integer.Sparse Key := [(key2689, -1), (key2679, -1), (key3110, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3050, 2), (key3103, 2), (key3050, 2), (key3069, -1), (key3061, -1), (key3136, -1), (key3061, -1), (key3136, -1), (key3069, -1), (key3072, 2), (key3047, 2), (key3110, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3066, -1), (key3050, -1), (key3103, -1), (key3050, -1), (key3103, -1), (key3066, -1), (key3069, 2), (key3136, 2), (key3069, 2), (key3072, -1), (key3054, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3072, -1)]

def rawRow18197 : Integer.Sparse Key := [(key2955, -1), (key2955, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key3047, -1), (key3103, 2), (key3050, 2), (key3050, 2), (key3136, -1), (key3136, -1), (key3069, -1), (key3069, -1), (key3061, -1), (key3061, -1), (key3110, 2), (key3110, 2), (key3072, 2), (key3072, 2), (key3047, 2), (key3047, 2), (key3103, -1), (key3103, -1), (key3066, -1), (key3066, -1), (key3050, -1), (key3050, -1), (key3136, 2), (key3069, 2), (key3069, 2), (key3110, -1), (key3110, -1), (key3072, -1), (key3072, -1), (key3054, -1), (key3054, -1)]

def rawRow18198 : Integer.Sparse Key := [(key2682, -1), (key2689, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2818, -1), (key2679, 2), (key3047, 2), (key3096, 2), (key3066, -1), (key3072, -1), (key3066, -1), (key3134, -1), (key3072, -1), (key3134, -1), (key3050, 2), (key3069, 2), (key3050, 2), (key3106, 2), (key3069, 2), (key3106, 2), (key3047, -1), (key3061, -1), (key3047, -1), (key3096, -1), (key3061, -1), (key3096, -1), (key3072, 2), (key3072, 2), (key3134, 2), (key3054, -1), (key3069, -1), (key3054, -1), (key3106, -1), (key3069, -1), (key3106, -1)]

def rawRow18199 : Integer.Sparse Key := [(key2689, -1), (key2682, -1), (key2818, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2679, 2), (key3096, 2), (key3047, 2), (key3072, -1), (key3066, -1), (key3134, -1), (key3066, -1), (key3134, -1), (key3072, -1), (key3069, 2), (key3050, 2), (key3106, 2), (key3050, 2), (key3106, 2), (key3069, 2), (key3061, -1), (key3047, -1), (key3096, -1), (key3047, -1), (key3096, -1), (key3061, -1), (key3072, 2), (key3134, 2), (key3072, 2), (key3069, -1), (key3054, -1), (key3106, -1), (key3054, -1), (key3106, -1), (key3069, -1)]

def rawRow18200 : Integer.Sparse Key := [(key2818, -1), (key2818, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2813, 2), (key2679, 2), (key3047, 2), (key3134, -1), (key3134, -1), (key3072, -1), (key3072, -1), (key3066, -1), (key3066, -1), (key3106, 2), (key3106, 2), (key3069, 2), (key3069, 2), (key3050, 2), (key3050, 2), (key3096, -1), (key3096, -1), (key3061, -1), (key3061, -1), (key3047, -1), (key3047, -1), (key3134, 2), (key3072, 2), (key3072, 2), (key3106, -1), (key3106, -1), (key3069, -1), (key3069, -1), (key3054, -1), (key3054, -1)]

def rawRow18201 : Integer.Sparse Key := [(key2710, -1), (key2715, -1), (key2710, -1), (key2979, -1), (key2715, -1), (key2979, -1), (key2715, 2), (key2715, 2), (key2979, 2), (key2679, -1), (key2689, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3047, 2), (key3072, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3110, 2), (key3054, -1), (key3072, -1), (key3054, -1), (key3110, -1), (key3072, -1), (key3110, -1), (key3050, 2), (key3050, 2), (key3103, 2), (key3050, -1), (key3066, -1), (key3050, -1), (key3103, -1), (key3066, -1), (key3103, -1)]

def rawRow18202 : Integer.Sparse Key := [(key2715, -1), (key2710, -1), (key2979, -1), (key2710, -1), (key2979, -1), (key2715, -1), (key2715, 2), (key2979, 2), (key2715, 2), (key2689, -1), (key2679, -1), (key3110, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3072, 2), (key3047, 2), (key3110, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3072, -1), (key3054, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3072, -1), (key3050, 2), (key3103, 2), (key3050, 2), (key3066, -1), (key3050, -1), (key3103, -1), (key3050, -1), (key3103, -1), (key3066, -1)]

def rawRow18203 : Integer.Sparse Key := [(key2979, -1), (key2979, -1), (key2715, -1), (key2715, -1), (key2710, -1), (key2710, -1), (key2979, 2), (key2715, 2), (key2715, 2), (key2955, -1), (key2955, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key3047, -1), (key3110, 2), (key3110, 2), (key3072, 2), (key3072, 2), (key3047, 2), (key3047, 2), (key3110, -1), (key3110, -1), (key3072, -1), (key3072, -1), (key3054, -1), (key3054, -1), (key3103, 2), (key3050, 2), (key3050, 2), (key3103, -1), (key3103, -1), (key3066, -1), (key3066, -1), (key3050, -1), (key3050, -1)]

def rawRow18204 : Integer.Sparse Key := [(key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2710, 2), (key2710, 2), (key2710, 2), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2679, -1), (key2679, -1), (key2679, -1), (key3047, -1), (key3047, -1), (key3047, -1), (key3066, 2), (key3066, 2), (key3066, 2), (key3050, -1), (key3050, -1), (key3050, -1), (key3050, -1), (key3050, -1), (key3050, -1)]

def rawRow18205 : Integer.Sparse Key := [(key2740, -1), (key2742, -1), (key2740, -1), (key2900, -1), (key2742, -1), (key2900, -1), (key2742, 2), (key2742, 2), (key2900, 2), (key2682, -1), (key2689, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2818, -1), (key2682, 2), (key2715, 2), (key2682, 2), (key2818, 2), (key2715, 2), (key2818, 2), (key2689, -1), (key2715, -1), (key2689, -1), (key2818, -1), (key2715, -1), (key2818, -1), (key2679, 2), (key3047, 2), (key3096, 2), (key3047, -1), (key3061, -1), (key3047, -1), (key3096, -1), (key3061, -1), (key3096, -1)]

def rawRow18206 : Integer.Sparse Key := [(key2742, -1), (key2740, -1), (key2900, -1), (key2740, -1), (key2900, -1), (key2742, -1), (key2742, 2), (key2900, 2), (key2742, 2), (key2689, -1), (key2682, -1), (key2818, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2715, 2), (key2682, 2), (key2818, 2), (key2682, 2), (key2818, 2), (key2715, 2), (key2715, -1), (key2689, -1), (key2818, -1), (key2689, -1), (key2818, -1), (key2715, -1), (key2679, 2), (key3096, 2), (key3047, 2), (key3061, -1), (key3047, -1), (key3096, -1), (key3047, -1), (key3096, -1), (key3061, -1)]

def rawRow18207 : Integer.Sparse Key := [(key2900, -1), (key2900, -1), (key2742, -1), (key2742, -1), (key2740, -1), (key2740, -1), (key2900, 2), (key2742, 2), (key2742, 2), (key2818, -1), (key2818, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2818, 2), (key2818, 2), (key2715, 2), (key2715, 2), (key2682, 2), (key2682, 2), (key2818, -1), (key2818, -1), (key2715, -1), (key2715, -1), (key2689, -1), (key2689, -1), (key2813, 2), (key2679, 2), (key3047, 2), (key3096, -1), (key3096, -1), (key3061, -1), (key3061, -1), (key3047, -1), (key3047, -1)]

def rawRow18208 : Integer.Sparse Key := [(key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2740, 2), (key2740, 2), (key2740, 2), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2682, -1), (key2682, -1), (key2682, -1), (key2682, -1), (key2682, -1), (key2682, -1), (key2710, 2), (key2710, 2), (key2710, 2), (key2679, -1), (key2679, -1), (key2679, -1), (key3047, -1), (key3047, -1), (key3047, -1)]

def rawRow18209 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, -2), (key1507, 6), (key1500, -2), (key1503, -2), (key1507, -2), (key1500, 2), (key1503, 2), (key1732, 2), (key1874, 2), (key1736, 2), (key1875, 2), (key1507, -2), (key1736, -2), (key1875, -2), (key1507, 6), (key1507, -2), (key1736, -2), (key1875, -2)]

def rawRow18210 : Integer.Sparse Key := [(key1503, -2), (key1500, -2), (key1507, -2), (key1507, 6), (key1503, -2), (key1500, -2), (key1507, -2), (key1503, 2), (key1500, 2), (key1874, 2), (key1732, 2), (key1875, 2), (key1736, 2), (key1507, -2), (key1875, -2), (key1736, -2), (key1507, 6), (key1507, -2), (key1875, -2), (key1736, -2)]

def rawRow18211 : Integer.Sparse Key := [(key1500, -2), (key1507, -2), (key1503, -2), (key1507, 6), (key1500, -2), (key1507, -2), (key1503, -2), (key1732, 2), (key1736, 2), (key1500, 2), (key1875, 2), (key1503, 2), (key1874, 2), (key1736, -2), (key1507, -2), (key1875, -2), (key1507, 6), (key1736, -2), (key1507, -2), (key1875, -2)]

def rawRow18212 : Integer.Sparse Key := [(key1507, -2), (key1500, -2), (key1503, -2), (key1507, 6), (key1507, -2), (key1500, -2), (key1503, -2), (key1736, 2), (key1732, 2), (key1875, 2), (key1500, 2), (key1874, 2), (key1503, 2), (key1736, -2), (key1875, -2), (key1507, -2), (key1507, 6), (key1736, -2), (key1875, -2), (key1507, -2)]

def rawRow18213 : Integer.Sparse Key := [(key1503, -2), (key1507, -2), (key1500, -2), (key1507, 6), (key1503, -2), (key1507, -2), (key1500, -2), (key1874, 2), (key1875, 2), (key1503, 2), (key1736, 2), (key1500, 2), (key1732, 2), (key1875, -2), (key1507, -2), (key1736, -2), (key1507, 6), (key1875, -2), (key1507, -2), (key1736, -2)]

def rawRow18214 : Integer.Sparse Key := [(key1507, -2), (key1503, -2), (key1500, -2), (key1507, 6), (key1507, -2), (key1503, -2), (key1500, -2), (key1875, 2), (key1874, 2), (key1736, 2), (key1503, 2), (key1732, 2), (key1500, 2), (key1875, -2), (key1736, -2), (key1507, -2), (key1507, 6), (key1875, -2), (key1736, -2), (key1507, -2)]

def rawRow18215 : Integer.Sparse Key := [(key1500, -2), (key1507, -2), (key1507, -2), (key1503, 6), (key1732, -2), (key1736, -2), (key1736, -2), (key1500, 2), (key1507, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1875, 2), (key1503, -2), (key1503, -2), (key1874, -2), (key1736, 6), (key1507, -2), (key1507, -2), (key1875, -2)]

def rawRow18216 : Integer.Sparse Key := [(key1507, -2), (key1500, -2), (key1507, -2), (key1503, 6), (key1736, -2), (key1732, -2), (key1736, -2), (key1507, 2), (key1500, 2), (key1875, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1503, -2), (key1874, -2), (key1503, -2), (key1736, 6), (key1507, -2), (key1875, -2), (key1507, -2)]

def rawRow18217 : Integer.Sparse Key := [(key1507, -2), (key1507, -2), (key1500, -2), (key1503, 6), (key1736, -2), (key1736, -2), (key1732, -2), (key1875, 2), (key1875, 2), (key1507, 2), (key1507, 2), (key1500, 2), (key1500, 2), (key1874, -2), (key1503, -2), (key1503, -2), (key1736, 6), (key1875, -2), (key1507, -2), (key1507, -2)]

def rawRow18218 : Integer.Sparse Key := [(key1503, -2), (key1507, -2), (key1507, -2), (key1500, 6), (key1874, -2), (key1875, -2), (key1875, -2), (key1503, 2), (key1507, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1736, 2), (key1500, -2), (key1500, -2), (key1732, -2), (key1875, 6), (key1507, -2), (key1507, -2), (key1736, -2)]

def rawRow18219 : Integer.Sparse Key := [(key1507, -2), (key1503, -2), (key1507, -2), (key1500, 6), (key1875, -2), (key1874, -2), (key1875, -2), (key1507, 2), (key1503, 2), (key1736, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1500, -2), (key1732, -2), (key1500, -2), (key1875, 6), (key1507, -2), (key1736, -2), (key1507, -2)]

def rawRow18220 : Integer.Sparse Key := [(key1507, -2), (key1507, -2), (key1503, -2), (key1500, 6), (key1875, -2), (key1875, -2), (key1874, -2), (key1736, 2), (key1736, 2), (key1507, 2), (key1507, 2), (key1503, 2), (key1503, 2), (key1732, -2), (key1500, -2), (key1500, -2), (key1875, 6), (key1736, -2), (key1507, -2), (key1507, -2)]

def rawRow18221 : Integer.Sparse Key := [(key1732, -2), (key1736, -2), (key1736, -2), (key1736, 6), (key1500, -2), (key1507, -2), (key1507, -2), (key1500, 2), (key1507, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1875, 2), (key1507, -2), (key1507, -2), (key1875, -2), (key1503, 6), (key1503, -2), (key1503, -2), (key1874, -2)]

def rawRow18222 : Integer.Sparse Key := [(key1736, -2), (key1732, -2), (key1736, -2), (key1736, 6), (key1507, -2), (key1500, -2), (key1507, -2), (key1507, 2), (key1500, 2), (key1875, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1507, -2), (key1875, -2), (key1507, -2), (key1503, 6), (key1503, -2), (key1874, -2), (key1503, -2)]

def rawRow18223 : Integer.Sparse Key := [(key1736, -2), (key1736, -2), (key1732, -2), (key1736, 6), (key1507, -2), (key1507, -2), (key1500, -2), (key1875, 2), (key1875, 2), (key1507, 2), (key1507, 2), (key1500, 2), (key1500, 2), (key1875, -2), (key1507, -2), (key1507, -2), (key1503, 6), (key1874, -2), (key1503, -2), (key1503, -2)]

def rawRow18224 : Integer.Sparse Key := [(key1736, -2), (key1736, -2), (key1736, -2), (key1732, 6), (key1875, -2), (key1875, -2), (key1875, -2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1500, -2), (key1500, -2), (key1500, -2), (key1874, 6), (key1503, -2), (key1503, -2), (key1503, -2)]

def rawRow18225 : Integer.Sparse Key := [(key1874, -2), (key1875, -2), (key1875, -2), (key1875, 6), (key1503, -2), (key1507, -2), (key1507, -2), (key1503, 2), (key1507, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1736, 2), (key1507, -2), (key1507, -2), (key1736, -2), (key1500, 6), (key1500, -2), (key1500, -2), (key1732, -2)]

def rawRow18226 : Integer.Sparse Key := [(key1875, -2), (key1874, -2), (key1875, -2), (key1875, 6), (key1507, -2), (key1503, -2), (key1507, -2), (key1507, 2), (key1503, 2), (key1736, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1507, -2), (key1736, -2), (key1507, -2), (key1500, 6), (key1500, -2), (key1732, -2), (key1500, -2)]

def rawRow18227 : Integer.Sparse Key := [(key1875, -2), (key1875, -2), (key1874, -2), (key1875, 6), (key1507, -2), (key1507, -2), (key1503, -2), (key1736, 2), (key1736, 2), (key1507, 2), (key1507, 2), (key1503, 2), (key1503, 2), (key1736, -2), (key1507, -2), (key1507, -2), (key1500, 6), (key1732, -2), (key1500, -2), (key1500, -2)]

def rawRow18228 : Integer.Sparse Key := [(key1875, -2), (key1875, -2), (key1875, -2), (key1874, 6), (key1736, -2), (key1736, -2), (key1736, -2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1503, -2), (key1503, -2), (key1503, -2), (key1732, 6), (key1500, -2), (key1500, -2), (key1500, -2)]

def rawRow18229 : Integer.Sparse Key := [(key2421, 2), (key2428, 2), (key2429, 2), (key2428, -2), (key2429, -2), (key2442, -2), (key2421, 2), (key2428, 2), (key2429, 2), (key2428, -1), (key2429, -1), (key2496, -1), (key2550, -1), (key2508, -1), (key2556, -1), (key2428, -2), (key2429, -2), (key2442, -2), (key2428, -1), (key2429, -1), (key2496, -1), (key2550, -1), (key2508, -1), (key2556, -1), (key2442, 4), (key2508, 4), (key2556, 4)]

def rawRow18230 : Integer.Sparse Key := [(key2421, 2), (key2429, 2), (key2428, 2), (key2429, -2), (key2428, -2), (key2442, -2), (key2421, 2), (key2429, 2), (key2428, 2), (key2429, -1), (key2428, -1), (key2550, -1), (key2496, -1), (key2556, -1), (key2508, -1), (key2429, -2), (key2428, -2), (key2442, -2), (key2429, -1), (key2428, -1), (key2550, -1), (key2496, -1), (key2556, -1), (key2508, -1), (key2442, 4), (key2556, 4), (key2508, 4)]

def rawRow18231 : Integer.Sparse Key := [(key2428, 2), (key2421, 2), (key2429, 2), (key2428, -2), (key2442, -2), (key2429, -2), (key2428, 2), (key2421, 2), (key2429, 2), (key2496, -1), (key2508, -1), (key2428, -1), (key2556, -1), (key2429, -1), (key2550, -1), (key2428, -2), (key2442, -2), (key2429, -2), (key2496, -1), (key2508, -1), (key2428, -1), (key2556, -1), (key2429, -1), (key2550, -1), (key2508, 4), (key2442, 4), (key2556, 4)]

def rawRow18232 : Integer.Sparse Key := [(key2428, 2), (key2429, 2), (key2421, 2), (key2442, -2), (key2428, -2), (key2429, -2), (key2428, 2), (key2429, 2), (key2421, 2), (key2508, -1), (key2496, -1), (key2556, -1), (key2428, -1), (key2550, -1), (key2429, -1), (key2442, -2), (key2428, -2), (key2429, -2), (key2508, -1), (key2496, -1), (key2556, -1), (key2428, -1), (key2550, -1), (key2429, -1), (key2508, 4), (key2556, 4), (key2442, 4)]

def rawRow18233 : Integer.Sparse Key := [(key2429, 2), (key2421, 2), (key2428, 2), (key2429, -2), (key2442, -2), (key2428, -2), (key2429, 2), (key2421, 2), (key2428, 2), (key2550, -1), (key2556, -1), (key2429, -1), (key2508, -1), (key2428, -1), (key2496, -1), (key2429, -2), (key2442, -2), (key2428, -2), (key2550, -1), (key2556, -1), (key2429, -1), (key2508, -1), (key2428, -1), (key2496, -1), (key2556, 4), (key2442, 4), (key2508, 4)]

def rawRow18234 : Integer.Sparse Key := [(key2429, 2), (key2428, 2), (key2421, 2), (key2442, -2), (key2429, -2), (key2428, -2), (key2429, 2), (key2428, 2), (key2421, 2), (key2556, -1), (key2550, -1), (key2508, -1), (key2429, -1), (key2496, -1), (key2428, -1), (key2442, -2), (key2429, -2), (key2428, -2), (key2556, -1), (key2550, -1), (key2508, -1), (key2429, -1), (key2496, -1), (key2428, -1), (key2556, 4), (key2508, 4), (key2442, 4)]

def rawRow18235 : Integer.Sparse Key := [(key2428, 2), (key2428, 2), (key2442, 2), (key2421, -2), (key2429, -2), (key2429, -2), (key2496, 2), (key2496, 2), (key2508, 2), (key2421, -1), (key2429, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2550, -1), (key2496, -2), (key2508, -2), (key2508, -2), (key2428, -1), (key2442, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2556, -1), (key2429, 4), (key2429, 4), (key2550, 4)]

def rawRow18236 : Integer.Sparse Key := [(key2428, 2), (key2442, 2), (key2428, 2), (key2429, -2), (key2421, -2), (key2429, -2), (key2496, 2), (key2508, 2), (key2496, 2), (key2429, -1), (key2421, -1), (key2550, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2508, -2), (key2496, -2), (key2508, -2), (key2442, -1), (key2428, -1), (key2556, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2429, 4), (key2550, 4), (key2429, 4)]

def rawRow18237 : Integer.Sparse Key := [(key2442, 2), (key2428, 2), (key2428, 2), (key2429, -2), (key2429, -2), (key2421, -2), (key2508, 2), (key2496, 2), (key2496, 2), (key2550, -1), (key2550, -1), (key2429, -1), (key2429, -1), (key2421, -1), (key2421, -1), (key2508, -2), (key2508, -2), (key2496, -2), (key2556, -1), (key2556, -1), (key2442, -1), (key2442, -1), (key2428, -1), (key2428, -1), (key2550, 4), (key2429, 4), (key2429, 4)]

def rawRow18238 : Integer.Sparse Key := [(key2429, 2), (key2429, 2), (key2442, 2), (key2421, -2), (key2428, -2), (key2428, -2), (key2550, 2), (key2550, 2), (key2556, 2), (key2421, -1), (key2428, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2496, -1), (key2550, -2), (key2556, -2), (key2556, -2), (key2429, -1), (key2442, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2508, -1), (key2428, 4), (key2428, 4), (key2496, 4)]

def rawRow18239 : Integer.Sparse Key := [(key2429, 2), (key2442, 2), (key2429, 2), (key2428, -2), (key2421, -2), (key2428, -2), (key2550, 2), (key2556, 2), (key2550, 2), (key2428, -1), (key2421, -1), (key2496, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2556, -2), (key2550, -2), (key2556, -2), (key2442, -1), (key2429, -1), (key2508, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2428, 4), (key2496, 4), (key2428, 4)]

def rawRow18240 : Integer.Sparse Key := [(key2442, 2), (key2429, 2), (key2429, 2), (key2428, -2), (key2428, -2), (key2421, -2), (key2556, 2), (key2550, 2), (key2550, 2), (key2496, -1), (key2496, -1), (key2428, -1), (key2428, -1), (key2421, -1), (key2421, -1), (key2556, -2), (key2556, -2), (key2550, -2), (key2508, -1), (key2508, -1), (key2442, -1), (key2442, -1), (key2429, -1), (key2429, -1), (key2496, 4), (key2428, 4), (key2428, 4)]

def rawRow18241 : Integer.Sparse Key := [(key2496, 2), (key2496, 2), (key2508, 2), (key2496, -2), (key2508, -2), (key2508, -2), (key2428, 2), (key2428, 2), (key2442, 2), (key2428, -1), (key2442, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2556, -1), (key2421, -2), (key2429, -2), (key2429, -2), (key2421, -1), (key2429, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2550, -1), (key2429, 4), (key2429, 4), (key2550, 4)]

def rawRow18242 : Integer.Sparse Key := [(key2496, 2), (key2508, 2), (key2496, 2), (key2508, -2), (key2496, -2), (key2508, -2), (key2428, 2), (key2442, 2), (key2428, 2), (key2442, -1), (key2428, -1), (key2556, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2429, -2), (key2421, -2), (key2429, -2), (key2429, -1), (key2421, -1), (key2550, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2429, 4), (key2550, 4), (key2429, 4)]

def rawRow18243 : Integer.Sparse Key := [(key2508, 2), (key2496, 2), (key2496, 2), (key2508, -2), (key2508, -2), (key2496, -2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, -1), (key2556, -1), (key2442, -1), (key2442, -1), (key2428, -1), (key2428, -1), (key2429, -2), (key2429, -2), (key2421, -2), (key2550, -1), (key2550, -1), (key2429, -1), (key2429, -1), (key2421, -1), (key2421, -1), (key2550, 4), (key2429, 4), (key2429, 4)]

def rawRow18244 : Integer.Sparse Key := [(key2508, 2), (key2508, 2), (key2508, 2), (key2496, -2), (key2496, -2), (key2496, -2), (key2556, 2), (key2556, 2), (key2556, 2), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2550, -2), (key2550, -2), (key2550, -2), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2421, 4), (key2421, 4), (key2421, 4)]

def rawRow18245 : Integer.Sparse Key := [(key2550, 2), (key2550, 2), (key2556, 2), (key2550, -2), (key2556, -2), (key2556, -2), (key2429, 2), (key2429, 2), (key2442, 2), (key2429, -1), (key2442, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2508, -1), (key2421, -2), (key2428, -2), (key2428, -2), (key2421, -1), (key2428, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2496, -1), (key2428, 4), (key2428, 4), (key2496, 4)]

def rawRow18246 : Integer.Sparse Key := [(key2550, 2), (key2556, 2), (key2550, 2), (key2556, -2), (key2550, -2), (key2556, -2), (key2429, 2), (key2442, 2), (key2429, 2), (key2442, -1), (key2429, -1), (key2508, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2428, -2), (key2421, -2), (key2428, -2), (key2428, -1), (key2421, -1), (key2496, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2428, 4), (key2496, 4), (key2428, 4)]

def rawRow18247 : Integer.Sparse Key := [(key2556, 2), (key2550, 2), (key2550, 2), (key2556, -2), (key2556, -2), (key2550, -2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, -1), (key2508, -1), (key2442, -1), (key2442, -1), (key2429, -1), (key2429, -1), (key2428, -2), (key2428, -2), (key2421, -2), (key2496, -1), (key2496, -1), (key2428, -1), (key2428, -1), (key2421, -1), (key2421, -1), (key2496, 4), (key2428, 4), (key2428, 4)]

def rawRow18248 : Integer.Sparse Key := [(key2556, 2), (key2556, 2), (key2556, 2), (key2550, -2), (key2550, -2), (key2550, -2), (key2508, 2), (key2508, 2), (key2508, 2), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2496, -2), (key2496, -2), (key2496, -2), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2421, 4), (key2421, 4), (key2421, 4)]

def rawRow18249 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, 2), (key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2680, 2), (key2683, 2), (key2690, 2), (key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2711, 2), (key2741, 2), (key2814, 2), (key2954, 2), (key2901, 2), (key2980, 2)]

def rawRow18250 : Integer.Sparse Key := [(key2683, 2), (key2680, 2), (key2690, 2), (key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2683, 2), (key2680, 2), (key2690, 2), (key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2741, 2), (key2711, 2), (key2954, 2), (key2814, 2), (key2980, 2), (key2901, 2)]

def rawRow18251 : Integer.Sparse Key := [(key2680, 2), (key2690, 2), (key2683, 2), (key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2680, 2), (key2690, 2), (key2683, 2), (key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2814, 2), (key2901, 2), (key2711, 2), (key2980, 2), (key2741, 2), (key2954, 2)]

def rawRow18252 : Integer.Sparse Key := [(key2690, 2), (key2680, 2), (key2683, 2), (key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2690, 2), (key2680, 2), (key2683, 2), (key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2901, 2), (key2814, 2), (key2980, 2), (key2711, 2), (key2954, 2), (key2741, 2)]

def rawRow18253 : Integer.Sparse Key := [(key2683, 2), (key2690, 2), (key2680, 2), (key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2683, 2), (key2690, 2), (key2680, 2), (key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2954, 2), (key2980, 2), (key2741, 2), (key2901, 2), (key2711, 2), (key2814, 2)]

def rawRow18254 : Integer.Sparse Key := [(key2690, 2), (key2683, 2), (key2680, 2), (key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2690, 2), (key2683, 2), (key2680, 2), (key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2980, 2), (key2954, 2), (key2901, 2), (key2741, 2), (key2814, 2), (key2711, 2)]

def rawRow18255 : Integer.Sparse Key := [(key2711, 2), (key2716, 2), (key2716, 2), (key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2814, 2), (key2819, 2), (key2819, 2), (key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2)]

def rawRow18256 : Integer.Sparse Key := [(key2716, 2), (key2711, 2), (key2716, 2), (key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2819, 2), (key2814, 2), (key2819, 2), (key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2)]

def rawRow18257 : Integer.Sparse Key := [(key2716, 2), (key2716, 2), (key2711, 2), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2819, 2), (key2819, 2), (key2814, 2), (key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2)]

def rawRow18258 : Integer.Sparse Key := [(key2741, 2), (key2743, 2), (key2743, 2), (key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2954, 2), (key2956, 2), (key2956, 2), (key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2)]

def rawRow18259 : Integer.Sparse Key := [(key2743, 2), (key2741, 2), (key2743, 2), (key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2956, 2), (key2954, 2), (key2956, 2), (key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2)]

def rawRow18260 : Integer.Sparse Key := [(key2743, 2), (key2743, 2), (key2741, 2), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2956, 2), (key2956, 2), (key2954, 2), (key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2)]

def rawRow18261 : Integer.Sparse Key := [(key2814, 2), (key2819, 2), (key2819, 2), (key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2711, 2), (key2716, 2), (key2716, 2), (key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2)]

def rawRow18262 : Integer.Sparse Key := [(key2819, 2), (key2814, 2), (key2819, 2), (key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2716, 2), (key2711, 2), (key2716, 2), (key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2)]

def rawRow18263 : Integer.Sparse Key := [(key2819, 2), (key2819, 2), (key2814, 2), (key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2716, 2), (key2716, 2), (key2711, 2), (key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2)]

def rawRow18264 : Integer.Sparse Key := [(key2901, 2), (key2901, 2), (key2901, 2), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2980, 2), (key2980, 2), (key2980, 2), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2)]

def rawRow18265 : Integer.Sparse Key := [(key2954, 2), (key2956, 2), (key2956, 2), (key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2741, 2), (key2743, 2), (key2743, 2), (key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2)]

def rawRow18266 : Integer.Sparse Key := [(key2956, 2), (key2954, 2), (key2956, 2), (key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2743, 2), (key2741, 2), (key2743, 2), (key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2)]

def rawRow18267 : Integer.Sparse Key := [(key2956, 2), (key2956, 2), (key2954, 2), (key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2743, 2), (key2743, 2), (key2741, 2), (key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2)]

def rawRow18268 : Integer.Sparse Key := [(key2980, 2), (key2980, 2), (key2980, 2), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2901, 2), (key2901, 2), (key2901, 2), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2)]

def rawRow18269 : Integer.Sparse Key := [(key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2690, 2), (key2716, 2), (key2743, 2), (key2680, 1), (key2683, 1), (key2814, 1), (key2954, 1), (key2819, 1), (key2956, 1), (key2690, -2), (key2819, -2), (key2956, -2), (key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2680, 1), (key2683, 1), (key2814, 1), (key2954, 1), (key2819, 1), (key2956, 1), (key2690, 2), (key2716, 2), (key2743, 2), (key2690, -2), (key2819, -2), (key2956, -2)]

def rawRow18270 : Integer.Sparse Key := [(key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2690, 2), (key2743, 2), (key2716, 2), (key2683, 1), (key2680, 1), (key2954, 1), (key2814, 1), (key2956, 1), (key2819, 1), (key2690, -2), (key2956, -2), (key2819, -2), (key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2683, 1), (key2680, 1), (key2954, 1), (key2814, 1), (key2956, 1), (key2819, 1), (key2690, 2), (key2743, 2), (key2716, 2), (key2690, -2), (key2956, -2), (key2819, -2)]

def rawRow18271 : Integer.Sparse Key := [(key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2716, 2), (key2690, 2), (key2743, 2), (key2814, 1), (key2819, 1), (key2680, 1), (key2956, 1), (key2683, 1), (key2954, 1), (key2819, -2), (key2690, -2), (key2956, -2), (key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2814, 1), (key2819, 1), (key2680, 1), (key2956, 1), (key2683, 1), (key2954, 1), (key2716, 2), (key2690, 2), (key2743, 2), (key2819, -2), (key2690, -2), (key2956, -2)]

def rawRow18272 : Integer.Sparse Key := [(key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2716, 2), (key2743, 2), (key2690, 2), (key2819, 1), (key2814, 1), (key2956, 1), (key2680, 1), (key2954, 1), (key2683, 1), (key2819, -2), (key2956, -2), (key2690, -2), (key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2819, 1), (key2814, 1), (key2956, 1), (key2680, 1), (key2954, 1), (key2683, 1), (key2716, 2), (key2743, 2), (key2690, 2), (key2819, -2), (key2956, -2), (key2690, -2)]

def rawRow18273 : Integer.Sparse Key := [(key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2743, 2), (key2690, 2), (key2716, 2), (key2954, 1), (key2956, 1), (key2683, 1), (key2819, 1), (key2680, 1), (key2814, 1), (key2956, -2), (key2690, -2), (key2819, -2), (key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2954, 1), (key2956, 1), (key2683, 1), (key2819, 1), (key2680, 1), (key2814, 1), (key2743, 2), (key2690, 2), (key2716, 2), (key2956, -2), (key2690, -2), (key2819, -2)]

def rawRow18274 : Integer.Sparse Key := [(key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2743, 2), (key2716, 2), (key2690, 2), (key2956, 1), (key2954, 1), (key2819, 1), (key2683, 1), (key2814, 1), (key2680, 1), (key2956, -2), (key2819, -2), (key2690, -2), (key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2956, 1), (key2954, 1), (key2819, 1), (key2683, 1), (key2814, 1), (key2680, 1), (key2743, 2), (key2716, 2), (key2690, 2), (key2956, -2), (key2819, -2), (key2690, -2)]

def rawRow18275 : Integer.Sparse Key := [(key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2683, 2), (key2683, 2), (key2741, 2), (key2680, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2683, -2), (key2683, -2), (key2954, -2), (key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2711, 1), (key2716, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2980, 1), (key2819, 2), (key2819, 2), (key2901, 2), (key2716, -2), (key2716, -2), (key2980, -2)]

def rawRow18276 : Integer.Sparse Key := [(key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2683, 2), (key2741, 2), (key2683, 2), (key2690, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2683, -2), (key2954, -2), (key2683, -2), (key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2716, 1), (key2711, 1), (key2980, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2819, 2), (key2901, 2), (key2819, 2), (key2716, -2), (key2980, -2), (key2716, -2)]

def rawRow18277 : Integer.Sparse Key := [(key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2741, 2), (key2683, 2), (key2683, 2), (key2956, 1), (key2956, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2954, -2), (key2683, -2), (key2683, -2), (key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2980, 1), (key2980, 1), (key2716, 1), (key2716, 1), (key2711, 1), (key2711, 1), (key2901, 2), (key2819, 2), (key2819, 2), (key2980, -2), (key2716, -2), (key2716, -2)]

def rawRow18278 : Integer.Sparse Key := [(key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2680, 2), (key2680, 2), (key2711, 2), (key2683, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2680, -2), (key2680, -2), (key2814, -2), (key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2741, 1), (key2743, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2901, 1), (key2956, 2), (key2956, 2), (key2980, 2), (key2743, -2), (key2743, -2), (key2901, -2)]

def rawRow18279 : Integer.Sparse Key := [(key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2680, 2), (key2711, 2), (key2680, 2), (key2690, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2680, -2), (key2814, -2), (key2680, -2), (key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2743, 1), (key2741, 1), (key2901, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2956, 2), (key2980, 2), (key2956, 2), (key2743, -2), (key2901, -2), (key2743, -2)]

def rawRow18280 : Integer.Sparse Key := [(key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2711, 2), (key2680, 2), (key2680, 2), (key2819, 1), (key2819, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2814, -2), (key2680, -2), (key2680, -2), (key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2901, 1), (key2901, 1), (key2743, 1), (key2743, 1), (key2741, 1), (key2741, 1), (key2980, 2), (key2956, 2), (key2956, 2), (key2901, -2), (key2743, -2), (key2743, -2)]

def rawRow18281 : Integer.Sparse Key := [(key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2819, 2), (key2819, 2), (key2901, 2), (key2711, 1), (key2716, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2980, 1), (key2716, -2), (key2716, -2), (key2980, -2), (key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2680, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2683, 2), (key2683, 2), (key2741, 2), (key2683, -2), (key2683, -2), (key2954, -2)]

def rawRow18282 : Integer.Sparse Key := [(key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2819, 2), (key2901, 2), (key2819, 2), (key2716, 1), (key2711, 1), (key2980, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2716, -2), (key2980, -2), (key2716, -2), (key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2690, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2683, 2), (key2741, 2), (key2683, 2), (key2683, -2), (key2954, -2), (key2683, -2)]

def rawRow18283 : Integer.Sparse Key := [(key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2901, 2), (key2819, 2), (key2819, 2), (key2980, 1), (key2980, 1), (key2716, 1), (key2716, 1), (key2711, 1), (key2711, 1), (key2980, -2), (key2716, -2), (key2716, -2), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, 1), (key2956, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2741, 2), (key2683, 2), (key2683, 2), (key2954, -2), (key2683, -2), (key2683, -2)]

def rawRow18284 : Integer.Sparse Key := [(key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2814, 2), (key2814, 2), (key2814, 2), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2711, -2), (key2711, -2), (key2711, -2), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2954, 2), (key2954, 2), (key2954, 2), (key2741, -2), (key2741, -2), (key2741, -2)]

def rawRow18285 : Integer.Sparse Key := [(key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2956, 2), (key2956, 2), (key2980, 2), (key2741, 1), (key2743, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2901, 1), (key2743, -2), (key2743, -2), (key2901, -2), (key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2683, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2680, 2), (key2680, 2), (key2711, 2), (key2680, -2), (key2680, -2), (key2814, -2)]

def rawRow18286 : Integer.Sparse Key := [(key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2956, 2), (key2980, 2), (key2956, 2), (key2743, 1), (key2741, 1), (key2901, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2743, -2), (key2901, -2), (key2743, -2), (key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2690, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2680, 2), (key2711, 2), (key2680, 2), (key2680, -2), (key2814, -2), (key2680, -2)]

def rawRow18287 : Integer.Sparse Key := [(key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2980, 2), (key2956, 2), (key2956, 2), (key2901, 1), (key2901, 1), (key2743, 1), (key2743, 1), (key2741, 1), (key2741, 1), (key2901, -2), (key2743, -2), (key2743, -2), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, 1), (key2819, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2711, 2), (key2680, 2), (key2680, 2), (key2814, -2), (key2680, -2), (key2680, -2)]

def rawRow18288 : Integer.Sparse Key := [(key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2954, 2), (key2954, 2), (key2954, 2), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2741, -2), (key2741, -2), (key2741, -2), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2814, 2), (key2814, 2), (key2814, 2), (key2711, -2), (key2711, -2), (key2711, -2)]

def rawRow18289 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2710, -1), (key2740, -1), (key2715, -1), (key2742, -1), (key2689, 2), (key2715, 2), (key2742, 2), (key3047, 1), (key3050, 1), (key3096, 1), (key3103, 1), (key3106, 1), (key3110, 1), (key3054, -2), (key3106, -2), (key3110, -2), (key3047, -1), (key3050, -1), (key3061, -1), (key3066, -1), (key3069, -1), (key3072, -1), (key3047, 1), (key3050, 1), (key3096, 1), (key3103, 1), (key3106, 1), (key3110, 1), (key3054, 2), (key3069, 2), (key3072, 2), (key3054, -2), (key3106, -2), (key3110, -2)]

def rawRow18290 : Integer.Sparse Key := [(key2682, -1), (key2679, -1), (key2740, -1), (key2710, -1), (key2742, -1), (key2715, -1), (key2689, 2), (key2742, 2), (key2715, 2), (key3050, 1), (key3047, 1), (key3103, 1), (key3096, 1), (key3110, 1), (key3106, 1), (key3054, -2), (key3110, -2), (key3106, -2), (key3050, -1), (key3047, -1), (key3066, -1), (key3061, -1), (key3072, -1), (key3069, -1), (key3050, 1), (key3047, 1), (key3103, 1), (key3096, 1), (key3110, 1), (key3106, 1), (key3054, 2), (key3072, 2), (key3069, 2), (key3054, -2), (key3110, -2), (key3106, -2)]

def rawRow18291 : Integer.Sparse Key := [(key2710, -1), (key2715, -1), (key2679, -1), (key2742, -1), (key2682, -1), (key2740, -1), (key2715, 2), (key2689, 2), (key2742, 2), (key3096, 1), (key3106, 1), (key3047, 1), (key3110, 1), (key3050, 1), (key3103, 1), (key3106, -2), (key3054, -2), (key3110, -2), (key3061, -1), (key3069, -1), (key3047, -1), (key3072, -1), (key3050, -1), (key3066, -1), (key3096, 1), (key3106, 1), (key3047, 1), (key3110, 1), (key3050, 1), (key3103, 1), (key3069, 2), (key3054, 2), (key3072, 2), (key3106, -2), (key3054, -2), (key3110, -2)]

def rawRow18292 : Integer.Sparse Key := [(key2715, -1), (key2710, -1), (key2742, -1), (key2679, -1), (key2740, -1), (key2682, -1), (key2715, 2), (key2742, 2), (key2689, 2), (key3106, 1), (key3096, 1), (key3110, 1), (key3047, 1), (key3103, 1), (key3050, 1), (key3106, -2), (key3110, -2), (key3054, -2), (key3069, -1), (key3061, -1), (key3072, -1), (key3047, -1), (key3066, -1), (key3050, -1), (key3106, 1), (key3096, 1), (key3110, 1), (key3047, 1), (key3103, 1), (key3050, 1), (key3069, 2), (key3072, 2), (key3054, 2), (key3106, -2), (key3110, -2), (key3054, -2)]

def rawRow18293 : Integer.Sparse Key := [(key2740, -1), (key2742, -1), (key2682, -1), (key2715, -1), (key2679, -1), (key2710, -1), (key2742, 2), (key2689, 2), (key2715, 2), (key3103, 1), (key3110, 1), (key3050, 1), (key3106, 1), (key3047, 1), (key3096, 1), (key3110, -2), (key3054, -2), (key3106, -2), (key3066, -1), (key3072, -1), (key3050, -1), (key3069, -1), (key3047, -1), (key3061, -1), (key3103, 1), (key3110, 1), (key3050, 1), (key3106, 1), (key3047, 1), (key3096, 1), (key3072, 2), (key3054, 2), (key3069, 2), (key3110, -2), (key3054, -2), (key3106, -2)]

def rawRow18294 : Integer.Sparse Key := [(key2742, -1), (key2740, -1), (key2715, -1), (key2682, -1), (key2710, -1), (key2679, -1), (key2742, 2), (key2715, 2), (key2689, 2), (key3110, 1), (key3103, 1), (key3106, 1), (key3050, 1), (key3096, 1), (key3047, 1), (key3110, -2), (key3106, -2), (key3054, -2), (key3072, -1), (key3066, -1), (key3069, -1), (key3050, -1), (key3061, -1), (key3047, -1), (key3110, 1), (key3103, 1), (key3106, 1), (key3050, 1), (key3096, 1), (key3047, 1), (key3072, 2), (key3069, 2), (key3054, 2), (key3110, -2), (key3106, -2), (key3054, -2)]

def rawRow18295 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2742, -1), (key2682, 2), (key2682, 2), (key2740, 2), (key2679, 1), (key2689, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3050, -2), (key3050, -2), (key3103, -2), (key3096, -1), (key3106, -1), (key3096, -1), (key3134, -1), (key3106, -1), (key3134, -1), (key3061, 1), (key3069, 1), (key3061, 1), (key3136, 1), (key3069, 1), (key3136, 1), (key3106, 2), (key3106, 2), (key3134, 2), (key3069, -2), (key3069, -2), (key3136, -2)]

def rawRow18296 : Integer.Sparse Key := [(key2689, -1), (key2679, -1), (key2742, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2682, 2), (key2740, 2), (key2682, 2), (key2689, 1), (key2679, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3050, -2), (key3103, -2), (key3050, -2), (key3106, -1), (key3096, -1), (key3134, -1), (key3096, -1), (key3134, -1), (key3106, -1), (key3069, 1), (key3061, 1), (key3136, 1), (key3061, 1), (key3136, 1), (key3069, 1), (key3106, 2), (key3134, 2), (key3106, 2), (key3069, -2), (key3136, -2), (key3069, -2)]

def rawRow18297 : Integer.Sparse Key := [(key2742, -1), (key2742, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key2679, -1), (key2740, 2), (key2682, 2), (key2682, 2), (key2955, 1), (key2955, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3047, 1), (key3103, -2), (key3050, -2), (key3050, -2), (key3134, -1), (key3134, -1), (key3106, -1), (key3106, -1), (key3096, -1), (key3096, -1), (key3136, 1), (key3136, 1), (key3069, 1), (key3069, 1), (key3061, 1), (key3061, 1), (key3134, 2), (key3106, 2), (key3106, 2), (key3136, -2), (key3069, -2), (key3069, -2)]

def rawRow18298 : Integer.Sparse Key := [(key2682, -1), (key2689, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2715, -1), (key2679, 2), (key2679, 2), (key2710, 2), (key2682, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2679, -2), (key3047, -2), (key3096, -2), (key3103, -1), (key3110, -1), (key3103, -1), (key3136, -1), (key3110, -1), (key3136, -1), (key3066, 1), (key3072, 1), (key3066, 1), (key3134, 1), (key3072, 1), (key3134, 1), (key3110, 2), (key3110, 2), (key3136, 2), (key3072, -2), (key3072, -2), (key3134, -2)]

def rawRow18299 : Integer.Sparse Key := [(key2689, -1), (key2682, -1), (key2715, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2679, 2), (key2710, 2), (key2679, 2), (key2689, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2679, -2), (key3096, -2), (key3047, -2), (key3110, -1), (key3103, -1), (key3136, -1), (key3103, -1), (key3136, -1), (key3110, -1), (key3072, 1), (key3066, 1), (key3134, 1), (key3066, 1), (key3134, 1), (key3072, 1), (key3110, 2), (key3136, 2), (key3110, 2), (key3072, -2), (key3134, -2), (key3072, -2)]

def rawRow18300 : Integer.Sparse Key := [(key2715, -1), (key2715, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2710, 2), (key2679, 2), (key2679, 2), (key2818, 1), (key2818, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2813, -2), (key2679, -2), (key3047, -2), (key3136, -1), (key3136, -1), (key3110, -1), (key3110, -1), (key3103, -1), (key3103, -1), (key3134, 1), (key3134, 1), (key3072, 1), (key3072, 1), (key3066, 1), (key3066, 1), (key3136, 2), (key3110, 2), (key3110, 2), (key3134, -2), (key3072, -2), (key3072, -2)]

def rawRow18301 : Integer.Sparse Key := [(key2813, -1), (key2818, -1), (key2813, -1), (key2900, -1), (key2818, -1), (key2900, -1), (key2818, 2), (key2818, 2), (key2900, 2), (key2710, 1), (key2715, 1), (key2710, 1), (key2979, 1), (key2715, 1), (key2979, 1), (key2715, -2), (key2715, -2), (key2979, -2), (key2679, -1), (key2689, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2742, -1), (key2679, 1), (key2689, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3050, 2), (key3050, 2), (key3066, 2), (key3050, -2), (key3050, -2), (key3103, -2)]

def rawRow18302 : Integer.Sparse Key := [(key2818, -1), (key2813, -1), (key2900, -1), (key2813, -1), (key2900, -1), (key2818, -1), (key2818, 2), (key2900, 2), (key2818, 2), (key2715, 1), (key2710, 1), (key2979, 1), (key2710, 1), (key2979, 1), (key2715, 1), (key2715, -2), (key2979, -2), (key2715, -2), (key2689, -1), (key2679, -1), (key2742, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2689, 1), (key2679, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3050, 2), (key3066, 2), (key3050, 2), (key3050, -2), (key3103, -2), (key3050, -2)]

def rawRow18303 : Integer.Sparse Key := [(key2900, -1), (key2900, -1), (key2818, -1), (key2818, -1), (key2813, -1), (key2813, -1), (key2900, 2), (key2818, 2), (key2818, 2), (key2979, 1), (key2979, 1), (key2715, 1), (key2715, 1), (key2710, 1), (key2710, 1), (key2979, -2), (key2715, -2), (key2715, -2), (key2742, -1), (key2742, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key2679, -1), (key2955, 1), (key2955, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3047, 1), (key3066, 2), (key3050, 2), (key3050, 2), (key3103, -2), (key3050, -2), (key3050, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18304 : Integer.Sparse Key := [(key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2813, 2), (key2813, 2), (key2813, 2), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2710, -2), (key2710, -2), (key2710, -2), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key3103, 2), (key3103, 2), (key3103, 2), (key3066, -2), (key3066, -2), (key3066, -2)]

def rawRow18305 : Integer.Sparse Key := [(key2953, -1), (key2955, -1), (key2953, -1), (key2979, -1), (key2955, -1), (key2979, -1), (key2955, 2), (key2955, 2), (key2979, 2), (key2740, 1), (key2742, 1), (key2740, 1), (key2900, 1), (key2742, 1), (key2900, 1), (key2742, -2), (key2742, -2), (key2900, -2), (key2682, -1), (key2689, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2715, -1), (key2682, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2679, 2), (key2679, 2), (key2710, 2), (key2679, -2), (key3047, -2), (key3096, -2)]

def rawRow18306 : Integer.Sparse Key := [(key2955, -1), (key2953, -1), (key2979, -1), (key2953, -1), (key2979, -1), (key2955, -1), (key2955, 2), (key2979, 2), (key2955, 2), (key2742, 1), (key2740, 1), (key2900, 1), (key2740, 1), (key2900, 1), (key2742, 1), (key2742, -2), (key2900, -2), (key2742, -2), (key2689, -1), (key2682, -1), (key2715, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2689, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2679, 2), (key2710, 2), (key2679, 2), (key2679, -2), (key3096, -2), (key3047, -2)]

def rawRow18307 : Integer.Sparse Key := [(key2979, -1), (key2979, -1), (key2955, -1), (key2955, -1), (key2953, -1), (key2953, -1), (key2979, 2), (key2955, 2), (key2955, 2), (key2900, 1), (key2900, 1), (key2742, 1), (key2742, 1), (key2740, 1), (key2740, 1), (key2900, -2), (key2742, -2), (key2742, -2), (key2715, -1), (key2715, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2818, 1), (key2818, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2710, 2), (key2679, 2), (key2679, 2), (key2813, -2), (key2679, -2), (key3047, -2)]

def rawRow18308 : Integer.Sparse Key := [(key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2953, 2), (key2953, 2), (key2953, 2), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2740, -2), (key2740, -2), (key2740, -2), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2813, 2), (key2813, 2), (key2813, 2), (key2710, -2), (key2710, -2), (key2710, -2)]

def rawRow18309 : Integer.Sparse Key := [(key2686, 2), (key2822, 2), (key2957, 2), (key2693, -1), (key2694, -1), (key2822, -1), (key2957, -1), (key2834, -1), (key2963, -1), (key2686, 2), (key2822, 2), (key2957, 2), (key2719, -1), (key2744, -1), (key2822, -1), (key2957, -1), (key2907, -1), (key2986, -1), (key2693, -1), (key2694, -1), (key2822, -1), (key2957, -1), (key2834, -1), (key2963, -1), (key2719, -1), (key2744, -1), (key2822, -1), (key2957, -1), (key2907, -1), (key2986, -1), (key2731, 2), (key2750, 2), (key2834, 2), (key2963, 2), (key2907, 2), (key2986, 2)]

def rawRow18310 : Integer.Sparse Key := [(key2686, 2), (key2957, 2), (key2822, 2), (key2694, -1), (key2693, -1), (key2957, -1), (key2822, -1), (key2963, -1), (key2834, -1), (key2686, 2), (key2957, 2), (key2822, 2), (key2744, -1), (key2719, -1), (key2957, -1), (key2822, -1), (key2986, -1), (key2907, -1), (key2694, -1), (key2693, -1), (key2957, -1), (key2822, -1), (key2963, -1), (key2834, -1), (key2744, -1), (key2719, -1), (key2957, -1), (key2822, -1), (key2986, -1), (key2907, -1), (key2750, 2), (key2731, 2), (key2963, 2), (key2834, 2), (key2986, 2), (key2907, 2)]

def rawRow18311 : Integer.Sparse Key := [(key2822, 2), (key2686, 2), (key2957, 2), (key2822, -1), (key2834, -1), (key2693, -1), (key2963, -1), (key2694, -1), (key2957, -1), (key2822, 2), (key2686, 2), (key2957, 2), (key2822, -1), (key2907, -1), (key2719, -1), (key2986, -1), (key2744, -1), (key2957, -1), (key2822, -1), (key2834, -1), (key2693, -1), (key2963, -1), (key2694, -1), (key2957, -1), (key2822, -1), (key2907, -1), (key2719, -1), (key2986, -1), (key2744, -1), (key2957, -1), (key2834, 2), (key2907, 2), (key2731, 2), (key2986, 2), (key2750, 2), (key2963, 2)]

def rawRow18312 : Integer.Sparse Key := [(key2822, 2), (key2957, 2), (key2686, 2), (key2834, -1), (key2822, -1), (key2963, -1), (key2693, -1), (key2957, -1), (key2694, -1), (key2822, 2), (key2957, 2), (key2686, 2), (key2907, -1), (key2822, -1), (key2986, -1), (key2719, -1), (key2957, -1), (key2744, -1), (key2834, -1), (key2822, -1), (key2963, -1), (key2693, -1), (key2957, -1), (key2694, -1), (key2907, -1), (key2822, -1), (key2986, -1), (key2719, -1), (key2957, -1), (key2744, -1), (key2907, 2), (key2834, 2), (key2986, 2), (key2731, 2), (key2963, 2), (key2750, 2)]

def rawRow18313 : Integer.Sparse Key := [(key2957, 2), (key2686, 2), (key2822, 2), (key2957, -1), (key2963, -1), (key2694, -1), (key2834, -1), (key2693, -1), (key2822, -1), (key2957, 2), (key2686, 2), (key2822, 2), (key2957, -1), (key2986, -1), (key2744, -1), (key2907, -1), (key2719, -1), (key2822, -1), (key2957, -1), (key2963, -1), (key2694, -1), (key2834, -1), (key2693, -1), (key2822, -1), (key2957, -1), (key2986, -1), (key2744, -1), (key2907, -1), (key2719, -1), (key2822, -1), (key2963, 2), (key2986, 2), (key2750, 2), (key2907, 2), (key2731, 2), (key2834, 2)]

def rawRow18314 : Integer.Sparse Key := [(key2957, 2), (key2822, 2), (key2686, 2), (key2963, -1), (key2957, -1), (key2834, -1), (key2694, -1), (key2822, -1), (key2693, -1), (key2957, 2), (key2822, 2), (key2686, 2), (key2986, -1), (key2957, -1), (key2907, -1), (key2744, -1), (key2822, -1), (key2719, -1), (key2963, -1), (key2957, -1), (key2834, -1), (key2694, -1), (key2822, -1), (key2693, -1), (key2986, -1), (key2957, -1), (key2907, -1), (key2744, -1), (key2822, -1), (key2719, -1), (key2986, 2), (key2963, 2), (key2907, 2), (key2750, 2), (key2834, 2), (key2731, 2)]

def rawRow18315 : Integer.Sparse Key := [(key2693, 2), (key2693, 2), (key2963, 2), (key2686, -1), (key2694, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2957, -1), (key2719, 2), (key2719, 2), (key2986, 2), (key2686, -1), (key2744, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2957, -1), (key2719, -1), (key2731, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2986, -1), (key2693, -1), (key2750, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2963, -1), (key2694, 2), (key2744, 2), (key2694, 2), (key2957, 2), (key2744, 2), (key2957, 2)]

def rawRow18316 : Integer.Sparse Key := [(key2693, 2), (key2963, 2), (key2693, 2), (key2694, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2719, 2), (key2986, 2), (key2719, 2), (key2744, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2731, -1), (key2719, -1), (key2986, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2750, -1), (key2693, -1), (key2963, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2744, 2), (key2694, 2), (key2957, 2), (key2694, 2), (key2957, 2), (key2744, 2)]

def rawRow18317 : Integer.Sparse Key := [(key2963, 2), (key2693, 2), (key2693, 2), (key2957, -1), (key2957, -1), (key2694, -1), (key2694, -1), (key2686, -1), (key2686, -1), (key2986, 2), (key2719, 2), (key2719, 2), (key2957, -1), (key2957, -1), (key2744, -1), (key2744, -1), (key2686, -1), (key2686, -1), (key2986, -1), (key2986, -1), (key2731, -1), (key2731, -1), (key2719, -1), (key2719, -1), (key2963, -1), (key2963, -1), (key2750, -1), (key2750, -1), (key2693, -1), (key2693, -1), (key2957, 2), (key2957, 2), (key2744, 2), (key2744, 2), (key2694, 2), (key2694, 2)]

def rawRow18318 : Integer.Sparse Key := [(key2694, 2), (key2694, 2), (key2834, 2), (key2686, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2822, -1), (key2744, 2), (key2744, 2), (key2907, 2), (key2686, -1), (key2719, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2822, -1), (key2744, -1), (key2750, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2907, -1), (key2694, -1), (key2731, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2834, -1), (key2693, 2), (key2719, 2), (key2693, 2), (key2822, 2), (key2719, 2), (key2822, 2)]

def rawRow18319 : Integer.Sparse Key := [(key2694, 2), (key2834, 2), (key2694, 2), (key2693, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2744, 2), (key2907, 2), (key2744, 2), (key2719, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2750, -1), (key2744, -1), (key2907, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2731, -1), (key2694, -1), (key2834, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2719, 2), (key2693, 2), (key2822, 2), (key2693, 2), (key2822, 2), (key2719, 2)]

def rawRow18320 : Integer.Sparse Key := [(key2834, 2), (key2694, 2), (key2694, 2), (key2822, -1), (key2822, -1), (key2693, -1), (key2693, -1), (key2686, -1), (key2686, -1), (key2907, 2), (key2744, 2), (key2744, 2), (key2822, -1), (key2822, -1), (key2719, -1), (key2719, -1), (key2686, -1), (key2686, -1), (key2907, -1), (key2907, -1), (key2750, -1), (key2750, -1), (key2744, -1), (key2744, -1), (key2834, -1), (key2834, -1), (key2731, -1), (key2731, -1), (key2694, -1), (key2694, -1), (key2822, 2), (key2822, 2), (key2719, 2), (key2719, 2), (key2693, 2), (key2693, 2)]

def rawRow18321 : Integer.Sparse Key := [(key2719, 2), (key2719, 2), (key2986, 2), (key2719, -1), (key2731, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2986, -1), (key2693, 2), (key2693, 2), (key2963, 2), (key2693, -1), (key2750, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2963, -1), (key2686, -1), (key2694, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2957, -1), (key2686, -1), (key2744, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2957, -1), (key2694, 2), (key2744, 2), (key2694, 2), (key2957, 2), (key2744, 2), (key2957, 2)]

def rawRow18322 : Integer.Sparse Key := [(key2719, 2), (key2986, 2), (key2719, 2), (key2731, -1), (key2719, -1), (key2986, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2693, 2), (key2963, 2), (key2693, 2), (key2750, -1), (key2693, -1), (key2963, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2694, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2744, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2744, 2), (key2694, 2), (key2957, 2), (key2694, 2), (key2957, 2), (key2744, 2)]

def rawRow18323 : Integer.Sparse Key := [(key2986, 2), (key2719, 2), (key2719, 2), (key2986, -1), (key2986, -1), (key2731, -1), (key2731, -1), (key2719, -1), (key2719, -1), (key2963, 2), (key2693, 2), (key2693, 2), (key2963, -1), (key2963, -1), (key2750, -1), (key2750, -1), (key2693, -1), (key2693, -1), (key2957, -1), (key2957, -1), (key2694, -1), (key2694, -1), (key2686, -1), (key2686, -1), (key2957, -1), (key2957, -1), (key2744, -1), (key2744, -1), (key2686, -1), (key2686, -1), (key2957, 2), (key2957, 2), (key2744, 2), (key2744, 2), (key2694, 2), (key2694, 2)]

def rawRow18324 : Integer.Sparse Key := [(key2731, 2), (key2731, 2), (key2731, 2), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2750, 2), (key2750, 2), (key2750, 2), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2)]

def rawRow18325 : Integer.Sparse Key := [(key2744, 2), (key2744, 2), (key2907, 2), (key2744, -1), (key2750, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2907, -1), (key2694, 2), (key2694, 2), (key2834, 2), (key2694, -1), (key2731, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2834, -1), (key2686, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2822, -1), (key2686, -1), (key2719, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2822, -1), (key2693, 2), (key2719, 2), (key2693, 2), (key2822, 2), (key2719, 2), (key2822, 2)]

def rawRow18326 : Integer.Sparse Key := [(key2744, 2), (key2907, 2), (key2744, 2), (key2750, -1), (key2744, -1), (key2907, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2694, 2), (key2834, 2), (key2694, 2), (key2731, -1), (key2694, -1), (key2834, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2719, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2719, 2), (key2693, 2), (key2822, 2), (key2693, 2), (key2822, 2), (key2719, 2)]

def rawRow18327 : Integer.Sparse Key := [(key2907, 2), (key2744, 2), (key2744, 2), (key2907, -1), (key2907, -1), (key2750, -1), (key2750, -1), (key2744, -1), (key2744, -1), (key2834, 2), (key2694, 2), (key2694, 2), (key2834, -1), (key2834, -1), (key2731, -1), (key2731, -1), (key2694, -1), (key2694, -1), (key2822, -1), (key2822, -1), (key2693, -1), (key2693, -1), (key2686, -1), (key2686, -1), (key2822, -1), (key2822, -1), (key2719, -1), (key2719, -1), (key2686, -1), (key2686, -1), (key2822, 2), (key2822, 2), (key2719, 2), (key2719, 2), (key2693, 2), (key2693, 2)]

def rawRow18328 : Integer.Sparse Key := [(key2750, 2), (key2750, 2), (key2750, 2), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2731, 2), (key2731, 2), (key2731, 2), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2)]

def rawRow18329 : Integer.Sparse Key := [(key2114, 4), (key2118, 4), (key2122, 4), (key2114, -2), (key2118, -2), (key2156, -2), (key2183, -2), (key2162, -2), (key2185, -2), (key2114, -2), (key2118, -2), (key2156, -2), (key2183, -2), (key2162, -2), (key2185, -2), (key2156, 4), (key2183, 4), (key2285, 4)]

def rawRow18330 : Integer.Sparse Key := [(key2118, 4), (key2114, 4), (key2122, 4), (key2118, -2), (key2114, -2), (key2183, -2), (key2156, -2), (key2185, -2), (key2162, -2), (key2118, -2), (key2114, -2), (key2183, -2), (key2156, -2), (key2185, -2), (key2162, -2), (key2183, 4), (key2156, 4), (key2285, 4)]

def rawRow18331 : Integer.Sparse Key := [(key2114, 4), (key2122, 4), (key2118, 4), (key2156, -2), (key2162, -2), (key2114, -2), (key2185, -2), (key2118, -2), (key2183, -2), (key2156, -2), (key2162, -2), (key2114, -2), (key2185, -2), (key2118, -2), (key2183, -2), (key2156, 4), (key2285, 4), (key2183, 4)]

def rawRow18332 : Integer.Sparse Key := [(key2122, 4), (key2114, 4), (key2118, 4), (key2162, -2), (key2156, -2), (key2185, -2), (key2114, -2), (key2183, -2), (key2118, -2), (key2162, -2), (key2156, -2), (key2185, -2), (key2114, -2), (key2183, -2), (key2118, -2), (key2285, 4), (key2156, 4), (key2183, 4)]

def rawRow18333 : Integer.Sparse Key := [(key2118, 4), (key2122, 4), (key2114, 4), (key2183, -2), (key2185, -2), (key2118, -2), (key2162, -2), (key2114, -2), (key2156, -2), (key2183, -2), (key2185, -2), (key2118, -2), (key2162, -2), (key2114, -2), (key2156, -2), (key2183, 4), (key2285, 4), (key2156, 4)]

def rawRow18334 : Integer.Sparse Key := [(key2122, 4), (key2118, 4), (key2114, 4), (key2185, -2), (key2183, -2), (key2162, -2), (key2118, -2), (key2156, -2), (key2114, -2), (key2185, -2), (key2183, -2), (key2162, -2), (key2118, -2), (key2156, -2), (key2114, -2), (key2285, 4), (key2183, 4), (key2156, 4)]

def rawRow18335 : Integer.Sparse Key := [(key2156, 4), (key2162, 4), (key2162, 4), (key2114, -2), (key2122, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2185, -2), (key2156, -2), (key2162, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2285, -2), (key2114, 4), (key2185, 4), (key2185, 4)]

def rawRow18336 : Integer.Sparse Key := [(key2162, 4), (key2156, 4), (key2162, 4), (key2122, -2), (key2114, -2), (key2185, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2162, -2), (key2156, -2), (key2285, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2185, 4), (key2114, 4), (key2185, 4)]

def rawRow18337 : Integer.Sparse Key := [(key2162, 4), (key2162, 4), (key2156, 4), (key2185, -2), (key2185, -2), (key2122, -2), (key2122, -2), (key2114, -2), (key2114, -2), (key2285, -2), (key2285, -2), (key2162, -2), (key2162, -2), (key2156, -2), (key2156, -2), (key2185, 4), (key2185, 4), (key2114, 4)]

def rawRow18338 : Integer.Sparse Key := [(key2183, 4), (key2185, 4), (key2185, 4), (key2118, -2), (key2122, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2162, -2), (key2183, -2), (key2185, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2285, -2), (key2118, 4), (key2162, 4), (key2162, 4)]

def rawRow18339 : Integer.Sparse Key := [(key2185, 4), (key2183, 4), (key2185, 4), (key2122, -2), (key2118, -2), (key2162, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2185, -2), (key2183, -2), (key2285, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2162, 4), (key2118, 4), (key2162, 4)]

def rawRow18340 : Integer.Sparse Key := [(key2185, 4), (key2185, 4), (key2183, 4), (key2162, -2), (key2162, -2), (key2122, -2), (key2122, -2), (key2118, -2), (key2118, -2), (key2285, -2), (key2285, -2), (key2185, -2), (key2185, -2), (key2183, -2), (key2183, -2), (key2162, 4), (key2162, 4), (key2118, 4)]

def rawRow18341 : Integer.Sparse Key := [(key2156, 4), (key2162, 4), (key2162, 4), (key2156, -2), (key2162, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2285, -2), (key2114, -2), (key2122, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2185, -2), (key2114, 4), (key2185, 4), (key2185, 4)]

def rawRow18342 : Integer.Sparse Key := [(key2162, 4), (key2156, 4), (key2162, 4), (key2162, -2), (key2156, -2), (key2285, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2122, -2), (key2114, -2), (key2185, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2185, 4), (key2114, 4), (key2185, 4)]

def rawRow18343 : Integer.Sparse Key := [(key2162, 4), (key2162, 4), (key2156, 4), (key2285, -2), (key2285, -2), (key2162, -2), (key2162, -2), (key2156, -2), (key2156, -2), (key2185, -2), (key2185, -2), (key2122, -2), (key2122, -2), (key2114, -2), (key2114, -2), (key2185, 4), (key2185, 4), (key2114, 4)]

def rawRow18344 : Integer.Sparse Key := [(key2285, 4), (key2285, 4), (key2285, 4), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2122, 4), (key2122, 4), (key2122, 4)]

def rawRow18345 : Integer.Sparse Key := [(key2183, 4), (key2185, 4), (key2185, 4), (key2183, -2), (key2185, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2285, -2), (key2118, -2), (key2122, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2162, -2), (key2118, 4), (key2162, 4), (key2162, 4)]

def rawRow18346 : Integer.Sparse Key := [(key2185, 4), (key2183, 4), (key2185, 4), (key2185, -2), (key2183, -2), (key2285, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2122, -2), (key2118, -2), (key2162, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2162, 4), (key2118, 4), (key2162, 4)]

def rawRow18347 : Integer.Sparse Key := [(key2185, 4), (key2185, 4), (key2183, 4), (key2285, -2), (key2285, -2), (key2185, -2), (key2185, -2), (key2183, -2), (key2183, -2), (key2162, -2), (key2162, -2), (key2122, -2), (key2122, -2), (key2118, -2), (key2118, -2), (key2162, 4), (key2162, 4), (key2118, 4)]

def rawRow18348 : Integer.Sparse Key := [(key2285, 4), (key2285, 4), (key2285, 4), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2122, 4), (key2122, 4), (key2122, 4)]

def rawRow18349 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, -2), (key2112, -2), (key2110, -2), (key2113, -2), (key2107, 2), (key2112, 2), (key2140, 2), (key2110, 2), (key2113, 2), (key2140, 2), (key2107, 2), (key2112, 2), (key2140, 2), (key2140, -6), (key2110, 2), (key2113, 2), (key2140, 2), (key2140, -6)]

def rawRow18350 : Integer.Sparse Key := [(key2104, -2), (key2102, -2), (key2112, -2), (key2107, -2), (key2113, -2), (key2110, -2), (key2112, 2), (key2107, 2), (key2140, 2), (key2113, 2), (key2110, 2), (key2140, 2), (key2112, 2), (key2107, 2), (key2140, 2), (key2140, -6), (key2113, 2), (key2110, 2), (key2140, 2), (key2140, -6)]

def rawRow18351 : Integer.Sparse Key := [(key2107, -2), (key2110, -2), (key2102, -2), (key2113, -2), (key2104, -2), (key2112, -2), (key2107, 2), (key2140, 2), (key2112, 2), (key2110, 2), (key2140, 2), (key2113, 2), (key2107, 2), (key2140, 2), (key2112, 2), (key2140, -6), (key2110, 2), (key2140, 2), (key2113, 2), (key2140, -6)]

def rawRow18352 : Integer.Sparse Key := [(key2110, -2), (key2107, -2), (key2113, -2), (key2102, -2), (key2112, -2), (key2104, -2), (key2140, 2), (key2107, 2), (key2112, 2), (key2140, 2), (key2110, 2), (key2113, 2), (key2140, 2), (key2107, 2), (key2112, 2), (key2140, -6), (key2140, 2), (key2110, 2), (key2113, 2), (key2140, -6)]

def rawRow18353 : Integer.Sparse Key := [(key2112, -2), (key2113, -2), (key2104, -2), (key2110, -2), (key2102, -2), (key2107, -2), (key2112, 2), (key2140, 2), (key2107, 2), (key2113, 2), (key2140, 2), (key2110, 2), (key2112, 2), (key2140, 2), (key2107, 2), (key2140, -6), (key2113, 2), (key2140, 2), (key2110, 2), (key2140, -6)]

def rawRow18354 : Integer.Sparse Key := [(key2113, -2), (key2112, -2), (key2110, -2), (key2104, -2), (key2107, -2), (key2102, -2), (key2140, 2), (key2112, 2), (key2107, 2), (key2140, 2), (key2113, 2), (key2110, 2), (key2140, 2), (key2112, 2), (key2107, 2), (key2140, -6), (key2140, 2), (key2113, 2), (key2110, 2), (key2140, -6)]

def rawRow18355 : Integer.Sparse Key := [(key2107, -2), (key2110, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2140, -2), (key2102, 2), (key2113, 2), (key2113, 2), (key2104, 2), (key2112, 2), (key2112, 2), (key2107, 2), (key2140, 2), (key2140, 2), (key2112, -6), (key2110, 2), (key2140, 2), (key2140, 2), (key2113, -6)]

def rawRow18356 : Integer.Sparse Key := [(key2110, -2), (key2107, -2), (key2140, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2113, 2), (key2102, 2), (key2113, 2), (key2112, 2), (key2104, 2), (key2112, 2), (key2140, 2), (key2107, 2), (key2140, 2), (key2112, -6), (key2140, 2), (key2110, 2), (key2140, 2), (key2113, -6)]

def rawRow18357 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2110, -2), (key2110, -2), (key2107, -2), (key2107, -2), (key2113, 2), (key2113, 2), (key2102, 2), (key2112, 2), (key2112, 2), (key2104, 2), (key2140, 2), (key2140, 2), (key2107, 2), (key2112, -6), (key2140, 2), (key2140, 2), (key2110, 2), (key2113, -6)]

def rawRow18358 : Integer.Sparse Key := [(key2112, -2), (key2113, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2140, -2), (key2104, 2), (key2110, 2), (key2110, 2), (key2102, 2), (key2107, 2), (key2107, 2), (key2112, 2), (key2140, 2), (key2140, 2), (key2107, -6), (key2113, 2), (key2140, 2), (key2140, 2), (key2110, -6)]

def rawRow18359 : Integer.Sparse Key := [(key2113, -2), (key2112, -2), (key2140, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2110, 2), (key2104, 2), (key2110, 2), (key2107, 2), (key2102, 2), (key2107, 2), (key2140, 2), (key2112, 2), (key2140, 2), (key2107, -6), (key2140, 2), (key2113, 2), (key2140, 2), (key2110, -6)]

def rawRow18360 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2113, -2), (key2113, -2), (key2112, -2), (key2112, -2), (key2110, 2), (key2110, 2), (key2104, 2), (key2107, 2), (key2107, 2), (key2102, 2), (key2140, 2), (key2140, 2), (key2112, 2), (key2107, -6), (key2140, 2), (key2140, 2), (key2113, 2), (key2110, -6)]

def rawRow18361 : Integer.Sparse Key := [(key2107, -2), (key2110, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2140, -2), (key2107, 2), (key2140, 2), (key2140, 2), (key2110, 2), (key2140, 2), (key2140, 2), (key2102, 2), (key2113, 2), (key2113, 2), (key2113, -6), (key2104, 2), (key2112, 2), (key2112, 2), (key2112, -6)]

def rawRow18362 : Integer.Sparse Key := [(key2110, -2), (key2107, -2), (key2140, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2140, 2), (key2107, 2), (key2140, 2), (key2140, 2), (key2110, 2), (key2140, 2), (key2113, 2), (key2102, 2), (key2113, 2), (key2113, -6), (key2112, 2), (key2104, 2), (key2112, 2), (key2112, -6)]

def rawRow18363 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2110, -2), (key2110, -2), (key2107, -2), (key2107, -2), (key2140, 2), (key2140, 2), (key2107, 2), (key2140, 2), (key2140, 2), (key2110, 2), (key2113, 2), (key2113, 2), (key2102, 2), (key2113, -6), (key2112, 2), (key2112, 2), (key2104, 2), (key2112, -6)]

def rawRow18364 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2110, 2), (key2110, 2), (key2110, 2), (key2107, 2), (key2107, 2), (key2107, 2), (key2113, 2), (key2113, 2), (key2113, 2), (key2102, -6), (key2112, 2), (key2112, 2), (key2112, 2), (key2104, -6)]

def rawRow18365 : Integer.Sparse Key := [(key2112, -2), (key2113, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2140, -2), (key2112, 2), (key2140, 2), (key2140, 2), (key2113, 2), (key2140, 2), (key2140, 2), (key2104, 2), (key2110, 2), (key2110, 2), (key2110, -6), (key2102, 2), (key2107, 2), (key2107, 2), (key2107, -6)]

def rawRow18366 : Integer.Sparse Key := [(key2113, -2), (key2112, -2), (key2140, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2140, 2), (key2112, 2), (key2140, 2), (key2140, 2), (key2113, 2), (key2140, 2), (key2110, 2), (key2104, 2), (key2110, 2), (key2110, -6), (key2107, 2), (key2102, 2), (key2107, 2), (key2107, -6)]

def rawRow18367 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2113, -2), (key2113, -2), (key2112, -2), (key2112, -2), (key2140, 2), (key2140, 2), (key2112, 2), (key2140, 2), (key2140, 2), (key2113, 2), (key2110, 2), (key2110, 2), (key2104, 2), (key2110, -6), (key2107, 2), (key2107, 2), (key2102, 2), (key2107, -6)]

def rawRow18368 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2113, 2), (key2113, 2), (key2113, 2), (key2112, 2), (key2112, 2), (key2112, 2), (key2110, 2), (key2110, 2), (key2110, 2), (key2104, -6), (key2107, 2), (key2107, 2), (key2107, 2), (key2102, -6)]

def rawRow18369 : Integer.Sparse Key := [(key1945, 4), (key1947, 4), (key1948, 4), (key1947, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1952, 12)]

def rawRow18370 : Integer.Sparse Key := [(key1945, 4), (key1948, 4), (key1947, 4), (key1948, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1952, 12)]

def rawRow18371 : Integer.Sparse Key := [(key1947, 4), (key1945, 4), (key1948, 4), (key1947, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1952, 12)]

def rawRow18372 : Integer.Sparse Key := [(key1947, 4), (key1948, 4), (key1945, 4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, 12)]

def rawRow18373 : Integer.Sparse Key := [(key1948, 4), (key1945, 4), (key1947, 4), (key1948, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1952, 12)]

def rawRow18374 : Integer.Sparse Key := [(key1948, 4), (key1947, 4), (key1945, 4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, 12)]

def rawRow18375 : Integer.Sparse Key := [(key1947, 4), (key1947, 4), (key1952, 4), (key1945, -4), (key1948, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1952, -4), (key1948, 12)]

def rawRow18376 : Integer.Sparse Key := [(key1947, 4), (key1952, 4), (key1947, 4), (key1948, -4), (key1945, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1952, -4), (key1948, 12)]

def rawRow18377 : Integer.Sparse Key := [(key1952, 4), (key1947, 4), (key1947, 4), (key1948, -4), (key1948, -4), (key1945, -4), (key1952, -4), (key1952, -4), (key1947, -4), (key1948, 12)]

def rawRow18378 : Integer.Sparse Key := [(key1948, 4), (key1948, 4), (key1952, 4), (key1945, -4), (key1947, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1952, -4), (key1947, 12)]

def rawRow18379 : Integer.Sparse Key := [(key1948, 4), (key1952, 4), (key1948, 4), (key1947, -4), (key1945, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1952, -4), (key1947, 12)]

def rawRow18380 : Integer.Sparse Key := [(key1952, 4), (key1948, 4), (key1948, 4), (key1947, -4), (key1947, -4), (key1945, -4), (key1952, -4), (key1952, -4), (key1948, -4), (key1947, 12)]

def rawRow18381 : Integer.Sparse Key := [(key1947, 4), (key1947, 4), (key1952, 4), (key1947, -4), (key1952, -4), (key1952, -4), (key1945, -4), (key1948, -4), (key1948, -4), (key1948, 12)]

def rawRow18382 : Integer.Sparse Key := [(key1947, 4), (key1952, 4), (key1947, 4), (key1952, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1945, -4), (key1948, -4), (key1948, 12)]

def rawRow18383 : Integer.Sparse Key := [(key1952, 4), (key1947, 4), (key1947, 4), (key1952, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1948, -4), (key1945, -4), (key1948, 12)]

def rawRow18384 : Integer.Sparse Key := [(key1952, 4), (key1952, 4), (key1952, 4), (key1947, -4), (key1947, -4), (key1947, -4), (key1948, -4), (key1948, -4), (key1948, -4), (key1945, 12)]

def rawRow18385 : Integer.Sparse Key := [(key1948, 4), (key1948, 4), (key1952, 4), (key1948, -4), (key1952, -4), (key1952, -4), (key1945, -4), (key1947, -4), (key1947, -4), (key1947, 12)]

def rawRow18386 : Integer.Sparse Key := [(key1948, 4), (key1952, 4), (key1948, 4), (key1952, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1945, -4), (key1947, -4), (key1947, 12)]

def rawRow18387 : Integer.Sparse Key := [(key1952, 4), (key1948, 4), (key1948, 4), (key1952, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1947, -4), (key1945, -4), (key1947, 12)]

def rawRow18388 : Integer.Sparse Key := [(key1952, 4), (key1952, 4), (key1952, 4), (key1948, -4), (key1948, -4), (key1948, -4), (key1947, -4), (key1947, -4), (key1947, -4), (key1945, 12)]

def rawRow18389 : Integer.Sparse Key := [(key2117, 4), (key2119, 4), (key2123, 4), (key2117, -2), (key2119, -2), (key2159, -2), (key2184, -2), (key2163, -2), (key2186, -2), (key2117, -2), (key2119, -2), (key2159, -2), (key2184, -2), (key2163, -2), (key2186, -2), (key2159, 4), (key2184, 4), (key2286, 4)]

def rawRow18390 : Integer.Sparse Key := [(key2119, 4), (key2117, 4), (key2123, 4), (key2119, -2), (key2117, -2), (key2184, -2), (key2159, -2), (key2186, -2), (key2163, -2), (key2119, -2), (key2117, -2), (key2184, -2), (key2159, -2), (key2186, -2), (key2163, -2), (key2184, 4), (key2159, 4), (key2286, 4)]

def rawRow18391 : Integer.Sparse Key := [(key2117, 4), (key2123, 4), (key2119, 4), (key2159, -2), (key2163, -2), (key2117, -2), (key2186, -2), (key2119, -2), (key2184, -2), (key2159, -2), (key2163, -2), (key2117, -2), (key2186, -2), (key2119, -2), (key2184, -2), (key2159, 4), (key2286, 4), (key2184, 4)]

def rawRow18392 : Integer.Sparse Key := [(key2123, 4), (key2117, 4), (key2119, 4), (key2163, -2), (key2159, -2), (key2186, -2), (key2117, -2), (key2184, -2), (key2119, -2), (key2163, -2), (key2159, -2), (key2186, -2), (key2117, -2), (key2184, -2), (key2119, -2), (key2286, 4), (key2159, 4), (key2184, 4)]

def rawRow18393 : Integer.Sparse Key := [(key2119, 4), (key2123, 4), (key2117, 4), (key2184, -2), (key2186, -2), (key2119, -2), (key2163, -2), (key2117, -2), (key2159, -2), (key2184, -2), (key2186, -2), (key2119, -2), (key2163, -2), (key2117, -2), (key2159, -2), (key2184, 4), (key2286, 4), (key2159, 4)]

def rawRow18394 : Integer.Sparse Key := [(key2123, 4), (key2119, 4), (key2117, 4), (key2186, -2), (key2184, -2), (key2163, -2), (key2119, -2), (key2159, -2), (key2117, -2), (key2186, -2), (key2184, -2), (key2163, -2), (key2119, -2), (key2159, -2), (key2117, -2), (key2286, 4), (key2184, 4), (key2159, 4)]

def rawRow18395 : Integer.Sparse Key := [(key2159, 4), (key2163, 4), (key2163, 4), (key2117, -2), (key2123, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2186, -2), (key2159, -2), (key2163, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2286, -2), (key2117, 4), (key2186, 4), (key2186, 4)]

def rawRow18396 : Integer.Sparse Key := [(key2163, 4), (key2159, 4), (key2163, 4), (key2123, -2), (key2117, -2), (key2186, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2163, -2), (key2159, -2), (key2286, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2186, 4), (key2117, 4), (key2186, 4)]

def rawRow18397 : Integer.Sparse Key := [(key2163, 4), (key2163, 4), (key2159, 4), (key2186, -2), (key2186, -2), (key2123, -2), (key2123, -2), (key2117, -2), (key2117, -2), (key2286, -2), (key2286, -2), (key2163, -2), (key2163, -2), (key2159, -2), (key2159, -2), (key2186, 4), (key2186, 4), (key2117, 4)]

def rawRow18398 : Integer.Sparse Key := [(key2184, 4), (key2186, 4), (key2186, 4), (key2119, -2), (key2123, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2163, -2), (key2184, -2), (key2186, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2286, -2), (key2119, 4), (key2163, 4), (key2163, 4)]

def rawRow18399 : Integer.Sparse Key := [(key2186, 4), (key2184, 4), (key2186, 4), (key2123, -2), (key2119, -2), (key2163, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2186, -2), (key2184, -2), (key2286, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2163, 4), (key2119, 4), (key2163, 4)]

def rawRow18400 : Integer.Sparse Key := [(key2186, 4), (key2186, 4), (key2184, 4), (key2163, -2), (key2163, -2), (key2123, -2), (key2123, -2), (key2119, -2), (key2119, -2), (key2286, -2), (key2286, -2), (key2186, -2), (key2186, -2), (key2184, -2), (key2184, -2), (key2163, 4), (key2163, 4), (key2119, 4)]

def rawRow18401 : Integer.Sparse Key := [(key2159, 4), (key2163, 4), (key2163, 4), (key2159, -2), (key2163, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2286, -2), (key2117, -2), (key2123, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2186, -2), (key2117, 4), (key2186, 4), (key2186, 4)]

def rawRow18402 : Integer.Sparse Key := [(key2163, 4), (key2159, 4), (key2163, 4), (key2163, -2), (key2159, -2), (key2286, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2123, -2), (key2117, -2), (key2186, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2186, 4), (key2117, 4), (key2186, 4)]

def rawRow18403 : Integer.Sparse Key := [(key2163, 4), (key2163, 4), (key2159, 4), (key2286, -2), (key2286, -2), (key2163, -2), (key2163, -2), (key2159, -2), (key2159, -2), (key2186, -2), (key2186, -2), (key2123, -2), (key2123, -2), (key2117, -2), (key2117, -2), (key2186, 4), (key2186, 4), (key2117, 4)]

def rawRow18404 : Integer.Sparse Key := [(key2286, 4), (key2286, 4), (key2286, 4), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2123, 4), (key2123, 4), (key2123, 4)]

def rawRow18405 : Integer.Sparse Key := [(key2184, 4), (key2186, 4), (key2186, 4), (key2184, -2), (key2186, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2286, -2), (key2119, -2), (key2123, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2163, -2), (key2119, 4), (key2163, 4), (key2163, 4)]

def rawRow18406 : Integer.Sparse Key := [(key2186, 4), (key2184, 4), (key2186, 4), (key2186, -2), (key2184, -2), (key2286, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2123, -2), (key2119, -2), (key2163, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2163, 4), (key2119, 4), (key2163, 4)]

def rawRow18407 : Integer.Sparse Key := [(key2186, 4), (key2186, 4), (key2184, 4), (key2286, -2), (key2286, -2), (key2186, -2), (key2186, -2), (key2184, -2), (key2184, -2), (key2163, -2), (key2163, -2), (key2123, -2), (key2123, -2), (key2119, -2), (key2119, -2), (key2163, 4), (key2163, 4), (key2119, 4)]

def rawRow18408 : Integer.Sparse Key := [(key2286, 4), (key2286, 4), (key2286, 4), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2123, 4), (key2123, 4), (key2123, 4)]

def rawRow18409 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, -2), (key3088, -2), (key3090, -2), (key3091, -2), (key3086, 2), (key3088, 2), (key3109, 2), (key3090, 2), (key3091, 2), (key3109, 2), (key3086, 2), (key3088, 2), (key3109, 2), (key3109, -6), (key3090, 2), (key3091, 2), (key3109, 2), (key3109, -6)]

def rawRow18410 : Integer.Sparse Key := [(key3082, -2), (key3081, -2), (key3088, -2), (key3086, -2), (key3091, -2), (key3090, -2), (key3088, 2), (key3086, 2), (key3109, 2), (key3091, 2), (key3090, 2), (key3109, 2), (key3088, 2), (key3086, 2), (key3109, 2), (key3109, -6), (key3091, 2), (key3090, 2), (key3109, 2), (key3109, -6)]

def rawRow18411 : Integer.Sparse Key := [(key3086, -2), (key3088, -2), (key3081, -2), (key3091, -2), (key3082, -2), (key3088, -2), (key3086, 2), (key3109, 2), (key3088, 2), (key3090, 2), (key3109, 2), (key3091, 2), (key3086, 2), (key3109, 2), (key3088, 2), (key3109, -6), (key3090, 2), (key3109, 2), (key3091, 2), (key3109, -6)]

def rawRow18412 : Integer.Sparse Key := [(key3088, -2), (key3086, -2), (key3091, -2), (key3081, -2), (key3088, -2), (key3082, -2), (key3109, 2), (key3086, 2), (key3088, 2), (key3109, 2), (key3090, 2), (key3091, 2), (key3109, 2), (key3086, 2), (key3088, 2), (key3109, -6), (key3109, 2), (key3090, 2), (key3091, 2), (key3109, -6)]

def rawRow18413 : Integer.Sparse Key := [(key3090, -2), (key3091, -2), (key3082, -2), (key3088, -2), (key3081, -2), (key3086, -2), (key3088, 2), (key3109, 2), (key3086, 2), (key3091, 2), (key3109, 2), (key3090, 2), (key3088, 2), (key3109, 2), (key3086, 2), (key3109, -6), (key3091, 2), (key3109, 2), (key3090, 2), (key3109, -6)]

def rawRow18414 : Integer.Sparse Key := [(key3091, -2), (key3090, -2), (key3088, -2), (key3082, -2), (key3086, -2), (key3081, -2), (key3109, 2), (key3088, 2), (key3086, 2), (key3109, 2), (key3091, 2), (key3090, 2), (key3109, 2), (key3088, 2), (key3086, 2), (key3109, -6), (key3109, 2), (key3091, 2), (key3090, 2), (key3109, -6)]

def rawRow18415 : Integer.Sparse Key := [(key3086, -2), (key3088, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3109, -2), (key3081, 2), (key3091, 2), (key3091, 2), (key3082, 2), (key3088, 2), (key3088, 2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, -6), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, -6)]

def rawRow18416 : Integer.Sparse Key := [(key3088, -2), (key3086, -2), (key3109, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3091, 2), (key3081, 2), (key3091, 2), (key3088, 2), (key3082, 2), (key3088, 2), (key3109, 2), (key3086, 2), (key3109, 2), (key3088, -6), (key3109, 2), (key3090, 2), (key3109, 2), (key3091, -6)]

def rawRow18417 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3088, -2), (key3088, -2), (key3086, -2), (key3086, -2), (key3091, 2), (key3091, 2), (key3081, 2), (key3088, 2), (key3088, 2), (key3082, 2), (key3109, 2), (key3109, 2), (key3086, 2), (key3088, -6), (key3109, 2), (key3109, 2), (key3090, 2), (key3091, -6)]

def rawRow18418 : Integer.Sparse Key := [(key3090, -2), (key3091, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3109, -2), (key3082, 2), (key3088, 2), (key3088, 2), (key3081, 2), (key3086, 2), (key3086, 2), (key3088, 2), (key3109, 2), (key3109, 2), (key3086, -6), (key3091, 2), (key3109, 2), (key3109, 2), (key3090, -6)]

def rawRow18419 : Integer.Sparse Key := [(key3091, -2), (key3090, -2), (key3109, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3088, 2), (key3082, 2), (key3088, 2), (key3086, 2), (key3081, 2), (key3086, 2), (key3109, 2), (key3088, 2), (key3109, 2), (key3086, -6), (key3109, 2), (key3091, 2), (key3109, 2), (key3090, -6)]

def rawRow18420 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3091, -2), (key3091, -2), (key3090, -2), (key3090, -2), (key3088, 2), (key3088, 2), (key3082, 2), (key3086, 2), (key3086, 2), (key3081, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3086, -6), (key3109, 2), (key3109, 2), (key3091, 2), (key3090, -6)]

def rawRow18421 : Integer.Sparse Key := [(key3086, -2), (key3088, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3109, -2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3109, 2), (key3109, 2), (key3081, 2), (key3091, 2), (key3091, 2), (key3091, -6), (key3082, 2), (key3088, 2), (key3088, 2), (key3088, -6)]

def rawRow18422 : Integer.Sparse Key := [(key3088, -2), (key3086, -2), (key3109, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3109, 2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3109, 2), (key3091, 2), (key3081, 2), (key3091, 2), (key3091, -6), (key3088, 2), (key3082, 2), (key3088, 2), (key3088, -6)]

def rawRow18423 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3088, -2), (key3088, -2), (key3086, -2), (key3086, -2), (key3109, 2), (key3109, 2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3091, 2), (key3091, 2), (key3081, 2), (key3091, -6), (key3088, 2), (key3088, 2), (key3082, 2), (key3088, -6)]

def rawRow18424 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3088, 2), (key3088, 2), (key3088, 2), (key3086, 2), (key3086, 2), (key3086, 2), (key3091, 2), (key3091, 2), (key3091, 2), (key3081, -6), (key3088, 2), (key3088, 2), (key3088, 2), (key3082, -6)]

def rawRow18425 : Integer.Sparse Key := [(key3090, -2), (key3091, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3109, -2), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, 2), (key3109, 2), (key3109, 2), (key3082, 2), (key3088, 2), (key3088, 2), (key3088, -6), (key3081, 2), (key3086, 2), (key3086, 2), (key3086, -6)]

def rawRow18426 : Integer.Sparse Key := [(key3091, -2), (key3090, -2), (key3109, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3109, 2), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, 2), (key3109, 2), (key3088, 2), (key3082, 2), (key3088, 2), (key3088, -6), (key3086, 2), (key3081, 2), (key3086, 2), (key3086, -6)]

def rawRow18427 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3091, -2), (key3091, -2), (key3090, -2), (key3090, -2), (key3109, 2), (key3109, 2), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, 2), (key3088, 2), (key3088, 2), (key3082, 2), (key3088, -6), (key3086, 2), (key3086, 2), (key3081, 2), (key3086, -6)]

def rawRow18428 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3091, 2), (key3091, 2), (key3091, 2), (key3090, 2), (key3090, 2), (key3090, 2), (key3088, 2), (key3088, 2), (key3088, 2), (key3082, -6), (key3086, 2), (key3086, 2), (key3086, 2), (key3081, -6)]

def rawRow18429 : Integer.Sparse Key := [(key2353, 6), (key2359, 6), (key2359, 6), (key2359, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2566, 6), (key2566, 6), (key2566, 6), (key2578, 6)]

def rawRow18430 : Integer.Sparse Key := [(key2359, 6), (key2353, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2566, 6)]

def rawRow18431 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2353, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2566, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18432 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2359, 6), (key2353, 6), (key2515, 6), (key2515, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2566, 6)]

def rawRow18433 : Integer.Sparse Key := [(key2448, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2353, 6), (key2359, 6), (key2359, 6), (key2448, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6)]

def rawRow18434 : Integer.Sparse Key := [(key2454, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2353, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2454, 6)]

def rawRow18435 : Integer.Sparse Key := [(key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2359, 6), (key2353, 6), (key2515, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2454, 6)]

def rawRow18436 : Integer.Sparse Key := [(key2448, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2353, 6), (key2359, 6), (key2448, 6), (key2515, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2515, 6)]

def rawRow18437 : Integer.Sparse Key := [(key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2353, 6), (key2515, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2515, 6), (key2454, 6)]

def rawRow18438 : Integer.Sparse Key := [(key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2353, 6), (key2578, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2515, 6)]

def rawRow18439 : Integer.Sparse Key := [(key2515, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2578, 6), (key2353, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6)]

def rawRow18440 : Integer.Sparse Key := [(key2454, 6), (key2515, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2515, 6), (key2353, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6)]

def rawRow18441 : Integer.Sparse Key := [(key2515, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2515, 6), (key2359, 6), (key2448, 6), (key2353, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2359, 6)]

def rawRow18442 : Integer.Sparse Key := [(key2454, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2515, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6)]

def rawRow18443 : Integer.Sparse Key := [(key2454, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2454, 6)]

def rawRow18444 : Integer.Sparse Key := [(key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2359, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2359, 6)]

def rawRow18445 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2515, 6), (key2515, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2448, 6)]

def rawRow18446 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2448, 6)]

def rawRow18447 : Integer.Sparse Key := [(key2566, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2448, 6)]

def rawRow18448 : Integer.Sparse Key := [(key2578, 6), (key2566, 6), (key2566, 6), (key2566, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2353, 6)]

def rawRow18449 : Integer.Sparse Key := [(key970, 6), (key970, 6), (key970, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1226, 6), (key1226, 6), (key1226, 6)]

def rawRow18450 : Integer.Sparse Key := [(key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6), (key970, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1226, 6), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6)]

def rawRow18451 : Integer.Sparse Key := [(key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6)]

def rawRow18452 : Integer.Sparse Key := [(key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6)]

def rawRow18453 : Integer.Sparse Key := [(key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1226, 6), (key970, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6)]

def rawRow18457 : Integer.Sparse Key := [(key83, 24), (key83, 24), (key83, 24), (key0, 24), (key83, 24)]

def rawRow18458 : Integer.Sparse Key := [(key83, 24), (key83, 24), (key83, 24), (key83, 24), (key0, 24)]

def rawRow18459 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2376, 6), (key2388, 6), (key2762, 6), (key2768, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key2876, 6), (key2916, 6), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3019, 6), (key3028, 6)]

def rawRow18460 : Integer.Sparse Key := [(key2376, 6), (key2370, 6), (key2376, 6), (key2388, 6), (key2768, 6), (key2762, 6), (key2768, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key2916, 6), (key2925, 6), (key2916, 6), (key3005, 6), (key3019, 6), (key3028, 6), (key3019, 6)]

def rawRow18461 : Integer.Sparse Key := [(key2376, 6), (key2376, 6), (key2370, 6), (key2388, 6), (key2768, 6), (key2768, 6), (key2762, 6), (key2876, 6), (key2876, 6), (key2845, 6), (key2845, 6), (key2839, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key2916, 6), (key3005, 6), (key3028, 6), (key3019, 6), (key3019, 6)]

def rawRow18462 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2376, 6), (key2839, 6), (key2845, 6), (key2916, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2876, 6), (key2916, 6), (key2925, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key3019, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def rawRow18463 : Integer.Sparse Key := [(key2376, 6), (key2370, 6), (key2388, 6), (key2376, 6), (key2845, 6), (key2839, 6), (key2916, 6), (key2768, 6), (key2762, 6), (key2876, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key3019, 6), (key3005, 6), (key3028, 6), (key3019, 6)]

def rawRow18464 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2376, 6), (key2376, 6), (key2839, 6), (key2916, 6), (key2845, 6), (key2839, 6), (key2916, 6), (key2762, 6), (key2925, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key2876, 6), (key3019, 6), (key3019, 6), (key3005, 6), (key3028, 6)]

def rawRow18465 : Integer.Sparse Key := [(key2388, 6), (key2370, 6), (key2376, 6), (key2376, 6), (key2916, 6), (key2839, 6), (key2845, 6), (key2916, 6), (key2839, 6), (key2925, 6), (key2762, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key2768, 6), (key3019, 6), (key3019, 6), (key3028, 6), (key3005, 6)]

def rawRow18466 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2370, 6), (key2376, 6), (key2845, 6), (key2916, 6), (key2839, 6), (key2876, 6), (key2925, 6), (key2768, 6), (key2916, 6), (key2762, 6), (key2839, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key3019, 6), (key3028, 6), (key3005, 6), (key3019, 6)]

def rawRow18467 : Integer.Sparse Key := [(key2388, 6), (key2376, 6), (key2370, 6), (key2376, 6), (key2916, 6), (key2845, 6), (key2839, 6), (key2925, 6), (key2876, 6), (key2916, 6), (key2768, 6), (key2839, 6), (key2762, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key3019, 6), (key3028, 6), (key3019, 6), (key3005, 6)]

def rawRow18468 : Integer.Sparse Key := [(key2376, 6), (key2376, 6), (key2388, 6), (key2370, 6), (key2876, 6), (key2876, 6), (key2925, 6), (key2768, 6), (key2768, 6), (key2845, 6), (key2845, 6), (key2916, 6), (key2916, 6), (key2762, 6), (key2839, 6), (key2839, 6), (key3028, 6), (key3005, 6), (key3019, 6), (key3019, 6)]

def rawRow18469 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2376, 6), (key2370, 6), (key2876, 6), (key2925, 6), (key2876, 6), (key2845, 6), (key2916, 6), (key2768, 6), (key2916, 6), (key2768, 6), (key2845, 6), (key2839, 6), (key2762, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key3005, 6), (key3019, 6)]

def rawRow18470 : Integer.Sparse Key := [(key2388, 6), (key2376, 6), (key2376, 6), (key2370, 6), (key2925, 6), (key2876, 6), (key2876, 6), (key2916, 6), (key2845, 6), (key2916, 6), (key2768, 6), (key2845, 6), (key2768, 6), (key2839, 6), (key2839, 6), (key2762, 6), (key3028, 6), (key3019, 6), (key3019, 6), (key3005, 6)]

def rawRow18471 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2404, 6), (key2435, 6), (key2583, 6), (key2589, 6), (key2589, 6), (key2839, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key2876, 6), (key3019, 6), (key3019, 6), (key3028, 6), (key2604, 6), (key2916, 6), (key2916, 6), (key2925, 6)]

def rawRow18472 : Integer.Sparse Key := [(key2404, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2589, 6), (key2583, 6), (key2589, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key3019, 6), (key3028, 6), (key3019, 6), (key2604, 6), (key2916, 6), (key2925, 6), (key2916, 6)]

def rawRow18473 : Integer.Sparse Key := [(key2404, 6), (key2404, 6), (key2398, 6), (key2435, 6), (key2589, 6), (key2589, 6), (key2583, 6), (key2876, 6), (key2876, 6), (key2845, 6), (key2845, 6), (key2839, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key3019, 6), (key2604, 6), (key2925, 6), (key2916, 6), (key2916, 6)]

def rawRow18474 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2404, 6), (key2839, 6), (key2845, 6), (key3019, 6), (key2583, 6), (key2589, 6), (key2839, 6), (key2876, 6), (key3019, 6), (key3028, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2916, 6), (key2604, 6), (key2916, 6), (key2925, 6)]

def rawRow18475 : Integer.Sparse Key := [(key2404, 6), (key2398, 6), (key2435, 6), (key2404, 6), (key2845, 6), (key2839, 6), (key3019, 6), (key2589, 6), (key2583, 6), (key2876, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2916, 6), (key2604, 6), (key2925, 6), (key2916, 6)]

def rawRow18476 : Integer.Sparse Key := [(key2398, 6), (key2435, 6), (key2404, 6), (key2404, 6), (key2839, 6), (key3019, 6), (key2845, 6), (key2839, 6), (key3019, 6), (key2583, 6), (key3028, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2876, 6), (key2916, 6), (key2916, 6), (key2604, 6), (key2925, 6)]

def rawRow18477 : Integer.Sparse Key := [(key2435, 6), (key2398, 6), (key2404, 6), (key2404, 6), (key3019, 6), (key2839, 6), (key2845, 6), (key3019, 6), (key2839, 6), (key3028, 6), (key2583, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2589, 6), (key2916, 6), (key2916, 6), (key2925, 6), (key2604, 6)]

def rawRow18478 : Integer.Sparse Key := [(key2404, 6), (key2435, 6), (key2398, 6), (key2404, 6), (key2845, 6), (key3019, 6), (key2839, 6), (key2876, 6), (key3028, 6), (key2589, 6), (key3019, 6), (key2583, 6), (key2839, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2916, 6), (key2925, 6), (key2604, 6), (key2916, 6)]

def rawRow18479 : Integer.Sparse Key := [(key2435, 6), (key2404, 6), (key2398, 6), (key2404, 6), (key3019, 6), (key2845, 6), (key2839, 6), (key3028, 6), (key2876, 6), (key3019, 6), (key2589, 6), (key2839, 6), (key2583, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2916, 6), (key2925, 6), (key2916, 6), (key2604, 6)]

def rawRow18480 : Integer.Sparse Key := [(key2404, 6), (key2404, 6), (key2435, 6), (key2398, 6), (key2876, 6), (key2876, 6), (key3028, 6), (key2589, 6), (key2589, 6), (key2845, 6), (key2845, 6), (key3019, 6), (key3019, 6), (key2583, 6), (key2839, 6), (key2839, 6), (key2925, 6), (key2604, 6), (key2916, 6), (key2916, 6)]

def rawRow18481 : Integer.Sparse Key := [(key2404, 6), (key2435, 6), (key2404, 6), (key2398, 6), (key2876, 6), (key3028, 6), (key2876, 6), (key2845, 6), (key3019, 6), (key2589, 6), (key3019, 6), (key2589, 6), (key2845, 6), (key2839, 6), (key2583, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key2604, 6), (key2916, 6)]

def rawRow18482 : Integer.Sparse Key := [(key2435, 6), (key2404, 6), (key2404, 6), (key2398, 6), (key3028, 6), (key2876, 6), (key2876, 6), (key3019, 6), (key2845, 6), (key3019, 6), (key2589, 6), (key2845, 6), (key2589, 6), (key2839, 6), (key2839, 6), (key2583, 6), (key2925, 6), (key2916, 6), (key2916, 6), (key2604, 6)]

def rawRow18483 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2370, 6), (key2376, 6), (key2388, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2876, 6), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

def rawRow18484 : Integer.Sparse Key := [(key2470, 6), (key2464, 6), (key2478, 6), (key2501, 6), (key2376, 6), (key2370, 6), (key2388, 6), (key2768, 6), (key2762, 6), (key2876, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key3005, 6), (key3028, 6), (key3019, 6), (key2589, 6), (key2768, 6), (key2876, 6), (key2845, 6)]

def rawRow18485 : Integer.Sparse Key := [(key2464, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2370, 6), (key2388, 6), (key2376, 6), (key2839, 6), (key2916, 6), (key2762, 6), (key2925, 6), (key2768, 6), (key2876, 6), (key3019, 6), (key3005, 6), (key3028, 6), (key2589, 6), (key2845, 6), (key2768, 6), (key2876, 6)]

def rawRow18486 : Integer.Sparse Key := [(key2478, 6), (key2464, 6), (key2470, 6), (key2501, 6), (key2388, 6), (key2370, 6), (key2376, 6), (key2916, 6), (key2839, 6), (key2925, 6), (key2762, 6), (key2876, 6), (key2768, 6), (key3019, 6), (key3028, 6), (key3005, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2768, 6)]

def rawRow18487 : Integer.Sparse Key := [(key2470, 6), (key2478, 6), (key2464, 6), (key2501, 6), (key2376, 6), (key2388, 6), (key2370, 6), (key2876, 6), (key2925, 6), (key2768, 6), (key2916, 6), (key2762, 6), (key2839, 6), (key3028, 6), (key3005, 6), (key3019, 6), (key2589, 6), (key2876, 6), (key2768, 6), (key2845, 6)]

def rawRow18488 : Integer.Sparse Key := [(key2478, 6), (key2470, 6), (key2464, 6), (key2501, 6), (key2388, 6), (key2376, 6), (key2370, 6), (key2925, 6), (key2876, 6), (key2916, 6), (key2768, 6), (key2839, 6), (key2762, 6), (key3028, 6), (key3019, 6), (key3005, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2768, 6)]

def rawRow18489 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2583, 6), (key2589, 6), (key2839, 6), (key2876, 6), (key3019, 6), (key3028, 6), (key2604, 6), (key2916, 6), (key2925, 6), (key2768, 6), (key2589, 6), (key2845, 6), (key2876, 6)]

def rawRow18490 : Integer.Sparse Key := [(key2470, 6), (key2464, 6), (key2501, 6), (key2478, 6), (key2404, 6), (key2398, 6), (key2435, 6), (key2589, 6), (key2583, 6), (key2876, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key2604, 6), (key2925, 6), (key2916, 6), (key2768, 6), (key2589, 6), (key2876, 6), (key2845, 6)]

def rawRow18491 : Integer.Sparse Key := [(key2464, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2398, 6), (key2435, 6), (key2404, 6), (key2839, 6), (key3019, 6), (key2583, 6), (key3028, 6), (key2589, 6), (key2876, 6), (key2916, 6), (key2604, 6), (key2925, 6), (key2768, 6), (key2845, 6), (key2589, 6), (key2876, 6)]

def rawRow18492 : Integer.Sparse Key := [(key2501, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2435, 6), (key2398, 6), (key2404, 6), (key3019, 6), (key2839, 6), (key3028, 6), (key2583, 6), (key2876, 6), (key2589, 6), (key2916, 6), (key2925, 6), (key2604, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key2589, 6)]

def rawRow18493 : Integer.Sparse Key := [(key2470, 6), (key2501, 6), (key2464, 6), (key2478, 6), (key2404, 6), (key2435, 6), (key2398, 6), (key2876, 6), (key3028, 6), (key2589, 6), (key3019, 6), (key2583, 6), (key2839, 6), (key2925, 6), (key2604, 6), (key2916, 6), (key2768, 6), (key2876, 6), (key2589, 6), (key2845, 6)]

def rawRow18494 : Integer.Sparse Key := [(key2501, 6), (key2470, 6), (key2464, 6), (key2478, 6), (key2435, 6), (key2404, 6), (key2398, 6), (key3028, 6), (key2876, 6), (key3019, 6), (key2589, 6), (key2839, 6), (key2583, 6), (key2925, 6), (key2916, 6), (key2604, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key2589, 6)]

def rawRow18495 : Integer.Sparse Key := [(key2464, 6), (key2478, 6), (key2501, 6), (key2470, 6), (key2464, 6), (key2478, 6), (key2501, 6), (key2370, 6), (key2388, 6), (key2762, 6), (key2925, 6), (key3005, 6), (key3028, 6), (key2589, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2768, 6), (key2876, 6)]

def rawRow18496 : Integer.Sparse Key := [(key2478, 6), (key2464, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2464, 6), (key2501, 6), (key2388, 6), (key2370, 6), (key2925, 6), (key2762, 6), (key3028, 6), (key3005, 6), (key2589, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key2589, 6), (key2876, 6), (key2768, 6)]

def rawRow18497 : Integer.Sparse Key := [(key2464, 6), (key2501, 6), (key2478, 6), (key2470, 6), (key2464, 6), (key2501, 6), (key2478, 6), (key2398, 6), (key2435, 6), (key2583, 6), (key3028, 6), (key2604, 6), (key2925, 6), (key2768, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key2589, 6), (key2876, 6)]

def rawRow18498 : Integer.Sparse Key := [(key2501, 6), (key2464, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2464, 6), (key2478, 6), (key2435, 6), (key2398, 6), (key3028, 6), (key2583, 6), (key2925, 6), (key2604, 6), (key2768, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2768, 6), (key2876, 6), (key2589, 6)]

def rawRow18499 : Integer.Sparse Key := [(key2478, 6), (key2501, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2464, 6), (key2570, 6), (key2575, 6), (key2388, 6), (key2435, 6), (key2370, 6), (key2762, 6), (key2876, 6), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key2589, 6), (key2768, 6)]

def rawRow18500 : Integer.Sparse Key := [(key2501, 6), (key2478, 6), (key2464, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2464, 6), (key2575, 6), (key2570, 6), (key2435, 6), (key2388, 6), (key2398, 6), (key2583, 6), (key2876, 6), (key2768, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2768, 6), (key2589, 6)]

def rawRow18501 : Integer.Sparse Key := [(key2470, 6), (key2478, 6), (key2501, 6), (key2464, 6), (key2568, 6), (key2570, 6), (key2575, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2478, 6), (key2435, 6), (key2501, 6), (key2370, 6), (key2762, 6), (key2839, 6), (key2876, 6), (key2589, 6), (key2768, 6), (key2845, 6)]

def rawRow18502 : Integer.Sparse Key := [(key2478, 6), (key2470, 6), (key2501, 6), (key2464, 6), (key2570, 6), (key2568, 6), (key2575, 6), (key2388, 6), (key2376, 6), (key2478, 6), (key2404, 6), (key2501, 6), (key2435, 6), (key2370, 6), (key2839, 6), (key2762, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2768, 6)]

def rawRow18503 : Integer.Sparse Key := [(key2470, 6), (key2501, 6), (key2478, 6), (key2464, 6), (key2568, 6), (key2575, 6), (key2570, 6), (key2404, 6), (key2435, 6), (key2376, 6), (key2501, 6), (key2388, 6), (key2478, 6), (key2398, 6), (key2583, 6), (key2839, 6), (key2876, 6), (key2768, 6), (key2589, 6), (key2845, 6)]

def rawRow18504 : Integer.Sparse Key := [(key2501, 6), (key2470, 6), (key2478, 6), (key2464, 6), (key2575, 6), (key2568, 6), (key2570, 6), (key2435, 6), (key2404, 6), (key2501, 6), (key2376, 6), (key2478, 6), (key2388, 6), (key2398, 6), (key2839, 6), (key2583, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key2589, 6)]

def rawRow18505 : Integer.Sparse Key := [(key2478, 6), (key2501, 6), (key2470, 6), (key2464, 6), (key2570, 6), (key2575, 6), (key2568, 6), (key2478, 6), (key2501, 6), (key2388, 6), (key2435, 6), (key2376, 6), (key2404, 6), (key2464, 6), (key2370, 6), (key2762, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2768, 6)]

def rawRow18506 : Integer.Sparse Key := [(key2501, 6), (key2478, 6), (key2470, 6), (key2464, 6), (key2575, 6), (key2570, 6), (key2568, 6), (key2501, 6), (key2478, 6), (key2435, 6), (key2388, 6), (key2404, 6), (key2376, 6), (key2464, 6), (key2398, 6), (key2583, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key2589, 6)]

def rawRow18507 : Integer.Sparse Key := [(key2568, 6), (key2568, 6), (key2570, 6), (key2575, 6), (key2376, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2404, 6), (key2470, 6), (key2470, 6), (key2478, 6), (key2478, 6), (key2435, 6), (key2501, 6), (key2501, 6), (key2370, 6), (key2762, 6), (key2839, 6), (key2839, 6)]

def rawRow18508 : Integer.Sparse Key := [(key2568, 6), (key2570, 6), (key2568, 6), (key2575, 6), (key2376, 6), (key2388, 6), (key2376, 6), (key2470, 6), (key2478, 6), (key2404, 6), (key2478, 6), (key2404, 6), (key2470, 6), (key2501, 6), (key2435, 6), (key2501, 6), (key2370, 6), (key2839, 6), (key2762, 6), (key2839, 6)]

def rawRow18509 : Integer.Sparse Key := [(key2570, 6), (key2568, 6), (key2568, 6), (key2575, 6), (key2388, 6), (key2376, 6), (key2376, 6), (key2478, 6), (key2470, 6), (key2478, 6), (key2404, 6), (key2470, 6), (key2404, 6), (key2501, 6), (key2501, 6), (key2435, 6), (key2370, 6), (key2839, 6), (key2839, 6), (key2762, 6)]

def rawRow18510 : Integer.Sparse Key := [(key2568, 6), (key2568, 6), (key2575, 6), (key2570, 6), (key2404, 6), (key2404, 6), (key2435, 6), (key2376, 6), (key2376, 6), (key2470, 6), (key2470, 6), (key2501, 6), (key2501, 6), (key2388, 6), (key2478, 6), (key2478, 6), (key2398, 6), (key2583, 6), (key2839, 6), (key2839, 6)]

def rawRow18511 : Integer.Sparse Key := [(key2568, 6), (key2575, 6), (key2568, 6), (key2570, 6), (key2404, 6), (key2435, 6), (key2404, 6), (key2470, 6), (key2501, 6), (key2376, 6), (key2501, 6), (key2376, 6), (key2470, 6), (key2478, 6), (key2388, 6), (key2478, 6), (key2398, 6), (key2839, 6), (key2583, 6), (key2839, 6)]

def rawRow18512 : Integer.Sparse Key := [(key2575, 6), (key2568, 6), (key2568, 6), (key2570, 6), (key2435, 6), (key2404, 6), (key2404, 6), (key2501, 6), (key2470, 6), (key2501, 6), (key2376, 6), (key2470, 6), (key2376, 6), (key2478, 6), (key2478, 6), (key2388, 6), (key2398, 6), (key2839, 6), (key2839, 6), (key2583, 6)]

def rawRow18513 : Integer.Sparse Key := [(key2568, 6), (key2570, 6), (key2575, 6), (key2568, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2478, 6), (key2435, 6), (key2501, 6), (key2376, 6), (key2404, 6), (key2470, 6), (key2464, 6), (key2370, 6), (key2762, 6), (key2839, 6)]

def rawRow18514 : Integer.Sparse Key := [(key2570, 6), (key2568, 6), (key2575, 6), (key2568, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2388, 6), (key2376, 6), (key2478, 6), (key2404, 6), (key2501, 6), (key2435, 6), (key2376, 6), (key2470, 6), (key2404, 6), (key2464, 6), (key2370, 6), (key2839, 6), (key2762, 6)]

def rawRow18515 : Integer.Sparse Key := [(key2568, 6), (key2575, 6), (key2570, 6), (key2568, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2404, 6), (key2435, 6), (key2376, 6), (key2501, 6), (key2388, 6), (key2478, 6), (key2404, 6), (key2376, 6), (key2470, 6), (key2464, 6), (key2398, 6), (key2583, 6), (key2839, 6)]

def rawRow18516 : Integer.Sparse Key := [(key2575, 6), (key2568, 6), (key2570, 6), (key2568, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2435, 6), (key2404, 6), (key2501, 6), (key2376, 6), (key2478, 6), (key2388, 6), (key2404, 6), (key2470, 6), (key2376, 6), (key2464, 6), (key2398, 6), (key2839, 6), (key2583, 6)]

def rawRow18517 : Integer.Sparse Key := [(key2570, 6), (key2575, 6), (key2568, 6), (key2568, 6), (key2478, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2388, 6), (key2435, 6), (key2376, 6), (key2404, 6), (key2470, 6), (key2376, 6), (key2404, 6), (key2464, 6), (key2464, 6), (key2370, 6), (key2762, 6)]

def rawRow18518 : Integer.Sparse Key := [(key2575, 6), (key2570, 6), (key2568, 6), (key2568, 6), (key2501, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2435, 6), (key2388, 6), (key2404, 6), (key2376, 6), (key2470, 6), (key2404, 6), (key2376, 6), (key2464, 6), (key2464, 6), (key2398, 6), (key2583, 6)]

def rawRow18519 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 24), (key1104, 24), (key1230, 24)]

def rawRow18520 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 24), (key1230, 24), (key1104, 24)]

def rawRow18521 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1230, 24), (key1104, 24), (key1104, 24)]

def rawRow18522 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1026, 24), (key1104, 24), (key1230, 24)]

def rawRow18523 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1026, 24), (key1230, 24), (key1104, 24)]

def rawRow18524 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1104, 24), (key1026, 24), (key1230, 24)]

def rawRow18525 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1104, 24), (key1230, 24), (key1026, 24)]

def rawRow18526 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1230, 24), (key1026, 24), (key1104, 24)]

def rawRow18527 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1230, 24), (key1104, 24), (key1026, 24)]

def rawRow18528 : Integer.Sparse Key := [(key991, 24), (key1230, 24), (key1026, 24), (key1104, 24), (key1104, 24)]

def rawRow18529 : Integer.Sparse Key := [(key991, 24), (key1230, 24), (key1104, 24), (key1026, 24), (key1104, 24)]

def rawRow18530 : Integer.Sparse Key := [(key991, 24), (key1230, 24), (key1104, 24), (key1104, 24), (key1026, 24)]

def rawRow18531 : Integer.Sparse Key := [(key1026, 24), (key991, 24), (key1104, 24), (key1104, 24), (key1230, 24)]

def rawRow18532 : Integer.Sparse Key := [(key1026, 24), (key991, 24), (key1104, 24), (key1230, 24), (key1104, 24)]

def rawRow18533 : Integer.Sparse Key := [(key1026, 24), (key991, 24), (key1230, 24), (key1104, 24), (key1104, 24)]

def rawRow18534 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key991, 24), (key1104, 24), (key1230, 24)]

def rawRow18535 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key991, 24), (key1230, 24), (key1104, 24)]

def rawRow18536 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1104, 24), (key991, 24), (key1230, 24)]

def rawRow18537 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1104, 24), (key1230, 24), (key991, 24)]

def rawRow18538 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1230, 24), (key991, 24), (key1104, 24)]

def rawRow18539 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1230, 24), (key1104, 24), (key991, 24)]

def rawRow18540 : Integer.Sparse Key := [(key1026, 24), (key1230, 24), (key991, 24), (key1104, 24), (key1104, 24)]

def rawRow18541 : Integer.Sparse Key := [(key1026, 24), (key1230, 24), (key1104, 24), (key991, 24), (key1104, 24)]

def rawRow18542 : Integer.Sparse Key := [(key1026, 24), (key1230, 24), (key1104, 24), (key1104, 24), (key991, 24)]

def rawRow18543 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1026, 24), (key1104, 24), (key1230, 24)]

def rawRow18544 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1026, 24), (key1230, 24), (key1104, 24)]

def rawRow18545 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1104, 24), (key1026, 24), (key1230, 24)]

def rawRow18546 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1104, 24), (key1230, 24), (key1026, 24)]

def rawRow18547 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1230, 24), (key1026, 24), (key1104, 24)]

def rawRow18548 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1230, 24), (key1104, 24), (key1026, 24)]

def rawRow18549 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key991, 24), (key1104, 24), (key1230, 24)]

def rawRow18550 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key991, 24), (key1230, 24), (key1104, 24)]

def rawRow18551 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1104, 24), (key991, 24), (key1230, 24)]

def rawRow18552 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1104, 24), (key1230, 24), (key991, 24)]

def rawRow18553 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1230, 24), (key991, 24), (key1104, 24)]

def rawRow18554 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1230, 24), (key1104, 24), (key991, 24)]

def rawRow18555 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key991, 24), (key1026, 24), (key1230, 24)]

def rawRow18556 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key991, 24), (key1230, 24), (key1026, 24)]

def rawRow18557 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1026, 24), (key991, 24), (key1230, 24)]

def rawRow18558 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1026, 24), (key1230, 24), (key991, 24)]

def rawRow18559 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1230, 24), (key991, 24), (key1026, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18560 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1230, 24), (key1026, 24), (key991, 24)]

def rawRow18561 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key991, 24), (key1026, 24), (key1104, 24)]

def rawRow18562 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key991, 24), (key1104, 24), (key1026, 24)]

def rawRow18563 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1026, 24), (key991, 24), (key1104, 24)]

def rawRow18564 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1026, 24), (key1104, 24), (key991, 24)]

def rawRow18565 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1104, 24), (key991, 24), (key1026, 24)]

def rawRow18566 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1104, 24), (key1026, 24), (key991, 24)]

def rawRow18567 : Integer.Sparse Key := [(key1230, 24), (key991, 24), (key1026, 24), (key1104, 24), (key1104, 24)]

def rawRow18568 : Integer.Sparse Key := [(key1230, 24), (key991, 24), (key1104, 24), (key1026, 24), (key1104, 24)]

def rawRow18569 : Integer.Sparse Key := [(key1230, 24), (key991, 24), (key1104, 24), (key1104, 24), (key1026, 24)]

def rawRow18570 : Integer.Sparse Key := [(key1230, 24), (key1026, 24), (key991, 24), (key1104, 24), (key1104, 24)]

def rawRow18571 : Integer.Sparse Key := [(key1230, 24), (key1026, 24), (key1104, 24), (key991, 24), (key1104, 24)]

def rawRow18572 : Integer.Sparse Key := [(key1230, 24), (key1026, 24), (key1104, 24), (key1104, 24), (key991, 24)]

def rawRow18573 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key991, 24), (key1026, 24), (key1104, 24)]

def rawRow18574 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key991, 24), (key1104, 24), (key1026, 24)]

def rawRow18575 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1026, 24), (key991, 24), (key1104, 24)]

def rawRow18576 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1026, 24), (key1104, 24), (key991, 24)]

def rawRow18577 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1104, 24), (key991, 24), (key1026, 24)]

def rawRow18578 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1104, 24), (key1026, 24), (key991, 24)]

def rawRow18579 : Integer.Sparse Key := [(key2608, 2), (key2614, 2), (key2614, 2), (key2624, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2657, 2), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 2), (key2669, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2752, 2), (key2752, 2), (key2757, 2), (key2778, 2), (key2784, 2), (key2778, 2), (key2792, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2922, 2), (key3007, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key3025, 2)]

def rawRow18580 : Integer.Sparse Key := [(key2614, 2), (key2608, 2), (key2614, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2657, 2), (key2659, 2), (key2657, 2), (key2669, 2), (key2663, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2752, 2), (key2757, 2), (key2752, 2), (key2784, 2), (key2778, 2), (key2792, 2), (key2778, 2), (key2792, 2), (key2784, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key3007, 2), (key3009, 2), (key3007, 2), (key3011, 2), (key3016, 2), (key3011, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3021, 2), (key3025, 2), (key3022, 2)]

def rawRow18581 : Integer.Sparse Key := [(key2614, 2), (key2614, 2), (key2608, 2), (key2638, 2), (key2638, 2), (key2630, 2), (key2630, 2), (key2624, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2657, 2), (key2669, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2724, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2752, 2), (key2792, 2), (key2792, 2), (key2784, 2), (key2784, 2), (key2778, 2), (key2778, 2), (key2827, 2), (key2827, 2), (key2807, 2), (key2807, 2), (key2801, 2), (key2801, 2), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key2922, 2), (key2922, 2), (key2919, 2), (key2919, 2), (key2918, 2), (key2918, 2), (key3009, 2), (key3007, 2), (key3007, 2), (key3016, 2), (key3011, 2), (key3011, 2), (key3025, 2), (key3025, 2), (key3022, 2), (key3022, 2), (key3021, 2), (key3021, 2)]

def rawRow18582 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2608, 2), (key2614, 2), (key2624, 2), (key2638, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2752, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2724, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2801, 2), (key2807, 2), (key2851, 2), (key2858, 2), (key2918, 2), (key2919, 2), (key2778, 2), (key2784, 2), (key2851, 2), (key2868, 2), (key2918, 2), (key2922, 2), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key3011, 2), (key3021, 2), (key3022, 2), (key3007, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3022, 2), (key3025, 2)]

def rawRow18583 : Integer.Sparse Key := [(key2630, 2), (key2624, 2), (key2638, 2), (key2614, 2), (key2608, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2614, 2), (key2638, 2), (key2630, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2807, 2), (key2801, 2), (key2858, 2), (key2851, 2), (key2919, 2), (key2918, 2), (key2784, 2), (key2778, 2), (key2868, 2), (key2851, 2), (key2922, 2), (key2918, 2), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key2792, 2), (key2784, 2), (key2827, 2), (key2807, 2), (key2868, 2), (key2858, 2), (key3011, 2), (key3022, 2), (key3021, 2), (key3007, 2), (key3025, 2), (key3021, 2), (key3009, 2), (key3007, 2), (key3016, 2), (key3011, 2), (key3025, 2), (key3022, 2)]

def rawRow18584 : Integer.Sparse Key := [(key2624, 2), (key2638, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2608, 2), (key2659, 2), (key2614, 2), (key2638, 2), (key2630, 2), (key2614, 2), (key2638, 2), (key2698, 2), (key2752, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2669, 2), (key2724, 2), (key2851, 2), (key2918, 2), (key2801, 2), (key2919, 2), (key2807, 2), (key2858, 2), (key2851, 2), (key2918, 2), (key2778, 2), (key2922, 2), (key2784, 2), (key2868, 2), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key2807, 2), (key2858, 2), (key2784, 2), (key2868, 2), (key2792, 2), (key2827, 2), (key3021, 2), (key3011, 2), (key3022, 2), (key3021, 2), (key3007, 2), (key3025, 2), (key3011, 2), (key3022, 2), (key3007, 2), (key3025, 2), (key3009, 2), (key3016, 2)]

def rawRow18585 : Integer.Sparse Key := [(key2638, 2), (key2624, 2), (key2630, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2608, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2752, 2), (key2698, 2), (key2704, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2918, 2), (key2851, 2), (key2919, 2), (key2801, 2), (key2858, 2), (key2807, 2), (key2918, 2), (key2851, 2), (key2922, 2), (key2778, 2), (key2868, 2), (key2784, 2), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key2858, 2), (key2807, 2), (key2868, 2), (key2784, 2), (key2827, 2), (key2792, 2), (key3021, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3022, 2), (key3011, 2), (key3025, 2), (key3007, 2), (key3016, 2), (key3009, 2)]

def rawRow18586 : Integer.Sparse Key := [(key2630, 2), (key2638, 2), (key2624, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2638, 2), (key2608, 2), (key2624, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2704, 2), (key2752, 2), (key2698, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2858, 2), (key2919, 2), (key2807, 2), (key2918, 2), (key2801, 2), (key2851, 2), (key2868, 2), (key2922, 2), (key2784, 2), (key2918, 2), (key2778, 2), (key2851, 2), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key2827, 2), (key2868, 2), (key2792, 2), (key2858, 2), (key2784, 2), (key2807, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3021, 2), (key3016, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3007, 2), (key3011, 2)]

def rawRow18587 : Integer.Sparse Key := [(key2638, 2), (key2630, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2638, 2), (key2614, 2), (key2624, 2), (key2608, 2), (key2638, 2), (key2630, 2), (key2614, 2), (key2752, 2), (key2704, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2752, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key2724, 2), (key2704, 2), (key2669, 2), (key2919, 2), (key2858, 2), (key2918, 2), (key2807, 2), (key2851, 2), (key2801, 2), (key2922, 2), (key2868, 2), (key2918, 2), (key2784, 2), (key2851, 2), (key2778, 2), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key2868, 2), (key2827, 2), (key2858, 2), (key2792, 2), (key2807, 2), (key2784, 2), (key3022, 2), (key3021, 2), (key3011, 2), (key3025, 2), (key3021, 2), (key3007, 2), (key3025, 2), (key3016, 2), (key3022, 2), (key3009, 2), (key3011, 2), (key3007, 2)]

def rawRow18588 : Integer.Sparse Key := [(key2657, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2614, 2), (key2630, 2), (key2630, 2), (key2638, 2), (key2638, 2), (key2608, 2), (key2624, 2), (key2624, 2), (key2724, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2669, 2), (key2704, 2), (key2704, 2), (key2752, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2698, 2), (key2827, 2), (key2827, 2), (key2868, 2), (key2868, 2), (key2922, 2), (key2922, 2), (key2792, 2), (key2792, 2), (key2858, 2), (key2858, 2), (key2919, 2), (key2919, 2), (key2784, 2), (key2784, 2), (key2807, 2), (key2807, 2), (key2918, 2), (key2918, 2), (key2778, 2), (key2778, 2), (key2801, 2), (key2801, 2), (key2851, 2), (key2851, 2), (key3016, 2), (key3025, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3022, 2), (key3007, 2), (key3007, 2), (key3011, 2), (key3011, 2), (key3021, 2), (key3021, 2)]

def rawRow18589 : Integer.Sparse Key := [(key2657, 2), (key2659, 2), (key2657, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2624, 2), (key2608, 2), (key2624, 2), (key2724, 2), (key2757, 2), (key2724, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2663, 2), (key2698, 2), (key2868, 2), (key2922, 2), (key2827, 2), (key2922, 2), (key2827, 2), (key2868, 2), (key2858, 2), (key2919, 2), (key2792, 2), (key2919, 2), (key2792, 2), (key2858, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key3025, 2), (key3016, 2), (key3025, 2), (key3022, 2), (key3009, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3007, 2), (key3021, 2), (key3007, 2), (key3011, 2)]

def rawRow18590 : Integer.Sparse Key := [(key2659, 2), (key2657, 2), (key2657, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2614, 2), (key2624, 2), (key2624, 2), (key2608, 2), (key2757, 2), (key2724, 2), (key2724, 2), (key2752, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2669, 2), (key2698, 2), (key2698, 2), (key2663, 2), (key2922, 2), (key2868, 2), (key2922, 2), (key2827, 2), (key2868, 2), (key2827, 2), (key2919, 2), (key2858, 2), (key2919, 2), (key2792, 2), (key2858, 2), (key2792, 2), (key2918, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2784, 2), (key2851, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key2778, 2), (key3025, 2), (key3025, 2), (key3016, 2), (key3022, 2), (key3022, 2), (key3009, 2), (key3021, 2), (key3011, 2), (key3021, 2), (key3007, 2), (key3011, 2), (key3007, 2)]

def rawRow18591 : Integer.Sparse Key := [(key2663, 2), (key2669, 2), (key2669, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2704, 2), (key2752, 2), (key2724, 2), (key2724, 2), (key2757, 2), (key2608, 2), (key2614, 2), (key2614, 2), (key2801, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key3011, 2), (key3011, 2), (key3016, 2), (key2624, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key3021, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key3025, 2), (key2657, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2752, 2), (key2757, 2), (key2918, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2922, 2)]

def rawRow18592 : Integer.Sparse Key := [(key2669, 2), (key2663, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2698, 2), (key2752, 2), (key2704, 2), (key2724, 2), (key2757, 2), (key2724, 2), (key2614, 2), (key2608, 2), (key2614, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key3011, 2), (key3016, 2), (key3011, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key2657, 2), (key2659, 2), (key2657, 2), (key2752, 2), (key2757, 2), (key2752, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2918, 2), (key2922, 2), (key2919, 2)]

def rawRow18593 : Integer.Sparse Key := [(key2669, 2), (key2669, 2), (key2663, 2), (key2752, 2), (key2752, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2724, 2), (key2614, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2827, 2), (key2807, 2), (key2807, 2), (key2801, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key3011, 2), (key2638, 2), (key2638, 2), (key2630, 2), (key2630, 2), (key2624, 2), (key2624, 2), (key2724, 2), (key2724, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key3025, 2), (key3025, 2), (key3022, 2), (key3022, 2), (key3021, 2), (key3021, 2), (key2659, 2), (key2657, 2), (key2657, 2), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, 2), (key2922, 2), (key2919, 2), (key2919, 2), (key2918, 2), (key2918, 2)]

def rawRow18594 : Integer.Sparse Key := [(key2698, 2), (key2704, 2), (key2724, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2752, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2704, 2), (key2752, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2608, 2), (key2614, 2), (key2801, 2), (key2827, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2807, 2), (key2827, 2), (key2698, 2), (key2704, 2), (key2851, 2), (key2858, 2), (key3021, 2), (key3022, 2), (key2624, 2), (key2630, 2), (key2851, 2), (key2868, 2), (key3021, 2), (key3025, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2724, 2), (key2858, 2), (key2868, 2), (key2752, 2), (key2918, 2), (key2919, 2), (key2657, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2757, 2), (key2919, 2), (key2922, 2)]

def rawRow18595 : Integer.Sparse Key := [(key2704, 2), (key2698, 2), (key2724, 2), (key2669, 2), (key2663, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2669, 2), (key2752, 2), (key2704, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2614, 2), (key2827, 2), (key2807, 2), (key2704, 2), (key2698, 2), (key2858, 2), (key2851, 2), (key3022, 2), (key3021, 2), (key2630, 2), (key2624, 2), (key2868, 2), (key2851, 2), (key3025, 2), (key3021, 2), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2638, 2), (key2630, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2858, 2), (key2752, 2), (key2919, 2), (key2918, 2), (key2657, 2), (key2922, 2), (key2918, 2), (key2659, 2), (key2657, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2919, 2)]

def rawRow18596 : Integer.Sparse Key := [(key2698, 2), (key2724, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2704, 2), (key2669, 2), (key2752, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2608, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2807, 2), (key2614, 2), (key2827, 2), (key2851, 2), (key3021, 2), (key2698, 2), (key3022, 2), (key2704, 2), (key2858, 2), (key2851, 2), (key3021, 2), (key2624, 2), (key3025, 2), (key2630, 2), (key2868, 2), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2704, 2), (key2858, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2724, 2), (key2918, 2), (key2752, 2), (key2919, 2), (key2918, 2), (key2657, 2), (key2922, 2), (key2752, 2), (key2919, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2757, 2)]

def rawRow18597 : Integer.Sparse Key := [(key2724, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2827, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key2608, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key3021, 2), (key2851, 2), (key3022, 2), (key2698, 2), (key2858, 2), (key2704, 2), (key3021, 2), (key2851, 2), (key3025, 2), (key2624, 2), (key2868, 2), (key2630, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2724, 2), (key2638, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2757, 2), (key2659, 2)]

def rawRow18598 : Integer.Sparse Key := [(key2704, 2), (key2724, 2), (key2698, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2663, 2), (key2698, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2807, 2), (key2827, 2), (key2801, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2858, 2), (key3022, 2), (key2704, 2), (key3021, 2), (key2698, 2), (key2851, 2), (key2868, 2), (key3025, 2), (key2630, 2), (key3021, 2), (key2624, 2), (key2851, 2), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2724, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2630, 2), (key2704, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2757, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2657, 2), (key2752, 2)]

def rawRow18599 : Integer.Sparse Key := [(key2724, 2), (key2704, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2724, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key2752, 2), (key2704, 2), (key2669, 2), (key2827, 2), (key2807, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2827, 2), (key2614, 2), (key2801, 2), (key2608, 2), (key2827, 2), (key2807, 2), (key2614, 2), (key3022, 2), (key2858, 2), (key3021, 2), (key2704, 2), (key2851, 2), (key2698, 2), (key3025, 2), (key2868, 2), (key3021, 2), (key2630, 2), (key2851, 2), (key2624, 2), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2868, 2), (key2724, 2), (key2858, 2), (key2638, 2), (key2704, 2), (key2630, 2), (key2919, 2), (key2918, 2), (key2752, 2), (key2922, 2), (key2918, 2), (key2657, 2), (key2922, 2), (key2757, 2), (key2919, 2), (key2659, 2), (key2752, 2), (key2657, 2)]

def rawRow18600 : Integer.Sparse Key := [(key2752, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2669, 2), (key2704, 2), (key2704, 2), (key2724, 2), (key2724, 2), (key2663, 2), (key2698, 2), (key2698, 2), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2614, 2), (key2807, 2), (key2807, 2), (key2827, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2801, 2), (key2724, 2), (key2724, 2), (key2868, 2), (key2868, 2), (key3025, 2), (key3025, 2), (key2638, 2), (key2638, 2), (key2858, 2), (key2858, 2), (key3022, 2), (key3022, 2), (key2630, 2), (key2630, 2), (key2704, 2), (key2704, 2), (key3021, 2), (key3021, 2), (key2624, 2), (key2624, 2), (key2698, 2), (key2698, 2), (key2851, 2), (key2851, 2), (key2757, 2), (key2922, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2919, 2), (key2657, 2), (key2657, 2), (key2752, 2), (key2752, 2), (key2918, 2), (key2918, 2)]

def rawRow18601 : Integer.Sparse Key := [(key2752, 2), (key2757, 2), (key2752, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2663, 2), (key2698, 2), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2801, 2), (key2608, 2), (key2801, 2), (key2868, 2), (key3025, 2), (key2724, 2), (key3025, 2), (key2724, 2), (key2868, 2), (key2858, 2), (key3022, 2), (key2638, 2), (key3022, 2), (key2638, 2), (key2858, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2922, 2), (key2757, 2), (key2922, 2), (key2919, 2), (key2659, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2918, 2), (key2657, 2), (key2752, 2)]

def rawRow18602 : Integer.Sparse Key := [(key2757, 2), (key2752, 2), (key2752, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2669, 2), (key2698, 2), (key2698, 2), (key2663, 2), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2614, 2), (key2801, 2), (key2801, 2), (key2608, 2), (key3025, 2), (key2868, 2), (key3025, 2), (key2724, 2), (key2868, 2), (key2724, 2), (key3022, 2), (key2858, 2), (key3022, 2), (key2638, 2), (key2858, 2), (key2638, 2), (key3021, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2630, 2), (key2851, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2624, 2), (key2922, 2), (key2922, 2), (key2757, 2), (key2919, 2), (key2919, 2), (key2659, 2), (key2918, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2752, 2), (key2657, 2)]

def rawRow18603 : Integer.Sparse Key := [(key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2851, 2), (key2918, 2), (key2858, 2), (key2919, 2), (key2827, 2), (key2868, 2), (key2922, 2), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2851, 2), (key3021, 2), (key2858, 2), (key3022, 2), (key2724, 2), (key2868, 2), (key3025, 2), (key2608, 2), (key2614, 2), (key2624, 2), (key2638, 2), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2724, 2), (key2752, 2), (key2757, 2), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3022, 2), (key3025, 2), (key2614, 2), (key2630, 2), (key2638, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2)]

def rawRow18604 : Integer.Sparse Key := [(key2784, 2), (key2778, 2), (key2792, 2), (key2807, 2), (key2801, 2), (key2918, 2), (key2851, 2), (key2919, 2), (key2858, 2), (key2827, 2), (key2922, 2), (key2868, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2704, 2), (key2698, 2), (key3021, 2), (key2851, 2), (key3022, 2), (key2858, 2), (key2724, 2), (key3025, 2), (key2868, 2), (key2614, 2), (key2608, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key3009, 2), (key3007, 2), (key3016, 2), (key3011, 2), (key3025, 2), (key3022, 2), (key2614, 2), (key2638, 2), (key2630, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2792, 2), (key2784, 2), (key2827, 2), (key2807, 2), (key2868, 2), (key2858, 2)]

def rawRow18605 : Integer.Sparse Key := [(key2778, 2), (key2792, 2), (key2784, 2), (key2851, 2), (key2858, 2), (key2801, 2), (key2919, 2), (key2807, 2), (key2918, 2), (key2868, 2), (key2827, 2), (key2922, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2851, 2), (key2858, 2), (key2698, 2), (key3022, 2), (key2704, 2), (key3021, 2), (key2868, 2), (key2724, 2), (key3025, 2), (key2624, 2), (key2638, 2), (key2608, 2), (key2659, 2), (key2614, 2), (key2638, 2), (key2698, 2), (key2752, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key3011, 2), (key3022, 2), (key3007, 2), (key3025, 2), (key3009, 2), (key3016, 2), (key2630, 2), (key2614, 2), (key2638, 2), (key2704, 2), (key2669, 2), (key2724, 2), (key2807, 2), (key2858, 2), (key2784, 2), (key2868, 2), (key2792, 2), (key2827, 2)]

def rawRow18606 : Integer.Sparse Key := [(key2792, 2), (key2778, 2), (key2784, 2), (key2858, 2), (key2851, 2), (key2919, 2), (key2801, 2), (key2918, 2), (key2807, 2), (key2868, 2), (key2922, 2), (key2827, 2), (key2638, 2), (key2624, 2), (key2630, 2), (key2858, 2), (key2851, 2), (key3022, 2), (key2698, 2), (key3021, 2), (key2704, 2), (key2868, 2), (key3025, 2), (key2724, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2608, 2), (key2638, 2), (key2614, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2724, 2), (key2669, 2), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key3022, 2), (key3011, 2), (key3025, 2), (key3007, 2), (key3016, 2), (key3009, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2858, 2), (key2807, 2), (key2868, 2), (key2784, 2), (key2827, 2), (key2792, 2)]

def rawRow18607 : Integer.Sparse Key := [(key2784, 2), (key2792, 2), (key2778, 2), (key2918, 2), (key2919, 2), (key2807, 2), (key2858, 2), (key2801, 2), (key2851, 2), (key2922, 2), (key2827, 2), (key2868, 2), (key2630, 2), (key2638, 2), (key2624, 2), (key3021, 2), (key3022, 2), (key2704, 2), (key2858, 2), (key2698, 2), (key2851, 2), (key3025, 2), (key2724, 2), (key2868, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2638, 2), (key2608, 2), (key2624, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key3016, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3007, 2), (key3011, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2827, 2), (key2868, 2), (key2792, 2), (key2858, 2), (key2784, 2), (key2807, 2)]

def rawRow18608 : Integer.Sparse Key := [(key2792, 2), (key2784, 2), (key2778, 2), (key2919, 2), (key2918, 2), (key2858, 2), (key2807, 2), (key2851, 2), (key2801, 2), (key2922, 2), (key2868, 2), (key2827, 2), (key2638, 2), (key2630, 2), (key2624, 2), (key3022, 2), (key3021, 2), (key2858, 2), (key2704, 2), (key2851, 2), (key2698, 2), (key3025, 2), (key2868, 2), (key2724, 2), (key2659, 2), (key2657, 2), (key2638, 2), (key2614, 2), (key2624, 2), (key2608, 2), (key2757, 2), (key2724, 2), (key2752, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key3025, 2), (key3016, 2), (key3022, 2), (key3009, 2), (key3011, 2), (key3007, 2), (key2638, 2), (key2630, 2), (key2614, 2), (key2724, 2), (key2704, 2), (key2669, 2), (key2868, 2), (key2827, 2), (key2858, 2), (key2792, 2), (key2807, 2), (key2784, 2)]

def rawRow18609 : Integer.Sparse Key := [(key2801, 2), (key2807, 2), (key2827, 2), (key2778, 2), (key2784, 2), (key2851, 2), (key2918, 2), (key2868, 2), (key2922, 2), (key2792, 2), (key2858, 2), (key2919, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2624, 2), (key2630, 2), (key2851, 2), (key3021, 2), (key2868, 2), (key3025, 2), (key2638, 2), (key2858, 2), (key3022, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2752, 2), (key2724, 2), (key2757, 2), (key2608, 2), (key2614, 2), (key2801, 2), (key2827, 2), (key3011, 2), (key3016, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2757, 2), (key2919, 2), (key2922, 2), (key2669, 2), (key2784, 2), (key2792, 2), (key2614, 2), (key2807, 2), (key2827, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2724, 2), (key2858, 2), (key2868, 2)]

def rawRow18610 : Integer.Sparse Key := [(key2807, 2), (key2801, 2), (key2827, 2), (key2784, 2), (key2778, 2), (key2918, 2), (key2851, 2), (key2922, 2), (key2868, 2), (key2792, 2), (key2919, 2), (key2858, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2630, 2), (key2624, 2), (key3021, 2), (key2851, 2), (key3025, 2), (key2868, 2), (key2638, 2), (key3022, 2), (key2858, 2), (key2669, 2), (key2663, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2659, 2), (key2657, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2919, 2), (key2669, 2), (key2792, 2), (key2784, 2), (key2614, 2), (key2827, 2), (key2807, 2), (key2638, 2), (key2630, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2858, 2)]

def rawRow18611 : Integer.Sparse Key := [(key2801, 2), (key2827, 2), (key2807, 2), (key2851, 2), (key2868, 2), (key2778, 2), (key2922, 2), (key2784, 2), (key2918, 2), (key2858, 2), (key2792, 2), (key2919, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2851, 2), (key2868, 2), (key2624, 2), (key3025, 2), (key2630, 2), (key3021, 2), (key2858, 2), (key2638, 2), (key3022, 2), (key2698, 2), (key2724, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2801, 2), (key2827, 2), (key2608, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2752, 2), (key2919, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2757, 2), (key2784, 2), (key2669, 2), (key2792, 2), (key2807, 2), (key2614, 2), (key2827, 2), (key2704, 2), (key2858, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2724, 2)]

def rawRow18612 : Integer.Sparse Key := [(key2827, 2), (key2801, 2), (key2807, 2), (key2868, 2), (key2851, 2), (key2922, 2), (key2778, 2), (key2918, 2), (key2784, 2), (key2858, 2), (key2919, 2), (key2792, 2), (key2724, 2), (key2698, 2), (key2704, 2), (key2868, 2), (key2851, 2), (key3025, 2), (key2624, 2), (key3021, 2), (key2630, 2), (key2858, 2), (key3022, 2), (key2638, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2752, 2), (key2669, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key2608, 2), (key2827, 2), (key2614, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2757, 2), (key2659, 2), (key2784, 2), (key2792, 2), (key2669, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2724, 2), (key2638, 2)]

def rawRow18613 : Integer.Sparse Key := [(key2807, 2), (key2827, 2), (key2801, 2), (key2918, 2), (key2922, 2), (key2784, 2), (key2868, 2), (key2778, 2), (key2851, 2), (key2919, 2), (key2792, 2), (key2858, 2), (key2704, 2), (key2724, 2), (key2698, 2), (key3021, 2), (key3025, 2), (key2630, 2), (key2868, 2), (key2624, 2), (key2851, 2), (key3022, 2), (key2638, 2), (key2858, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2663, 2), (key2698, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2757, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2657, 2), (key2752, 2), (key2792, 2), (key2669, 2), (key2784, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2724, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2630, 2), (key2704, 2)]

def rawRow18614 : Integer.Sparse Key := [(key2827, 2), (key2807, 2), (key2801, 2), (key2922, 2), (key2918, 2), (key2868, 2), (key2784, 2), (key2851, 2), (key2778, 2), (key2919, 2), (key2858, 2), (key2792, 2), (key2724, 2), (key2704, 2), (key2698, 2), (key3025, 2), (key3021, 2), (key2868, 2), (key2630, 2), (key2851, 2), (key2624, 2), (key3022, 2), (key2858, 2), (key2638, 2), (key2757, 2), (key2752, 2), (key2724, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key3016, 2), (key3011, 2), (key2827, 2), (key2614, 2), (key2801, 2), (key2608, 2), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2922, 2), (key2757, 2), (key2919, 2), (key2659, 2), (key2752, 2), (key2657, 2), (key2792, 2), (key2784, 2), (key2669, 2), (key2827, 2), (key2807, 2), (key2614, 2), (key2868, 2), (key2724, 2), (key2858, 2), (key2638, 2), (key2704, 2), (key2630, 2)]

def rawRow18615 : Integer.Sparse Key := [(key2851, 2), (key2858, 2), (key2868, 2), (key2778, 2), (key2792, 2), (key2801, 2), (key2919, 2), (key2827, 2), (key2922, 2), (key2784, 2), (key2807, 2), (key2918, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key3022, 2), (key2724, 2), (key3025, 2), (key2630, 2), (key2704, 2), (key3021, 2), (key2778, 2), (key2792, 2), (key2801, 2), (key2919, 2), (key2827, 2), (key2922, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key3022, 2), (key2724, 2), (key3025, 2), (key2608, 2), (key2659, 2), (key2663, 2), (key2757, 2), (key3009, 2), (key3016, 2), (key2614, 2), (key2638, 2), (key2669, 2), (key2724, 2), (key2792, 2), (key2827, 2), (key2704, 2), (key2807, 2), (key2858, 2), (key2630, 2), (key2784, 2), (key2868, 2), (key2614, 2), (key2638, 2), (key2669, 2), (key2724, 2), (key2792, 2), (key2827, 2)]

def rawRow18616 : Integer.Sparse Key := [(key2858, 2), (key2851, 2), (key2868, 2), (key2792, 2), (key2778, 2), (key2919, 2), (key2801, 2), (key2922, 2), (key2827, 2), (key2784, 2), (key2918, 2), (key2807, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2638, 2), (key2624, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2724, 2), (key2630, 2), (key3021, 2), (key2704, 2), (key2792, 2), (key2778, 2), (key2919, 2), (key2801, 2), (key2922, 2), (key2827, 2), (key2638, 2), (key2624, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2724, 2), (key2659, 2), (key2608, 2), (key2757, 2), (key2663, 2), (key3016, 2), (key3009, 2), (key2638, 2), (key2614, 2), (key2724, 2), (key2669, 2), (key2827, 2), (key2792, 2), (key2704, 2), (key2858, 2), (key2807, 2), (key2630, 2), (key2868, 2), (key2784, 2), (key2638, 2), (key2614, 2), (key2724, 2), (key2669, 2), (key2827, 2), (key2792, 2)]

def rawRow18617 : Integer.Sparse Key := [(key2851, 2), (key2868, 2), (key2858, 2), (key2801, 2), (key2827, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2807, 2), (key2784, 2), (key2918, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2698, 2), (key2724, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2704, 2), (key2630, 2), (key3021, 2), (key2801, 2), (key2827, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2698, 2), (key2724, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2663, 2), (key2757, 2), (key2608, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2669, 2), (key2792, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2807, 2), (key2704, 2), (key2858, 2), (key2784, 2), (key2630, 2), (key2868, 2), (key2669, 2), (key2792, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2724, 2)]

def rawRow18618 : Integer.Sparse Key := [(key2868, 2), (key2851, 2), (key2858, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2919, 2), (key2792, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2868, 2), (key2851, 2), (key2858, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key3022, 2), (key2638, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2919, 2), (key2792, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key3022, 2), (key2638, 2), (key2757, 2), (key2663, 2), (key3016, 2), (key2608, 2), (key2757, 2), (key2659, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2724, 2), (key2638, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2724, 2), (key2638, 2)]

def rawRow18619 : Integer.Sparse Key := [(key2858, 2), (key2868, 2), (key2851, 2), (key2919, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key2778, 2), (key2801, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2858, 2), (key2868, 2), (key2851, 2), (key3022, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2624, 2), (key2698, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2919, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key2778, 2), (key2801, 2), (key3022, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2624, 2), (key2698, 2), (key3009, 2), (key3016, 2), (key2659, 2), (key2757, 2), (key2608, 2), (key2663, 2), (key2724, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2614, 2), (key2669, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2724, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2614, 2), (key2669, 2)]

def rawRow18620 : Integer.Sparse Key := [(key2868, 2), (key2858, 2), (key2851, 2), (key2922, 2), (key2919, 2), (key2827, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key2918, 2), (key2807, 2), (key2784, 2), (key2868, 2), (key2858, 2), (key2851, 2), (key3025, 2), (key3022, 2), (key2724, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key3021, 2), (key2704, 2), (key2630, 2), (key2922, 2), (key2919, 2), (key2827, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key3025, 2), (key3022, 2), (key2724, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key3016, 2), (key3009, 2), (key2757, 2), (key2659, 2), (key2663, 2), (key2608, 2), (key2827, 2), (key2724, 2), (key2792, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2858, 2), (key2807, 2), (key2704, 2), (key2868, 2), (key2784, 2), (key2630, 2), (key2827, 2), (key2724, 2), (key2792, 2), (key2638, 2), (key2669, 2), (key2614, 2)]

def rawRow18621 : Integer.Sparse Key := [(key2918, 2), (key2919, 2), (key2922, 2), (key2784, 2), (key2792, 2), (key2807, 2), (key2858, 2), (key2827, 2), (key2868, 2), (key2778, 2), (key2801, 2), (key2851, 2), (key3021, 2), (key3022, 2), (key3025, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2858, 2), (key2724, 2), (key2868, 2), (key2624, 2), (key2698, 2), (key2851, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3022, 2), (key3016, 2), (key3025, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2919, 2), (key2757, 2), (key2922, 2), (key2614, 2), (key2638, 2), (key2669, 2), (key2792, 2), (key2724, 2), (key2827, 2), (key2608, 2), (key2624, 2), (key2663, 2), (key2698, 2), (key2778, 2), (key2801, 2), (key2724, 2), (key2827, 2), (key2868, 2), (key2638, 2), (key2792, 2), (key2858, 2), (key2614, 2), (key2630, 2), (key2669, 2), (key2704, 2), (key2784, 2), (key2807, 2)]

def rawRow18622 : Integer.Sparse Key := [(key2919, 2), (key2918, 2), (key2922, 2), (key2792, 2), (key2784, 2), (key2858, 2), (key2807, 2), (key2868, 2), (key2827, 2), (key2778, 2), (key2851, 2), (key2801, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key2638, 2), (key2630, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2724, 2), (key2624, 2), (key2851, 2), (key2698, 2), (key3009, 2), (key3007, 2), (key3022, 2), (key3011, 2), (key3025, 2), (key3016, 2), (key2659, 2), (key2657, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2757, 2), (key2638, 2), (key2614, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2724, 2), (key2624, 2), (key2608, 2), (key2698, 2), (key2663, 2), (key2801, 2), (key2778, 2), (key2724, 2), (key2868, 2), (key2827, 2), (key2638, 2), (key2858, 2), (key2792, 2), (key2630, 2), (key2614, 2), (key2704, 2), (key2669, 2), (key2807, 2), (key2784, 2)]

def rawRow18623 : Integer.Sparse Key := [(key2918, 2), (key2922, 2), (key2919, 2), (key2807, 2), (key2827, 2), (key2784, 2), (key2868, 2), (key2792, 2), (key2858, 2), (key2801, 2), (key2778, 2), (key2851, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key2704, 2), (key2724, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2698, 2), (key2624, 2), (key2851, 2), (key3011, 2), (key3016, 2), (key3007, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key2752, 2), (key2757, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2669, 2), (key2724, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2663, 2), (key2698, 2), (key2608, 2), (key2801, 2), (key2624, 2), (key2698, 2), (key2827, 2), (key2724, 2), (key2868, 2), (key2792, 2), (key2638, 2), (key2858, 2), (key2669, 2), (key2784, 2), (key2614, 2), (key2807, 2), (key2630, 2), (key2704, 2)]

def rawRow18624 : Integer.Sparse Key := [(key2922, 2), (key2918, 2), (key2919, 2), (key2827, 2), (key2807, 2), (key2868, 2), (key2784, 2), (key2858, 2), (key2792, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key3025, 2), (key3021, 2), (key3022, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2858, 2), (key2638, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key3016, 2), (key3011, 2), (key3025, 2), (key3007, 2), (key3022, 2), (key3009, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2919, 2), (key2659, 2), (key2724, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2792, 2), (key2638, 2), (key2698, 2), (key2663, 2), (key2801, 2), (key2608, 2), (key2698, 2), (key2624, 2), (key2827, 2), (key2868, 2), (key2724, 2), (key2792, 2), (key2858, 2), (key2638, 2), (key2784, 2), (key2669, 2), (key2807, 2), (key2614, 2), (key2704, 2), (key2630, 2)]

def rawRow18625 : Integer.Sparse Key := [(key2919, 2), (key2922, 2), (key2918, 2), (key2858, 2), (key2868, 2), (key2792, 2), (key2827, 2), (key2784, 2), (key2807, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key3022, 2), (key3025, 2), (key3021, 2), (key2858, 2), (key2868, 2), (key2638, 2), (key2724, 2), (key2630, 2), (key2704, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key3022, 2), (key3025, 2), (key3009, 2), (key3016, 2), (key3007, 2), (key3011, 2), (key2919, 2), (key2922, 2), (key2659, 2), (key2757, 2), (key2657, 2), (key2752, 2), (key2792, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2614, 2), (key2669, 2), (key2778, 2), (key2801, 2), (key2624, 2), (key2698, 2), (key2608, 2), (key2663, 2), (key2868, 2), (key2724, 2), (key2827, 2), (key2858, 2), (key2638, 2), (key2792, 2), (key2704, 2), (key2807, 2), (key2630, 2), (key2784, 2), (key2614, 2), (key2669, 2)]

def rawRow18626 : Integer.Sparse Key := [(key2922, 2), (key2919, 2), (key2918, 2), (key2868, 2), (key2858, 2), (key2827, 2), (key2792, 2), (key2807, 2), (key2784, 2), (key2851, 2), (key2801, 2), (key2778, 2), (key3025, 2), (key3022, 2), (key3021, 2), (key2868, 2), (key2858, 2), (key2724, 2), (key2638, 2), (key2704, 2), (key2630, 2), (key2851, 2), (key2698, 2), (key2624, 2), (key3025, 2), (key3022, 2), (key3016, 2), (key3009, 2), (key3011, 2), (key3007, 2), (key2922, 2), (key2919, 2), (key2757, 2), (key2659, 2), (key2752, 2), (key2657, 2), (key2827, 2), (key2792, 2), (key2724, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2801, 2), (key2778, 2), (key2698, 2), (key2624, 2), (key2663, 2), (key2608, 2), (key2868, 2), (key2827, 2), (key2724, 2), (key2858, 2), (key2792, 2), (key2638, 2), (key2807, 2), (key2704, 2), (key2784, 2), (key2630, 2), (key2669, 2), (key2614, 2)]

def rawRow18627 : Integer.Sparse Key := [(key3007, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3011, 2), (key3021, 2), (key3021, 2), (key3022, 2), (key3022, 2), (key3016, 2), (key3025, 2), (key3025, 2), (key2657, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2752, 2), (key2918, 2), (key2918, 2), (key2919, 2), (key2919, 2), (key2757, 2), (key2922, 2), (key2922, 2), (key2614, 2), (key2614, 2), (key2630, 2), (key2630, 2), (key2638, 2), (key2638, 2), (key2669, 2), (key2669, 2), (key2784, 2), (key2784, 2), (key2792, 2), (key2792, 2), (key2704, 2), (key2704, 2), (key2807, 2), (key2807, 2), (key2858, 2), (key2858, 2), (key2724, 2), (key2724, 2), (key2827, 2), (key2827, 2), (key2868, 2), (key2868, 2), (key2608, 2), (key2624, 2), (key2624, 2), (key2663, 2), (key2698, 2), (key2698, 2), (key2778, 2), (key2778, 2), (key2801, 2), (key2801, 2), (key2851, 2), (key2851, 2)]

def rawRow18628 : Integer.Sparse Key := [(key3007, 2), (key3009, 2), (key3007, 2), (key3021, 2), (key3022, 2), (key3011, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, 2), (key3016, 2), (key3025, 2), (key2657, 2), (key2659, 2), (key2657, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2757, 2), (key2922, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2784, 2), (key2792, 2), (key2669, 2), (key2792, 2), (key2669, 2), (key2784, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2827, 2), (key2868, 2), (key2724, 2), (key2868, 2), (key2724, 2), (key2827, 2), (key2624, 2), (key2608, 2), (key2624, 2), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2851, 2), (key2778, 2), (key2801, 2)]

def rawRow18629 : Integer.Sparse Key := [(key3009, 2), (key3007, 2), (key3007, 2), (key3022, 2), (key3021, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3011, 2), (key3025, 2), (key3025, 2), (key3016, 2), (key2659, 2), (key2657, 2), (key2657, 2), (key2919, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2752, 2), (key2922, 2), (key2922, 2), (key2757, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2614, 2), (key2792, 2), (key2784, 2), (key2792, 2), (key2669, 2), (key2784, 2), (key2669, 2), (key2858, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2704, 2), (key2868, 2), (key2827, 2), (key2868, 2), (key2724, 2), (key2827, 2), (key2724, 2), (key2624, 2), (key2624, 2), (key2608, 2), (key2698, 2), (key2698, 2), (key2663, 2), (key2851, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key2778, 2)]

def rawRow18630 : Integer.Sparse Key := [(key3011, 2), (key3011, 2), (key3016, 2), (key3007, 2), (key3007, 2), (key3021, 2), (key3021, 2), (key3025, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3022, 2), (key2752, 2), (key2752, 2), (key2757, 2), (key2657, 2), (key2657, 2), (key2918, 2), (key2918, 2), (key2922, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2919, 2), (key2669, 2), (key2669, 2), (key2704, 2), (key2704, 2), (key2724, 2), (key2724, 2), (key2614, 2), (key2614, 2), (key2807, 2), (key2807, 2), (key2827, 2), (key2827, 2), (key2630, 2), (key2630, 2), (key2784, 2), (key2784, 2), (key2868, 2), (key2868, 2), (key2638, 2), (key2638, 2), (key2792, 2), (key2792, 2), (key2858, 2), (key2858, 2), (key2663, 2), (key2698, 2), (key2698, 2), (key2608, 2), (key2801, 2), (key2801, 2), (key2624, 2), (key2624, 2), (key2698, 2), (key2698, 2), (key2851, 2), (key2851, 2)]

def rawRow18631 : Integer.Sparse Key := [(key3011, 2), (key3016, 2), (key3011, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3025, 2), (key3007, 2), (key3021, 2), (key3022, 2), (key3009, 2), (key3022, 2), (key2752, 2), (key2757, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2919, 2), (key2659, 2), (key2919, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2792, 2), (key2858, 2), (key2638, 2), (key2858, 2), (key2638, 2), (key2792, 2), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, 2), (key2608, 2), (key2801, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2851, 2), (key2624, 2), (key2698, 2)]

def rawRow18632 : Integer.Sparse Key := [(key3016, 2), (key3011, 2), (key3011, 2), (key3025, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3021, 2), (key3007, 2), (key3022, 2), (key3022, 2), (key3009, 2), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2657, 2), (key2919, 2), (key2919, 2), (key2659, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2669, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2614, 2), (key2868, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2630, 2), (key2858, 2), (key2792, 2), (key2858, 2), (key2638, 2), (key2792, 2), (key2638, 2), (key2698, 2), (key2698, 2), (key2663, 2), (key2801, 2), (key2801, 2), (key2608, 2), (key2851, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2624, 2)]

def rawRow18633 : Integer.Sparse Key := [(key3021, 2), (key3022, 2), (key3025, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3022, 2), (key3016, 2), (key3025, 2), (key3007, 2), (key3011, 2), (key3021, 2), (key2918, 2), (key2919, 2), (key2922, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2919, 2), (key2757, 2), (key2922, 2), (key2657, 2), (key2752, 2), (key2918, 2), (key2784, 2), (key2792, 2), (key2807, 2), (key2858, 2), (key2827, 2), (key2868, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2858, 2), (key2724, 2), (key2868, 2), (key2614, 2), (key2638, 2), (key2669, 2), (key2792, 2), (key2724, 2), (key2827, 2), (key2614, 2), (key2630, 2), (key2669, 2), (key2784, 2), (key2704, 2), (key2807, 2), (key2778, 2), (key2801, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2851, 2), (key2608, 2), (key2624, 2), (key2663, 2), (key2698, 2), (key2778, 2), (key2801, 2)]

def rawRow18634 : Integer.Sparse Key := [(key3022, 2), (key3021, 2), (key3025, 2), (key3009, 2), (key3007, 2), (key3022, 2), (key3011, 2), (key3025, 2), (key3016, 2), (key3007, 2), (key3021, 2), (key3011, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2659, 2), (key2657, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2757, 2), (key2657, 2), (key2918, 2), (key2752, 2), (key2792, 2), (key2784, 2), (key2858, 2), (key2807, 2), (key2868, 2), (key2827, 2), (key2638, 2), (key2630, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2724, 2), (key2638, 2), (key2614, 2), (key2792, 2), (key2669, 2), (key2827, 2), (key2724, 2), (key2630, 2), (key2614, 2), (key2784, 2), (key2669, 2), (key2807, 2), (key2704, 2), (key2778, 2), (key2851, 2), (key2801, 2), (key2624, 2), (key2851, 2), (key2698, 2), (key2624, 2), (key2608, 2), (key2698, 2), (key2663, 2), (key2801, 2), (key2778, 2)]

def rawRow18635 : Integer.Sparse Key := [(key3021, 2), (key3025, 2), (key3022, 2), (key3011, 2), (key3016, 2), (key3007, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3011, 2), (key3007, 2), (key3021, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2752, 2), (key2757, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2752, 2), (key2657, 2), (key2918, 2), (key2807, 2), (key2827, 2), (key2784, 2), (key2868, 2), (key2792, 2), (key2858, 2), (key2704, 2), (key2724, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2669, 2), (key2724, 2), (key2614, 2), (key2827, 2), (key2638, 2), (key2792, 2), (key2669, 2), (key2704, 2), (key2614, 2), (key2807, 2), (key2630, 2), (key2784, 2), (key2801, 2), (key2778, 2), (key2851, 2), (key2698, 2), (key2624, 2), (key2851, 2), (key2663, 2), (key2698, 2), (key2608, 2), (key2801, 2), (key2624, 2), (key2698, 2)]

def rawRow18636 : Integer.Sparse Key := [(key3025, 2), (key3021, 2), (key3022, 2), (key3016, 2), (key3011, 2), (key3025, 2), (key3007, 2), (key3022, 2), (key3009, 2), (key3011, 2), (key3021, 2), (key3007, 2), (key2922, 2), (key2918, 2), (key2919, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2919, 2), (key2659, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2827, 2), (key2807, 2), (key2868, 2), (key2784, 2), (key2858, 2), (key2792, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2858, 2), (key2638, 2), (key2724, 2), (key2669, 2), (key2827, 2), (key2614, 2), (key2792, 2), (key2638, 2), (key2704, 2), (key2669, 2), (key2807, 2), (key2614, 2), (key2784, 2), (key2630, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2663, 2), (key2801, 2), (key2608, 2), (key2698, 2), (key2624, 2)]

def rawRow18637 : Integer.Sparse Key := [(key3022, 2), (key3025, 2), (key3021, 2), (key3022, 2), (key3025, 2), (key3009, 2), (key3016, 2), (key3007, 2), (key3011, 2), (key3021, 2), (key3007, 2), (key3011, 2), (key2919, 2), (key2922, 2), (key2918, 2), (key2919, 2), (key2922, 2), (key2659, 2), (key2757, 2), (key2657, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2752, 2), (key2858, 2), (key2868, 2), (key2792, 2), (key2827, 2), (key2784, 2), (key2807, 2), (key2858, 2), (key2868, 2), (key2638, 2), (key2724, 2), (key2630, 2), (key2704, 2), (key2792, 2), (key2827, 2), (key2638, 2), (key2724, 2), (key2614, 2), (key2669, 2), (key2784, 2), (key2807, 2), (key2630, 2), (key2704, 2), (key2614, 2), (key2669, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2778, 2), (key2801, 2), (key2624, 2), (key2698, 2), (key2608, 2), (key2663, 2)]

def rawRow18638 : Integer.Sparse Key := [(key3025, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key3016, 2), (key3009, 2), (key3011, 2), (key3007, 2), (key3021, 2), (key3011, 2), (key3007, 2), (key2922, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2757, 2), (key2659, 2), (key2752, 2), (key2657, 2), (key2918, 2), (key2752, 2), (key2657, 2), (key2868, 2), (key2858, 2), (key2827, 2), (key2792, 2), (key2807, 2), (key2784, 2), (key2868, 2), (key2858, 2), (key2724, 2), (key2638, 2), (key2704, 2), (key2630, 2), (key2827, 2), (key2792, 2), (key2724, 2), (key2638, 2), (key2669, 2), (key2614, 2), (key2807, 2), (key2784, 2), (key2704, 2), (key2630, 2), (key2669, 2), (key2614, 2), (key2851, 2), (key2801, 2), (key2778, 2), (key2851, 2), (key2698, 2), (key2624, 2), (key2801, 2), (key2778, 2), (key2698, 2), (key2624, 2), (key2663, 2), (key2608, 2)]

def rawRow18639 : Integer.Sparse Key := [(key2355, 6), (key2355, 6), (key2355, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2512, 6), (key2512, 6), (key2512, 6)]

def rawRow18640 : Integer.Sparse Key := [(key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2355, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2512, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6)]

def rawRow18641 : Integer.Sparse Key := [(key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6)]

def rawRow18642 : Integer.Sparse Key := [(key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6)]

def rawRow18643 : Integer.Sparse Key := [(key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6)]

def rawRow18644 : Integer.Sparse Key := [(key968, 24), (key1082, 24), (key1082, 24), (key1082, 24), (key1082, 24)]

def rawRow18645 : Integer.Sparse Key := [(key1082, 24), (key968, 24), (key1082, 24), (key1082, 24), (key1082, 24)]

def rawRow18646 : Integer.Sparse Key := [(key1082, 24), (key1082, 24), (key968, 24), (key1082, 24), (key1082, 24)]

def rawRow18647 : Integer.Sparse Key := [(key1082, 24), (key1082, 24), (key1082, 24), (key968, 24), (key1082, 24)]

def rawRow18648 : Integer.Sparse Key := [(key1082, 24), (key1082, 24), (key1082, 24), (key1082, 24), (key968, 24)]

def rawRow18649 : Integer.Sparse Key := [(key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2)]

def rawRow18650 : Integer.Sparse Key := [(key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2)]

def rawRow18651 : Integer.Sparse Key := [(key2841, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2)]

def rawRow18652 : Integer.Sparse Key := [(key2841, 2), (key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2873, 2), (key2585, 2), (key2873, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2764, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2764, 2)]

def rawRow18653 : Integer.Sparse Key := [(key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2764, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2873, 2), (key2764, 2), (key2873, 2), (key2585, 2), (key2764, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2764, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2764, 2), (key2585, 2)]

def rawRow18654 : Integer.Sparse Key := [(key2351, 24), (key2446, 24), (key2446, 24), (key2446, 24), (key2446, 24)]

def rawRow18655 : Integer.Sparse Key := [(key2446, 24), (key2351, 24), (key2446, 24), (key2446, 24), (key2446, 24)]

def rawRow18656 : Integer.Sparse Key := [(key2446, 24), (key2446, 24), (key2351, 24), (key2446, 24), (key2446, 24)]

def rawRow18657 : Integer.Sparse Key := [(key2446, 24), (key2446, 24), (key2446, 24), (key2351, 24), (key2446, 24)]

def rawRow18658 : Integer.Sparse Key := [(key2446, 24), (key2446, 24), (key2446, 24), (key2446, 24), (key2351, 24)]

def rawRow18659 : Integer.Sparse Key := [(key971, 6), (key979, 6), (key979, 6), (key979, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key1228, 6), (key1228, 6), (key1228, 6), (key1245, 6)]

def rawRow18660 : Integer.Sparse Key := [(key979, 6), (key971, 6), (key979, 6), (key979, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key1245, 6), (key1228, 6)]

def rawRow18661 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key971, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1245, 6), (key1228, 6), (key1228, 6)]

def rawRow18662 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key979, 6), (key971, 6), (key1164, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key1085, 6), (key1245, 6), (key1228, 6), (key1228, 6), (key1228, 6)]

def rawRow18663 : Integer.Sparse Key := [(key1085, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key971, 6), (key979, 6), (key979, 6), (key1085, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1164, 6), (key1228, 6), (key1228, 6), (key1245, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1164, 6)]

def rawRow18664 : Integer.Sparse Key := [(key1093, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key979, 6), (key971, 6), (key979, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key1245, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1164, 6), (key1093, 6)]

def rawRow18665 : Integer.Sparse Key := [(key1093, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key979, 6), (key979, 6), (key971, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key1245, 6), (key1228, 6), (key1228, 6), (key979, 6), (key1164, 6), (key1093, 6), (key1093, 6)]

def rawRow18666 : Integer.Sparse Key := [(key1085, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key971, 6), (key979, 6), (key1085, 6), (key1164, 6), (key1228, 6), (key1245, 6), (key979, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1164, 6)]

def rawRow18667 : Integer.Sparse Key := [(key1093, 6), (key1085, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key979, 6), (key971, 6), (key1164, 6), (key1085, 6), (key1245, 6), (key1228, 6), (key979, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1164, 6), (key1093, 6)]

def rawRow18668 : Integer.Sparse Key := [(key1085, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key971, 6), (key1245, 6), (key979, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1164, 6)]

def rawRow18669 : Integer.Sparse Key := [(key1228, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1245, 6), (key971, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key979, 6)]

def rawRow18670 : Integer.Sparse Key := [(key1093, 6), (key1228, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1164, 6), (key1245, 6), (key979, 6), (key1228, 6), (key971, 6), (key1085, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key979, 6), (key1093, 6)]

def rawRow18671 : Integer.Sparse Key := [(key1228, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1245, 6), (key1164, 6), (key1228, 6), (key979, 6), (key1085, 6), (key971, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key979, 6)]

def rawRow18672 : Integer.Sparse Key := [(key1093, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1164, 6), (key1164, 6), (key1245, 6), (key979, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key971, 6), (key1085, 6), (key1085, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1093, 6)]

def rawRow18673 : Integer.Sparse Key := [(key1093, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1245, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1085, 6), (key971, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1093, 6)]

def rawRow18674 : Integer.Sparse Key := [(key1228, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1245, 6), (key1164, 6), (key1164, 6), (key1228, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1093, 6), (key979, 6), (key1085, 6), (key1085, 6), (key971, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key979, 6)]

def rawRow18675 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1164, 6), (key1245, 6), (key979, 6), (key979, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key1228, 6), (key971, 6), (key1085, 6), (key1085, 6), (key1085, 6)]

def rawRow18676 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1245, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key979, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key971, 6), (key1085, 6), (key1085, 6)]

def rawRow18677 : Integer.Sparse Key := [(key1164, 6), (key1245, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key971, 6), (key1085, 6)]

def rawRow18678 : Integer.Sparse Key := [(key1245, 6), (key1164, 6), (key1164, 6), (key1164, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1085, 6), (key1085, 6), (key1085, 6), (key971, 6)]

def rawRow18679 : Integer.Sparse Key := [(key3, 24), (key86, 24), (key86, 24), (key86, 24), (key147, 24)]

def rawRow18680 : Integer.Sparse Key := [(key3, 24), (key86, 24), (key86, 24), (key147, 24), (key86, 24)]

def rawRow18681 : Integer.Sparse Key := [(key3, 24), (key86, 24), (key147, 24), (key86, 24), (key86, 24)]

def rawRow18682 : Integer.Sparse Key := [(key3, 24), (key147, 24), (key86, 24), (key86, 24), (key86, 24)]

def rawRow18683 : Integer.Sparse Key := [(key86, 24), (key3, 24), (key86, 24), (key86, 24), (key147, 24)]

def rawRow18684 : Integer.Sparse Key := [(key86, 24), (key3, 24), (key86, 24), (key147, 24), (key86, 24)]

def rawRow18685 : Integer.Sparse Key := [(key86, 24), (key3, 24), (key147, 24), (key86, 24), (key86, 24)]

def rawRow18686 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key3, 24), (key86, 24), (key147, 24)]

def rawRow18687 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key3, 24), (key147, 24), (key86, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18688 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key86, 24), (key3, 24), (key147, 24)]

def rawRow18689 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key86, 24), (key147, 24), (key3, 24)]

def rawRow18690 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key147, 24), (key3, 24), (key86, 24)]

def rawRow18691 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key147, 24), (key86, 24), (key3, 24)]

def rawRow18692 : Integer.Sparse Key := [(key86, 24), (key147, 24), (key3, 24), (key86, 24), (key86, 24)]

def rawRow18693 : Integer.Sparse Key := [(key86, 24), (key147, 24), (key86, 24), (key3, 24), (key86, 24)]

def rawRow18694 : Integer.Sparse Key := [(key86, 24), (key147, 24), (key86, 24), (key86, 24), (key3, 24)]

def rawRow18695 : Integer.Sparse Key := [(key147, 24), (key3, 24), (key86, 24), (key86, 24), (key86, 24)]

def rawRow18696 : Integer.Sparse Key := [(key147, 24), (key86, 24), (key3, 24), (key86, 24), (key86, 24)]

def rawRow18697 : Integer.Sparse Key := [(key147, 24), (key86, 24), (key86, 24), (key3, 24), (key86, 24)]

def rawRow18698 : Integer.Sparse Key := [(key147, 24), (key86, 24), (key86, 24), (key86, 24), (key3, 24)]

def rawRow18699 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1001, 2), (key993, 2), (key1001, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1150, 2), (key1114, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1150, 2), (key1232, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1235, 2), (key1242, 2)]

def rawRow18700 : Integer.Sparse Key := [(key1001, 2), (key993, 2), (key1001, 2), (key1001, 2), (key993, 2), (key1015, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1015, 2), (key1001, 2), (key1036, 2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1242, 2), (key1235, 2)]

def rawRow18701 : Integer.Sparse Key := [(key1001, 2), (key1001, 2), (key993, 2), (key1015, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key993, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1242, 2), (key1235, 2), (key1235, 2), (key1232, 2), (key1232, 2)]

def rawRow18702 : Integer.Sparse Key := [(key1015, 2), (key1015, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key993, 2), (key993, 2), (key993, 2), (key1071, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1028, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1242, 2), (key1242, 2), (key1235, 2), (key1235, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2)]

def rawRow18703 : Integer.Sparse Key := [(key1028, 2), (key1036, 2), (key1036, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1232, 2), (key1232, 2), (key1235, 2), (key993, 2), (key1001, 2), (key1001, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key993, 2), (key1001, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1071, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1150, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1235, 2), (key1242, 2), (key1001, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1114, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1150, 2)]

def rawRow18704 : Integer.Sparse Key := [(key1036, 2), (key1028, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1015, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1242, 2), (key1235, 2), (key1001, 2), (key1015, 2), (key1001, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1123, 2)]

def rawRow18705 : Integer.Sparse Key := [(key1036, 2), (key1036, 2), (key1028, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key993, 2), (key1150, 2), (key1150, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1232, 2), (key1015, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key993, 2), (key993, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1242, 2), (key1235, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2)]

def rawRow18706 : Integer.Sparse Key := [(key1106, 2), (key1114, 2), (key1232, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1123, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1114, 2), (key1232, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1150, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1114, 2), (key1150, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1123, 2), (key1232, 2), (key1235, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1150, 2), (key1232, 2), (key1242, 2), (key993, 2), (key1015, 2), (key1028, 2), (key1071, 2), (key1235, 2), (key1242, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1071, 2), (key1123, 2), (key1150, 2), (key1036, 2), (key1114, 2), (key1123, 2), (key1001, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1071, 2), (key1123, 2), (key1150, 2)]

def rawRow18707 : Integer.Sparse Key := [(key1114, 2), (key1106, 2), (key1232, 2), (key1036, 2), (key1028, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1001, 2), (key1150, 2), (key1114, 2), (key1036, 2), (key1028, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1015, 2), (key993, 2), (key1071, 2), (key1028, 2), (key1242, 2), (key1235, 2), (key1015, 2), (key1001, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1114, 2), (key1015, 2), (key1001, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1123, 2)]

def rawRow18708 : Integer.Sparse Key := [(key1106, 2), (key1232, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1036, 2), (key1123, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1106, 2), (key1232, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1106, 2), (key1232, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key1028, 2), (key1235, 2), (key993, 2), (key1242, 2), (key1015, 2), (key1071, 2), (key1036, 2), (key1123, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1114, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1036, 2), (key1123, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1071, 2)]

def rawRow18709 : Integer.Sparse Key := [(key1232, 2), (key1106, 2), (key1114, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1106, 2), (key1114, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1150, 2), (key1001, 2), (key1235, 2), (key1028, 2), (key1242, 2), (key993, 2), (key1071, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1071, 2), (key1015, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1071, 2), (key1015, 2)]

def rawRow18710 : Integer.Sparse Key := [(key1114, 2), (key1232, 2), (key1106, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1028, 2), (key1106, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key993, 2), (key1106, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1028, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key993, 2), (key1106, 2), (key1071, 2), (key1242, 2), (key1015, 2), (key1235, 2), (key993, 2), (key1028, 2), (key1071, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1001, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1071, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1001, 2), (key1036, 2)]

def rawRow18711 : Integer.Sparse Key := [(key1232, 2), (key1114, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1232, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1123, 2), (key1114, 2), (key1036, 2), (key1232, 2), (key1114, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1232, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1150, 2), (key1114, 2), (key1001, 2), (key1235, 2), (key1123, 2), (key1232, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1242, 2), (key1150, 2), (key1232, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1242, 2), (key1071, 2), (key1235, 2), (key1015, 2), (key1028, 2), (key993, 2), (key1150, 2), (key1071, 2), (key1123, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1123, 2), (key1114, 2), (key1036, 2), (key1150, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1071, 2), (key1123, 2), (key1015, 2), (key1036, 2), (key1001, 2)]

def rawRow18712 : Integer.Sparse Key := [(key1123, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key993, 2), (key1106, 2), (key1106, 2), (key1071, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1242, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1232, 2), (key1232, 2), (key993, 2), (key993, 2), (key1028, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2)]

def rawRow18713 : Integer.Sparse Key := [(key1123, 2), (key1235, 2), (key1123, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1150, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1106, 2), (key993, 2), (key1028, 2), (key1150, 2), (key1071, 2), (key1150, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1036, 2)]

def rawRow18714 : Integer.Sparse Key := [(key1235, 2), (key1123, 2), (key1123, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1106, 2), (key1106, 2), (key1028, 2), (key1242, 2), (key1150, 2), (key1150, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1242, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1071, 2), (key1235, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1015, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1001, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1028, 2), (key993, 2), (key1150, 2), (key1150, 2), (key1071, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1114, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1036, 2), (key1001, 2)]

def rawRow18715 : Integer.Sparse Key := [(key1071, 2), (key1071, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1242, 2), (key1242, 2), (key1015, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1235, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key993, 2), (key993, 2), (key993, 2), (key1028, 2), (key1028, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2)]

def rawRow18716 : Integer.Sparse Key := [(key1150, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1106, 2), (key993, 2), (key993, 2), (key1028, 2), (key1028, 2), (key1106, 2), (key1106, 2)]

def rawRow18717 : Integer.Sparse Key := [(key1150, 2), (key1242, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1071, 2), (key1150, 2), (key1123, 2), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1106, 2), (key993, 2), (key1028, 2)]

def rawRow18718 : Integer.Sparse Key := [(key1242, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1071, 2), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1001, 2), (key1114, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1036, 2), (key1001, 2), (key1106, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1028, 2), (key993, 2)]

def rawRow18719 : Integer.Sparse Key := [(key973, 24), (key1087, 24), (key1087, 24), (key1087, 24), (key1160, 24)]

def rawRow18720 : Integer.Sparse Key := [(key973, 24), (key1087, 24), (key1087, 24), (key1160, 24), (key1087, 24)]

def rawRow18721 : Integer.Sparse Key := [(key973, 24), (key1087, 24), (key1160, 24), (key1087, 24), (key1087, 24)]

def rawRow18722 : Integer.Sparse Key := [(key973, 24), (key1160, 24), (key1087, 24), (key1087, 24), (key1087, 24)]

def rawRow18723 : Integer.Sparse Key := [(key1087, 24), (key973, 24), (key1087, 24), (key1087, 24), (key1160, 24)]

def rawRow18724 : Integer.Sparse Key := [(key1087, 24), (key973, 24), (key1087, 24), (key1160, 24), (key1087, 24)]

def rawRow18725 : Integer.Sparse Key := [(key1087, 24), (key973, 24), (key1160, 24), (key1087, 24), (key1087, 24)]

def rawRow18726 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key973, 24), (key1087, 24), (key1160, 24)]

def rawRow18727 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key973, 24), (key1160, 24), (key1087, 24)]

def rawRow18728 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1087, 24), (key973, 24), (key1160, 24)]

def rawRow18729 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1087, 24), (key1160, 24), (key973, 24)]

def rawRow18730 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1160, 24), (key973, 24), (key1087, 24)]

def rawRow18731 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1160, 24), (key1087, 24), (key973, 24)]

def rawRow18732 : Integer.Sparse Key := [(key1087, 24), (key1160, 24), (key973, 24), (key1087, 24), (key1087, 24)]

def rawRow18733 : Integer.Sparse Key := [(key1087, 24), (key1160, 24), (key1087, 24), (key973, 24), (key1087, 24)]

def rawRow18734 : Integer.Sparse Key := [(key1087, 24), (key1160, 24), (key1087, 24), (key1087, 24), (key973, 24)]

def rawRow18735 : Integer.Sparse Key := [(key1160, 24), (key973, 24), (key1087, 24), (key1087, 24), (key1087, 24)]

def rawRow18736 : Integer.Sparse Key := [(key1160, 24), (key1087, 24), (key973, 24), (key1087, 24), (key1087, 24)]

def rawRow18737 : Integer.Sparse Key := [(key1160, 24), (key1087, 24), (key1087, 24), (key973, 24), (key1087, 24)]

def rawRow18738 : Integer.Sparse Key := [(key1160, 24), (key1087, 24), (key1087, 24), (key1087, 24), (key973, 24)]

def rawRow18739 : Integer.Sparse Key := [(key1, 6), (key7, 6), (key7, 6), (key7, 6), (key84, 6), (key90, 6), (key90, 6), (key84, 6), (key90, 6), (key84, 6), (key151, 6), (key90, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key193, 6), (key193, 6), (key193, 6), (key202, 6)]

def rawRow18740 : Integer.Sparse Key := [(key7, 6), (key1, 6), (key7, 6), (key7, 6), (key90, 6), (key84, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key84, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key90, 6), (key193, 6), (key193, 6), (key202, 6), (key193, 6)]

def rawRow18741 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key1, 6), (key7, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key84, 6), (key151, 6), (key90, 6), (key90, 6), (key193, 6), (key202, 6), (key193, 6), (key193, 6)]

def rawRow18742 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key7, 6), (key1, 6), (key151, 6), (key151, 6), (key151, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key84, 6), (key84, 6), (key84, 6), (key202, 6), (key193, 6), (key193, 6), (key193, 6)]

def rawRow18743 : Integer.Sparse Key := [(key84, 6), (key90, 6), (key90, 6), (key151, 6), (key1, 6), (key7, 6), (key7, 6), (key84, 6), (key90, 6), (key84, 6), (key151, 6), (key90, 6), (key151, 6), (key193, 6), (key193, 6), (key202, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6)]

def rawRow18744 : Integer.Sparse Key := [(key90, 6), (key84, 6), (key90, 6), (key151, 6), (key7, 6), (key1, 6), (key7, 6), (key90, 6), (key84, 6), (key151, 6), (key84, 6), (key151, 6), (key90, 6), (key193, 6), (key202, 6), (key193, 6), (key7, 6), (key90, 6), (key151, 6), (key90, 6)]

def rawRow18745 : Integer.Sparse Key := [(key90, 6), (key90, 6), (key84, 6), (key151, 6), (key7, 6), (key7, 6), (key1, 6), (key151, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key84, 6), (key202, 6), (key193, 6), (key193, 6), (key7, 6), (key151, 6), (key90, 6), (key90, 6)]

def rawRow18746 : Integer.Sparse Key := [(key84, 6), (key90, 6), (key151, 6), (key90, 6), (key84, 6), (key90, 6), (key151, 6), (key1, 6), (key7, 6), (key84, 6), (key151, 6), (key193, 6), (key202, 6), (key7, 6), (key90, 6), (key151, 6), (key90, 6), (key7, 6), (key90, 6), (key151, 6)]

def rawRow18747 : Integer.Sparse Key := [(key90, 6), (key84, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key7, 6), (key1, 6), (key151, 6), (key84, 6), (key202, 6), (key193, 6), (key7, 6), (key151, 6), (key90, 6), (key90, 6), (key7, 6), (key151, 6), (key90, 6)]

def rawRow18748 : Integer.Sparse Key := [(key84, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key90, 6), (key84, 6), (key151, 6), (key1, 6), (key202, 6), (key7, 6), (key151, 6), (key90, 6), (key7, 6), (key151, 6), (key90, 6), (key90, 6), (key7, 6), (key151, 6)]

def rawRow18749 : Integer.Sparse Key := [(key151, 6), (key84, 6), (key90, 6), (key90, 6), (key151, 6), (key84, 6), (key90, 6), (key151, 6), (key84, 6), (key202, 6), (key1, 6), (key151, 6), (key7, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6)]

def rawRow18750 : Integer.Sparse Key := [(key90, 6), (key151, 6), (key84, 6), (key90, 6), (key90, 6), (key151, 6), (key84, 6), (key193, 6), (key202, 6), (key7, 6), (key151, 6), (key1, 6), (key84, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6)]

def rawRow18751 : Integer.Sparse Key := [(key151, 6), (key90, 6), (key84, 6), (key90, 6), (key151, 6), (key90, 6), (key84, 6), (key202, 6), (key193, 6), (key151, 6), (key7, 6), (key84, 6), (key1, 6), (key151, 6), (key90, 6), (key7, 6), (key90, 6), (key151, 6), (key90, 6), (key7, 6)]

def rawRow18752 : Integer.Sparse Key := [(key90, 6), (key90, 6), (key151, 6), (key84, 6), (key193, 6), (key193, 6), (key202, 6), (key7, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key151, 6), (key1, 6), (key84, 6), (key84, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6)]

def rawRow18753 : Integer.Sparse Key := [(key90, 6), (key151, 6), (key90, 6), (key84, 6), (key193, 6), (key202, 6), (key193, 6), (key90, 6), (key151, 6), (key7, 6), (key151, 6), (key7, 6), (key90, 6), (key84, 6), (key1, 6), (key84, 6), (key151, 6), (key90, 6), (key7, 6), (key90, 6)]

def rawRow18754 : Integer.Sparse Key := [(key151, 6), (key90, 6), (key90, 6), (key84, 6), (key202, 6), (key193, 6), (key193, 6), (key151, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6), (key7, 6), (key84, 6), (key84, 6), (key1, 6), (key151, 6), (key90, 6), (key90, 6), (key7, 6)]

def rawRow18755 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key193, 6), (key202, 6), (key7, 6), (key7, 6), (key7, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key151, 6), (key151, 6), (key151, 6), (key1, 6), (key84, 6), (key84, 6), (key84, 6)]

def rawRow18756 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key202, 6), (key193, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key84, 6), (key1, 6), (key84, 6), (key84, 6)]

def rawRow18757 : Integer.Sparse Key := [(key193, 6), (key202, 6), (key193, 6), (key193, 6), (key90, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key7, 6), (key90, 6), (key84, 6), (key84, 6), (key1, 6), (key84, 6)]

def rawRow18758 : Integer.Sparse Key := [(key202, 6), (key193, 6), (key193, 6), (key193, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6), (key7, 6), (key90, 6), (key90, 6), (key7, 6), (key84, 6), (key84, 6), (key84, 6), (key1, 6)]

def rawRow18759 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 6), (key2366, 6), (key2456, 6), (key2456, 6), (key2461, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2523, 6), (key2567, 6), (key2567, 6), (key2579, 6), (key2579, 6)]

def rawRow18760 : Integer.Sparse Key := [(key2357, 6), (key2363, 6), (key2361, 6), (key2366, 6), (key2456, 6), (key2461, 6), (key2456, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2567, 6), (key2579, 6), (key2567, 6), (key2579, 6)]

def rawRow18761 : Integer.Sparse Key := [(key2363, 6), (key2357, 6), (key2361, 6), (key2366, 6), (key2461, 6), (key2456, 6), (key2456, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2567, 6), (key2579, 6), (key2579, 6), (key2567, 6)]

def rawRow18762 : Integer.Sparse Key := [(key2357, 6), (key2363, 6), (key2363, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2456, 6), (key2461, 6), (key2456, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2579, 6), (key2567, 6), (key2567, 6), (key2579, 6)]

def rawRow18763 : Integer.Sparse Key := [(key2363, 6), (key2357, 6), (key2363, 6), (key2361, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2461, 6), (key2456, 6), (key2523, 6), (key2456, 6), (key2523, 6), (key2461, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2579, 6), (key2567, 6), (key2579, 6), (key2567, 6)]

def rawRow18764 : Integer.Sparse Key := [(key2363, 6), (key2363, 6), (key2357, 6), (key2361, 6), (key2523, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2461, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2456, 6), (key2579, 6), (key2579, 6), (key2567, 6), (key2567, 6)]

def rawRow18765 : Integer.Sparse Key := [(key2452, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2357, 6), (key2361, 6), (key2366, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2567, 6), (key2579, 6), (key2579, 6), (key2366, 6), (key2461, 6), (key2523, 6), (key2523, 6)]

def rawRow18766 : Integer.Sparse Key := [(key2452, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2363, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2579, 6), (key2567, 6), (key2579, 6), (key2366, 6), (key2523, 6), (key2461, 6), (key2523, 6)]

def rawRow18767 : Integer.Sparse Key := [(key2458, 6), (key2452, 6), (key2452, 6), (key2519, 6), (key2363, 6), (key2357, 6), (key2361, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2579, 6), (key2579, 6), (key2567, 6), (key2366, 6), (key2523, 6), (key2523, 6), (key2461, 6)]

def rawRow18768 : Integer.Sparse Key := [(key2452, 6), (key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2361, 6), (key2517, 6), (key2517, 6), (key2579, 6), (key2579, 6), (key2366, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2366, 6), (key2523, 6), (key2523, 6)]

def rawRow18769 : Integer.Sparse Key := [(key2452, 6), (key2519, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2452, 6), (key2528, 6), (key2560, 6), (key2357, 6), (key2560, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2366, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2366, 6), (key2523, 6)]

def rawRow18770 : Integer.Sparse Key := [(key2519, 6), (key2452, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2452, 6), (key2560, 6), (key2528, 6), (key2560, 6), (key2357, 6), (key2517, 6), (key2361, 6), (key2523, 6), (key2523, 6), (key2366, 6), (key2461, 6), (key2523, 6), (key2523, 6), (key2366, 6)]

def rawRow18771 : Integer.Sparse Key := [(key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2357, 6), (key2363, 6), (key2452, 6), (key2530, 6), (key2519, 6), (key2560, 6), (key2361, 6), (key2456, 6), (key2517, 6), (key2523, 6), (key2366, 6), (key2461, 6), (key2523, 6)]

def rawRow18772 : Integer.Sparse Key := [(key2458, 6), (key2452, 6), (key2519, 6), (key2452, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2363, 6), (key2357, 6), (key2530, 6), (key2452, 6), (key2560, 6), (key2519, 6), (key2361, 6), (key2517, 6), (key2456, 6), (key2523, 6), (key2366, 6), (key2523, 6), (key2461, 6)]

def rawRow18773 : Integer.Sparse Key := [(key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2560, 6), (key2363, 6), (key2530, 6), (key2456, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2461, 6), (key2366, 6), (key2523, 6)]

def rawRow18774 : Integer.Sparse Key := [(key2519, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2519, 6), (key2452, 6), (key2560, 6), (key2357, 6), (key2530, 6), (key2363, 6), (key2456, 6), (key2517, 6), (key2361, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2366, 6)]

def rawRow18775 : Integer.Sparse Key := [(key2458, 6), (key2519, 6), (key2452, 6), (key2452, 6), (key2530, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2519, 6), (key2357, 6), (key2452, 6), (key2517, 6), (key2361, 6), (key2456, 6), (key2523, 6), (key2523, 6), (key2366, 6), (key2461, 6)]

def rawRow18776 : Integer.Sparse Key := [(key2519, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2560, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2519, 6), (key2363, 6), (key2452, 6), (key2357, 6), (key2517, 6), (key2456, 6), (key2361, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2366, 6)]

def rawRow18777 : Integer.Sparse Key := [(key2528, 6), (key2530, 6), (key2530, 6), (key2560, 6), (key2357, 6), (key2363, 6), (key2363, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2530, 6), (key2458, 6), (key2530, 6), (key2519, 6), (key2519, 6), (key2560, 6), (key2361, 6), (key2456, 6), (key2456, 6), (key2517, 6)]

def rawRow18778 : Integer.Sparse Key := [(key2530, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2357, 6), (key2363, 6), (key2458, 6), (key2452, 6), (key2530, 6), (key2452, 6), (key2530, 6), (key2458, 6), (key2519, 6), (key2560, 6), (key2519, 6), (key2361, 6), (key2456, 6), (key2517, 6), (key2456, 6)]

def rawRow18779 : Integer.Sparse Key := [(key2530, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2363, 6), (key2363, 6), (key2357, 6), (key2530, 6), (key2530, 6), (key2458, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2560, 6), (key2519, 6), (key2519, 6), (key2361, 6), (key2517, 6), (key2456, 6), (key2456, 6)]

def rawRow18780 : Integer.Sparse Key := [(key2528, 6), (key2530, 6), (key2560, 6), (key2530, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2357, 6), (key2363, 6), (key2452, 6), (key2530, 6), (key2519, 6), (key2560, 6), (key2363, 6), (key2458, 6), (key2530, 6), (key2456, 6), (key2361, 6), (key2456, 6), (key2517, 6)]

def rawRow18781 : Integer.Sparse Key := [(key2530, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2363, 6), (key2357, 6), (key2530, 6), (key2452, 6), (key2560, 6), (key2519, 6), (key2363, 6), (key2530, 6), (key2458, 6), (key2456, 6), (key2361, 6), (key2517, 6), (key2456, 6)]

def rawRow18782 : Integer.Sparse Key := [(key2528, 6), (key2560, 6), (key2530, 6), (key2530, 6), (key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2560, 6), (key2363, 6), (key2530, 6), (key2458, 6), (key2363, 6), (key2530, 6), (key2456, 6), (key2456, 6), (key2361, 6), (key2517, 6)]

def rawRow18783 : Integer.Sparse Key := [(key2560, 6), (key2528, 6), (key2530, 6), (key2530, 6), (key2519, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2560, 6), (key2357, 6), (key2530, 6), (key2363, 6), (key2458, 6), (key2530, 6), (key2363, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2361, 6)]

def rawRow18784 : Integer.Sparse Key := [(key2530, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2519, 6), (key2357, 6), (key2452, 6), (key2530, 6), (key2363, 6), (key2458, 6), (key2456, 6), (key2517, 6), (key2361, 6), (key2456, 6)]

def rawRow18785 : Integer.Sparse Key := [(key2560, 6), (key2530, 6), (key2528, 6), (key2530, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2560, 6), (key2530, 6), (key2519, 6), (key2363, 6), (key2452, 6), (key2357, 6), (key2530, 6), (key2458, 6), (key2363, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2361, 6)]

def rawRow18786 : Integer.Sparse Key := [(key2530, 6), (key2530, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2363, 6), (key2458, 6), (key2458, 6), (key2519, 6), (key2519, 6), (key2357, 6), (key2452, 6), (key2452, 6), (key2517, 6), (key2361, 6), (key2456, 6), (key2456, 6)]

def rawRow18787 : Integer.Sparse Key := [(key2530, 6), (key2560, 6), (key2530, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2530, 6), (key2458, 6), (key2519, 6), (key2363, 6), (key2519, 6), (key2363, 6), (key2458, 6), (key2452, 6), (key2357, 6), (key2452, 6), (key2517, 6), (key2456, 6), (key2361, 6), (key2456, 6)]

def rawRow18788 : Integer.Sparse Key := [(key2560, 6), (key2530, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2530, 6), (key2519, 6), (key2458, 6), (key2519, 6), (key2363, 6), (key2458, 6), (key2363, 6), (key2452, 6), (key2452, 6), (key2357, 6), (key2517, 6), (key2456, 6), (key2456, 6), (key2361, 6)]

def rawRow18789 : Integer.Sparse Key := [(key974, 24), (key1088, 24), (key1088, 24), (key1178, 24), (key1178, 24)]

def rawRow18790 : Integer.Sparse Key := [(key974, 24), (key1088, 24), (key1178, 24), (key1088, 24), (key1178, 24)]

def rawRow18791 : Integer.Sparse Key := [(key974, 24), (key1088, 24), (key1178, 24), (key1178, 24), (key1088, 24)]

def rawRow18792 : Integer.Sparse Key := [(key974, 24), (key1178, 24), (key1088, 24), (key1088, 24), (key1178, 24)]

def rawRow18793 : Integer.Sparse Key := [(key974, 24), (key1178, 24), (key1088, 24), (key1178, 24), (key1088, 24)]

def rawRow18794 : Integer.Sparse Key := [(key974, 24), (key1178, 24), (key1178, 24), (key1088, 24), (key1088, 24)]

def rawRow18795 : Integer.Sparse Key := [(key1088, 24), (key974, 24), (key1088, 24), (key1178, 24), (key1178, 24)]

def rawRow18796 : Integer.Sparse Key := [(key1088, 24), (key974, 24), (key1178, 24), (key1088, 24), (key1178, 24)]

def rawRow18797 : Integer.Sparse Key := [(key1088, 24), (key974, 24), (key1178, 24), (key1178, 24), (key1088, 24)]

def rawRow18798 : Integer.Sparse Key := [(key1088, 24), (key1088, 24), (key974, 24), (key1178, 24), (key1178, 24)]

def rawRow18799 : Integer.Sparse Key := [(key1088, 24), (key1088, 24), (key1178, 24), (key974, 24), (key1178, 24)]

def rawRow18800 : Integer.Sparse Key := [(key1088, 24), (key1088, 24), (key1178, 24), (key1178, 24), (key974, 24)]

def rawRow18801 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key974, 24), (key1088, 24), (key1178, 24)]

def rawRow18802 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key974, 24), (key1178, 24), (key1088, 24)]

def rawRow18803 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1088, 24), (key974, 24), (key1178, 24)]

def rawRow18804 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1088, 24), (key1178, 24), (key974, 24)]

def rawRow18805 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1178, 24), (key974, 24), (key1088, 24)]

def rawRow18806 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1178, 24), (key1088, 24), (key974, 24)]

def rawRow18807 : Integer.Sparse Key := [(key1178, 24), (key974, 24), (key1088, 24), (key1088, 24), (key1178, 24)]

def rawRow18808 : Integer.Sparse Key := [(key1178, 24), (key974, 24), (key1088, 24), (key1178, 24), (key1088, 24)]

def rawRow18809 : Integer.Sparse Key := [(key1178, 24), (key974, 24), (key1178, 24), (key1088, 24), (key1088, 24)]

def rawRow18810 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key974, 24), (key1088, 24), (key1178, 24)]

def rawRow18811 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key974, 24), (key1178, 24), (key1088, 24)]

def rawRow18812 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1088, 24), (key974, 24), (key1178, 24)]

def rawRow18813 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1088, 24), (key1178, 24), (key974, 24)]

def rawRow18814 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1178, 24), (key974, 24), (key1088, 24)]

def rawRow18815 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1178, 24), (key1088, 24), (key974, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18816 : Integer.Sparse Key := [(key1178, 24), (key1178, 24), (key974, 24), (key1088, 24), (key1088, 24)]

def rawRow18817 : Integer.Sparse Key := [(key1178, 24), (key1178, 24), (key1088, 24), (key974, 24), (key1088, 24)]

def rawRow18818 : Integer.Sparse Key := [(key1178, 24), (key1178, 24), (key1088, 24), (key1088, 24), (key974, 24)]

def rawRow18819 : Integer.Sparse Key := [(key2378, 2), (key2378, 2), (key2383, 2), (key2378, 2), (key2378, 2), (key2390, 2), (key2390, 2), (key2394, 2), (key2394, 2), (key2383, 2), (key2394, 2), (key2394, 2), (key2406, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2443, 2), (key2472, 2), (key2472, 2), (key2480, 2), (key2480, 2), (key2484, 2), (key2484, 2), (key2472, 2), (key2472, 2), (key2503, 2), (key2503, 2), (key2509, 2), (key2509, 2), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2484, 2), (key2484, 2), (key2509, 2), (key2509, 2), (key2524, 2), (key2524, 2), (key2569, 2), (key2571, 2), (key2571, 2), (key2569, 2), (key2576, 2), (key2576, 2), (key2571, 2), (key2571, 2), (key2576, 2), (key2576, 2), (key2580, 2), (key2580, 2)]

def rawRow18820 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2378, 2), (key2390, 2), (key2394, 2), (key2378, 2), (key2394, 2), (key2378, 2), (key2390, 2), (key2394, 2), (key2383, 2), (key2394, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2480, 2), (key2484, 2), (key2472, 2), (key2484, 2), (key2472, 2), (key2480, 2), (key2503, 2), (key2509, 2), (key2472, 2), (key2509, 2), (key2472, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2524, 2), (key2484, 2), (key2509, 2), (key2571, 2), (key2569, 2), (key2571, 2), (key2576, 2), (key2569, 2), (key2576, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2580, 2), (key2571, 2), (key2576, 2)]

def rawRow18821 : Integer.Sparse Key := [(key2383, 2), (key2378, 2), (key2378, 2), (key2394, 2), (key2390, 2), (key2394, 2), (key2378, 2), (key2390, 2), (key2378, 2), (key2394, 2), (key2394, 2), (key2383, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2484, 2), (key2480, 2), (key2484, 2), (key2472, 2), (key2480, 2), (key2472, 2), (key2509, 2), (key2503, 2), (key2509, 2), (key2472, 2), (key2503, 2), (key2472, 2), (key2524, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2524, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2509, 2), (key2484, 2), (key2571, 2), (key2571, 2), (key2569, 2), (key2576, 2), (key2576, 2), (key2569, 2), (key2580, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2576, 2), (key2571, 2)]

def rawRow18822 : Integer.Sparse Key := [(key2390, 2), (key2394, 2), (key2394, 2), (key2378, 2), (key2383, 2), (key2378, 2), (key2394, 2), (key2383, 2), (key2394, 2), (key2378, 2), (key2378, 2), (key2390, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2503, 2), (key2509, 2), (key2503, 2), (key2524, 2), (key2509, 2), (key2524, 2), (key2480, 2), (key2484, 2), (key2480, 2), (key2524, 2), (key2484, 2), (key2524, 2), (key2472, 2), (key2484, 2), (key2472, 2), (key2509, 2), (key2484, 2), (key2509, 2), (key2472, 2), (key2480, 2), (key2472, 2), (key2503, 2), (key2480, 2), (key2503, 2), (key2576, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2571, 2), (key2580, 2), (key2569, 2), (key2571, 2), (key2569, 2), (key2576, 2), (key2571, 2), (key2576, 2)]

def rawRow18823 : Integer.Sparse Key := [(key2394, 2), (key2390, 2), (key2394, 2), (key2383, 2), (key2378, 2), (key2394, 2), (key2378, 2), (key2394, 2), (key2383, 2), (key2378, 2), (key2390, 2), (key2378, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2411, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2509, 2), (key2503, 2), (key2524, 2), (key2503, 2), (key2524, 2), (key2509, 2), (key2484, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2484, 2), (key2484, 2), (key2472, 2), (key2509, 2), (key2472, 2), (key2509, 2), (key2484, 2), (key2480, 2), (key2472, 2), (key2503, 2), (key2472, 2), (key2503, 2), (key2480, 2), (key2576, 2), (key2580, 2), (key2576, 2), (key2571, 2), (key2580, 2), (key2571, 2), (key2571, 2), (key2569, 2), (key2576, 2), (key2569, 2), (key2576, 2), (key2571, 2)]

def rawRow18824 : Integer.Sparse Key := [(key2394, 2), (key2394, 2), (key2390, 2), (key2394, 2), (key2394, 2), (key2383, 2), (key2383, 2), (key2378, 2), (key2378, 2), (key2390, 2), (key2378, 2), (key2378, 2), (key2443, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2406, 2), (key2524, 2), (key2524, 2), (key2509, 2), (key2509, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2484, 2), (key2484, 2), (key2480, 2), (key2480, 2), (key2509, 2), (key2509, 2), (key2484, 2), (key2484, 2), (key2472, 2), (key2472, 2), (key2503, 2), (key2503, 2), (key2480, 2), (key2480, 2), (key2472, 2), (key2472, 2), (key2580, 2), (key2576, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2571, 2), (key2576, 2), (key2576, 2), (key2571, 2), (key2571, 2), (key2569, 2), (key2569, 2)]

def rawRow18825 : Integer.Sparse Key := [(key2766, 2), (key2766, 2), (key2772, 2), (key2843, 2), (key2843, 2), (key2887, 2), (key2887, 2), (key2889, 2), (key2889, 2), (key2880, 2), (key2910, 2), (key2910, 2), (key2587, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2843, 2), (key2966, 2), (key2966, 2), (key2968, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2989, 2), (key2378, 2), (key2378, 2), (key2390, 2), (key2390, 2), (key2394, 2), (key2394, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2571, 2), (key2571, 2), (key2576, 2), (key2576, 2), (key2580, 2), (key2580, 2), (key2383, 2), (key2394, 2), (key2394, 2), (key2411, 2), (key2443, 2), (key2443, 2), (key2484, 2), (key2484, 2), (key2509, 2), (key2509, 2), (key2524, 2), (key2524, 2)]

def rawRow18826 : Integer.Sparse Key := [(key2766, 2), (key2772, 2), (key2766, 2), (key2887, 2), (key2889, 2), (key2843, 2), (key2889, 2), (key2843, 2), (key2887, 2), (key2910, 2), (key2880, 2), (key2910, 2), (key2587, 2), (key2593, 2), (key2587, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2880, 2), (key2989, 2), (key2390, 2), (key2394, 2), (key2378, 2), (key2394, 2), (key2378, 2), (key2390, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2580, 2), (key2571, 2), (key2576, 2), (key2394, 2), (key2383, 2), (key2394, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2524, 2), (key2484, 2), (key2509, 2)]

def rawRow18827 : Integer.Sparse Key := [(key2772, 2), (key2766, 2), (key2766, 2), (key2889, 2), (key2887, 2), (key2889, 2), (key2843, 2), (key2887, 2), (key2843, 2), (key2910, 2), (key2910, 2), (key2880, 2), (key2593, 2), (key2587, 2), (key2587, 2), (key2968, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2843, 2), (key2989, 2), (key2989, 2), (key2880, 2), (key2394, 2), (key2390, 2), (key2394, 2), (key2378, 2), (key2390, 2), (key2378, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2524, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2580, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2576, 2), (key2571, 2), (key2394, 2), (key2394, 2), (key2383, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2509, 2), (key2484, 2)]

def rawRow18828 : Integer.Sparse Key := [(key2843, 2), (key2843, 2), (key2880, 2), (key2766, 2), (key2766, 2), (key2887, 2), (key2887, 2), (key2910, 2), (key2910, 2), (key2772, 2), (key2889, 2), (key2889, 2), (key2843, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2587, 2), (key2966, 2), (key2966, 2), (key2989, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2968, 2), (key2766, 2), (key2766, 2), (key2887, 2), (key2887, 2), (key2910, 2), (key2910, 2), (key2587, 2), (key2587, 2), (key2966, 2), (key2966, 2), (key2989, 2), (key2989, 2), (key2390, 2), (key2390, 2), (key2437, 2), (key2437, 2), (key2580, 2), (key2580, 2), (key2394, 2), (key2394, 2), (key2443, 2), (key2443, 2), (key2524, 2), (key2524, 2), (key2411, 2), (key2484, 2), (key2484, 2), (key2383, 2), (key2509, 2), (key2509, 2), (key2394, 2), (key2394, 2), (key2443, 2), (key2443, 2), (key2524, 2), (key2524, 2)]

def rawRow18829 : Integer.Sparse Key := [(key2843, 2), (key2880, 2), (key2843, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2889, 2), (key2772, 2), (key2889, 2), (key2843, 2), (key2880, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2968, 2), (key2593, 2), (key2968, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2929, 2), (key3002, 2), (key2598, 2), (key3002, 2), (key2390, 2), (key2437, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2484, 2), (key2411, 2), (key2484, 2), (key2509, 2), (key2383, 2), (key2509, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2524, 2), (key2394, 2), (key2443, 2)]

def rawRow18830 : Integer.Sparse Key := [(key2880, 2), (key2843, 2), (key2843, 2), (key2910, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2766, 2), (key2889, 2), (key2889, 2), (key2772, 2), (key2880, 2), (key2843, 2), (key2843, 2), (key2989, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2587, 2), (key2968, 2), (key2968, 2), (key2593, 2), (key2910, 2), (key2887, 2), (key2910, 2), (key2766, 2), (key2887, 2), (key2766, 2), (key2989, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2587, 2), (key3002, 2), (key2929, 2), (key3002, 2), (key2598, 2), (key2437, 2), (key2390, 2), (key2524, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2394, 2), (key2484, 2), (key2484, 2), (key2411, 2), (key2509, 2), (key2509, 2), (key2383, 2), (key2524, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2394, 2)]

def rawRow18831 : Integer.Sparse Key := [(key2887, 2), (key2889, 2), (key2910, 2), (key2766, 2), (key2772, 2), (key2843, 2), (key2889, 2), (key2880, 2), (key2910, 2), (key2766, 2), (key2843, 2), (key2887, 2), (key2966, 2), (key2968, 2), (key2989, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2587, 2), (key2843, 2), (key2966, 2), (key2929, 2), (key2931, 2), (key2966, 2), (key2995, 2), (key2989, 2), (key3002, 2), (key2598, 2), (key2600, 2), (key2887, 2), (key2995, 2), (key2910, 2), (key3002, 2), (key2587, 2), (key2600, 2), (key2766, 2), (key2931, 2), (key2910, 2), (key2989, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2437, 2), (key2480, 2), (key2503, 2), (key2443, 2), (key2509, 2), (key2524, 2), (key2394, 2), (key2484, 2), (key2524, 2), (key2383, 2), (key2394, 2), (key2411, 2), (key2443, 2), (key2484, 2), (key2509, 2)]

def rawRow18832 : Integer.Sparse Key := [(key2889, 2), (key2887, 2), (key2910, 2), (key2772, 2), (key2766, 2), (key2889, 2), (key2843, 2), (key2910, 2), (key2880, 2), (key2766, 2), (key2887, 2), (key2843, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2593, 2), (key2587, 2), (key2968, 2), (key2843, 2), (key2989, 2), (key2880, 2), (key2587, 2), (key2966, 2), (key2843, 2), (key2931, 2), (key2929, 2), (key2995, 2), (key2966, 2), (key3002, 2), (key2989, 2), (key2600, 2), (key2598, 2), (key2995, 2), (key2887, 2), (key3002, 2), (key2910, 2), (key2600, 2), (key2587, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2910, 2), (key2390, 2), (key2378, 2), (key2437, 2), (key2406, 2), (key2503, 2), (key2480, 2), (key2443, 2), (key2524, 2), (key2509, 2), (key2394, 2), (key2524, 2), (key2484, 2), (key2394, 2), (key2383, 2), (key2443, 2), (key2411, 2), (key2509, 2), (key2484, 2)]

def rawRow18833 : Integer.Sparse Key := [(key2887, 2), (key2910, 2), (key2889, 2), (key2843, 2), (key2880, 2), (key2766, 2), (key2910, 2), (key2772, 2), (key2889, 2), (key2843, 2), (key2766, 2), (key2887, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2843, 2), (key2587, 2), (key2966, 2), (key2966, 2), (key2989, 2), (key2929, 2), (key3002, 2), (key2931, 2), (key2995, 2), (key2887, 2), (key2910, 2), (key2598, 2), (key3002, 2), (key2600, 2), (key2995, 2), (key2766, 2), (key2910, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2406, 2), (key2480, 2), (key2378, 2), (key2503, 2), (key2390, 2), (key2437, 2), (key2509, 2), (key2443, 2), (key2524, 2), (key2484, 2), (key2394, 2), (key2524, 2), (key2411, 2), (key2484, 2), (key2383, 2), (key2509, 2), (key2394, 2), (key2443, 2)]

def rawRow18834 : Integer.Sparse Key := [(key2910, 2), (key2887, 2), (key2889, 2), (key2880, 2), (key2843, 2), (key2910, 2), (key2766, 2), (key2889, 2), (key2772, 2), (key2843, 2), (key2887, 2), (key2766, 2), (key2989, 2), (key2966, 2), (key2968, 2), (key2880, 2), (key2843, 2), (key2989, 2), (key2587, 2), (key2968, 2), (key2593, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2989, 2), (key2966, 2), (key3002, 2), (key2929, 2), (key2995, 2), (key2931, 2), (key2910, 2), (key2887, 2), (key3002, 2), (key2598, 2), (key2995, 2), (key2600, 2), (key2910, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2931, 2), (key2600, 2), (key2480, 2), (key2406, 2), (key2503, 2), (key2378, 2), (key2437, 2), (key2390, 2), (key2509, 2), (key2524, 2), (key2443, 2), (key2484, 2), (key2524, 2), (key2394, 2), (key2484, 2), (key2411, 2), (key2509, 2), (key2383, 2), (key2443, 2), (key2394, 2)]

def rawRow18835 : Integer.Sparse Key := [(key2889, 2), (key2910, 2), (key2887, 2), (key2889, 2), (key2910, 2), (key2772, 2), (key2880, 2), (key2766, 2), (key2843, 2), (key2887, 2), (key2766, 2), (key2843, 2), (key2968, 2), (key2989, 2), (key2966, 2), (key2968, 2), (key2989, 2), (key2593, 2), (key2880, 2), (key2587, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2843, 2), (key2995, 2), (key3002, 2), (key2931, 2), (key2989, 2), (key2929, 2), (key2966, 2), (key2995, 2), (key3002, 2), (key2600, 2), (key2910, 2), (key2598, 2), (key2887, 2), (key2931, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2587, 2), (key2766, 2), (key2437, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2378, 2), (key2406, 2), (key2524, 2), (key2443, 2), (key2509, 2), (key2524, 2), (key2394, 2), (key2484, 2), (key2443, 2), (key2509, 2), (key2394, 2), (key2484, 2), (key2383, 2), (key2411, 2)]

def rawRow18836 : Integer.Sparse Key := [(key2910, 2), (key2889, 2), (key2887, 2), (key2910, 2), (key2889, 2), (key2880, 2), (key2772, 2), (key2843, 2), (key2766, 2), (key2887, 2), (key2843, 2), (key2766, 2), (key2989, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2880, 2), (key2593, 2), (key2843, 2), (key2587, 2), (key2966, 2), (key2843, 2), (key2587, 2), (key3002, 2), (key2995, 2), (key2989, 2), (key2931, 2), (key2966, 2), (key2929, 2), (key3002, 2), (key2995, 2), (key2910, 2), (key2600, 2), (key2887, 2), (key2598, 2), (key2989, 2), (key2931, 2), (key2910, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2503, 2), (key2437, 2), (key2480, 2), (key2390, 2), (key2406, 2), (key2378, 2), (key2524, 2), (key2509, 2), (key2443, 2), (key2524, 2), (key2484, 2), (key2394, 2), (key2509, 2), (key2443, 2), (key2484, 2), (key2394, 2), (key2411, 2), (key2383, 2)]

def rawRow18837 : Integer.Sparse Key := [(key2929, 2), (key2931, 2), (key2931, 2), (key2966, 2), (key2968, 2), (key2966, 2), (key2995, 2), (key2968, 2), (key2995, 2), (key2989, 2), (key2989, 2), (key3002, 2), (key2598, 2), (key2600, 2), (key2600, 2), (key2887, 2), (key2889, 2), (key2887, 2), (key2995, 2), (key2889, 2), (key2995, 2), (key2910, 2), (key2910, 2), (key3002, 2), (key2587, 2), (key2593, 2), (key2587, 2), (key2600, 2), (key2593, 2), (key2600, 2), (key2766, 2), (key2772, 2), (key2766, 2), (key2931, 2), (key2772, 2), (key2931, 2), (key2843, 2), (key2889, 2), (key2843, 2), (key2968, 2), (key2889, 2), (key2968, 2), (key2880, 2), (key2910, 2), (key2880, 2), (key2989, 2), (key2910, 2), (key2989, 2), (key2378, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2472, 2), (key2480, 2), (key2472, 2), (key2503, 2), (key2480, 2), (key2503, 2)]

def rawRow18838 : Integer.Sparse Key := [(key2931, 2), (key2929, 2), (key2931, 2), (key2968, 2), (key2966, 2), (key2995, 2), (key2966, 2), (key2995, 2), (key2968, 2), (key2989, 2), (key3002, 2), (key2989, 2), (key2600, 2), (key2598, 2), (key2600, 2), (key2889, 2), (key2887, 2), (key2995, 2), (key2887, 2), (key2995, 2), (key2889, 2), (key2910, 2), (key3002, 2), (key2910, 2), (key2593, 2), (key2587, 2), (key2600, 2), (key2587, 2), (key2600, 2), (key2593, 2), (key2772, 2), (key2766, 2), (key2931, 2), (key2766, 2), (key2931, 2), (key2772, 2), (key2889, 2), (key2843, 2), (key2968, 2), (key2843, 2), (key2968, 2), (key2889, 2), (key2910, 2), (key2880, 2), (key2989, 2), (key2880, 2), (key2989, 2), (key2910, 2), (key2378, 2), (key2390, 2), (key2378, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2480, 2), (key2472, 2), (key2503, 2), (key2472, 2), (key2503, 2), (key2480, 2)]

def rawRow18839 : Integer.Sparse Key := [(key2931, 2), (key2931, 2), (key2929, 2), (key2995, 2), (key2995, 2), (key2968, 2), (key2968, 2), (key2966, 2), (key2966, 2), (key3002, 2), (key2989, 2), (key2989, 2), (key2600, 2), (key2600, 2), (key2598, 2), (key2995, 2), (key2995, 2), (key2889, 2), (key2889, 2), (key2887, 2), (key2887, 2), (key3002, 2), (key2910, 2), (key2910, 2), (key2600, 2), (key2600, 2), (key2593, 2), (key2593, 2), (key2587, 2), (key2587, 2), (key2931, 2), (key2931, 2), (key2772, 2), (key2772, 2), (key2766, 2), (key2766, 2), (key2968, 2), (key2968, 2), (key2889, 2), (key2889, 2), (key2843, 2), (key2843, 2), (key2989, 2), (key2989, 2), (key2910, 2), (key2910, 2), (key2880, 2), (key2880, 2), (key2390, 2), (key2378, 2), (key2378, 2), (key2437, 2), (key2406, 2), (key2406, 2), (key2503, 2), (key2503, 2), (key2480, 2), (key2480, 2), (key2472, 2), (key2472, 2)]

def rawRow18840 : Integer.Sparse Key := [(key2966, 2), (key2968, 2), (key2989, 2), (key2929, 2), (key2931, 2), (key2966, 2), (key2995, 2), (key2989, 2), (key3002, 2), (key2931, 2), (key2968, 2), (key2995, 2), (key2887, 2), (key2889, 2), (key2910, 2), (key2598, 2), (key2600, 2), (key2887, 2), (key2995, 2), (key2910, 2), (key3002, 2), (key2600, 2), (key2889, 2), (key2995, 2), (key2766, 2), (key2772, 2), (key2843, 2), (key2889, 2), (key2880, 2), (key2910, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2587, 2), (key2600, 2), (key2766, 2), (key2931, 2), (key2910, 2), (key2989, 2), (key2593, 2), (key2600, 2), (key2772, 2), (key2931, 2), (key2889, 2), (key2968, 2), (key2406, 2), (key2472, 2), (key2480, 2), (key2378, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2437, 2), (key2480, 2), (key2503, 2)]

def rawRow18841 : Integer.Sparse Key := [(key2968, 2), (key2966, 2), (key2989, 2), (key2931, 2), (key2929, 2), (key2995, 2), (key2966, 2), (key3002, 2), (key2989, 2), (key2931, 2), (key2995, 2), (key2968, 2), (key2889, 2), (key2887, 2), (key2910, 2), (key2600, 2), (key2598, 2), (key2995, 2), (key2887, 2), (key3002, 2), (key2910, 2), (key2600, 2), (key2995, 2), (key2889, 2), (key2772, 2), (key2766, 2), (key2889, 2), (key2843, 2), (key2910, 2), (key2880, 2), (key2593, 2), (key2587, 2), (key2968, 2), (key2843, 2), (key2989, 2), (key2880, 2), (key2600, 2), (key2587, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2910, 2), (key2600, 2), (key2593, 2), (key2931, 2), (key2772, 2), (key2968, 2), (key2889, 2), (key2406, 2), (key2480, 2), (key2472, 2), (key2378, 2), (key2503, 2), (key2472, 2), (key2390, 2), (key2378, 2), (key2437, 2), (key2406, 2), (key2503, 2), (key2480, 2)]

def rawRow18842 : Integer.Sparse Key := [(key2966, 2), (key2989, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2929, 2), (key3002, 2), (key2931, 2), (key2995, 2), (key2968, 2), (key2931, 2), (key2995, 2), (key2887, 2), (key2910, 2), (key2889, 2), (key2887, 2), (key2910, 2), (key2598, 2), (key3002, 2), (key2600, 2), (key2995, 2), (key2889, 2), (key2600, 2), (key2995, 2), (key2843, 2), (key2880, 2), (key2766, 2), (key2910, 2), (key2772, 2), (key2889, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2766, 2), (key2910, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2772, 2), (key2889, 2), (key2593, 2), (key2968, 2), (key2600, 2), (key2931, 2), (key2472, 2), (key2406, 2), (key2480, 2), (key2472, 2), (key2378, 2), (key2503, 2), (key2406, 2), (key2480, 2), (key2378, 2), (key2503, 2), (key2390, 2), (key2437, 2)]

def rawRow18843 : Integer.Sparse Key := [(key2989, 2), (key2966, 2), (key2968, 2), (key2989, 2), (key2966, 2), (key3002, 2), (key2929, 2), (key2995, 2), (key2931, 2), (key2968, 2), (key2995, 2), (key2931, 2), (key2910, 2), (key2887, 2), (key2889, 2), (key2910, 2), (key2887, 2), (key3002, 2), (key2598, 2), (key2995, 2), (key2600, 2), (key2889, 2), (key2995, 2), (key2600, 2), (key2880, 2), (key2843, 2), (key2910, 2), (key2766, 2), (key2889, 2), (key2772, 2), (key2880, 2), (key2843, 2), (key2989, 2), (key2587, 2), (key2968, 2), (key2593, 2), (key2910, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2931, 2), (key2600, 2), (key2889, 2), (key2772, 2), (key2968, 2), (key2593, 2), (key2931, 2), (key2600, 2), (key2472, 2), (key2480, 2), (key2406, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2480, 2), (key2406, 2), (key2503, 2), (key2378, 2), (key2437, 2), (key2390, 2)]

def rawRow18844 : Integer.Sparse Key := [(key2968, 2), (key2989, 2), (key2966, 2), (key2995, 2), (key3002, 2), (key2931, 2), (key2989, 2), (key2929, 2), (key2966, 2), (key2995, 2), (key2931, 2), (key2968, 2), (key2889, 2), (key2910, 2), (key2887, 2), (key2995, 2), (key3002, 2), (key2600, 2), (key2910, 2), (key2598, 2), (key2887, 2), (key2995, 2), (key2600, 2), (key2889, 2), (key2889, 2), (key2910, 2), (key2772, 2), (key2880, 2), (key2766, 2), (key2843, 2), (key2968, 2), (key2989, 2), (key2593, 2), (key2880, 2), (key2587, 2), (key2843, 2), (key2931, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2587, 2), (key2766, 2), (key2931, 2), (key2968, 2), (key2600, 2), (key2889, 2), (key2593, 2), (key2772, 2), (key2480, 2), (key2406, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2472, 2), (key2437, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2378, 2), (key2406, 2)]

def rawRow18845 : Integer.Sparse Key := [(key2989, 2), (key2968, 2), (key2966, 2), (key3002, 2), (key2995, 2), (key2989, 2), (key2931, 2), (key2966, 2), (key2929, 2), (key2995, 2), (key2968, 2), (key2931, 2), (key2910, 2), (key2889, 2), (key2887, 2), (key3002, 2), (key2995, 2), (key2910, 2), (key2600, 2), (key2887, 2), (key2598, 2), (key2995, 2), (key2889, 2), (key2600, 2), (key2910, 2), (key2889, 2), (key2880, 2), (key2772, 2), (key2843, 2), (key2766, 2), (key2989, 2), (key2968, 2), (key2880, 2), (key2593, 2), (key2843, 2), (key2587, 2), (key2989, 2), (key2931, 2), (key2910, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2968, 2), (key2931, 2), (key2889, 2), (key2600, 2), (key2772, 2), (key2593, 2), (key2480, 2), (key2472, 2), (key2406, 2), (key2503, 2), (key2472, 2), (key2378, 2), (key2503, 2), (key2437, 2), (key2480, 2), (key2390, 2), (key2406, 2), (key2378, 2)]

def rawRow18846 : Integer.Sparse Key := [(key2995, 2), (key2995, 2), (key3002, 2), (key2931, 2), (key2931, 2), (key2968, 2), (key2968, 2), (key2989, 2), (key2989, 2), (key2929, 2), (key2966, 2), (key2966, 2), (key2995, 2), (key2995, 2), (key3002, 2), (key2600, 2), (key2600, 2), (key2889, 2), (key2889, 2), (key2910, 2), (key2910, 2), (key2598, 2), (key2887, 2), (key2887, 2), (key2931, 2), (key2931, 2), (key2968, 2), (key2968, 2), (key2989, 2), (key2989, 2), (key2600, 2), (key2600, 2), (key2889, 2), (key2889, 2), (key2910, 2), (key2910, 2), (key2593, 2), (key2593, 2), (key2772, 2), (key2772, 2), (key2880, 2), (key2880, 2), (key2587, 2), (key2587, 2), (key2766, 2), (key2766, 2), (key2843, 2), (key2843, 2), (key2437, 2), (key2503, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2480, 2), (key2378, 2), (key2378, 2), (key2406, 2), (key2406, 2), (key2472, 2), (key2472, 2)]

def rawRow18847 : Integer.Sparse Key := [(key2995, 2), (key3002, 2), (key2995, 2), (key2968, 2), (key2989, 2), (key2931, 2), (key2989, 2), (key2931, 2), (key2968, 2), (key2966, 2), (key2929, 2), (key2966, 2), (key2995, 2), (key3002, 2), (key2995, 2), (key2889, 2), (key2910, 2), (key2600, 2), (key2910, 2), (key2600, 2), (key2889, 2), (key2887, 2), (key2598, 2), (key2887, 2), (key2968, 2), (key2989, 2), (key2931, 2), (key2989, 2), (key2931, 2), (key2968, 2), (key2889, 2), (key2910, 2), (key2600, 2), (key2910, 2), (key2600, 2), (key2889, 2), (key2772, 2), (key2880, 2), (key2593, 2), (key2880, 2), (key2593, 2), (key2772, 2), (key2766, 2), (key2843, 2), (key2587, 2), (key2843, 2), (key2587, 2), (key2766, 2), (key2503, 2), (key2437, 2), (key2503, 2), (key2480, 2), (key2390, 2), (key2480, 2), (key2406, 2), (key2472, 2), (key2378, 2), (key2472, 2), (key2378, 2), (key2406, 2)]

def rawRow18848 : Integer.Sparse Key := [(key3002, 2), (key2995, 2), (key2995, 2), (key2989, 2), (key2968, 2), (key2989, 2), (key2931, 2), (key2968, 2), (key2931, 2), (key2966, 2), (key2966, 2), (key2929, 2), (key3002, 2), (key2995, 2), (key2995, 2), (key2910, 2), (key2889, 2), (key2910, 2), (key2600, 2), (key2889, 2), (key2600, 2), (key2887, 2), (key2887, 2), (key2598, 2), (key2989, 2), (key2968, 2), (key2989, 2), (key2931, 2), (key2968, 2), (key2931, 2), (key2910, 2), (key2889, 2), (key2910, 2), (key2600, 2), (key2889, 2), (key2600, 2), (key2880, 2), (key2772, 2), (key2880, 2), (key2593, 2), (key2772, 2), (key2593, 2), (key2843, 2), (key2766, 2), (key2843, 2), (key2587, 2), (key2766, 2), (key2587, 2), (key2503, 2), (key2503, 2), (key2437, 2), (key2480, 2), (key2480, 2), (key2390, 2), (key2472, 2), (key2406, 2), (key2472, 2), (key2378, 2), (key2406, 2), (key2378, 2)]

def rawRow18849 : Integer.Sparse Key := [(key2360, 24), (key2455, 24), (key2455, 24), (key2516, 24), (key2516, 24)]

def rawRow18850 : Integer.Sparse Key := [(key2360, 24), (key2455, 24), (key2516, 24), (key2455, 24), (key2516, 24)]

def rawRow18851 : Integer.Sparse Key := [(key2360, 24), (key2455, 24), (key2516, 24), (key2516, 24), (key2455, 24)]

def rawRow18852 : Integer.Sparse Key := [(key2360, 24), (key2516, 24), (key2455, 24), (key2455, 24), (key2516, 24)]

def rawRow18853 : Integer.Sparse Key := [(key2360, 24), (key2516, 24), (key2455, 24), (key2516, 24), (key2455, 24)]

def rawRow18854 : Integer.Sparse Key := [(key2360, 24), (key2516, 24), (key2516, 24), (key2455, 24), (key2455, 24)]

def rawRow18855 : Integer.Sparse Key := [(key2455, 24), (key2360, 24), (key2455, 24), (key2516, 24), (key2516, 24)]

def rawRow18856 : Integer.Sparse Key := [(key2455, 24), (key2360, 24), (key2516, 24), (key2455, 24), (key2516, 24)]

def rawRow18857 : Integer.Sparse Key := [(key2455, 24), (key2360, 24), (key2516, 24), (key2516, 24), (key2455, 24)]

def rawRow18858 : Integer.Sparse Key := [(key2455, 24), (key2455, 24), (key2360, 24), (key2516, 24), (key2516, 24)]

def rawRow18859 : Integer.Sparse Key := [(key2455, 24), (key2455, 24), (key2516, 24), (key2360, 24), (key2516, 24)]

def rawRow18860 : Integer.Sparse Key := [(key2455, 24), (key2455, 24), (key2516, 24), (key2516, 24), (key2360, 24)]

def rawRow18861 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2360, 24), (key2455, 24), (key2516, 24)]

def rawRow18862 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2360, 24), (key2516, 24), (key2455, 24)]

def rawRow18863 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2455, 24), (key2360, 24), (key2516, 24)]

def rawRow18864 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2455, 24), (key2516, 24), (key2360, 24)]

def rawRow18865 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2516, 24), (key2360, 24), (key2455, 24)]

def rawRow18866 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2516, 24), (key2455, 24), (key2360, 24)]

def rawRow18867 : Integer.Sparse Key := [(key2516, 24), (key2360, 24), (key2455, 24), (key2455, 24), (key2516, 24)]

def rawRow18868 : Integer.Sparse Key := [(key2516, 24), (key2360, 24), (key2455, 24), (key2516, 24), (key2455, 24)]

def rawRow18869 : Integer.Sparse Key := [(key2516, 24), (key2360, 24), (key2516, 24), (key2455, 24), (key2455, 24)]

def rawRow18870 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2360, 24), (key2455, 24), (key2516, 24)]

def rawRow18871 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2360, 24), (key2516, 24), (key2455, 24)]

def rawRow18872 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2455, 24), (key2360, 24), (key2516, 24)]

def rawRow18873 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2455, 24), (key2516, 24), (key2360, 24)]

def rawRow18874 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2516, 24), (key2360, 24), (key2455, 24)]

def rawRow18875 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2516, 24), (key2455, 24), (key2360, 24)]

def rawRow18876 : Integer.Sparse Key := [(key2516, 24), (key2516, 24), (key2360, 24), (key2455, 24), (key2455, 24)]

def rawRow18877 : Integer.Sparse Key := [(key2516, 24), (key2516, 24), (key2455, 24), (key2360, 24), (key2455, 24)]

def rawRow18878 : Integer.Sparse Key := [(key2516, 24), (key2516, 24), (key2455, 24), (key2455, 24), (key2360, 24)]

def rawRow18879 : Integer.Sparse Key := [(key976, 6), (key976, 6), (key984, 6), (key984, 6), (key1090, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1169, 6), (key1220, 6), (key1220, 6)]

def rawRow18880 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key976, 6), (key984, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key1169, 6), (key1220, 6)]

def rawRow18881 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key976, 6), (key984, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key1220, 6), (key1220, 6), (key1169, 6)]

def rawRow18882 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key984, 6), (key976, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key1169, 6), (key1169, 6), (key1220, 6)]

def rawRow18883 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key984, 6), (key976, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key1220, 6), (key1169, 6)]

def rawRow18884 : Integer.Sparse Key := [(key984, 6), (key984, 6), (key976, 6), (key976, 6), (key1183, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1220, 6), (key1169, 6), (key1169, 6)]

def rawRow18885 : Integer.Sparse Key := [(key1090, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key976, 6), (key976, 6), (key984, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key1220, 6), (key984, 6), (key1098, 6), (key1183, 6), (key1183, 6)]

def rawRow18886 : Integer.Sparse Key := [(key1090, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key976, 6), (key984, 6), (key976, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key1169, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1098, 6), (key1183, 6)]

def rawRow18887 : Integer.Sparse Key := [(key1098, 6), (key1090, 6), (key1090, 6), (key1169, 6), (key984, 6), (key976, 6), (key976, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1220, 6), (key1220, 6), (key1169, 6), (key984, 6), (key1183, 6), (key1183, 6), (key1098, 6)]

def rawRow18888 : Integer.Sparse Key := [(key1090, 6), (key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1169, 6), (key976, 6), (key976, 6), (key1180, 6), (key1180, 6), (key1220, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1183, 6), (key1183, 6)]

def rawRow18889 : Integer.Sparse Key := [(key1090, 6), (key1169, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key976, 6), (key1220, 6), (key976, 6), (key1180, 6), (key1183, 6), (key984, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key984, 6), (key1183, 6)]

def rawRow18890 : Integer.Sparse Key := [(key1169, 6), (key1090, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1180, 6), (key1220, 6), (key976, 6), (key1180, 6), (key976, 6), (key1183, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1183, 6), (key1183, 6), (key984, 6)]

def rawRow18891 : Integer.Sparse Key := [(key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key976, 6), (key984, 6), (key1090, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key976, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1183, 6)]

def rawRow18892 : Integer.Sparse Key := [(key1098, 6), (key1090, 6), (key1169, 6), (key1090, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key984, 6), (key976, 6), (key1183, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key976, 6), (key1180, 6), (key1090, 6), (key1183, 6), (key984, 6), (key1183, 6), (key1098, 6)]

def rawRow18893 : Integer.Sparse Key := [(key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1090, 6), (key1169, 6), (key976, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1183, 6)]

def rawRow18894 : Integer.Sparse Key := [(key1169, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1169, 6), (key1090, 6), (key1220, 6), (key976, 6), (key1183, 6), (key984, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key984, 6)]

def rawRow18895 : Integer.Sparse Key := [(key1098, 6), (key1169, 6), (key1090, 6), (key1090, 6), (key1183, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key984, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1090, 6), (key1183, 6), (key1183, 6), (key984, 6), (key1098, 6)]

def rawRow18896 : Integer.Sparse Key := [(key1169, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1169, 6), (key984, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1090, 6), (key976, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key984, 6)]

def rawRow18897 : Integer.Sparse Key := [(key1180, 6), (key1183, 6), (key1183, 6), (key1220, 6), (key976, 6), (key984, 6), (key984, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1169, 6), (key1169, 6), (key1220, 6), (key976, 6), (key1090, 6), (key1090, 6), (key1180, 6)]

def rawRow18898 : Integer.Sparse Key := [(key1183, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key984, 6), (key976, 6), (key984, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key1220, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1180, 6), (key1090, 6)]

def rawRow18899 : Integer.Sparse Key := [(key1183, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key984, 6), (key984, 6), (key976, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key1169, 6), (key976, 6), (key1180, 6), (key1090, 6), (key1090, 6)]

def rawRow18900 : Integer.Sparse Key := [(key1180, 6), (key1183, 6), (key1220, 6), (key1183, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key976, 6), (key984, 6), (key1090, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key984, 6), (key1098, 6), (key1183, 6), (key1090, 6), (key976, 6), (key1090, 6), (key1180, 6)]

def rawRow18901 : Integer.Sparse Key := [(key1183, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key984, 6), (key976, 6), (key1183, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key984, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1090, 6)]

def rawRow18902 : Integer.Sparse Key := [(key1180, 6), (key1220, 6), (key1183, 6), (key1183, 6), (key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key976, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1183, 6), (key1090, 6), (key1090, 6), (key976, 6), (key1180, 6)]

def rawRow18903 : Integer.Sparse Key := [(key1220, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1220, 6), (key976, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1183, 6), (key984, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key976, 6)]

def rawRow18904 : Integer.Sparse Key := [(key1183, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1183, 6), (key1220, 6), (key984, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1090, 6)]

def rawRow18905 : Integer.Sparse Key := [(key1220, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1220, 6), (key1183, 6), (key1169, 6), (key984, 6), (key1090, 6), (key976, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key976, 6)]

def rawRow18906 : Integer.Sparse Key := [(key1183, 6), (key1183, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1220, 6), (key984, 6), (key984, 6), (key1098, 6), (key1098, 6), (key1169, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1090, 6), (key1090, 6)]

def rawRow18907 : Integer.Sparse Key := [(key1183, 6), (key1220, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key984, 6), (key1169, 6), (key984, 6), (key1098, 6), (key1090, 6), (key976, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key976, 6), (key1090, 6)]

def rawRow18908 : Integer.Sparse Key := [(key1220, 6), (key1183, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1098, 6), (key1169, 6), (key984, 6), (key1098, 6), (key984, 6), (key1090, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1090, 6), (key1090, 6), (key976, 6)]

def rawRow18909 : Integer.Sparse Key := [(key2362, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2457, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2525, 4), (key2532, 4), (key2532, 4), (key2533, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2533, 4), (key2564, 4), (key2564, 4)]

def rawRow18910 : Integer.Sparse Key := [(key2365, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2365, 4), (key2460, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2532, 4), (key2533, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow18911 : Integer.Sparse Key := [(key2365, 4), (key2365, 4), (key2362, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2457, 4), (key2525, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2533, 4), (key2532, 4), (key2532, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow18912 : Integer.Sparse Key := [(key2365, 4), (key2365, 4), (key2367, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2525, 4), (key2457, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2532, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2564, 4), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow18913 : Integer.Sparse Key := [(key2365, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2365, 4), (key2521, 4), (key2525, 4), (key2521, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow18914 : Integer.Sparse Key := [(key2367, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2525, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2457, 4), (key2564, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2533, 4), (key2533, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow18915 : Integer.Sparse Key := [(key2457, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2525, 4), (key2533, 4), (key2564, 4), (key2564, 4)]

def rawRow18916 : Integer.Sparse Key := [(key2460, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2525, 4), (key2521, 4), (key2365, 4), (key2362, 4), (key2365, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2367, 4), (key2365, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow18917 : Integer.Sparse Key := [(key2460, 4), (key2460, 4), (key2457, 4), (key2525, 4), (key2521, 4), (key2521, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2521, 4), (key2457, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2525, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow18918 : Integer.Sparse Key := [(key2457, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2525, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2362, 4), (key2562, 4), (key2562, 4), (key2365, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2564, 4), (key2564, 4), (key2460, 4), (key2460, 4), (key2533, 4), (key2365, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2564, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2525, 4)]

def rawRow18919 : Integer.Sparse Key := [(key2521, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2562, 4), (key2362, 4), (key2562, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2533, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2525, 4), (key2367, 4), (key2525, 4)]

def rawRow18920 : Integer.Sparse Key := [(key2521, 4), (key2521, 4), (key2457, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2562, 4), (key2362, 4), (key2564, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2533, 4), (key2460, 4), (key2460, 4), (key2564, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2525, 4), (key2525, 4), (key2367, 4)]

def rawRow18921 : Integer.Sparse Key := [(key2460, 4), (key2521, 4), (key2525, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2564, 4), (key2362, 4), (key2365, 4), (key2457, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2521, 4), (key2525, 4), (key2564, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2525, 4), (key2533, 4), (key2564, 4), (key2365, 4), (key2460, 4), (key2521, 4)]

def rawRow18922 : Integer.Sparse Key := [(key2460, 4), (key2525, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2532, 4), (key2564, 4), (key2562, 4), (key2365, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2367, 4), (key2365, 4), (key2525, 4), (key2460, 4), (key2564, 4), (key2533, 4), (key2365, 4), (key2521, 4), (key2460, 4)]

def rawRow18923 : Integer.Sparse Key := [(key2521, 4), (key2460, 4), (key2525, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2457, 4), (key2521, 4), (key2362, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2460, 4), (key2533, 4), (key2365, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2460, 4), (key2365, 4), (key2521, 4)]

def rawRow18924 : Integer.Sparse Key := [(key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2460, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2362, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2521, 4), (key2525, 4), (key2533, 4), (key2460, 4), (key2564, 4), (key2365, 4), (key2525, 4), (key2367, 4), (key2460, 4), (key2521, 4), (key2365, 4)]

def rawRow18925 : Integer.Sparse Key := [(key2525, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2362, 4), (key2457, 4), (key2525, 4), (key2564, 4), (key2521, 4), (key2525, 4), (key2564, 4), (key2367, 4), (key2533, 4), (key2365, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2460, 4)]

def rawRow18926 : Integer.Sparse Key := [(key2525, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2564, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2562, 4), (key2532, 4), (key2521, 4), (key2365, 4), (key2457, 4), (key2362, 4), (key2564, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2533, 4), (key2367, 4), (key2460, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2365, 4)]

def rawRow18927 : Integer.Sparse Key := [(key2532, 4), (key2532, 4), (key2533, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2460, 4), (key2533, 4), (key2521, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2564, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2457, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow18939 : Integer.Sparse Key := [(key2354, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2514, 6), (key2514, 6), (key2514, 6), (key2559, 6)]

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

def rawRow176 : Integer.Sparse Key := [(key2660, -2), (key2658, 1), (key2660, 1), (key2644, 2), (key2621, -1), (key2644, -1), (key2632, -1), (key2640, -1), (key2616, 1), (key2640, 1), (key2747, 2), (key2728, -1), (key2747, -1), (key2737, -2), (key2673, 1), (key2737, 1), (key2702, 1), (key2735, 1), (key2667, -1), (key2735, -1), (key2904, -2), (key2831, 1), (key2904, 1), (key2897, 2), (key2795, -1), (key2897, -1), (key2805, -1), (key2893, -1), (key2782, 1), (key2893, 1), (key2983, 1), (key3000, 1), (key2960, -1), (key3000, -1), (key2976, -1), (key2998, -1), (key2943, 1), (key2998, 1), (key2950, 1), (key2997, 1), (key2938, -1), (key2997, -1)]

def rawRow177 : Integer.Sparse Key := [(key2660, -2), (key2660, 1), (key2658, 1), (key2644, 2), (key2644, -1), (key2621, -1), (key2640, -1), (key2632, -1), (key2640, 1), (key2616, 1), (key2747, 2), (key2747, -1), (key2728, -1), (key2737, -2), (key2737, 1), (key2673, 1), (key2735, 1), (key2702, 1), (key2735, -1), (key2667, -1), (key2904, -2), (key2904, 1), (key2831, 1), (key2897, 2), (key2897, -1), (key2795, -1), (key2893, -1), (key2805, -1), (key2893, 1), (key2782, 1), (key3000, 1), (key2983, 1), (key3000, -1), (key2960, -1), (key2998, -1), (key2976, -1), (key2998, 1), (key2943, 1), (key2997, 1), (key2950, 1), (key2997, -1), (key2938, -1)]

def rawRow178 : Integer.Sparse Key := [(key2671, -2), (key2671, 1), (key2676, 1), (key2706, 2), (key2706, -1), (key2753, -1), (key2726, -1), (key2732, -1), (key2726, 1), (key2758, 1), (key2612, 2), (key2612, -1), (key2618, -1), (key2805, -2), (key2805, 1), (key2831, 1), (key2948, 1), (key2950, 1), (key2948, -1), (key2960, -1), (key2628, -2), (key2628, 1), (key2641, 1), (key2702, 2), (key2702, -1), (key2728, -1), (key2972, -1), (key2976, -1), (key2972, 1), (key2983, 1), (key2646, 1), (key2648, 1), (key2646, -1), (key2653, -1), (key2735, -1), (key2737, -1), (key2735, 1), (key2747, 1), (key2893, 1), (key2897, 1), (key2893, -1), (key2904, -1)]

def rawRow179 : Integer.Sparse Key := [(key2671, -2), (key2676, 1), (key2671, 1), (key2706, 2), (key2753, -1), (key2706, -1), (key2732, -1), (key2726, -1), (key2758, 1), (key2726, 1), (key2616, 2), (key2618, -1), (key2612, -1), (key2805, -2), (key2831, 1), (key2805, 1), (key2950, 1), (key2948, 1), (key2960, -1), (key2948, -1), (key2628, -2), (key2641, 1), (key2628, 1), (key2702, 2), (key2728, -1), (key2702, -1), (key2976, -1), (key2972, -1), (key2983, 1), (key2972, 1), (key2648, 1), (key2646, 1), (key2653, -1), (key2646, -1), (key2737, -1), (key2735, -1), (key2747, 1), (key2735, 1), (key2897, 1), (key2893, 1), (key2904, -1), (key2893, -1)]

def rawRow180 : Integer.Sparse Key := [(key2676, -2), (key2671, 1), (key2671, 1), (key2753, 2), (key2706, -1), (key2706, -1), (key2758, -1), (key2758, -1), (key2732, 1), (key2732, 1), (key2621, 2), (key2616, -1), (key2616, -1), (key2831, -2), (key2805, 1), (key2805, 1), (key2960, 1), (key2960, 1), (key2950, -1), (key2950, -1), (key2641, -2), (key2628, 1), (key2628, 1), (key2728, 2), (key2702, -1), (key2702, -1), (key2983, -1), (key2983, -1), (key2976, 1), (key2976, 1), (key2653, 1), (key2653, 1), (key2648, -1), (key2648, -1), (key2747, -1), (key2747, -1), (key2737, 1), (key2737, 1), (key2904, 1), (key2904, 1), (key2897, -1), (key2897, -1)]

def rawRow181 : Integer.Sparse Key := [(key2706, -2), (key2726, 1), (key2732, 1), (key2671, 2), (key2726, -1), (key2758, -1), (key2671, -1), (key2676, -1), (key2706, 1), (key2753, 1), (key2809, 2), (key2829, -1), (key2835, -1), (key2612, -2), (key2948, 1), (key2960, 1), (key2612, 1), (key2618, 1), (key2805, -1), (key2831, -1), (key2702, -2), (key2972, 1), (key2976, 1), (key2628, 2), (key2972, -1), (key2983, -1), (key2628, -1), (key2641, -1), (key2702, 1), (key2728, 1), (key2735, 1), (key2737, 1), (key2893, -1), (key2897, -1), (key2646, -1), (key2648, -1), (key2893, 1), (key2904, 1), (key2646, 1), (key2653, 1), (key2735, -1), (key2747, -1)]

def rawRow182 : Integer.Sparse Key := [(key2706, -2), (key2732, 1), (key2726, 1), (key2671, 2), (key2758, -1), (key2726, -1), (key2676, -1), (key2671, -1), (key2753, 1), (key2706, 1), (key2809, 2), (key2835, -1), (key2829, -1), (key2616, -2), (key2960, 1), (key2948, 1), (key2618, 1), (key2612, 1), (key2831, -1), (key2805, -1), (key2702, -2), (key2976, 1), (key2972, 1), (key2628, 2), (key2983, -1), (key2972, -1), (key2641, -1), (key2628, -1), (key2728, 1), (key2702, 1), (key2737, 1), (key2735, 1), (key2897, -1), (key2893, -1), (key2648, -1), (key2646, -1), (key2904, 1), (key2893, 1), (key2653, 1), (key2646, 1), (key2747, -1), (key2735, -1)]

def rawRow183 : Integer.Sparse Key := [(key2732, -2), (key2706, 1), (key2726, 1), (key2758, 2), (key2671, -1), (key2726, -1), (key2753, -1), (key2758, -1), (key2676, 1), (key2732, 1), (key2835, 2), (key2809, -1), (key2829, -1), (key3017, -2), (key2616, 1), (key2829, 1), (key2831, 1), (key2960, 1), (key2618, -1), (key2950, -1), (key2976, -2), (key2702, 1), (key2972, 1), (key2983, 2), (key2628, -1), (key2972, -1), (key2728, -1), (key2983, -1), (key2641, 1), (key2976, 1), (key2897, 1), (key2998, 1), (key2737, -1), (key2997, -1), (key2904, -1), (key3000, -1), (key2648, 1), (key2997, 1), (key2747, 1), (key3000, 1), (key2653, -1), (key2998, -1)]

def rawRow184 : Integer.Sparse Key := [(key2732, -2), (key2726, 1), (key2706, 1), (key2758, 2), (key2726, -1), (key2671, -1), (key2758, -1), (key2753, -1), (key2732, 1), (key2676, 1), (key2835, 2), (key2829, -1), (key2809, -1), (key3017, -2), (key2829, 1), (key2616, 1), (key2960, 1), (key2831, 1), (key2950, -1), (key2618, -1), (key2976, -2), (key2972, 1), (key2702, 1), (key2983, 2), (key2972, -1), (key2628, -1), (key2983, -1), (key2728, -1), (key2976, 1), (key2641, 1), (key2998, 1), (key2897, 1), (key2997, -1), (key2737, -1), (key3000, -1), (key2904, -1), (key2997, 1), (key2648, 1), (key3000, 1), (key2747, 1), (key2998, -1), (key2653, -1)]

def rawRow185 : Integer.Sparse Key := [(key2753, -2), (key2758, 1), (key2758, 1), (key2676, 2), (key2732, -1), (key2732, -1), (key2671, -1), (key2671, -1), (key2706, 1), (key2706, 1), (key3012, 2), (key3017, -1), (key3017, -1), (key2621, -2), (key2835, 1), (key2835, 1), (key2616, 1), (key2616, 1), (key2809, -1), (key2809, -1), (key2728, -2), (key2983, 1), (key2983, 1), (key2641, 2), (key2976, -1), (key2976, -1), (key2628, -1), (key2628, -1), (key2702, 1), (key2702, 1), (key2747, 1), (key2747, 1), (key2904, -1), (key2904, -1), (key2653, -1), (key2653, -1), (key2897, 1), (key2897, 1), (key2648, 1), (key2648, 1), (key2737, -1), (key2737, -1)]

def rawRow186 : Integer.Sparse Key := [(key2758, -2), (key2753, 1), (key2758, 1), (key2732, 2), (key2676, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2671, 1), (key2726, 1), (key3017, 2), (key3012, -1), (key3017, -1), (key2835, -2), (key2621, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2616, -1), (key2829, -1), (key2983, -2), (key2728, 1), (key2983, 1), (key2976, 2), (key2641, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2628, 1), (key2972, 1), (key2904, 1), (key3000, 1), (key2747, -1), (key3000, -1), (key2897, -1), (key2998, -1), (key2653, 1), (key2998, 1), (key2737, 1), (key2997, 1), (key2648, -1), (key2997, -1)]

def rawRow187 : Integer.Sparse Key := [(key2758, -2), (key2758, 1), (key2753, 1), (key2732, 2), (key2732, -1), (key2676, -1), (key2726, -1), (key2706, -1), (key2726, 1), (key2671, 1), (key3017, 2), (key3017, -1), (key3012, -1), (key2835, -2), (key2835, 1), (key2621, 1), (key2829, 1), (key2809, 1), (key2829, -1), (key2616, -1), (key2983, -2), (key2983, 1), (key2728, 1), (key2976, 2), (key2976, -1), (key2641, -1), (key2972, -1), (key2702, -1), (key2972, 1), (key2628, 1), (key3000, 1), (key2904, 1), (key3000, -1), (key2747, -1), (key2998, -1), (key2897, -1), (key2998, 1), (key2653, 1), (key2997, 1), (key2737, 1), (key2997, -1), (key2648, -1)]

def rawRow188 : Integer.Sparse Key := [(key2786, -2), (key2794, 1), (key2798, 1), (key2809, 2), (key2860, -1), (key2920, -1), (key2829, -1), (key2835, -1), (key2870, 1), (key2923, 1), (key2632, 2), (key2640, -1), (key2644, -1), (key2706, -2), (key2860, 1), (key3023, 1), (key2726, 1), (key2732, 1), (key2870, -1), (key3026, -1), (key2612, -2), (key2646, 1), (key2653, 1), (key2667, 2), (key2735, -1), (key2747, -1), (key2936, -1), (key2943, -1), (key2948, 1), (key2960, 1), (key2612, 1), (key2618, 1), (key2628, -1), (key2641, -1), (key2667, -1), (key2673, -1), (key2702, 1), (key2728, 1), (key2782, 1), (key2795, 1), (key2805, -1), (key2831, -1)]

def rawRow189 : Integer.Sparse Key := [(key2786, -2), (key2798, 1), (key2794, 1), (key2809, 2), (key2920, -1), (key2860, -1), (key2835, -1), (key2829, -1), (key2923, 1), (key2870, 1), (key2632, 2), (key2644, -1), (key2640, -1), (key2706, -2), (key3023, 1), (key2860, 1), (key2732, 1), (key2726, 1), (key3026, -1), (key2870, -1), (key2616, -2), (key2653, 1), (key2646, 1), (key2667, 2), (key2747, -1), (key2735, -1), (key2943, -1), (key2936, -1), (key2960, 1), (key2948, 1), (key2618, 1), (key2612, 1), (key2641, -1), (key2628, -1), (key2673, -1), (key2667, -1), (key2728, 1), (key2702, 1), (key2795, 1), (key2782, 1), (key2831, -1), (key2805, -1)]

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

def rawRow1753 : Integer.Sparse Key := [(key2952, -2), (key2999, -2), (key2978, -2), (key2964, 1), (key2962, 1), (key3001, 1), (key2985, 1), (key3004, 1), (key2994, 1), (key2620, 2), (key2656, 2), (key2643, 2), (key2751, -1), (key2730, -1), (key2964, -1), (key2833, -1), (key2994, -1), (key2915, -1), (key2620, -1), (key2617, -1), (key2643, -1), (key2633, -1), (key2655, -1), (key2650, -1), (key2797, 1), (key2787, 1), (key2833, 1), (key2810, 1), (key2906, 1), (key2899, 1)]

def rawRow1754 : Integer.Sparse Key := [(key2978, -2), (key2952, -2), (key2999, -2), (key2985, 1), (key2994, 1), (key2962, 1), (key3004, 1), (key2964, 1), (key3001, 1), (key2643, 2), (key2620, 2), (key2656, 2), (key2833, -1), (key2915, -1), (key2730, -1), (key2994, -1), (key2751, -1), (key2964, -1), (key2633, -1), (key2643, -1), (key2617, -1), (key2655, -1), (key2620, -1), (key2643, -1), (key2810, 1), (key2899, 1), (key2787, 1), (key2906, 1), (key2797, 1), (key2833, 1)]

def rawRow1755 : Integer.Sparse Key := [(key2978, -2), (key2999, -2), (key2952, -2), (key2994, 1), (key2985, 1), (key3004, 1), (key2962, 1), (key3001, 1), (key2964, 1), (key2643, 2), (key2656, 2), (key2620, 2), (key2915, -1), (key2833, -1), (key2994, -1), (key2730, -1), (key2964, -1), (key2751, -1), (key2643, -1), (key2633, -1), (key2655, -1), (key2617, -1), (key2643, -1), (key2620, -1), (key2899, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2833, 1), (key2797, 1)]

def rawRow1756 : Integer.Sparse Key := [(key2999, -2), (key2952, -2), (key2978, -2), (key3001, 1), (key3004, 1), (key2964, 1), (key2994, 1), (key2962, 1), (key2985, 1), (key2656, 2), (key2620, 2), (key2643, 2), (key2964, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2730, -1), (key2833, -1), (key2650, -1), (key2655, -1), (key2620, -1), (key2643, -1), (key2617, -1), (key2633, -1), (key2833, 1), (key2906, 1), (key2797, 1), (key2899, 1), (key2787, 1), (key2810, 1)]

def rawRow1757 : Integer.Sparse Key := [(key2999, -2), (key2978, -2), (key2952, -2), (key3004, 1), (key3001, 1), (key2994, 1), (key2964, 1), (key2985, 1), (key2962, 1), (key2656, 2), (key2643, 2), (key2620, 2), (key2994, -1), (key2964, -1), (key2915, -1), (key2751, -1), (key2833, -1), (key2730, -1), (key2655, -1), (key2650, -1), (key2643, -1), (key2620, -1), (key2633, -1), (key2617, -1), (key2906, 1), (key2833, 1), (key2899, 1), (key2797, 1), (key2810, 1), (key2787, 1)]

def rawRow1758 : Integer.Sparse Key := [(key2945, -2), (key2962, -2), (key3004, -2), (key2940, 1), (key2946, 1), (key2952, 1), (key2999, 1), (key2964, 1), (key3001, 1), (key2797, 2), (key2833, 2), (key2915, 2), (key2620, -1), (key2656, -1), (key2675, -1), (key2946, -1), (key2751, -1), (key2964, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2899, -1), (key2833, -1), (key2906, -1), (key2617, 1), (key2655, 1), (key2672, 1), (key2749, 1), (key2945, 1), (key2962, 1)]

def rawRow1759 : Integer.Sparse Key := [(key2945, -2), (key3004, -2), (key2962, -2), (key2946, 1), (key2940, 1), (key2999, 1), (key2952, 1), (key3001, 1), (key2964, 1), (key2797, 2), (key2915, 2), (key2833, 2), (key2656, -1), (key2620, -1), (key2946, -1), (key2675, -1), (key2964, -1), (key2751, -1), (key2797, -1), (key2787, -1), (key2899, -1), (key2810, -1), (key2906, -1), (key2833, -1), (key2655, 1), (key2617, 1), (key2749, 1), (key2672, 1), (key2962, 1), (key2945, 1)]

def rawRow1760 : Integer.Sparse Key := [(key2962, -2), (key2945, -2), (key3004, -2), (key2952, 1), (key2964, 1), (key2940, 1), (key3001, 1), (key2946, 1), (key2999, 1), (key2833, 2), (key2797, 2), (key2915, 2), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, -1), (key2946, -1), (key2810, -1), (key2833, -1), (key2787, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2672, 1), (key2749, 1), (key2617, 1), (key2962, 1), (key2655, 1), (key2749, 1)]

def rawRow1761 : Integer.Sparse Key := [(key2962, -2), (key3004, -2), (key2945, -2), (key2964, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2999, 1), (key2946, 1), (key2833, 2), (key2915, 2), (key2797, 2), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, -1), (key2656, -1), (key2833, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2899, -1), (key2797, -1), (key2749, 1), (key2672, 1), (key2962, 1), (key2617, 1), (key2749, 1), (key2655, 1)]

def rawRow1762 : Integer.Sparse Key := [(key3004, -2), (key2945, -2), (key2962, -2), (key2999, 1), (key3001, 1), (key2946, 1), (key2964, 1), (key2940, 1), (key2952, 1), (key2915, 2), (key2797, 2), (key2833, 2), (key2946, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2620, -1), (key2675, -1), (key2899, -1), (key2906, -1), (key2797, -1), (key2833, -1), (key2787, -1), (key2810, -1), (key2945, 1), (key2962, 1), (key2655, 1), (key2749, 1), (key2617, 1), (key2672, 1)]

def rawRow1763 : Integer.Sparse Key := [(key3004, -2), (key2962, -2), (key2945, -2), (key3001, 1), (key2999, 1), (key2964, 1), (key2946, 1), (key2952, 1), (key2940, 1), (key2915, 2), (key2833, 2), (key2797, 2), (key2964, -1), (key2946, -1), (key2751, -1), (key2656, -1), (key2675, -1), (key2620, -1), (key2906, -1), (key2899, -1), (key2833, -1), (key2797, -1), (key2810, -1), (key2787, -1), (key2962, 1), (key2945, 1), (key2749, 1), (key2655, 1), (key2672, 1), (key2617, 1)]

def rawRow1764 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2439, -2), (key2402, 1), (key2408, 1), (key2402, 1), (key2439, 1), (key2408, 1), (key2439, 1), (key2468, 2), (key2468, 2), (key2505, 2), (key2468, -1), (key2481, -1), (key2468, -1), (key2505, -1), (key2481, -1), (key2505, -1), (key2535, -1), (key2537, -1), (key2535, -1), (key2553, -1), (key2537, -1), (key2553, -1), (key2535, 1), (key2542, 1), (key2535, 1), (key2553, 1), (key2542, 1), (key2553, 1)]

def rawRow1765 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2402, -2), (key2408, 1), (key2402, 1), (key2439, 1), (key2402, 1), (key2439, 1), (key2408, 1), (key2468, 2), (key2505, 2), (key2468, 2), (key2481, -1), (key2468, -1), (key2505, -1), (key2468, -1), (key2505, -1), (key2481, -1), (key2537, -1), (key2535, -1), (key2553, -1), (key2535, -1), (key2553, -1), (key2537, -1), (key2542, 1), (key2535, 1), (key2553, 1), (key2535, 1), (key2553, 1), (key2542, 1)]

def rawRow1766 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2402, -2), (key2439, 1), (key2439, 1), (key2408, 1), (key2408, 1), (key2402, 1), (key2402, 1), (key2505, 2), (key2468, 2), (key2468, 2), (key2505, -1), (key2505, -1), (key2481, -1), (key2481, -1), (key2468, -1), (key2468, -1), (key2553, -1), (key2553, -1), (key2537, -1), (key2537, -1), (key2535, -1), (key2535, -1), (key2553, 1), (key2553, 1), (key2542, 1), (key2542, 1), (key2535, 1), (key2535, 1)]

def rawRow1767 : Integer.Sparse Key := [(key2408, -2), (key2408, -2), (key2408, -2), (key2402, 1), (key2402, 1), (key2402, 1), (key2402, 1), (key2402, 1), (key2402, 1), (key2481, 2), (key2481, 2), (key2481, 2), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1)]

def rawRow1768 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key3020, -2), (key2878, 1), (key2884, 1), (key2878, 1), (key3029, 1), (key2884, 1), (key3029, 1), (key2402, 2), (key2402, 2), (key2439, 2), (key2535, -1), (key2542, -1), (key2535, -1), (key2553, -1), (key2542, -1), (key2553, -1), (key2402, -1), (key2408, -1), (key2402, -1), (key2439, -1), (key2408, -1), (key2439, -1), (key2468, 1), (key2481, 1), (key2468, 1), (key2505, 1), (key2481, 1), (key2505, 1)]

def rawRow1769 : Integer.Sparse Key := [(key2847, -2), (key3020, -2), (key2847, -2), (key2884, 1), (key2878, 1), (key3029, 1), (key2878, 1), (key3029, 1), (key2884, 1), (key2402, 2), (key2439, 2), (key2402, 2), (key2542, -1), (key2535, -1), (key2553, -1), (key2535, -1), (key2553, -1), (key2542, -1), (key2408, -1), (key2402, -1), (key2439, -1), (key2402, -1), (key2439, -1), (key2408, -1), (key2481, 1), (key2468, 1), (key2505, 1), (key2468, 1), (key2505, 1), (key2481, 1)]

def rawRow1770 : Integer.Sparse Key := [(key3020, -2), (key2847, -2), (key2847, -2), (key3029, 1), (key3029, 1), (key2884, 1), (key2884, 1), (key2878, 1), (key2878, 1), (key2439, 2), (key2402, 2), (key2402, 2), (key2553, -1), (key2553, -1), (key2542, -1), (key2542, -1), (key2535, -1), (key2535, -1), (key2439, -1), (key2439, -1), (key2408, -1), (key2408, -1), (key2402, -1), (key2402, -1), (key2505, 1), (key2505, 1), (key2481, 1), (key2481, 1), (key2468, 1), (key2468, 1)]

def rawRow1771 : Integer.Sparse Key := [(key2596, -2), (key2884, -2), (key2884, -2), (key2591, 1), (key2591, 1), (key2847, 1), (key2847, 1), (key2878, 1), (key2878, 1), (key2605, 2), (key2926, 2), (key2926, 2), (key2591, -1), (key2591, -1), (key2770, -1), (key2770, -1), (key2878, -1), (key2878, -1), (key2391, -1), (key2391, -1), (key2481, -1), (key2481, -1), (key2542, -1), (key2542, -1), (key2380, 1), (key2380, 1), (key2408, 1), (key2408, 1), (key2537, 1), (key2537, 1)]

def rawRow1772 : Integer.Sparse Key := [(key2884, -2), (key2596, -2), (key2884, -2), (key2847, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2847, 1), (key2926, 2), (key2605, 2), (key2926, 2), (key2770, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2481, -1), (key2542, -1), (key2391, -1), (key2542, -1), (key2391, -1), (key2481, -1), (key2408, 1), (key2537, 1), (key2380, 1), (key2537, 1), (key2380, 1), (key2408, 1)]

def rawRow1773 : Integer.Sparse Key := [(key2884, -2), (key2884, -2), (key2596, -2), (key2878, 1), (key2847, 1), (key2878, 1), (key2591, 1), (key2847, 1), (key2591, 1), (key2926, 2), (key2926, 2), (key2605, 2), (key2878, -1), (key2770, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2591, -1), (key2542, -1), (key2481, -1), (key2542, -1), (key2391, -1), (key2481, -1), (key2391, -1), (key2537, 1), (key2408, 1), (key2537, 1), (key2380, 1), (key2408, 1), (key2380, 1)]

def rawRow1774 : Integer.Sparse Key := [(key2917, -2), (key2917, -2), (key2917, -2), (key2926, 1), (key2926, 1), (key2926, 1), (key2926, 1), (key2926, 1), (key2926, 1), (key2775, 2), (key2775, 2), (key2775, 2), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1)]

def rawRow1775 : Integer.Sparse Key := [(key2605, -2), (key2926, -2), (key2926, -2), (key2605, 1), (key2605, 1), (key2917, 1), (key2917, 1), (key2926, 1), (key2926, 1), (key2596, 2), (key2884, 2), (key2884, 2), (key2596, -1), (key2596, -1), (key2775, -1), (key2775, -1), (key2884, -1), (key2884, -1), (key2591, -1), (key2591, -1), (key2847, -1), (key2847, -1), (key2878, -1), (key2878, -1), (key2591, 1), (key2591, 1), (key2770, 1), (key2770, 1), (key2878, 1), (key2878, 1)]

def rawRow1776 : Integer.Sparse Key := [(key2926, -2), (key2605, -2), (key2926, -2), (key2917, 1), (key2926, 1), (key2605, 1), (key2926, 1), (key2605, 1), (key2917, 1), (key2884, 2), (key2596, 2), (key2884, 2), (key2775, -1), (key2884, -1), (key2596, -1), (key2884, -1), (key2596, -1), (key2775, -1), (key2847, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2847, -1), (key2770, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2770, 1)]

def rawRow1777 : Integer.Sparse Key := [(key2926, -2), (key2926, -2), (key2605, -2), (key2926, 1), (key2917, 1), (key2926, 1), (key2605, 1), (key2917, 1), (key2605, 1), (key2884, 2), (key2884, 2), (key2596, 2), (key2884, -1), (key2775, -1), (key2884, -1), (key2596, -1), (key2775, -1), (key2596, -1), (key2878, -1), (key2847, -1), (key2878, -1), (key2591, -1), (key2847, -1), (key2591, -1), (key2878, 1), (key2770, 1), (key2878, 1), (key2591, 1), (key2770, 1), (key2591, 1)]

def rawRow1778 : Integer.Sparse Key := [(key1250, -6), (key1250, 2), (key1250, 2), (key1269, 2), (key1525, 6), (key1525, -2), (key1525, -2), (key1892, -2), (key1603, -2), (key1603, -2), (key1677, -2), (key1603, 2), (key1603, 2), (key1914, 2)]

def rawRow1779 : Integer.Sparse Key := [(key1250, -6), (key1250, 2), (key1269, 2), (key1250, 2), (key1525, 6), (key1525, -2), (key1892, -2), (key1525, -2), (key1603, -2), (key1677, -2), (key1603, -2), (key1603, 2), (key1914, 2), (key1603, 2)]

def rawRow1780 : Integer.Sparse Key := [(key1250, -6), (key1269, 2), (key1250, 2), (key1250, 2), (key1525, 6), (key1892, -2), (key1525, -2), (key1525, -2), (key1677, -2), (key1603, -2), (key1603, -2), (key1914, 2), (key1603, 2), (key1603, 2)]

def rawRow1781 : Integer.Sparse Key := [(key1269, -6), (key1250, 2), (key1250, 2), (key1250, 2), (key1892, 6), (key1525, -2), (key1525, -2), (key1525, -2), (key1914, -2), (key1914, -2), (key1914, -2), (key1677, 2), (key1677, 2), (key1677, 2)]

def rawRow1782 : Integer.Sparse Key := [(key1525, -6), (key1603, 2), (key1603, 2), (key1677, 2), (key1250, 6), (key1603, -2), (key1603, -2), (key1914, -2), (key1250, -2), (key1250, -2), (key1269, -2), (key1525, 2), (key1525, 2), (key1892, 2)]

def rawRow1783 : Integer.Sparse Key := [(key1525, -6), (key1603, 2), (key1677, 2), (key1603, 2), (key1250, 6), (key1603, -2), (key1914, -2), (key1603, -2), (key1250, -2), (key1269, -2), (key1250, -2), (key1525, 2), (key1892, 2), (key1525, 2)]

def rawRow1784 : Integer.Sparse Key := [(key1525, -6), (key1677, 2), (key1603, 2), (key1603, 2), (key1250, 6), (key1914, -2), (key1603, -2), (key1603, -2), (key1269, -2), (key1250, -2), (key1250, -2), (key1892, 2), (key1525, 2), (key1525, 2)]

def rawRow1785 : Integer.Sparse Key := [(key1677, -6), (key1525, 2), (key1603, 2), (key1603, 2), (key1914, 6), (key1250, -2), (key1603, -2), (key1603, -2), (key1892, -2), (key1914, -2), (key1914, -2), (key1269, 2), (key1677, 2), (key1677, 2)]

def rawRow1786 : Integer.Sparse Key := [(key1677, -6), (key1603, 2), (key1525, 2), (key1603, 2), (key1914, 6), (key1603, -2), (key1250, -2), (key1603, -2), (key1914, -2), (key1892, -2), (key1914, -2), (key1677, 2), (key1269, 2), (key1677, 2)]

def rawRow1787 : Integer.Sparse Key := [(key1677, -6), (key1603, 2), (key1603, 2), (key1525, 2), (key1914, 6), (key1603, -2), (key1603, -2), (key1250, -2), (key1914, -2), (key1914, -2), (key1892, -2), (key1677, 2), (key1677, 2), (key1269, 2)]

def rawRow1788 : Integer.Sparse Key := [(key1892, -6), (key1914, 2), (key1914, 2), (key1914, 2), (key1269, 6), (key1677, -2), (key1677, -2), (key1677, -2), (key1250, -2), (key1250, -2), (key1250, -2), (key1525, 2), (key1525, 2), (key1525, 2)]

def rawRow1789 : Integer.Sparse Key := [(key1914, -6), (key1892, 2), (key1914, 2), (key1914, 2), (key1677, 6), (key1269, -2), (key1677, -2), (key1677, -2), (key1525, -2), (key1603, -2), (key1603, -2), (key1250, 2), (key1603, 2), (key1603, 2)]

def rawRow1790 : Integer.Sparse Key := [(key1914, -6), (key1914, 2), (key1892, 2), (key1914, 2), (key1677, 6), (key1677, -2), (key1269, -2), (key1677, -2), (key1603, -2), (key1525, -2), (key1603, -2), (key1603, 2), (key1250, 2), (key1603, 2)]

def rawRow1791 : Integer.Sparse Key := [(key1914, -6), (key1914, 2), (key1914, 2), (key1892, 2), (key1677, 6), (key1677, -2), (key1677, -2), (key1269, -2), (key1603, -2), (key1603, -2), (key1525, -2), (key1603, 2), (key1603, 2), (key1250, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1792 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2376, -2), (key2370, 1), (key2376, 1), (key2370, 1), (key2388, 1), (key2376, 1), (key2388, 1), (key2398, 2), (key2404, 2), (key2404, 2), (key2398, -1), (key2404, -1), (key2398, -1), (key2435, -1), (key2404, -1), (key2435, -1), (key2464, -1), (key2470, -1), (key2464, -1), (key2478, -1), (key2470, -1), (key2478, -1), (key2464, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2501, 1)]

def rawRow1793 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2376, -2), (key2376, 1), (key2370, 1), (key2388, 1), (key2370, 1), (key2388, 1), (key2376, 1), (key2404, 2), (key2398, 2), (key2404, 2), (key2404, -1), (key2398, -1), (key2435, -1), (key2398, -1), (key2435, -1), (key2404, -1), (key2470, -1), (key2464, -1), (key2478, -1), (key2464, -1), (key2478, -1), (key2470, -1), (key2470, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2470, 1)]

def rawRow1794 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2370, -2), (key2388, 1), (key2388, 1), (key2376, 1), (key2376, 1), (key2370, 1), (key2370, 1), (key2404, 2), (key2404, 2), (key2398, 2), (key2435, -1), (key2435, -1), (key2404, -1), (key2404, -1), (key2398, -1), (key2398, -1), (key2478, -1), (key2478, -1), (key2470, -1), (key2470, -1), (key2464, -1), (key2464, -1), (key2501, 1), (key2501, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1)]

def rawRow1795 : Integer.Sparse Key := [(key2388, -2), (key2388, -2), (key2388, -2), (key2376, 1), (key2376, 1), (key2376, 1), (key2376, 1), (key2376, 1), (key2376, 1), (key2435, 2), (key2435, 2), (key2435, 2), (key2404, -1), (key2404, -1), (key2404, -1), (key2404, -1), (key2404, -1), (key2404, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1)]

def rawRow1796 : Integer.Sparse Key := [(key2762, -2), (key2768, -2), (key2768, -2), (key2839, 1), (key2845, 1), (key2839, 1), (key2916, 1), (key2845, 1), (key2916, 1), (key2583, 2), (key2589, 2), (key2589, 2), (key2839, -1), (key2845, -1), (key2839, -1), (key3019, -1), (key2845, -1), (key3019, -1), (key2370, -1), (key2376, -1), (key2370, -1), (key2388, -1), (key2376, -1), (key2388, -1), (key2398, 1), (key2404, 1), (key2398, 1), (key2435, 1), (key2404, 1), (key2435, 1)]

def rawRow1797 : Integer.Sparse Key := [(key2768, -2), (key2762, -2), (key2768, -2), (key2845, 1), (key2839, 1), (key2916, 1), (key2839, 1), (key2916, 1), (key2845, 1), (key2589, 2), (key2583, 2), (key2589, 2), (key2845, -1), (key2839, -1), (key3019, -1), (key2839, -1), (key3019, -1), (key2845, -1), (key2376, -1), (key2370, -1), (key2388, -1), (key2370, -1), (key2388, -1), (key2376, -1), (key2404, 1), (key2398, 1), (key2435, 1), (key2398, 1), (key2435, 1), (key2404, 1)]

def rawRow1798 : Integer.Sparse Key := [(key2768, -2), (key2768, -2), (key2762, -2), (key2916, 1), (key2916, 1), (key2845, 1), (key2845, 1), (key2839, 1), (key2839, 1), (key2589, 2), (key2589, 2), (key2583, 2), (key3019, -1), (key3019, -1), (key2845, -1), (key2845, -1), (key2839, -1), (key2839, -1), (key2388, -1), (key2388, -1), (key2376, -1), (key2376, -1), (key2370, -1), (key2370, -1), (key2435, 1), (key2435, 1), (key2404, 1), (key2404, 1), (key2398, 1), (key2398, 1)]

def rawRow1799 : Integer.Sparse Key := [(key2916, -2), (key2916, -2), (key2925, -2), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key3019, 2), (key3019, 2), (key3028, 2), (key2589, -1), (key2589, -1), (key2845, -1), (key2845, -1), (key2876, -1), (key2876, -1), (key3005, -1), (key3005, -1), (key3019, -1), (key3019, -1), (key3028, -1), (key3028, -1), (key2604, 1), (key2604, 1), (key2916, 1), (key2916, 1), (key2925, 1), (key2925, 1)]

def rawRow1800 : Integer.Sparse Key := [(key2916, -2), (key2925, -2), (key2916, -2), (key2845, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key3019, 2), (key3028, 2), (key3019, 2), (key2845, -1), (key2876, -1), (key2589, -1), (key2876, -1), (key2589, -1), (key2845, -1), (key3019, -1), (key3028, -1), (key3005, -1), (key3028, -1), (key3005, -1), (key3019, -1), (key2916, 1), (key2925, 1), (key2604, 1), (key2925, 1), (key2604, 1), (key2916, 1)]

def rawRow1801 : Integer.Sparse Key := [(key2925, -2), (key2916, -2), (key2916, -2), (key2876, 1), (key2845, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2768, 1), (key3028, 2), (key3019, 2), (key3019, 2), (key2876, -1), (key2845, -1), (key2876, -1), (key2589, -1), (key2845, -1), (key2589, -1), (key3028, -1), (key3019, -1), (key3028, -1), (key3005, -1), (key3019, -1), (key3005, -1), (key2925, 1), (key2916, 1), (key2925, 1), (key2604, 1), (key2916, 1), (key2604, 1)]

def rawRow1802 : Integer.Sparse Key := [(key3005, -2), (key3005, -2), (key3005, -2), (key3019, 1), (key3019, 1), (key3019, 1), (key3019, 1), (key3019, 1), (key3019, 1), (key2604, 2), (key2604, 2), (key2604, 2), (key2916, -1), (key2916, -1), (key2916, -1), (key2916, -1), (key2916, -1), (key2916, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1)]

def rawRow1803 : Integer.Sparse Key := [(key3019, -2), (key3019, -2), (key3028, -2), (key3005, 1), (key3005, 1), (key3019, 1), (key3019, 1), (key3028, 1), (key3028, 1), (key2916, 2), (key2916, 2), (key2925, 2), (key2604, -1), (key2604, -1), (key2916, -1), (key2916, -1), (key2925, -1), (key2925, -1), (key2768, -1), (key2768, -1), (key2845, -1), (key2845, -1), (key2876, -1), (key2876, -1), (key2589, 1), (key2589, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1)]

def rawRow1804 : Integer.Sparse Key := [(key3019, -2), (key3028, -2), (key3019, -2), (key3019, 1), (key3028, 1), (key3005, 1), (key3028, 1), (key3005, 1), (key3019, 1), (key2916, 2), (key2925, 2), (key2916, 2), (key2916, -1), (key2925, -1), (key2604, -1), (key2925, -1), (key2604, -1), (key2916, -1), (key2845, -1), (key2876, -1), (key2768, -1), (key2876, -1), (key2768, -1), (key2845, -1), (key2845, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2845, 1)]

def rawRow1805 : Integer.Sparse Key := [(key3028, -2), (key3019, -2), (key3019, -2), (key3028, 1), (key3019, 1), (key3028, 1), (key3005, 1), (key3019, 1), (key3005, 1), (key2925, 2), (key2916, 2), (key2916, 2), (key2925, -1), (key2916, -1), (key2925, -1), (key2604, -1), (key2916, -1), (key2604, -1), (key2876, -1), (key2845, -1), (key2876, -1), (key2768, -1), (key2845, -1), (key2768, -1), (key2876, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2589, 1)]

def rawRow1806 : Integer.Sparse Key := [(key971, -2), (key979, -2), (key979, -2), (key979, 6), (key1085, 2), (key1093, 2), (key1093, 2), (key1093, -2), (key1093, -2), (key1228, -2), (key1164, -6), (key1164, 2), (key1164, 2), (key1245, 2)]

def rawRow1807 : Integer.Sparse Key := [(key979, -2), (key971, -2), (key979, -2), (key979, 6), (key1093, 2), (key1085, 2), (key1093, 2), (key1093, -2), (key1228, -2), (key1093, -2), (key1164, -6), (key1164, 2), (key1245, 2), (key1164, 2)]

def rawRow1808 : Integer.Sparse Key := [(key979, -2), (key979, -2), (key971, -2), (key979, 6), (key1093, 2), (key1093, 2), (key1085, 2), (key1228, -2), (key1093, -2), (key1093, -2), (key1164, -6), (key1245, 2), (key1164, 2), (key1164, 2)]

def rawRow1809 : Integer.Sparse Key := [(key979, -2), (key979, -2), (key979, -2), (key971, 6), (key1228, 2), (key1228, 2), (key1228, 2), (key1085, -2), (key1085, -2), (key1085, -2), (key1245, -6), (key1164, 2), (key1164, 2), (key1164, 2)]

def rawRow1810 : Integer.Sparse Key := [(key1085, -2), (key1093, -2), (key1093, -2), (key1164, 6), (key971, 2), (key979, 2), (key979, 2), (key1164, -2), (key1164, -2), (key1245, -2), (key979, -6), (key1093, 2), (key1093, 2), (key1228, 2)]

def rawRow1811 : Integer.Sparse Key := [(key1093, -2), (key1085, -2), (key1093, -2), (key1164, 6), (key979, 2), (key971, 2), (key979, 2), (key1164, -2), (key1245, -2), (key1164, -2), (key979, -6), (key1093, 2), (key1228, 2), (key1093, 2)]

def rawRow1812 : Integer.Sparse Key := [(key1093, -2), (key1093, -2), (key1085, -2), (key1164, 6), (key979, 2), (key979, 2), (key971, 2), (key1245, -2), (key1164, -2), (key1164, -2), (key979, -6), (key1228, 2), (key1093, 2), (key1093, 2)]

def rawRow1813 : Integer.Sparse Key := [(key1093, -2), (key1093, -2), (key1164, -2), (key1085, 6), (key1228, 2), (key1228, 2), (key1245, 2), (key971, -2), (key1085, -2), (key1085, -2), (key1228, -6), (key979, 2), (key1093, 2), (key1093, 2)]

def rawRow1814 : Integer.Sparse Key := [(key1093, -2), (key1164, -2), (key1093, -2), (key1085, 6), (key1228, 2), (key1245, 2), (key1228, 2), (key1085, -2), (key971, -2), (key1085, -2), (key1228, -6), (key1093, 2), (key979, 2), (key1093, 2)]

def rawRow1815 : Integer.Sparse Key := [(key1164, -2), (key1093, -2), (key1093, -2), (key1085, 6), (key1245, 2), (key1228, 2), (key1228, 2), (key1085, -2), (key1085, -2), (key971, -2), (key1228, -6), (key1093, 2), (key1093, 2), (key979, 2)]

def rawRow1816 : Integer.Sparse Key := [(key1228, -2), (key1228, -2), (key1228, -2), (key1245, 6), (key979, 2), (key979, 2), (key979, 2), (key1164, -2), (key1164, -2), (key1164, -2), (key971, -6), (key1085, 2), (key1085, 2), (key1085, 2)]

def rawRow1817 : Integer.Sparse Key := [(key1228, -2), (key1228, -2), (key1245, -2), (key1228, 6), (key1093, 2), (key1093, 2), (key1164, 2), (key979, -2), (key1093, -2), (key1093, -2), (key1085, -6), (key971, 2), (key1085, 2), (key1085, 2)]

def rawRow1818 : Integer.Sparse Key := [(key1228, -2), (key1245, -2), (key1228, -2), (key1228, 6), (key1093, 2), (key1164, 2), (key1093, 2), (key1093, -2), (key979, -2), (key1093, -2), (key1085, -6), (key1085, 2), (key971, 2), (key1085, 2)]

def rawRow1819 : Integer.Sparse Key := [(key1245, -2), (key1228, -2), (key1228, -2), (key1228, 6), (key1164, 2), (key1093, 2), (key1093, 2), (key1093, -2), (key1093, -2), (key979, -2), (key1085, -6), (key1085, 2), (key1085, 2), (key971, 2)]

def rawRow1820 : Integer.Sparse Key := [(key2372, -6), (key2372, 2), (key2372, 2), (key2385, 2), (key2400, 6), (key2400, -2), (key2400, -2), (key2432, -2), (key2466, -2), (key2466, -2), (key2475, -2), (key2466, 2), (key2466, 2), (key2498, 2)]

def rawRow1821 : Integer.Sparse Key := [(key2372, -6), (key2372, 2), (key2385, 2), (key2372, 2), (key2400, 6), (key2400, -2), (key2432, -2), (key2400, -2), (key2466, -2), (key2475, -2), (key2466, -2), (key2466, 2), (key2498, 2), (key2466, 2)]

def rawRow1822 : Integer.Sparse Key := [(key2372, -6), (key2385, 2), (key2372, 2), (key2372, 2), (key2400, 6), (key2432, -2), (key2400, -2), (key2400, -2), (key2475, -2), (key2466, -2), (key2466, -2), (key2498, 2), (key2466, 2), (key2466, 2)]

def rawRow1823 : Integer.Sparse Key := [(key2385, -6), (key2372, 2), (key2372, 2), (key2372, 2), (key2432, 6), (key2400, -2), (key2400, -2), (key2400, -2), (key2498, -2), (key2498, -2), (key2498, -2), (key2475, 2), (key2475, 2), (key2475, 2)]

def rawRow1824 : Integer.Sparse Key := [(key2400, -6), (key2466, 2), (key2466, 2), (key2475, 2), (key2372, 6), (key2466, -2), (key2466, -2), (key2498, -2), (key2372, -2), (key2372, -2), (key2385, -2), (key2400, 2), (key2400, 2), (key2432, 2)]

def rawRow1825 : Integer.Sparse Key := [(key2400, -6), (key2466, 2), (key2475, 2), (key2466, 2), (key2372, 6), (key2466, -2), (key2498, -2), (key2466, -2), (key2372, -2), (key2385, -2), (key2372, -2), (key2400, 2), (key2432, 2), (key2400, 2)]

def rawRow1826 : Integer.Sparse Key := [(key2400, -6), (key2475, 2), (key2466, 2), (key2466, 2), (key2372, 6), (key2498, -2), (key2466, -2), (key2466, -2), (key2385, -2), (key2372, -2), (key2372, -2), (key2432, 2), (key2400, 2), (key2400, 2)]

def rawRow1827 : Integer.Sparse Key := [(key2475, -6), (key2400, 2), (key2466, 2), (key2466, 2), (key2498, 6), (key2372, -2), (key2466, -2), (key2466, -2), (key2432, -2), (key2498, -2), (key2498, -2), (key2385, 2), (key2475, 2), (key2475, 2)]

def rawRow1828 : Integer.Sparse Key := [(key2475, -6), (key2466, 2), (key2400, 2), (key2466, 2), (key2498, 6), (key2466, -2), (key2372, -2), (key2466, -2), (key2498, -2), (key2432, -2), (key2498, -2), (key2475, 2), (key2385, 2), (key2475, 2)]

def rawRow1829 : Integer.Sparse Key := [(key2475, -6), (key2466, 2), (key2466, 2), (key2400, 2), (key2498, 6), (key2466, -2), (key2466, -2), (key2372, -2), (key2498, -2), (key2498, -2), (key2432, -2), (key2475, 2), (key2475, 2), (key2385, 2)]

def rawRow1830 : Integer.Sparse Key := [(key2432, -6), (key2498, 2), (key2498, 2), (key2498, 2), (key2385, 6), (key2475, -2), (key2475, -2), (key2475, -2), (key2372, -2), (key2372, -2), (key2372, -2), (key2400, 2), (key2400, 2), (key2400, 2)]

def rawRow1831 : Integer.Sparse Key := [(key2498, -6), (key2432, 2), (key2498, 2), (key2498, 2), (key2475, 6), (key2385, -2), (key2475, -2), (key2475, -2), (key2400, -2), (key2466, -2), (key2466, -2), (key2372, 2), (key2466, 2), (key2466, 2)]

def rawRow1832 : Integer.Sparse Key := [(key2498, -6), (key2498, 2), (key2432, 2), (key2498, 2), (key2475, 6), (key2475, -2), (key2385, -2), (key2475, -2), (key2466, -2), (key2400, -2), (key2466, -2), (key2466, 2), (key2372, 2), (key2466, 2)]

def rawRow1833 : Integer.Sparse Key := [(key2498, -6), (key2498, 2), (key2498, 2), (key2432, 2), (key2475, 6), (key2475, -2), (key2475, -2), (key2385, -2), (key2466, -2), (key2466, -2), (key2400, -2), (key2466, 2), (key2466, 2), (key2372, 2)]

def rawRow1834 : Integer.Sparse Key := [(key1526, -1), (key1534, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1894, -1), (key1534, 2), (key1534, 2), (key1894, 2), (key1604, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1612, -1), (key1679, -1), (key1612, -1), (key1916, -1), (key1679, -1), (key1916, -1), (key1640, -2), (key1640, -2), (key1930, -2), (key1640, 1), (key1693, 1), (key1640, 1), (key1930, 1), (key1693, 1), (key1930, 1)]

def rawRow1835 : Integer.Sparse Key := [(key1534, -1), (key1526, -1), (key1894, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1534, 2), (key1894, 2), (key1534, 2), (key1612, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1679, -1), (key1612, -1), (key1916, -1), (key1612, -1), (key1916, -1), (key1679, -1), (key1640, -2), (key1930, -2), (key1640, -2), (key1693, 1), (key1640, 1), (key1930, 1), (key1640, 1), (key1930, 1), (key1693, 1)]

def rawRow1836 : Integer.Sparse Key := [(key1894, -1), (key1894, -1), (key1534, -1), (key1534, -1), (key1526, -1), (key1526, -1), (key1894, 2), (key1534, 2), (key1534, 2), (key1916, 1), (key1916, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1916, -1), (key1916, -1), (key1679, -1), (key1679, -1), (key1612, -1), (key1612, -1), (key1930, -2), (key1640, -2), (key1640, -2), (key1930, 1), (key1930, 1), (key1693, 1), (key1693, 1), (key1640, 1), (key1640, 1)]

def rawRow1837 : Integer.Sparse Key := [(key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1526, 2), (key1526, 2), (key1526, 2), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1604, -1), (key1604, -1), (key1604, -1), (key1604, -1), (key1604, -1), (key1604, -1), (key1693, -2), (key1693, -2), (key1693, -2), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1)]

def rawRow1838 : Integer.Sparse Key := [(key1604, -1), (key1612, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1916, -1), (key1640, 2), (key1640, 2), (key1930, 2), (key1526, 1), (key1534, 1), (key1526, 1), (key1894, 1), (key1534, 1), (key1894, 1), (key1640, -1), (key1693, -1), (key1640, -1), (key1930, -1), (key1693, -1), (key1930, -1), (key1534, -2), (key1534, -2), (key1894, -2), (key1612, 1), (key1679, 1), (key1612, 1), (key1916, 1), (key1679, 1), (key1916, 1)]

def rawRow1839 : Integer.Sparse Key := [(key1612, -1), (key1604, -1), (key1916, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1640, 2), (key1930, 2), (key1640, 2), (key1534, 1), (key1526, 1), (key1894, 1), (key1526, 1), (key1894, 1), (key1534, 1), (key1693, -1), (key1640, -1), (key1930, -1), (key1640, -1), (key1930, -1), (key1693, -1), (key1534, -2), (key1894, -2), (key1534, -2), (key1679, 1), (key1612, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1679, 1)]

def rawRow1840 : Integer.Sparse Key := [(key1916, -1), (key1916, -1), (key1612, -1), (key1612, -1), (key1604, -1), (key1604, -1), (key1930, 2), (key1640, 2), (key1640, 2), (key1894, 1), (key1894, 1), (key1534, 1), (key1534, 1), (key1526, 1), (key1526, 1), (key1930, -1), (key1930, -1), (key1693, -1), (key1693, -1), (key1640, -1), (key1640, -1), (key1894, -2), (key1534, -2), (key1534, -2), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1)]

def rawRow1841 : Integer.Sparse Key := [(key1259, -1), (key1259, -1), (key1612, -1), (key1612, -1), (key1640, -1), (key1640, -1), (key1251, 2), (key1604, 2), (key1604, 2), (key1271, 1), (key1271, 1), (key1679, 1), (key1679, 1), (key1693, 1), (key1693, 1), (key1251, -1), (key1251, -1), (key1526, -1), (key1526, -1), (key1604, -1), (key1604, -1), (key1271, -2), (key1679, -2), (key1679, -2), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1)]

def rawRow1842 : Integer.Sparse Key := [(key1612, -1), (key1640, -1), (key1259, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1604, 2), (key1251, 2), (key1604, 2), (key1679, 1), (key1693, 1), (key1271, 1), (key1693, 1), (key1271, 1), (key1679, 1), (key1526, -1), (key1604, -1), (key1251, -1), (key1604, -1), (key1251, -1), (key1526, -1), (key1679, -2), (key1271, -2), (key1679, -2), (key1534, 1), (key1612, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1534, 1)]

def rawRow1843 : Integer.Sparse Key := [(key1640, -1), (key1612, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1259, -1), (key1604, 2), (key1604, 2), (key1251, 2), (key1693, 1), (key1679, 1), (key1693, 1), (key1271, 1), (key1679, 1), (key1271, 1), (key1604, -1), (key1526, -1), (key1604, -1), (key1251, -1), (key1526, -1), (key1251, -1), (key1679, -2), (key1679, -2), (key1271, -2), (key1612, 1), (key1534, 1), (key1612, 1), (key1259, 1), (key1534, 1), (key1259, 1)]

def rawRow1844 : Integer.Sparse Key := [(key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1693, 2), (key1693, 2), (key1693, 2), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1640, -1), (key1640, -1), (key1640, -1), (key1640, -1), (key1640, -1), (key1640, -1), (key1526, -2), (key1526, -2), (key1526, -2), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1)]

def rawRow1845 : Integer.Sparse Key := [(key1271, -1), (key1271, -1), (key1679, -1), (key1679, -1), (key1693, -1), (key1693, -1), (key1271, 2), (key1679, 2), (key1679, 2), (key1259, 1), (key1259, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1259, -1), (key1259, -1), (key1534, -1), (key1534, -1), (key1612, -1), (key1612, -1), (key1251, -2), (key1604, -2), (key1604, -2), (key1251, 1), (key1251, 1), (key1526, 1), (key1526, 1), (key1604, 1), (key1604, 1)]

def rawRow1846 : Integer.Sparse Key := [(key1679, -1), (key1693, -1), (key1271, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1679, 2), (key1271, 2), (key1679, 2), (key1612, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1534, -1), (key1612, -1), (key1259, -1), (key1612, -1), (key1259, -1), (key1534, -1), (key1604, -2), (key1251, -2), (key1604, -2), (key1526, 1), (key1604, 1), (key1251, 1), (key1604, 1), (key1251, 1), (key1526, 1)]

def rawRow1847 : Integer.Sparse Key := [(key1693, -1), (key1679, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1271, -1), (key1679, 2), (key1679, 2), (key1271, 2), (key1640, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1612, -1), (key1534, -1), (key1612, -1), (key1259, -1), (key1534, -1), (key1259, -1), (key1604, -2), (key1604, -2), (key1251, -2), (key1604, 1), (key1526, 1), (key1604, 1), (key1251, 1), (key1526, 1), (key1251, 1)]

def rawRow1848 : Integer.Sparse Key := [(key2414, -2), (key2426, -2), (key2426, -2), (key2419, 2), (key2426, 2), (key2426, 2), (key2487, 2), (key2494, 2), (key2494, 2), (key2494, -6), (key2572, -2), (key2573, -2), (key2573, -2), (key2573, 6)]

def rawRow1849 : Integer.Sparse Key := [(key2426, -2), (key2414, -2), (key2426, -2), (key2426, 2), (key2419, 2), (key2426, 2), (key2494, 2), (key2487, 2), (key2494, 2), (key2494, -6), (key2573, -2), (key2572, -2), (key2573, -2), (key2573, 6)]

def rawRow1850 : Integer.Sparse Key := [(key2426, -2), (key2426, -2), (key2414, -2), (key2426, 2), (key2426, 2), (key2419, 2), (key2494, 2), (key2494, 2), (key2487, 2), (key2494, -6), (key2573, -2), (key2573, -2), (key2572, -2), (key2573, 6)]

def rawRow1851 : Integer.Sparse Key := [(key2419, -2), (key2419, -2), (key2419, -2), (key2414, 2), (key2414, 2), (key2414, 2), (key2494, 2), (key2494, 2), (key2494, 2), (key2487, -6), (key2573, -2), (key2573, -2), (key2573, -2), (key2572, 6)]

def rawRow1852 : Integer.Sparse Key := [(key3120, -2), (key3141, -2), (key3141, -2), (key3130, 2), (key3144, 2), (key3144, 2), (key2414, 2), (key2426, 2), (key2426, 2), (key2573, -6), (key2419, -2), (key2426, -2), (key2426, -2), (key2494, 6)]

def rawRow1853 : Integer.Sparse Key := [(key3141, -2), (key3120, -2), (key3141, -2), (key3144, 2), (key3130, 2), (key3144, 2), (key2426, 2), (key2414, 2), (key2426, 2), (key2573, -6), (key2426, -2), (key2419, -2), (key2426, -2), (key2494, 6)]

def rawRow1854 : Integer.Sparse Key := [(key3141, -2), (key3141, -2), (key3120, -2), (key3144, 2), (key3144, 2), (key3130, 2), (key2426, 2), (key2426, 2), (key2414, 2), (key2573, -6), (key2426, -2), (key2426, -2), (key2419, -2), (key2494, 6)]

def rawRow1855 : Integer.Sparse Key := [(key3038, -2), (key3038, -2), (key3130, -2), (key3033, 2), (key3033, 2), (key3120, 2), (key3043, 2), (key3043, 2), (key3144, 2), (key2414, -6), (key2426, -2), (key2426, -2), (key2494, -2), (key2419, 6)]

def rawRow1856 : Integer.Sparse Key := [(key3038, -2), (key3130, -2), (key3038, -2), (key3033, 2), (key3120, 2), (key3033, 2), (key3043, 2), (key3144, 2), (key3043, 2), (key3033, -6), (key2426, -2), (key2494, -2), (key2426, -2), (key2419, 6)]

def rawRow1857 : Integer.Sparse Key := [(key3130, -2), (key3038, -2), (key3038, -2), (key3120, 2), (key3033, 2), (key3033, 2), (key3144, 2), (key3043, 2), (key3043, 2), (key3033, -6), (key2494, -2), (key2426, -2), (key2426, -2), (key2419, 6)]

def rawRow1858 : Integer.Sparse Key := [(key3141, -2), (key3141, -2), (key3141, -2), (key3144, 2), (key3144, 2), (key3144, 2), (key3038, 2), (key3038, 2), (key3038, 2), (key3130, -6), (key2414, -2), (key2414, -2), (key2414, -2), (key2487, 6)]

def rawRow1859 : Integer.Sparse Key := [(key3043, -2), (key3043, -2), (key3144, -2), (key3043, 2), (key3043, 2), (key3141, 2), (key3038, 2), (key3038, 2), (key3130, 2), (key3038, -6), (key3033, -2), (key3033, -2), (key3120, -2), (key2414, 6)]

def rawRow1860 : Integer.Sparse Key := [(key3043, -2), (key3144, -2), (key3043, -2), (key3043, 2), (key3141, 2), (key3043, 2), (key3038, 2), (key3130, 2), (key3038, 2), (key3038, -6), (key3033, -2), (key3120, -2), (key3033, -2), (key3033, 6)]

def rawRow1861 : Integer.Sparse Key := [(key3144, -2), (key3043, -2), (key3043, -2), (key3141, 2), (key3043, 2), (key3043, 2), (key3130, 2), (key3038, 2), (key3038, 2), (key3038, -6), (key3120, -2), (key3033, -2), (key3033, -2), (key3033, 6)]

def rawRow1862 : Integer.Sparse Key := [(key1251, -2), (key1259, -2), (key1259, -2), (key1251, 1), (key1259, 1), (key1251, 1), (key1271, 1), (key1259, 1), (key1271, 1), (key1526, 2), (key1534, 2), (key1534, 2), (key1526, -1), (key1534, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1894, -1), (key1604, -1), (key1612, -1), (key1604, -1), (key1679, -1), (key1612, -1), (key1679, -1), (key1604, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1916, 1)]

def rawRow1863 : Integer.Sparse Key := [(key1259, -2), (key1251, -2), (key1259, -2), (key1259, 1), (key1251, 1), (key1271, 1), (key1251, 1), (key1271, 1), (key1259, 1), (key1534, 2), (key1526, 2), (key1534, 2), (key1534, -1), (key1526, -1), (key1894, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1612, -1), (key1604, -1), (key1679, -1), (key1604, -1), (key1679, -1), (key1612, -1), (key1612, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1612, 1)]

def rawRow1864 : Integer.Sparse Key := [(key1259, -2), (key1259, -2), (key1251, -2), (key1271, 1), (key1271, 1), (key1259, 1), (key1259, 1), (key1251, 1), (key1251, 1), (key1534, 2), (key1534, 2), (key1526, 2), (key1894, -1), (key1894, -1), (key1534, -1), (key1534, -1), (key1526, -1), (key1526, -1), (key1679, -1), (key1679, -1), (key1612, -1), (key1612, -1), (key1604, -1), (key1604, -1), (key1916, 1), (key1916, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1)]

def rawRow1865 : Integer.Sparse Key := [(key1271, -2), (key1271, -2), (key1271, -2), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1894, 2), (key1894, 2), (key1894, 2), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1)]

def rawRow1866 : Integer.Sparse Key := [(key1526, -2), (key1534, -2), (key1534, -2), (key1604, 1), (key1612, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1679, 1), (key1251, 2), (key1259, 2), (key1259, 2), (key1604, -1), (key1612, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1916, -1), (key1251, -1), (key1259, -1), (key1251, -1), (key1271, -1), (key1259, -1), (key1271, -1), (key1526, 1), (key1534, 1), (key1526, 1), (key1894, 1), (key1534, 1), (key1894, 1)]

def rawRow1867 : Integer.Sparse Key := [(key1534, -2), (key1526, -2), (key1534, -2), (key1612, 1), (key1604, 1), (key1679, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1259, 2), (key1251, 2), (key1259, 2), (key1612, -1), (key1604, -1), (key1916, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1259, -1), (key1251, -1), (key1271, -1), (key1251, -1), (key1271, -1), (key1259, -1), (key1534, 1), (key1526, 1), (key1894, 1), (key1526, 1), (key1894, 1), (key1534, 1)]

def rawRow1868 : Integer.Sparse Key := [(key1534, -2), (key1534, -2), (key1526, -2), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1259, 2), (key1259, 2), (key1251, 2), (key1916, -1), (key1916, -1), (key1612, -1), (key1612, -1), (key1604, -1), (key1604, -1), (key1271, -1), (key1271, -1), (key1259, -1), (key1259, -1), (key1251, -1), (key1251, -1), (key1894, 1), (key1894, 1), (key1534, 1), (key1534, 1), (key1526, 1), (key1526, 1)]

def rawRow1869 : Integer.Sparse Key := [(key1679, -2), (key1679, -2), (key1693, -2), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1916, 2), (key1916, 2), (key1930, 2), (key1259, -1), (key1259, -1), (key1612, -1), (key1612, -1), (key1640, -1), (key1640, -1), (key1894, -1), (key1894, -1), (key1916, -1), (key1916, -1), (key1930, -1), (key1930, -1), (key1271, 1), (key1271, 1), (key1679, 1), (key1679, 1), (key1693, 1), (key1693, 1)]

def rawRow1870 : Integer.Sparse Key := [(key1679, -2), (key1693, -2), (key1679, -2), (key1612, 1), (key1640, 1), (key1534, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1916, 2), (key1930, 2), (key1916, 2), (key1612, -1), (key1640, -1), (key1259, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1916, -1), (key1930, -1), (key1894, -1), (key1930, -1), (key1894, -1), (key1916, -1), (key1679, 1), (key1693, 1), (key1271, 1), (key1693, 1), (key1271, 1), (key1679, 1)]

def rawRow1871 : Integer.Sparse Key := [(key1693, -2), (key1679, -2), (key1679, -2), (key1640, 1), (key1612, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1534, 1), (key1930, 2), (key1916, 2), (key1916, 2), (key1640, -1), (key1612, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1259, -1), (key1930, -1), (key1916, -1), (key1930, -1), (key1894, -1), (key1916, -1), (key1894, -1), (key1693, 1), (key1679, 1), (key1693, 1), (key1271, 1), (key1679, 1), (key1271, 1)]

def rawRow1872 : Integer.Sparse Key := [(key1894, -2), (key1894, -2), (key1894, -2), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1271, 2), (key1271, 2), (key1271, 2), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1)]

def rawRow1873 : Integer.Sparse Key := [(key1916, -2), (key1916, -2), (key1930, -2), (key1894, 1), (key1894, 1), (key1916, 1), (key1916, 1), (key1930, 1), (key1930, 1), (key1679, 2), (key1679, 2), (key1693, 2), (key1271, -1), (key1271, -1), (key1679, -1), (key1679, -1), (key1693, -1), (key1693, -1), (key1534, -1), (key1534, -1), (key1612, -1), (key1612, -1), (key1640, -1), (key1640, -1), (key1259, 1), (key1259, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1)]

def rawRow1874 : Integer.Sparse Key := [(key1916, -2), (key1930, -2), (key1916, -2), (key1916, 1), (key1930, 1), (key1894, 1), (key1930, 1), (key1894, 1), (key1916, 1), (key1679, 2), (key1693, 2), (key1679, 2), (key1679, -1), (key1693, -1), (key1271, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1612, -1), (key1640, -1), (key1534, -1), (key1640, -1), (key1534, -1), (key1612, -1), (key1612, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1612, 1)]

def rawRow1875 : Integer.Sparse Key := [(key1930, -2), (key1916, -2), (key1916, -2), (key1930, 1), (key1916, 1), (key1930, 1), (key1894, 1), (key1916, 1), (key1894, 1), (key1693, 2), (key1679, 2), (key1679, 2), (key1693, -1), (key1679, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1271, -1), (key1640, -1), (key1612, -1), (key1640, -1), (key1534, -1), (key1612, -1), (key1534, -1), (key1640, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1259, 1)]

def rawRow1876 : Integer.Sparse Key := [(key972, -2), (key978, -2), (key978, -2), (key978, 6), (key1086, 2), (key1092, 2), (key1092, 2), (key1092, -2), (key1092, -2), (key1227, -2), (key1163, -6), (key1163, 2), (key1163, 2), (key1244, 2)]

def rawRow1877 : Integer.Sparse Key := [(key978, -2), (key972, -2), (key978, -2), (key978, 6), (key1092, 2), (key1086, 2), (key1092, 2), (key1092, -2), (key1227, -2), (key1092, -2), (key1163, -6), (key1163, 2), (key1244, 2), (key1163, 2)]

def rawRow1878 : Integer.Sparse Key := [(key978, -2), (key978, -2), (key972, -2), (key978, 6), (key1092, 2), (key1092, 2), (key1086, 2), (key1227, -2), (key1092, -2), (key1092, -2), (key1163, -6), (key1244, 2), (key1163, 2), (key1163, 2)]

def rawRow1879 : Integer.Sparse Key := [(key978, -2), (key978, -2), (key978, -2), (key972, 6), (key1227, 2), (key1227, 2), (key1227, 2), (key1086, -2), (key1086, -2), (key1086, -2), (key1244, -6), (key1163, 2), (key1163, 2), (key1163, 2)]

def rawRow1880 : Integer.Sparse Key := [(key1086, -2), (key1092, -2), (key1092, -2), (key1163, 6), (key972, 2), (key978, 2), (key978, 2), (key1163, -2), (key1163, -2), (key1244, -2), (key978, -6), (key1092, 2), (key1092, 2), (key1227, 2)]

def rawRow1881 : Integer.Sparse Key := [(key1092, -2), (key1086, -2), (key1092, -2), (key1163, 6), (key978, 2), (key972, 2), (key978, 2), (key1163, -2), (key1244, -2), (key1163, -2), (key978, -6), (key1092, 2), (key1227, 2), (key1092, 2)]

def rawRow1882 : Integer.Sparse Key := [(key1092, -2), (key1092, -2), (key1086, -2), (key1163, 6), (key978, 2), (key978, 2), (key972, 2), (key1244, -2), (key1163, -2), (key1163, -2), (key978, -6), (key1227, 2), (key1092, 2), (key1092, 2)]

def rawRow1883 : Integer.Sparse Key := [(key1092, -2), (key1092, -2), (key1163, -2), (key1086, 6), (key1227, 2), (key1227, 2), (key1244, 2), (key972, -2), (key1086, -2), (key1086, -2), (key1227, -6), (key978, 2), (key1092, 2), (key1092, 2)]

def rawRow1884 : Integer.Sparse Key := [(key1092, -2), (key1163, -2), (key1092, -2), (key1086, 6), (key1227, 2), (key1244, 2), (key1227, 2), (key1086, -2), (key972, -2), (key1086, -2), (key1227, -6), (key1092, 2), (key978, 2), (key1092, 2)]

def rawRow1885 : Integer.Sparse Key := [(key1163, -2), (key1092, -2), (key1092, -2), (key1086, 6), (key1244, 2), (key1227, 2), (key1227, 2), (key1086, -2), (key1086, -2), (key972, -2), (key1227, -6), (key1092, 2), (key1092, 2), (key978, 2)]

def rawRow1886 : Integer.Sparse Key := [(key1227, -2), (key1227, -2), (key1227, -2), (key1244, 6), (key978, 2), (key978, 2), (key978, 2), (key1163, -2), (key1163, -2), (key1163, -2), (key972, -6), (key1086, 2), (key1086, 2), (key1086, 2)]

def rawRow1887 : Integer.Sparse Key := [(key1227, -2), (key1227, -2), (key1244, -2), (key1227, 6), (key1092, 2), (key1092, 2), (key1163, 2), (key978, -2), (key1092, -2), (key1092, -2), (key1086, -6), (key972, 2), (key1086, 2), (key1086, 2)]

def rawRow1888 : Integer.Sparse Key := [(key1227, -2), (key1244, -2), (key1227, -2), (key1227, 6), (key1092, 2), (key1163, 2), (key1092, 2), (key1092, -2), (key978, -2), (key1092, -2), (key1086, -6), (key1086, 2), (key972, 2), (key1086, 2)]

def rawRow1889 : Integer.Sparse Key := [(key1244, -2), (key1227, -2), (key1227, -2), (key1227, 6), (key1163, 2), (key1092, 2), (key1092, 2), (key1092, -2), (key1092, -2), (key978, -2), (key1086, -6), (key1086, 2), (key1086, 2), (key972, 2)]

def rawRow1890 : Integer.Sparse Key := [(key2374, -2), (key2374, -2), (key2391, -2), (key2374, 1), (key2380, 1), (key2374, 1), (key2391, 1), (key2380, 1), (key2391, 1), (key2468, 2), (key2468, 2), (key2481, 2), (key2468, -1), (key2481, -1), (key2468, -1), (key2505, -1), (key2481, -1), (key2505, -1), (key2535, -1), (key2537, -1), (key2535, -1), (key2542, -1), (key2537, -1), (key2542, -1), (key2535, 1), (key2542, 1), (key2535, 1), (key2553, 1), (key2542, 1), (key2553, 1)]

def rawRow1891 : Integer.Sparse Key := [(key2374, -2), (key2391, -2), (key2374, -2), (key2380, 1), (key2374, 1), (key2391, 1), (key2374, 1), (key2391, 1), (key2380, 1), (key2468, 2), (key2481, 2), (key2468, 2), (key2481, -1), (key2468, -1), (key2505, -1), (key2468, -1), (key2505, -1), (key2481, -1), (key2537, -1), (key2535, -1), (key2542, -1), (key2535, -1), (key2542, -1), (key2537, -1), (key2542, 1), (key2535, 1), (key2553, 1), (key2535, 1), (key2553, 1), (key2542, 1)]

def rawRow1892 : Integer.Sparse Key := [(key2391, -2), (key2374, -2), (key2374, -2), (key2391, 1), (key2391, 1), (key2380, 1), (key2380, 1), (key2374, 1), (key2374, 1), (key2481, 2), (key2468, 2), (key2468, 2), (key2505, -1), (key2505, -1), (key2481, -1), (key2481, -1), (key2468, -1), (key2468, -1), (key2542, -1), (key2542, -1), (key2537, -1), (key2537, -1), (key2535, -1), (key2535, -1), (key2553, 1), (key2553, 1), (key2542, 1), (key2542, 1), (key2535, 1), (key2535, 1)]

end MUB6.Certificate.GramRows

end OAI
end


