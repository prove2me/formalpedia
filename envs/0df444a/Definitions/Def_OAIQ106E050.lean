-- Prove2me | Definitions.Def_OAIQ106E050
-- name    : OAIQ106E050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:02:59.657199+00:00
-- url     : https://prove2.me/theorems/8ded09f9-54b5-4c24-83de-3dd50f9b904a
-- title:
--   Definitions bundle OAIQ106E050 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1780 declarations of OpenAI's Lean: 1780 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow18928`, `OAI.MUB6.Certificate.GramRows.rawRow18929`, `OAI.MUB6.Certificate.GramRows.rawRow1893`, `OAI.MUB6.Certificate.GramRows.rawRow18930`, `OAI.MUB6.Certificate.GramRows.rawRow18931`, `OAI.MUB6.Certificate.GramRows.rawRow18932`, `OAI.MUB6.Certificate.GramRows.rawRow18933`, `OAI.MUB6.Certificate.GramRows.rawRow18934`, `OAI.MUB6.Certificate.GramRows.rawRow18935`, `OAI.MUB6.Certificate.GramRows.rawRow18936`, `OAI.MUB6.Certificate.GramRows.rawRow18937`, `OAI.MUB6.Certificate.GramRows.rawRow18938`, `OAI.MUB6.Certificate.GramRows.rawRow1894`, `OAI.MUB6.Certificate.GramRows.rawRow18940`, `OAI.MUB6.Certificate.GramRows.rawRow18941`, `OAI.MUB6.Certificate.GramRows.rawRow18942`, `OAI.MUB6.Certificate.GramRows.rawRow18943`, `OAI.MUB6.Certificate.GramRows.rawRow18944`, `OAI.MUB6.Certificate.GramRows.rawRow18945`, `OAI.MUB6.Certificate.GramRows.rawRow18946`, `OAI.MUB6.Certificate.GramRows.rawRow18947`, `OAI.MUB6.Certificate.GramRows.rawRow18948`, `OAI.MUB6.Certificate.GramRows.rawRow18949`, `OAI.MUB6.Certificate.GramRows.rawRow1895`, `OAI.MUB6.Certificate.GramRows.rawRow18950`, `OAI.MUB6.Certificate.GramRows.rawRow18951`, `OAI.MUB6.Certificate.GramRows.rawRow18952`, `OAI.MUB6.Certificate.GramRows.rawRow18953`, `OAI.MUB6.Certificate.GramRows.rawRow18954`, `OAI.MUB6.Certificate.GramRows.rawRow18955`, `OAI.MUB6.Certificate.GramRows.rawRow18956`, `OAI.MUB6.Certificate.GramRows.rawRow18957`, `OAI.MUB6.Certificate.GramRows.rawRow18958`, `OAI.MUB6.Certificate.GramRows.rawRow18959`, `OAI.MUB6.Certificate.GramRows.rawRow1896`, `OAI.MUB6.Certificate.GramRows.rawRow18960`, `OAI.MUB6.Certificate.GramRows.rawRow18961`, `OAI.MUB6.Certificate.GramRows.rawRow18962`, `OAI.MUB6.Certificate.GramRows.rawRow18963`, `OAI.MUB6.Certificate.GramRows.rawRow18964` and 1740 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block171`, `MutuallyUnbiased_GramRows_Block172`, `MutuallyUnbiased_GramRows_Block173`, `MutuallyUnbiased_GramRows_Block174`, `MutuallyUnbiased_GramRows_Block175`, `MutuallyUnbiased_GramRows_Block176`, `MutuallyUnbiased_GramRows_Block177`, `MutuallyUnbiased_GramRows_Block178`, `MutuallyUnbiased_GramRows_Block179`, `MutuallyUnbiased_GramRows_Block180`, `MutuallyUnbiased_GramRows_Block181`, `MutuallyUnbiased_GramRows_Block182`, `MutuallyUnbiased_GramRows_Block2`, `MutuallyUnbiased_GramRows_Block3`, `MutuallyUnbiased_GramRows_Block38`, `MutuallyUnbiased_GramRows_Block39`, `MutuallyUnbiased_GramRows_Block40`, `MutuallyUnbiased_GramRows_Block41`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_10_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_11_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_3_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_4_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_5_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_6_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow7_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow9_e`.
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

def rawRow2 : Integer.Sparse Key := [(key239, -1), (key239, -1), (key236, 2), (key260, 1), (key260, 1), (key248, -1), (key248, -1), (key271, -2), (key267, 1), (key267, 1), (key305, 1), (key305, 1), (key302, -2), (key328, -1), (key328, -1), (key316, 1), (key316, 1), (key340, 2), (key335, -1), (key335, -1), (key397, -1), (key397, -1), (key385, 1), (key385, 1), (key418, 1), (key418, 1), (key406, -1), (key406, -1), (key475, -1), (key475, -1), (key469, 1), (key469, 1), (key572, 2), (key568, -1), (key568, -1), (key583, -2), (key578, 1), (key578, 1), (key601, 1), (key601, 1), (key595, -1), (key595, -1)]

def rawRow19 : Integer.Sparse Key := [(key340, -1), (key335, -1), (key335, 2), (key328, 1), (key319, 1), (key319, -1), (key305, -1), (key316, -2), (key316, 1), (key302, 1), (key583, 1), (key578, 1), (key578, -2), (key418, -1), (key409, -1), (key409, 1), (key239, 1), (key406, 2), (key406, -1), (key236, -1), (key601, -1), (key450, -1), (key450, 1), (key328, 1), (key595, 1), (key442, 1), (key442, -1), (key260, -1), (key435, -1), (key316, -1), (key435, 1), (key248, 1), (key475, 2), (key475, -1), (key340, -1), (key469, -2), (key469, 1), (key271, 1), (key467, 1), (key335, 1), (key467, -1), (key267, -1)]

def rawRow20 : Integer.Sparse Key := [(key385, -1), (key388, -1), (key397, 2), (key406, 1), (key409, 1), (key442, -1), (key469, -1), (key418, -2), (key450, 1), (key475, 1), (key248, 1), (key251, 1), (key260, -2), (key316, -1), (key319, -1), (key442, 1), (key595, 1), (key328, 2), (key450, -1), (key601, -1), (key236, -1), (key239, -1), (key267, 1), (key271, 1), (key302, 1), (key305, 1), (key335, -1), (key340, -1), (key568, -1), (key572, -1), (key578, 1), (key583, 1), (key239, 2), (key251, -1), (key260, -1), (key305, -2), (key319, 1), (key328, 1), (key388, 1), (key397, 1), (key409, -1), (key418, -1)]

def rawRow21 : Integer.Sparse Key := [(key388, -1), (key385, -1), (key397, 2), (key409, 1), (key406, 1), (key469, -1), (key442, -1), (key418, -2), (key475, 1), (key450, 1), (key251, 1), (key248, 1), (key260, -2), (key319, -1), (key316, -1), (key595, 1), (key442, 1), (key328, 2), (key601, -1), (key450, -1), (key239, -1), (key236, -1), (key271, 1), (key267, 1), (key305, 1), (key302, 1), (key340, -1), (key335, -1), (key572, -1), (key568, -1), (key583, 1), (key578, 1), (key239, 2), (key260, -1), (key251, -1), (key305, -2), (key328, 1), (key319, 1), (key397, 1), (key388, 1), (key418, -1), (key409, -1)]

def rawRow22 : Integer.Sparse Key := [(key388, -1), (key397, -1), (key385, 2), (key467, 1), (key469, 1), (key406, -1), (key435, -1), (key475, -2), (key418, 1), (key450, 1), (key251, 1), (key260, 1), (key248, -2), (key593, -1), (key595, -1), (key316, 1), (key435, 1), (key601, 2), (key328, -1), (key450, -1), (key267, -1), (key271, -1), (key236, 1), (key248, 1), (key328, 1), (key340, 1), (key302, -1), (key316, -1), (key583, -1), (key601, -1), (key572, 1), (key595, 1), (key260, 2), (key239, -1), (key251, -1), (key328, -2), (key305, 1), (key319, 1), (key418, 1), (key450, 1), (key397, -1), (key442, -1)]

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

def rawRow18928 : Integer.Sparse Key := [(key2532, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2365, 4), (key2367, 4), (key2365, 4), (key2460, 4), (key2533, 4), (key2460, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2365, 4), (key2362, 4), (key2365, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow18929 : Integer.Sparse Key := [(key2533, 4), (key2532, 4), (key2532, 4), (key2564, 4), (key2564, 4), (key2562, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2533, 4), (key2460, 4), (key2460, 4), (key2564, 4), (key2564, 4), (key2525, 4), (key2525, 4), (key2521, 4), (key2521, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow18930 : Integer.Sparse Key := [(key2532, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2533, 4), (key2564, 4), (key2460, 4), (key2521, 4), (key2525, 4), (key2365, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2533, 4), (key2525, 4), (key2564, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2362, 4), (key2365, 4), (key2457, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2460, 4), (key2521, 4)]

def rawRow18931 : Integer.Sparse Key := [(key2532, 4), (key2564, 4), (key2562, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2460, 4), (key2525, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2521, 4), (key2367, 4), (key2365, 4), (key2533, 4), (key2460, 4), (key2564, 4), (key2525, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2365, 4), (key2521, 4), (key2460, 4)]

def rawRow18932 : Integer.Sparse Key := [(key2562, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2521, 4), (key2460, 4), (key2525, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2460, 4), (key2525, 4), (key2365, 4), (key2564, 4), (key2367, 4), (key2533, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2362, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2365, 4), (key2521, 4)]

def rawRow18933 : Integer.Sparse Key := [(key2562, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2533, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2525, 4), (key2460, 4), (key2564, 4), (key2365, 4), (key2533, 4), (key2367, 4), (key2521, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2362, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2521, 4), (key2365, 4)]

def rawRow18934 : Integer.Sparse Key := [(key2564, 4), (key2532, 4), (key2562, 4), (key2533, 4), (key2564, 4), (key2532, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2533, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2362, 4), (key2457, 4), (key2521, 4), (key2365, 4), (key2460, 4)]

def rawRow18935 : Integer.Sparse Key := [(key2564, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2532, 4), (key2525, 4), (key2521, 4), (key2460, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2533, 4), (key2525, 4), (key2367, 4), (key2460, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2521, 4), (key2365, 4), (key2457, 4), (key2362, 4), (key2521, 4), (key2460, 4), (key2365, 4)]

def rawRow18936 : Integer.Sparse Key := [(key2533, 4), (key2564, 4), (key2564, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2533, 4), (key2564, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2525, 4), (key2365, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2362, 4), (key2457, 4), (key2457, 4)]

def rawRow18937 : Integer.Sparse Key := [(key2564, 4), (key2533, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2564, 4), (key2525, 4), (key2367, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2457, 4), (key2362, 4), (key2457, 4)]

def rawRow18938 : Integer.Sparse Key := [(key2564, 4), (key2564, 4), (key2533, 4), (key2562, 4), (key2532, 4), (key2532, 4), (key2564, 4), (key2564, 4), (key2533, 4), (key2525, 4), (key2525, 4), (key2367, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2365, 4), (key2562, 4), (key2532, 4), (key2532, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2365, 4), (key2457, 4), (key2457, 4), (key2362, 4)]

def rawRow18940 : Integer.Sparse Key := [(key2358, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2559, 6), (key2514, 6)]

def rawRow18941 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2559, 6), (key2514, 6), (key2514, 6)]

def rawRow18942 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2529, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2449, 6), (key2559, 6), (key2514, 6), (key2514, 6), (key2514, 6)]

def rawRow18943 : Integer.Sparse Key := [(key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2449, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2529, 6), (key2514, 6), (key2514, 6), (key2559, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2529, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18944 : Integer.Sparse Key := [(key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2559, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2453, 6)]

def rawRow18945 : Integer.Sparse Key := [(key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2559, 6), (key2514, 6), (key2514, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2453, 6)]

def rawRow18946 : Integer.Sparse Key := [(key2449, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2354, 6), (key2358, 6), (key2449, 6), (key2529, 6), (key2514, 6), (key2559, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2529, 6)]

def rawRow18947 : Integer.Sparse Key := [(key2453, 6), (key2449, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2358, 6), (key2354, 6), (key2529, 6), (key2449, 6), (key2559, 6), (key2514, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2529, 6), (key2453, 6)]

def rawRow18948 : Integer.Sparse Key := [(key2449, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2354, 6), (key2559, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2529, 6)]

def rawRow18949 : Integer.Sparse Key := [(key2514, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2559, 6), (key2354, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2358, 6)]

def rawRow18950 : Integer.Sparse Key := [(key2453, 6), (key2514, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2529, 6), (key2559, 6), (key2358, 6), (key2514, 6), (key2354, 6), (key2449, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2358, 6), (key2453, 6)]

def rawRow18951 : Integer.Sparse Key := [(key2514, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2559, 6), (key2529, 6), (key2514, 6), (key2358, 6), (key2449, 6), (key2354, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2358, 6)]

def rawRow18952 : Integer.Sparse Key := [(key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2529, 6), (key2529, 6), (key2559, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2354, 6), (key2449, 6), (key2449, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2453, 6)]

def rawRow18953 : Integer.Sparse Key := [(key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2559, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2354, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2453, 6)]

def rawRow18954 : Integer.Sparse Key := [(key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2559, 6), (key2529, 6), (key2529, 6), (key2514, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2358, 6), (key2449, 6), (key2449, 6), (key2354, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2358, 6)]

def rawRow18955 : Integer.Sparse Key := [(key2529, 6), (key2529, 6), (key2529, 6), (key2559, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2514, 6), (key2354, 6), (key2449, 6), (key2449, 6), (key2449, 6)]

def rawRow18956 : Integer.Sparse Key := [(key2529, 6), (key2529, 6), (key2559, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2354, 6), (key2449, 6), (key2449, 6)]

def rawRow18957 : Integer.Sparse Key := [(key2529, 6), (key2559, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2354, 6), (key2449, 6)]

def rawRow18958 : Integer.Sparse Key := [(key2559, 6), (key2529, 6), (key2529, 6), (key2529, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2449, 6), (key2449, 6), (key2449, 6), (key2354, 6)]

def rawRow18959 : Integer.Sparse Key := [(key969, 24), (key1083, 24), (key1083, 24), (key1083, 24), (key1177, 24)]

def rawRow18960 : Integer.Sparse Key := [(key969, 24), (key1083, 24), (key1083, 24), (key1177, 24), (key1083, 24)]

def rawRow18961 : Integer.Sparse Key := [(key969, 24), (key1083, 24), (key1177, 24), (key1083, 24), (key1083, 24)]

def rawRow18962 : Integer.Sparse Key := [(key969, 24), (key1177, 24), (key1083, 24), (key1083, 24), (key1083, 24)]

def rawRow18963 : Integer.Sparse Key := [(key1083, 24), (key969, 24), (key1083, 24), (key1083, 24), (key1177, 24)]

def rawRow18964 : Integer.Sparse Key := [(key1083, 24), (key969, 24), (key1083, 24), (key1177, 24), (key1083, 24)]

def rawRow18965 : Integer.Sparse Key := [(key1083, 24), (key969, 24), (key1177, 24), (key1083, 24), (key1083, 24)]

def rawRow18966 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key969, 24), (key1083, 24), (key1177, 24)]

def rawRow18967 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key969, 24), (key1177, 24), (key1083, 24)]

def rawRow18968 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1083, 24), (key969, 24), (key1177, 24)]

def rawRow18969 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1083, 24), (key1177, 24), (key969, 24)]

def rawRow18970 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1177, 24), (key969, 24), (key1083, 24)]

def rawRow18971 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1177, 24), (key1083, 24), (key969, 24)]

def rawRow18972 : Integer.Sparse Key := [(key1083, 24), (key1177, 24), (key969, 24), (key1083, 24), (key1083, 24)]

def rawRow18973 : Integer.Sparse Key := [(key1083, 24), (key1177, 24), (key1083, 24), (key969, 24), (key1083, 24)]

def rawRow18974 : Integer.Sparse Key := [(key1083, 24), (key1177, 24), (key1083, 24), (key1083, 24), (key969, 24)]

def rawRow18975 : Integer.Sparse Key := [(key1177, 24), (key969, 24), (key1083, 24), (key1083, 24), (key1083, 24)]

def rawRow18976 : Integer.Sparse Key := [(key1177, 24), (key1083, 24), (key969, 24), (key1083, 24), (key1083, 24)]

def rawRow18977 : Integer.Sparse Key := [(key1177, 24), (key1083, 24), (key1083, 24), (key969, 24), (key1083, 24)]

def rawRow18978 : Integer.Sparse Key := [(key1177, 24), (key1083, 24), (key1083, 24), (key1083, 24), (key969, 24)]

def rawRow18979 : Integer.Sparse Key := [(key2584, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2599, 2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2888, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2844, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2875, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2909, 2), (key2988, 2)]

def rawRow18980 : Integer.Sparse Key := [(key2588, 2), (key2584, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2599, 2), (key2588, 2), (key2767, 2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2888, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2988, 2), (key2909, 2)]

def rawRow18981 : Integer.Sparse Key := [(key2588, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2988, 2), (key2909, 2), (key2909, 2), (key2875, 2), (key2875, 2)]

def rawRow18982 : Integer.Sparse Key := [(key2599, 2), (key2599, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2584, 2), (key2584, 2), (key2930, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2763, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2988, 2), (key2988, 2), (key2909, 2), (key2909, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2)]

def rawRow18983 : Integer.Sparse Key := [(key2763, 2), (key2767, 2), (key2767, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2888, 2), (key2875, 2), (key2875, 2), (key2909, 2), (key2584, 2), (key2588, 2), (key2588, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2584, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2599, 2), (key2763, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2930, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2909, 2), (key2988, 2), (key2588, 2), (key2588, 2), (key2599, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2844, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2888, 2), (key2967, 2)]

def rawRow18984 : Integer.Sparse Key := [(key2767, 2), (key2763, 2), (key2767, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2588, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2988, 2), (key2909, 2), (key2588, 2), (key2599, 2), (key2588, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2888, 2)]

def rawRow18985 : Integer.Sparse Key := [(key2767, 2), (key2767, 2), (key2763, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2967, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2875, 2), (key2599, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2584, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2988, 2), (key2909, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2)]

def rawRow18986 : Integer.Sparse Key := [(key2840, 2), (key2844, 2), (key2875, 2), (key2763, 2), (key2767, 2), (key2840, 2), (key2888, 2), (key2875, 2), (key2909, 2), (key2767, 2), (key2844, 2), (key2888, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2584, 2), (key2588, 2), (key2840, 2), (key2967, 2), (key2875, 2), (key2988, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2763, 2), (key2767, 2), (key2840, 2), (key2888, 2), (key2875, 2), (key2909, 2), (key2584, 2), (key2588, 2), (key2840, 2), (key2967, 2), (key2875, 2), (key2988, 2), (key2584, 2), (key2599, 2), (key2763, 2), (key2930, 2), (key2909, 2), (key2988, 2), (key2588, 2), (key2599, 2), (key2767, 2), (key2930, 2), (key2888, 2), (key2967, 2), (key2767, 2), (key2844, 2), (key2888, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2599, 2), (key2767, 2), (key2930, 2), (key2888, 2), (key2967, 2)]

def rawRow18987 : Integer.Sparse Key := [(key2844, 2), (key2840, 2), (key2875, 2), (key2767, 2), (key2763, 2), (key2888, 2), (key2840, 2), (key2909, 2), (key2875, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2767, 2), (key2763, 2), (key2888, 2), (key2840, 2), (key2909, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2599, 2), (key2584, 2), (key2930, 2), (key2763, 2), (key2988, 2), (key2909, 2), (key2599, 2), (key2588, 2), (key2930, 2), (key2767, 2), (key2967, 2), (key2888, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2599, 2), (key2588, 2), (key2930, 2), (key2767, 2), (key2967, 2), (key2888, 2)]

def rawRow18988 : Integer.Sparse Key := [(key2840, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2767, 2), (key2888, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2840, 2), (key2875, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2840, 2), (key2875, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2763, 2), (key2909, 2), (key2584, 2), (key2988, 2), (key2599, 2), (key2930, 2), (key2767, 2), (key2888, 2), (key2588, 2), (key2967, 2), (key2599, 2), (key2930, 2), (key2844, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2767, 2), (key2888, 2), (key2588, 2), (key2967, 2), (key2599, 2), (key2930, 2)]

def rawRow18989 : Integer.Sparse Key := [(key2875, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2875, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2888, 2), (key2767, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2967, 2), (key2588, 2), (key2909, 2), (key2763, 2), (key2988, 2), (key2584, 2), (key2930, 2), (key2599, 2), (key2888, 2), (key2767, 2), (key2967, 2), (key2588, 2), (key2930, 2), (key2599, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2888, 2), (key2767, 2), (key2967, 2), (key2588, 2), (key2930, 2), (key2599, 2)]

def rawRow18990 : Integer.Sparse Key := [(key2844, 2), (key2875, 2), (key2840, 2), (key2888, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2763, 2), (key2840, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2888, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2763, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2930, 2), (key2988, 2), (key2599, 2), (key2909, 2), (key2584, 2), (key2763, 2), (key2930, 2), (key2967, 2), (key2599, 2), (key2888, 2), (key2588, 2), (key2767, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2930, 2), (key2967, 2), (key2599, 2), (key2888, 2), (key2588, 2), (key2767, 2)]

def rawRow18991 : Integer.Sparse Key := [(key2875, 2), (key2844, 2), (key2840, 2), (key2909, 2), (key2888, 2), (key2875, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2888, 2), (key2844, 2), (key2767, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2875, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2909, 2), (key2888, 2), (key2875, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2988, 2), (key2967, 2), (key2875, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2988, 2), (key2930, 2), (key2909, 2), (key2599, 2), (key2763, 2), (key2584, 2), (key2967, 2), (key2930, 2), (key2888, 2), (key2599, 2), (key2767, 2), (key2588, 2), (key2888, 2), (key2844, 2), (key2767, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2930, 2), (key2888, 2), (key2599, 2), (key2767, 2), (key2588, 2)]

def rawRow18992 : Integer.Sparse Key := [(key2888, 2), (key2888, 2), (key2909, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2840, 2), (key2930, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2988, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2584, 2), (key2763, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2)]

def rawRow18993 : Integer.Sparse Key := [(key2888, 2), (key2909, 2), (key2888, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2967, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2584, 2), (key2763, 2), (key2967, 2), (key2930, 2), (key2967, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2767, 2)]

def rawRow18994 : Integer.Sparse Key := [(key2909, 2), (key2888, 2), (key2888, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2840, 2), (key2840, 2), (key2763, 2), (key2988, 2), (key2967, 2), (key2967, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2988, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2930, 2), (key2909, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2599, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2763, 2), (key2584, 2), (key2967, 2), (key2967, 2), (key2930, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2844, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2767, 2), (key2588, 2)]

def rawRow18995 : Integer.Sparse Key := [(key2930, 2), (key2930, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2988, 2), (key2988, 2), (key2599, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2909, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2584, 2), (key2584, 2), (key2763, 2), (key2763, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2)]

def rawRow18996 : Integer.Sparse Key := [(key2967, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2584, 2), (key2763, 2), (key2763, 2), (key2840, 2), (key2840, 2)]

def rawRow18997 : Integer.Sparse Key := [(key2967, 2), (key2988, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2930, 2), (key2967, 2), (key2888, 2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2584, 2), (key2763, 2)]

def rawRow18998 : Integer.Sparse Key := [(key2988, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2930, 2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2844, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2840, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2763, 2), (key2584, 2)]

def rawRow18999 : Integer.Sparse Key := [(key2352, 24), (key2447, 24), (key2447, 24), (key2447, 24), (key2511, 24)]

def rawRow19000 : Integer.Sparse Key := [(key2352, 24), (key2447, 24), (key2447, 24), (key2511, 24), (key2447, 24)]

def rawRow19001 : Integer.Sparse Key := [(key2352, 24), (key2447, 24), (key2511, 24), (key2447, 24), (key2447, 24)]

def rawRow19002 : Integer.Sparse Key := [(key2352, 24), (key2511, 24), (key2447, 24), (key2447, 24), (key2447, 24)]

def rawRow19003 : Integer.Sparse Key := [(key2447, 24), (key2352, 24), (key2447, 24), (key2447, 24), (key2511, 24)]

def rawRow19004 : Integer.Sparse Key := [(key2447, 24), (key2352, 24), (key2447, 24), (key2511, 24), (key2447, 24)]

def rawRow19005 : Integer.Sparse Key := [(key2447, 24), (key2352, 24), (key2511, 24), (key2447, 24), (key2447, 24)]

def rawRow19006 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2352, 24), (key2447, 24), (key2511, 24)]

def rawRow19007 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2352, 24), (key2511, 24), (key2447, 24)]

def rawRow19008 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2447, 24), (key2352, 24), (key2511, 24)]

def rawRow19009 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2447, 24), (key2511, 24), (key2352, 24)]

def rawRow19010 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2511, 24), (key2352, 24), (key2447, 24)]

def rawRow19011 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2511, 24), (key2447, 24), (key2352, 24)]

def rawRow19012 : Integer.Sparse Key := [(key2447, 24), (key2511, 24), (key2352, 24), (key2447, 24), (key2447, 24)]

def rawRow19013 : Integer.Sparse Key := [(key2447, 24), (key2511, 24), (key2447, 24), (key2352, 24), (key2447, 24)]

def rawRow19014 : Integer.Sparse Key := [(key2447, 24), (key2511, 24), (key2447, 24), (key2447, 24), (key2352, 24)]

def rawRow19015 : Integer.Sparse Key := [(key2511, 24), (key2352, 24), (key2447, 24), (key2447, 24), (key2447, 24)]

def rawRow19016 : Integer.Sparse Key := [(key2511, 24), (key2447, 24), (key2352, 24), (key2447, 24), (key2447, 24)]

def rawRow19017 : Integer.Sparse Key := [(key2511, 24), (key2447, 24), (key2447, 24), (key2352, 24), (key2447, 24)]

def rawRow19018 : Integer.Sparse Key := [(key2511, 24), (key2447, 24), (key2447, 24), (key2447, 24), (key2352, 24)]

def rawRow19019 : Integer.Sparse Key := [(key972, 6), (key977, 6), (key977, 6), (key977, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key1162, 6), (key1162, 6), (key1162, 6), (key1218, 6)]

def rawRow19020 : Integer.Sparse Key := [(key977, 6), (key972, 6), (key977, 6), (key977, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key1218, 6), (key1162, 6)]

def rawRow19021 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key972, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1218, 6), (key1162, 6), (key1162, 6)]

def rawRow19022 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key977, 6), (key972, 6), (key1181, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key1086, 6), (key1218, 6), (key1162, 6), (key1162, 6), (key1162, 6)]

def rawRow19023 : Integer.Sparse Key := [(key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key972, 6), (key977, 6), (key977, 6), (key1086, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1181, 6), (key1162, 6), (key1162, 6), (key1218, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1181, 6)]

def rawRow19024 : Integer.Sparse Key := [(key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key977, 6), (key972, 6), (key977, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key1218, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1181, 6), (key1091, 6)]

def rawRow19025 : Integer.Sparse Key := [(key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key977, 6), (key977, 6), (key972, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key1218, 6), (key1162, 6), (key1162, 6), (key977, 6), (key1181, 6), (key1091, 6), (key1091, 6)]

def rawRow19026 : Integer.Sparse Key := [(key1086, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key972, 6), (key977, 6), (key1086, 6), (key1181, 6), (key1162, 6), (key1218, 6), (key977, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1181, 6)]

def rawRow19027 : Integer.Sparse Key := [(key1091, 6), (key1086, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key977, 6), (key972, 6), (key1181, 6), (key1086, 6), (key1218, 6), (key1162, 6), (key977, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1181, 6), (key1091, 6)]

def rawRow19028 : Integer.Sparse Key := [(key1086, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key972, 6), (key1218, 6), (key977, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1181, 6)]

def rawRow19029 : Integer.Sparse Key := [(key1162, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1218, 6), (key972, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key977, 6)]

def rawRow19030 : Integer.Sparse Key := [(key1091, 6), (key1162, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1181, 6), (key1218, 6), (key977, 6), (key1162, 6), (key972, 6), (key1086, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key977, 6), (key1091, 6)]

def rawRow19031 : Integer.Sparse Key := [(key1162, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1218, 6), (key1181, 6), (key1162, 6), (key977, 6), (key1086, 6), (key972, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key977, 6)]

def rawRow19032 : Integer.Sparse Key := [(key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1181, 6), (key1181, 6), (key1218, 6), (key977, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key972, 6), (key1086, 6), (key1086, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1091, 6)]

def rawRow19033 : Integer.Sparse Key := [(key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1218, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1086, 6), (key972, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1091, 6)]

def rawRow19034 : Integer.Sparse Key := [(key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1218, 6), (key1181, 6), (key1181, 6), (key1162, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1091, 6), (key977, 6), (key1086, 6), (key1086, 6), (key972, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key977, 6)]

def rawRow19035 : Integer.Sparse Key := [(key1181, 6), (key1181, 6), (key1181, 6), (key1218, 6), (key977, 6), (key977, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key1162, 6), (key972, 6), (key1086, 6), (key1086, 6), (key1086, 6)]

def rawRow19036 : Integer.Sparse Key := [(key1181, 6), (key1181, 6), (key1218, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key977, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key972, 6), (key1086, 6), (key1086, 6)]

def rawRow19037 : Integer.Sparse Key := [(key1181, 6), (key1218, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key972, 6), (key1086, 6)]

def rawRow19038 : Integer.Sparse Key := [(key1218, 6), (key1181, 6), (key1181, 6), (key1181, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1086, 6), (key1086, 6), (key1086, 6), (key972, 6)]

def rawRow19039 : Integer.Sparse Key := [(key2361, 4), (key2361, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2364, 4), (key2456, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2531, 4), (key2517, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2561, 4)]

def rawRow19040 : Integer.Sparse Key := [(key2361, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2520, 4), (key2517, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2561, 4), (key2520, 4)]

def rawRow19041 : Integer.Sparse Key := [(key2364, 4), (key2361, 4), (key2361, 4), (key2364, 4), (key2364, 4), (key2361, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2531, 4), (key2459, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2520, 4)]

def rawRow19042 : Integer.Sparse Key := [(key2364, 4), (key2364, 4), (key2364, 4), (key2361, 4), (key2361, 4), (key2361, 4), (key2531, 4), (key2531, 4), (key2531, 4), (key2459, 4), (key2459, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2561, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2517, 4), (key2517, 4)]

def rawRow19043 : Integer.Sparse Key := [(key2456, 4), (key2456, 4), (key2459, 4), (key2517, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2517, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2561, 4), (key2361, 4), (key2364, 4), (key2364, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2531, 4), (key2520, 4), (key2520, 4), (key2561, 4)]

def rawRow19044 : Integer.Sparse Key := [(key2456, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2520, 4), (key2361, 4), (key2364, 4), (key2361, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2520, 4), (key2561, 4), (key2520, 4)]

def rawRow19045 : Integer.Sparse Key := [(key2459, 4), (key2456, 4), (key2456, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2364, 4), (key2361, 4), (key2361, 4), (key2531, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2517, 4), (key2364, 4), (key2364, 4), (key2361, 4), (key2531, 4), (key2531, 4), (key2459, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2520, 4), (key2520, 4)]

def rawRow19046 : Integer.Sparse Key := [(key2456, 4), (key2517, 4), (key2520, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2520, 4), (key2361, 4), (key2517, 4), (key2561, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2531, 4), (key2520, 4), (key2561, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2531, 4), (key2520, 4), (key2561, 4), (key2364, 4), (key2459, 4), (key2531, 4)]

def rawRow19047 : Integer.Sparse Key := [(key2456, 4), (key2520, 4), (key2517, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2361, 4), (key2561, 4), (key2517, 4), (key2364, 4), (key2361, 4), (key2531, 4), (key2456, 4), (key2561, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2364, 4), (key2361, 4), (key2531, 4), (key2456, 4), (key2561, 4), (key2520, 4), (key2364, 4), (key2531, 4), (key2459, 4)]

def rawRow19048 : Integer.Sparse Key := [(key2517, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2459, 4), (key2517, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2361, 4), (key2561, 4), (key2456, 4), (key2520, 4), (key2361, 4), (key2561, 4), (key2364, 4), (key2531, 4), (key2456, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2361, 4), (key2561, 4), (key2364, 4), (key2531, 4), (key2459, 4), (key2364, 4), (key2531, 4)]

def rawRow19049 : Integer.Sparse Key := [(key2517, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2459, 4), (key2517, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2561, 4), (key2361, 4), (key2520, 4), (key2456, 4), (key2561, 4), (key2361, 4), (key2531, 4), (key2364, 4), (key2520, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2561, 4), (key2361, 4), (key2531, 4), (key2364, 4), (key2459, 4), (key2531, 4), (key2364, 4)]

def rawRow19050 : Integer.Sparse Key := [(key2520, 4), (key2456, 4), (key2517, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2561, 4), (key2361, 4), (key2517, 4), (key2531, 4), (key2561, 4), (key2364, 4), (key2520, 4), (key2361, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2531, 4), (key2561, 4), (key2364, 4), (key2520, 4), (key2361, 4), (key2456, 4), (key2531, 4), (key2364, 4), (key2459, 4)]

def rawRow19051 : Integer.Sparse Key := [(key2520, 4), (key2517, 4), (key2456, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2456, 4), (key2561, 4), (key2517, 4), (key2361, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2364, 4), (key2456, 4), (key2361, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2364, 4), (key2456, 4), (key2361, 4), (key2531, 4), (key2459, 4), (key2364, 4)]

def rawRow19052 : Integer.Sparse Key := [(key2459, 4), (key2520, 4), (key2520, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2531, 4), (key2561, 4), (key2561, 4), (key2364, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2517, 4), (key2531, 4), (key2531, 4), (key2561, 4), (key2364, 4), (key2364, 4), (key2459, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2456, 4), (key2456, 4)]

def rawRow19053 : Integer.Sparse Key := [(key2520, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2456, 4), (key2561, 4), (key2531, 4), (key2561, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2456, 4), (key2361, 4), (key2456, 4)]

def rawRow19054 : Integer.Sparse Key := [(key2520, 4), (key2520, 4), (key2459, 4), (key2517, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2517, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2361, 4), (key2561, 4), (key2531, 4), (key2531, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2364, 4), (key2456, 4), (key2456, 4), (key2361, 4)]

def rawRow19055 : Integer.Sparse Key := [(key2531, 4), (key2531, 4), (key2531, 4), (key2561, 4), (key2561, 4), (key2561, 4), (key2364, 4), (key2364, 4), (key2364, 4), (key2459, 4), (key2459, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2361, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2517, 4), (key2517, 4)]

def rawRow19056 : Integer.Sparse Key := [(key2531, 4), (key2561, 4), (key2561, 4), (key2531, 4), (key2531, 4), (key2561, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2364, 4), (key2459, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2456, 4)]

def rawRow19057 : Integer.Sparse Key := [(key2561, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2456, 4), (key2517, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2361, 4), (key2456, 4)]

def rawRow19058 : Integer.Sparse Key := [(key2561, 4), (key2561, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2531, 4), (key2520, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2364, 4), (key2517, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2361, 4)]

def rawRow19059 : Integer.Sparse Key := [(key2353, 6), (key2356, 6), (key2356, 6), (key2356, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2527, 6), (key2527, 6), (key2527, 6), (key2558, 6)]

def rawRow19060 : Integer.Sparse Key := [(key2356, 6), (key2353, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2527, 6)]

def rawRow19061 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2353, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2527, 6)]

def rawRow19062 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2356, 6), (key2353, 6), (key2513, 6), (key2513, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2527, 6)]

def rawRow19063 : Integer.Sparse Key := [(key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2353, 6), (key2356, 6), (key2356, 6), (key2448, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6)]

def rawRow19064 : Integer.Sparse Key := [(key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2353, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2451, 6)]

def rawRow19065 : Integer.Sparse Key := [(key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2356, 6), (key2353, 6), (key2513, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2451, 6)]

def rawRow19066 : Integer.Sparse Key := [(key2448, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2353, 6), (key2356, 6), (key2448, 6), (key2513, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2513, 6)]

def rawRow19067 : Integer.Sparse Key := [(key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2353, 6), (key2513, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2513, 6), (key2451, 6)]

def rawRow19068 : Integer.Sparse Key := [(key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2353, 6), (key2558, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2513, 6)]

def rawRow19069 : Integer.Sparse Key := [(key2513, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2558, 6), (key2353, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6)]

def rawRow19070 : Integer.Sparse Key := [(key2451, 6), (key2513, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2513, 6), (key2353, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6)]

def rawRow19071 : Integer.Sparse Key := [(key2513, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2513, 6), (key2356, 6), (key2448, 6), (key2353, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2356, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19072 : Integer.Sparse Key := [(key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2513, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6)]

def rawRow19073 : Integer.Sparse Key := [(key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2451, 6)]

def rawRow19074 : Integer.Sparse Key := [(key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2356, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2356, 6)]

def rawRow19075 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2513, 6), (key2513, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2448, 6)]

def rawRow19076 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2448, 6)]

def rawRow19077 : Integer.Sparse Key := [(key2527, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2448, 6)]

def rawRow19078 : Integer.Sparse Key := [(key2558, 6), (key2527, 6), (key2527, 6), (key2527, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2353, 6)]

def rawRow19079 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2372, 6), (key2385, 6), (key2400, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2475, 6), (key2432, 6), (key2498, 6), (key2498, 6), (key2498, 6)]

def rawRow19080 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2385, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2432, 6), (key2498, 6), (key2498, 6)]

def rawRow19081 : Integer.Sparse Key := [(key2372, 6), (key2385, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2432, 6), (key2498, 6)]

def rawRow19082 : Integer.Sparse Key := [(key2385, 6), (key2372, 6), (key2372, 6), (key2372, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2498, 6), (key2498, 6), (key2498, 6), (key2432, 6)]

def rawRow19083 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2400, 6), (key2432, 6), (key2372, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2498, 6), (key2385, 6), (key2475, 6), (key2475, 6), (key2475, 6)]

def rawRow19084 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2432, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2385, 6), (key2475, 6), (key2475, 6)]

def rawRow19085 : Integer.Sparse Key := [(key2400, 6), (key2432, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2385, 6), (key2475, 6)]

def rawRow19086 : Integer.Sparse Key := [(key2432, 6), (key2400, 6), (key2400, 6), (key2400, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2475, 6), (key2475, 6), (key2475, 6), (key2385, 6)]

def rawRow19087 : Integer.Sparse Key := [(key2466, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2372, 6), (key2372, 6), (key2385, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2432, 6), (key2498, 6), (key2498, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2466, 6)]

def rawRow19088 : Integer.Sparse Key := [(key2466, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2385, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2432, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2466, 6)]

def rawRow19089 : Integer.Sparse Key := [(key2475, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2385, 6), (key2372, 6), (key2372, 6), (key2475, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2400, 6), (key2498, 6), (key2498, 6), (key2432, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2400, 6)]

def rawRow19090 : Integer.Sparse Key := [(key2466, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2400, 6), (key2400, 6), (key2432, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2385, 6), (key2475, 6), (key2475, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2466, 6)]

def rawRow19091 : Integer.Sparse Key := [(key2466, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2432, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2385, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2466, 6)]

def rawRow19092 : Integer.Sparse Key := [(key2498, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2432, 6), (key2400, 6), (key2400, 6), (key2498, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2372, 6), (key2475, 6), (key2475, 6), (key2385, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2372, 6)]

def rawRow19093 : Integer.Sparse Key := [(key2466, 6), (key2475, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2372, 6), (key2385, 6), (key2400, 6), (key2475, 6), (key2432, 6), (key2498, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2400, 6), (key2466, 6)]

def rawRow19094 : Integer.Sparse Key := [(key2475, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2385, 6), (key2372, 6), (key2475, 6), (key2400, 6), (key2498, 6), (key2432, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2400, 6)]

def rawRow19095 : Integer.Sparse Key := [(key2466, 6), (key2498, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2400, 6), (key2432, 6), (key2372, 6), (key2498, 6), (key2385, 6), (key2475, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2372, 6), (key2466, 6)]

def rawRow19096 : Integer.Sparse Key := [(key2498, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2432, 6), (key2400, 6), (key2498, 6), (key2372, 6), (key2475, 6), (key2385, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2372, 6)]

def rawRow19097 : Integer.Sparse Key := [(key2475, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2385, 6), (key2432, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2400, 6)]

def rawRow19098 : Integer.Sparse Key := [(key2498, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2432, 6), (key2385, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2372, 6)]

def rawRow19099 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 24), (key1102, 24), (key1102, 24)]

def rawRow19100 : Integer.Sparse Key := [(key989, 24), (key1102, 24), (key1024, 24), (key1102, 24), (key1102, 24)]

def rawRow19101 : Integer.Sparse Key := [(key989, 24), (key1102, 24), (key1102, 24), (key1024, 24), (key1102, 24)]

def rawRow19102 : Integer.Sparse Key := [(key989, 24), (key1102, 24), (key1102, 24), (key1102, 24), (key1024, 24)]

def rawRow19103 : Integer.Sparse Key := [(key1024, 24), (key989, 24), (key1102, 24), (key1102, 24), (key1102, 24)]

def rawRow19104 : Integer.Sparse Key := [(key1024, 24), (key1102, 24), (key989, 24), (key1102, 24), (key1102, 24)]

def rawRow19105 : Integer.Sparse Key := [(key1024, 24), (key1102, 24), (key1102, 24), (key989, 24), (key1102, 24)]

def rawRow19106 : Integer.Sparse Key := [(key1024, 24), (key1102, 24), (key1102, 24), (key1102, 24), (key989, 24)]

def rawRow19107 : Integer.Sparse Key := [(key1102, 24), (key989, 24), (key1024, 24), (key1102, 24), (key1102, 24)]

def rawRow19108 : Integer.Sparse Key := [(key1102, 24), (key989, 24), (key1102, 24), (key1024, 24), (key1102, 24)]

def rawRow19109 : Integer.Sparse Key := [(key1102, 24), (key989, 24), (key1102, 24), (key1102, 24), (key1024, 24)]

def rawRow19110 : Integer.Sparse Key := [(key1102, 24), (key1024, 24), (key989, 24), (key1102, 24), (key1102, 24)]

def rawRow19111 : Integer.Sparse Key := [(key1102, 24), (key1024, 24), (key1102, 24), (key989, 24), (key1102, 24)]

def rawRow19112 : Integer.Sparse Key := [(key1102, 24), (key1024, 24), (key1102, 24), (key1102, 24), (key989, 24)]

def rawRow19113 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key989, 24), (key1024, 24), (key1102, 24)]

def rawRow19114 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key989, 24), (key1102, 24), (key1024, 24)]

def rawRow19115 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1024, 24), (key989, 24), (key1102, 24)]

def rawRow19116 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1024, 24), (key1102, 24), (key989, 24)]

def rawRow19117 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1102, 24), (key989, 24), (key1024, 24)]

def rawRow19118 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1102, 24), (key1024, 24), (key989, 24)]

def rawRow19119 : Integer.Sparse Key := [(key2610, 2), (key2610, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2635, 2), (key2635, 2), (key2665, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2789, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2721, 2), (key2721, 2), (key2721, 2), (key2824, 2), (key2824, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2)]

def rawRow19120 : Integer.Sparse Key := [(key2626, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2721, 2), (key2824, 2), (key2824, 2), (key2865, 2), (key2865, 2)]

def rawRow19121 : Integer.Sparse Key := [(key2626, 2), (key2635, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2610, 2), (key2626, 2), (key2780, 2), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2803, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2721, 2), (key2824, 2)]

def rawRow19122 : Integer.Sparse Key := [(key2635, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2610, 2), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2700, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2803, 2), (key2700, 2), (key2865, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2824, 2), (key2721, 2)]

def rawRow19123 : Integer.Sparse Key := [(key2665, 2), (key2665, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2721, 2), (key2721, 2), (key2610, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2824, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2635, 2), (key2635, 2), (key2789, 2), (key2789, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2)]

def rawRow19124 : Integer.Sparse Key := [(key2700, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2635, 2), (key2789, 2), (key2789, 2), (key2855, 2), (key2855, 2)]

def rawRow19125 : Integer.Sparse Key := [(key2700, 2), (key2721, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2635, 2), (key2789, 2)]

def rawRow19126 : Integer.Sparse Key := [(key2721, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2626, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2626, 2), (key2855, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2635, 2)]

def rawRow19127 : Integer.Sparse Key := [(key2780, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2721, 2), (key2865, 2), (key2865, 2), (key2610, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2635, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2855, 2), (key2855, 2), (key2721, 2), (key2721, 2), (key2824, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

def rawRow19128 : Integer.Sparse Key := [(key2780, 2), (key2789, 2), (key2780, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2626, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2721, 2), (key2824, 2), (key2626, 2), (key2610, 2), (key2626, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2803, 2)]

def rawRow19129 : Integer.Sparse Key := [(key2789, 2), (key2780, 2), (key2780, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2803, 2), (key2865, 2), (key2865, 2), (key2824, 2), (key2635, 2), (key2626, 2), (key2626, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2635, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2610, 2), (key2789, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2665, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2700, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2824, 2), (key2721, 2), (key2626, 2), (key2626, 2), (key2610, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2803, 2), (key2700, 2)]

def rawRow19130 : Integer.Sparse Key := [(key2803, 2), (key2803, 2), (key2824, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2626, 2), (key2626, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2855, 2), (key2665, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2721, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2635, 2), (key2789, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2)]

def rawRow19131 : Integer.Sparse Key := [(key2803, 2), (key2824, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2780, 2)]

def rawRow19132 : Integer.Sparse Key := [(key2824, 2), (key2803, 2), (key2803, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2855, 2), (key2855, 2), (key2789, 2), (key2721, 2), (key2700, 2), (key2700, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2721, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2665, 2), (key2824, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2610, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2626, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2635, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2626, 2)]

def rawRow19133 : Integer.Sparse Key := [(key2853, 2), (key2855, 2), (key2865, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2855, 2), (key2824, 2), (key2865, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2855, 2), (key2721, 2), (key2865, 2), (key2626, 2), (key2700, 2), (key2853, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2855, 2), (key2824, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2855, 2), (key2721, 2), (key2865, 2), (key2610, 2), (key2635, 2), (key2665, 2), (key2789, 2), (key2721, 2), (key2824, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2780, 2), (key2700, 2), (key2803, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2853, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2780, 2), (key2700, 2), (key2803, 2)]

def rawRow19134 : Integer.Sparse Key := [(key2855, 2), (key2853, 2), (key2865, 2), (key2789, 2), (key2780, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2824, 2), (key2780, 2), (key2853, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2635, 2), (key2626, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2721, 2), (key2626, 2), (key2853, 2), (key2700, 2), (key2789, 2), (key2780, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2824, 2), (key2635, 2), (key2626, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2721, 2), (key2635, 2), (key2610, 2), (key2789, 2), (key2665, 2), (key2824, 2), (key2721, 2), (key2626, 2), (key2610, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2700, 2), (key2780, 2), (key2853, 2), (key2803, 2), (key2626, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2610, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2700, 2)]

def rawRow19135 : Integer.Sparse Key := [(key2853, 2), (key2865, 2), (key2855, 2), (key2803, 2), (key2824, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2700, 2), (key2626, 2), (key2853, 2), (key2803, 2), (key2824, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2665, 2), (key2721, 2), (key2610, 2), (key2824, 2), (key2635, 2), (key2789, 2), (key2665, 2), (key2700, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2853, 2), (key2665, 2), (key2700, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2780, 2)]

def rawRow19136 : Integer.Sparse Key := [(key2865, 2), (key2853, 2), (key2855, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2853, 2), (key2855, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2855, 2), (key2789, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2855, 2), (key2635, 2), (key2721, 2), (key2665, 2), (key2824, 2), (key2610, 2), (key2789, 2), (key2635, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2780, 2), (key2626, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2780, 2), (key2626, 2)]

def rawRow19137 : Integer.Sparse Key := [(key2855, 2), (key2865, 2), (key2853, 2), (key2855, 2), (key2865, 2), (key2789, 2), (key2824, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2855, 2), (key2865, 2), (key2853, 2), (key2855, 2), (key2865, 2), (key2635, 2), (key2721, 2), (key2626, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2855, 2), (key2865, 2), (key2789, 2), (key2824, 2), (key2780, 2), (key2803, 2), (key2855, 2), (key2865, 2), (key2635, 2), (key2721, 2), (key2626, 2), (key2700, 2), (key2789, 2), (key2824, 2), (key2635, 2), (key2721, 2), (key2610, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2626, 2), (key2700, 2), (key2610, 2), (key2665, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2780, 2), (key2803, 2), (key2626, 2), (key2700, 2), (key2610, 2), (key2665, 2)]

def rawRow19138 : Integer.Sparse Key := [(key2865, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2824, 2), (key2789, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2803, 2), (key2780, 2), (key2865, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2721, 2), (key2635, 2), (key2700, 2), (key2626, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2865, 2), (key2855, 2), (key2824, 2), (key2789, 2), (key2803, 2), (key2780, 2), (key2865, 2), (key2855, 2), (key2721, 2), (key2635, 2), (key2700, 2), (key2626, 2), (key2824, 2), (key2789, 2), (key2721, 2), (key2635, 2), (key2665, 2), (key2610, 2), (key2803, 2), (key2780, 2), (key2700, 2), (key2626, 2), (key2665, 2), (key2610, 2), (key2853, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2803, 2), (key2780, 2), (key2700, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

def rawRow19139 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 24), (key2837, 24), (key2837, 24)]

def rawRow19140 : Integer.Sparse Key := [(key2368, 24), (key2837, 24), (key2760, 24), (key2837, 24), (key2837, 24)]

def rawRow19141 : Integer.Sparse Key := [(key2368, 24), (key2837, 24), (key2837, 24), (key2760, 24), (key2837, 24)]

def rawRow19142 : Integer.Sparse Key := [(key2368, 24), (key2837, 24), (key2837, 24), (key2837, 24), (key2760, 24)]

def rawRow19143 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 24), (key2837, 24), (key2837, 24)]

def rawRow19144 : Integer.Sparse Key := [(key2396, 24), (key2837, 24), (key2581, 24), (key2837, 24), (key2837, 24)]

def rawRow19145 : Integer.Sparse Key := [(key2396, 24), (key2837, 24), (key2837, 24), (key2581, 24), (key2837, 24)]

def rawRow19146 : Integer.Sparse Key := [(key2396, 24), (key2837, 24), (key2837, 24), (key2837, 24), (key2581, 24)]

def rawRow19147 : Integer.Sparse Key := [(key2462, 24), (key2368, 24), (key2760, 24), (key2837, 24), (key2837, 24)]

def rawRow19148 : Integer.Sparse Key := [(key2462, 24), (key2368, 24), (key2837, 24), (key2760, 24), (key2837, 24)]

def rawRow19149 : Integer.Sparse Key := [(key2462, 24), (key2368, 24), (key2837, 24), (key2837, 24), (key2760, 24)]

def rawRow19150 : Integer.Sparse Key := [(key2462, 24), (key2396, 24), (key2581, 24), (key2837, 24), (key2837, 24)]

def rawRow19151 : Integer.Sparse Key := [(key2462, 24), (key2396, 24), (key2837, 24), (key2581, 24), (key2837, 24)]

def rawRow19152 : Integer.Sparse Key := [(key2462, 24), (key2396, 24), (key2837, 24), (key2837, 24), (key2581, 24)]

def rawRow19153 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2368, 24), (key2760, 24), (key2837, 24)]

def rawRow19154 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2368, 24), (key2837, 24), (key2760, 24)]

def rawRow19155 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2396, 24), (key2581, 24), (key2837, 24)]

def rawRow19156 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2396, 24), (key2837, 24), (key2581, 24)]

def rawRow19157 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2462, 24), (key2368, 24), (key2760, 24)]

def rawRow19158 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2462, 24), (key2396, 24), (key2581, 24)]

def rawRow19159 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key995, 6), (key1011, 6), (key1030, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1119, 6), (key1067, 6), (key1146, 6), (key1146, 6), (key1146, 6)]

def rawRow19160 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key1011, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1067, 6), (key1146, 6), (key1146, 6)]

def rawRow19161 : Integer.Sparse Key := [(key995, 6), (key1011, 6), (key995, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key1067, 6), (key1146, 6)]

def rawRow19162 : Integer.Sparse Key := [(key1011, 6), (key995, 6), (key995, 6), (key995, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key1146, 6), (key1146, 6), (key1146, 6), (key1067, 6)]

def rawRow19163 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1030, 6), (key1067, 6), (key995, 6), (key995, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key1146, 6), (key1011, 6), (key1119, 6), (key1119, 6), (key1119, 6)]

def rawRow19164 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1067, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key995, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1011, 6), (key1119, 6), (key1119, 6)]

def rawRow19165 : Integer.Sparse Key := [(key1030, 6), (key1067, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1011, 6), (key1119, 6)]

def rawRow19166 : Integer.Sparse Key := [(key1067, 6), (key1030, 6), (key1030, 6), (key1030, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1119, 6), (key1119, 6), (key1119, 6), (key1011, 6)]

def rawRow19167 : Integer.Sparse Key := [(key1108, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key995, 6), (key995, 6), (key1011, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1067, 6), (key1146, 6), (key1146, 6), (key995, 6), (key1030, 6), (key1108, 6), (key1108, 6)]

def rawRow19168 : Integer.Sparse Key := [(key1108, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1011, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key1067, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1030, 6), (key1108, 6)]

def rawRow19169 : Integer.Sparse Key := [(key1119, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1011, 6), (key995, 6), (key995, 6), (key1119, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1030, 6), (key1146, 6), (key1146, 6), (key1067, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1030, 6)]

def rawRow19170 : Integer.Sparse Key := [(key1108, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1030, 6), (key1030, 6), (key1067, 6), (key995, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key1011, 6), (key1119, 6), (key1119, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1108, 6)]

def rawRow19171 : Integer.Sparse Key := [(key1108, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1067, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1011, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1108, 6)]

def rawRow19172 : Integer.Sparse Key := [(key1146, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1067, 6), (key1030, 6), (key1030, 6), (key1146, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1108, 6), (key995, 6), (key1119, 6), (key1119, 6), (key1011, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key995, 6)]

def rawRow19173 : Integer.Sparse Key := [(key1108, 6), (key1119, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key995, 6), (key1011, 6), (key1030, 6), (key1119, 6), (key1067, 6), (key1146, 6), (key995, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1030, 6), (key1108, 6)]

def rawRow19174 : Integer.Sparse Key := [(key1119, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key1011, 6), (key995, 6), (key1119, 6), (key1030, 6), (key1146, 6), (key1067, 6), (key995, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1030, 6)]

def rawRow19175 : Integer.Sparse Key := [(key1108, 6), (key1146, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1030, 6), (key1067, 6), (key995, 6), (key1146, 6), (key1011, 6), (key1119, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key995, 6), (key1108, 6)]

def rawRow19176 : Integer.Sparse Key := [(key1146, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1067, 6), (key1030, 6), (key1146, 6), (key995, 6), (key1119, 6), (key1011, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key995, 6)]

def rawRow19177 : Integer.Sparse Key := [(key1119, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key1011, 6), (key1067, 6), (key995, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1030, 6)]

def rawRow19178 : Integer.Sparse Key := [(key1146, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1067, 6), (key1011, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key995, 6)]

def rawRow19179 : Integer.Sparse Key := [(key2377, 4), (key2377, 4), (key2377, 4), (key2389, 4), (key2389, 4), (key2389, 4), (key2405, 4), (key2405, 4), (key2405, 4), (key2471, 4), (key2471, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2436, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2518, 4), (key2518, 4)]

def rawRow19180 : Integer.Sparse Key := [(key2377, 4), (key2389, 4), (key2389, 4), (key2377, 4), (key2377, 4), (key2389, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2405, 4), (key2471, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2502, 4)]

def rawRow19181 : Integer.Sparse Key := [(key2389, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2502, 4), (key2518, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2436, 4), (key2502, 4)]

def rawRow19182 : Integer.Sparse Key := [(key2389, 4), (key2389, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2377, 4), (key2479, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2405, 4), (key2518, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2436, 4)]

def rawRow19183 : Integer.Sparse Key := [(key2405, 4), (key2405, 4), (key2405, 4), (key2436, 4), (key2436, 4), (key2436, 4), (key2377, 4), (key2377, 4), (key2377, 4), (key2471, 4), (key2471, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2389, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2518, 4), (key2518, 4)]

def rawRow19184 : Integer.Sparse Key := [(key2405, 4), (key2436, 4), (key2436, 4), (key2405, 4), (key2405, 4), (key2436, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2377, 4), (key2471, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2479, 4)]

def rawRow19185 : Integer.Sparse Key := [(key2436, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2479, 4), (key2518, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2389, 4), (key2479, 4)]

def rawRow19186 : Integer.Sparse Key := [(key2436, 4), (key2436, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2405, 4), (key2502, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2377, 4), (key2518, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2389, 4)]

def rawRow19187 : Integer.Sparse Key := [(key2471, 4), (key2479, 4), (key2479, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2377, 4), (key2389, 4), (key2389, 4), (key2405, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2518, 4), (key2377, 4), (key2377, 4), (key2389, 4), (key2405, 4), (key2405, 4), (key2471, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2502, 4), (key2502, 4)]

def rawRow19188 : Integer.Sparse Key := [(key2479, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2502, 4), (key2389, 4), (key2377, 4), (key2389, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2502, 4), (key2436, 4), (key2502, 4)]

def rawRow19189 : Integer.Sparse Key := [(key2479, 4), (key2479, 4), (key2471, 4), (key2518, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2518, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2436, 4), (key2389, 4), (key2377, 4), (key2377, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2405, 4), (key2502, 4), (key2502, 4), (key2436, 4)]

def rawRow19190 : Integer.Sparse Key := [(key2471, 4), (key2502, 4), (key2502, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2405, 4), (key2436, 4), (key2436, 4), (key2377, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2518, 4), (key2405, 4), (key2405, 4), (key2436, 4), (key2377, 4), (key2377, 4), (key2471, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2479, 4), (key2479, 4)]

def rawRow19191 : Integer.Sparse Key := [(key2502, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2479, 4), (key2436, 4), (key2405, 4), (key2436, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2479, 4), (key2389, 4), (key2479, 4)]

def rawRow19192 : Integer.Sparse Key := [(key2502, 4), (key2502, 4), (key2471, 4), (key2518, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2518, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2389, 4), (key2436, 4), (key2405, 4), (key2405, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2377, 4), (key2479, 4), (key2479, 4), (key2389, 4)]

def rawRow19193 : Integer.Sparse Key := [(key2479, 4), (key2502, 4), (key2518, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2389, 4), (key2436, 4), (key2518, 4), (key2377, 4), (key2389, 4), (key2405, 4), (key2479, 4), (key2436, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2377, 4), (key2389, 4), (key2405, 4), (key2479, 4), (key2436, 4), (key2502, 4), (key2377, 4), (key2405, 4), (key2471, 4)]

def rawRow19194 : Integer.Sparse Key := [(key2479, 4), (key2518, 4), (key2502, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2502, 4), (key2389, 4), (key2518, 4), (key2436, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2405, 4), (key2502, 4), (key2436, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2405, 4), (key2502, 4), (key2436, 4), (key2377, 4), (key2471, 4), (key2405, 4)]

def rawRow19195 : Integer.Sparse Key := [(key2502, 4), (key2479, 4), (key2518, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2436, 4), (key2389, 4), (key2518, 4), (key2405, 4), (key2436, 4), (key2377, 4), (key2502, 4), (key2389, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2405, 4), (key2436, 4), (key2377, 4), (key2502, 4), (key2389, 4), (key2479, 4), (key2405, 4), (key2377, 4), (key2471, 4)]

def rawRow19196 : Integer.Sparse Key := [(key2502, 4), (key2518, 4), (key2479, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2479, 4), (key2436, 4), (key2518, 4), (key2389, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2377, 4), (key2479, 4), (key2389, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2377, 4), (key2479, 4), (key2389, 4), (key2405, 4), (key2471, 4), (key2377, 4)]

def rawRow19197 : Integer.Sparse Key := [(key2518, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2471, 4), (key2518, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2389, 4), (key2436, 4), (key2479, 4), (key2502, 4), (key2389, 4), (key2436, 4), (key2377, 4), (key2405, 4), (key2479, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2389, 4), (key2436, 4), (key2377, 4), (key2405, 4), (key2471, 4), (key2377, 4), (key2405, 4)]

def rawRow19198 : Integer.Sparse Key := [(key2518, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2471, 4), (key2518, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2436, 4), (key2389, 4), (key2502, 4), (key2479, 4), (key2436, 4), (key2389, 4), (key2405, 4), (key2377, 4), (key2502, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2436, 4), (key2389, 4), (key2405, 4), (key2377, 4), (key2471, 4), (key2405, 4), (key2377, 4)]

def rawRow19199 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2369, 6), (key2384, 6), (key2397, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2474, 6), (key2431, 6), (key2497, 6), (key2497, 6), (key2497, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19200 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2384, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2431, 6), (key2497, 6), (key2497, 6)]

def rawRow19201 : Integer.Sparse Key := [(key2369, 6), (key2384, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2431, 6), (key2497, 6)]

def rawRow19202 : Integer.Sparse Key := [(key2384, 6), (key2369, 6), (key2369, 6), (key2369, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2497, 6), (key2497, 6), (key2497, 6), (key2431, 6)]

def rawRow19203 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2397, 6), (key2431, 6), (key2369, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2497, 6), (key2384, 6), (key2474, 6), (key2474, 6), (key2474, 6)]

def rawRow19204 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2431, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2384, 6), (key2474, 6), (key2474, 6)]

def rawRow19205 : Integer.Sparse Key := [(key2397, 6), (key2431, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2384, 6), (key2474, 6)]

def rawRow19206 : Integer.Sparse Key := [(key2431, 6), (key2397, 6), (key2397, 6), (key2397, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2474, 6), (key2474, 6), (key2474, 6), (key2384, 6)]

def rawRow19207 : Integer.Sparse Key := [(key2463, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2369, 6), (key2369, 6), (key2384, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2431, 6), (key2497, 6), (key2497, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2463, 6)]

def rawRow19208 : Integer.Sparse Key := [(key2463, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2384, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2431, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2463, 6)]

def rawRow19209 : Integer.Sparse Key := [(key2474, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2384, 6), (key2369, 6), (key2369, 6), (key2474, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2397, 6), (key2497, 6), (key2497, 6), (key2431, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2397, 6)]

def rawRow19210 : Integer.Sparse Key := [(key2463, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2397, 6), (key2397, 6), (key2431, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2384, 6), (key2474, 6), (key2474, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2463, 6)]

def rawRow19211 : Integer.Sparse Key := [(key2463, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2431, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2384, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2463, 6)]

def rawRow19212 : Integer.Sparse Key := [(key2497, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2431, 6), (key2397, 6), (key2397, 6), (key2497, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2369, 6), (key2474, 6), (key2474, 6), (key2384, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2369, 6)]

def rawRow19213 : Integer.Sparse Key := [(key2463, 6), (key2474, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2369, 6), (key2384, 6), (key2397, 6), (key2474, 6), (key2431, 6), (key2497, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2397, 6), (key2463, 6)]

def rawRow19214 : Integer.Sparse Key := [(key2474, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2384, 6), (key2369, 6), (key2474, 6), (key2397, 6), (key2497, 6), (key2431, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2397, 6)]

def rawRow19215 : Integer.Sparse Key := [(key2463, 6), (key2497, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2397, 6), (key2431, 6), (key2369, 6), (key2497, 6), (key2384, 6), (key2474, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2369, 6), (key2463, 6)]

def rawRow19216 : Integer.Sparse Key := [(key2497, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2431, 6), (key2397, 6), (key2497, 6), (key2369, 6), (key2474, 6), (key2384, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2369, 6)]

def rawRow19217 : Integer.Sparse Key := [(key2474, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2384, 6), (key2431, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2397, 6)]

def rawRow19218 : Integer.Sparse Key := [(key2497, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2431, 6), (key2384, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2369, 6)]

def rawRow19219 : Integer.Sparse Key := [(key2606, 6), (key2622, 6), (key2622, 6), (key2622, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2776, 6), (key2776, 6), (key2776, 6), (key2799, 6), (key2799, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6)]

def rawRow19220 : Integer.Sparse Key := [(key2622, 6), (key2606, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2776, 6), (key2799, 6), (key2799, 6), (key2849, 6), (key2849, 6)]

def rawRow19221 : Integer.Sparse Key := [(key2622, 6), (key2622, 6), (key2606, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2776, 6), (key2799, 6)]

def rawRow19222 : Integer.Sparse Key := [(key2622, 6), (key2622, 6), (key2622, 6), (key2606, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2849, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2776, 6)]

def rawRow19223 : Integer.Sparse Key := [(key2661, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2606, 6), (key2799, 6), (key2799, 6), (key2799, 6), (key2622, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6)]

def rawRow19224 : Integer.Sparse Key := [(key2696, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2799, 6), (key2606, 6), (key2799, 6), (key2799, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2849, 6), (key2849, 6)]

def rawRow19225 : Integer.Sparse Key := [(key2696, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2799, 6), (key2799, 6), (key2606, 6), (key2799, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2622, 6), (key2696, 6)]

def rawRow19226 : Integer.Sparse Key := [(key2696, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2799, 6), (key2799, 6), (key2606, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2622, 6)]

def rawRow19227 : Integer.Sparse Key := [(key2776, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2606, 6), (key2622, 6), (key2622, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2776, 6), (key2776, 6), (key2799, 6), (key2799, 6), (key2849, 6), (key2849, 6)]

def rawRow19228 : Integer.Sparse Key := [(key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2606, 6), (key2622, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2776, 6), (key2799, 6)]

def rawRow19229 : Integer.Sparse Key := [(key2776, 6), (key2849, 6), (key2849, 6), (key2799, 6), (key2622, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2622, 6), (key2606, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2776, 6)]

def rawRow19230 : Integer.Sparse Key := [(key2799, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2849, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2606, 6), (key2799, 6), (key2799, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2849, 6), (key2849, 6)]

def rawRow19231 : Integer.Sparse Key := [(key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2799, 6), (key2606, 6), (key2799, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2622, 6), (key2696, 6)]

def rawRow19232 : Integer.Sparse Key := [(key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2799, 6), (key2606, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2622, 6)]

def rawRow19233 : Integer.Sparse Key := [(key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2606, 6), (key2622, 6), (key2661, 6), (key2696, 6), (key2776, 6), (key2799, 6)]

def rawRow19234 : Integer.Sparse Key := [(key2849, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2606, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2776, 6)]

def rawRow19235 : Integer.Sparse Key := [(key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2661, 6), (key2696, 6), (key2606, 6), (key2799, 6), (key2622, 6), (key2696, 6)]

def rawRow19236 : Integer.Sparse Key := [(key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2606, 6), (key2696, 6), (key2622, 6)]

def rawRow19237 : Integer.Sparse Key := [(key2849, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2776, 6), (key2799, 6), (key2622, 6), (key2696, 6), (key2606, 6), (key2661, 6)]

def rawRow19238 : Integer.Sparse Key := [(key2849, 6), (key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2799, 6), (key2776, 6), (key2696, 6), (key2622, 6), (key2661, 6), (key2606, 6)]

def rawRow19239 : Integer.Sparse Key := [(key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6)]

def rawRow19240 : Integer.Sparse Key := [(key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6)]

def rawRow19241 : Integer.Sparse Key := [(key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6)]

def rawRow19242 : Integer.Sparse Key := [(key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1884, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1850, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6)]

def rawRow19243 : Integer.Sparse Key := [(key1884, 6), (key1884, 6), (key1884, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1850, 6), (key1850, 6), (key1850, 6)]

def rawRow19244 : Integer.Sparse Key := [(key685, 24), (key685, 24), (key685, 24), (key685, 24), (key692, 24)]

def rawRow19245 : Integer.Sparse Key := [(key685, 24), (key685, 24), (key685, 24), (key692, 24), (key685, 24)]

def rawRow19246 : Integer.Sparse Key := [(key685, 24), (key685, 24), (key692, 24), (key685, 24), (key685, 24)]

def rawRow19247 : Integer.Sparse Key := [(key685, 24), (key692, 24), (key685, 24), (key685, 24), (key685, 24)]

def rawRow19248 : Integer.Sparse Key := [(key692, 24), (key685, 24), (key685, 24), (key685, 24), (key685, 24)]

def rawRow19249 : Integer.Sparse Key := [(key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1867, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1859, 2), (key1867, 2), (key1859, 2), (key1877, 2), (key1867, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1867, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1867, 2), (key1877, 2)]

def rawRow19250 : Integer.Sparse Key := [(key1861, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1867, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1867, 2)]

def rawRow19251 : Integer.Sparse Key := [(key1861, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2)]

def rawRow19252 : Integer.Sparse Key := [(key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2)]

def rawRow19253 : Integer.Sparse Key := [(key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2)]

def rawRow19254 : Integer.Sparse Key := [(key1957, 24), (key1957, 24), (key1957, 24), (key1957, 24), (key1969, 24)]

def rawRow19255 : Integer.Sparse Key := [(key1957, 24), (key1957, 24), (key1957, 24), (key1969, 24), (key1957, 24)]

def rawRow19256 : Integer.Sparse Key := [(key1957, 24), (key1957, 24), (key1969, 24), (key1957, 24), (key1957, 24)]

def rawRow19257 : Integer.Sparse Key := [(key1957, 24), (key1969, 24), (key1957, 24), (key1957, 24), (key1957, 24)]

def rawRow19258 : Integer.Sparse Key := [(key1969, 24), (key1957, 24), (key1957, 24), (key1957, 24), (key1957, 24)]

def rawRow19259 : Integer.Sparse Key := [(key617, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, 6), (key617, 6), (key619, 6), (key617, 6), (key645, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key645, 6)]

def rawRow19260 : Integer.Sparse Key := [(key619, 6), (key617, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, 6), (key617, 6), (key645, 6), (key617, 6), (key645, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6)]

def rawRow19261 : Integer.Sparse Key := [(key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key645, 6), (key645, 6), (key619, 6), (key619, 6), (key617, 6), (key617, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6)]

def rawRow19262 : Integer.Sparse Key := [(key619, 6), (key619, 6), (key619, 6), (key617, 6), (key645, 6), (key645, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key617, 6), (key617, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6)]

def rawRow19263 : Integer.Sparse Key := [(key645, 6), (key645, 6), (key645, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key617, 6), (key617, 6), (key617, 6)]

def rawRow19264 : Integer.Sparse Key := [(key1851, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4)]

def rawRow19265 : Integer.Sparse Key := [(key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4), (key1855, 4)]

def rawRow19266 : Integer.Sparse Key := [(key1855, 4), (key1851, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4)]

def rawRow19267 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow19268 : Integer.Sparse Key := [(key1886, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow19269 : Integer.Sparse Key := [(key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6)]

def rawRow19270 : Integer.Sparse Key := [(key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6)]

def rawRow19271 : Integer.Sparse Key := [(key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6)]

def rawRow19272 : Integer.Sparse Key := [(key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1953, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1932, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6)]

def rawRow19273 : Integer.Sparse Key := [(key1953, 6), (key1953, 6), (key1953, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1932, 6), (key1932, 6), (key1932, 6)]

def rawRow19274 : Integer.Sparse Key := [(key1958, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1966, 6), (key1960, 6), (key1966, 6)]

def rawRow19275 : Integer.Sparse Key := [(key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1966, 6), (key1960, 6)]

def rawRow19276 : Integer.Sparse Key := [(key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1966, 6), (key1960, 6), (key1960, 6), (key1958, 6), (key1958, 6)]

def rawRow19277 : Integer.Sparse Key := [(key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1966, 6), (key1966, 6), (key1960, 6), (key1960, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6)]

def rawRow19278 : Integer.Sparse Key := [(key1966, 6), (key1966, 6), (key1966, 6), (key1966, 6), (key1960, 6), (key1960, 6), (key1960, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6)]

def rawRow19279 : Integer.Sparse Key := [(key288, 24), (key289, 24), (key289, 24), (key289, 24), (key289, 24)]

def rawRow19280 : Integer.Sparse Key := [(key289, 24), (key288, 24), (key289, 24), (key289, 24), (key289, 24)]

def rawRow19281 : Integer.Sparse Key := [(key289, 24), (key289, 24), (key288, 24), (key289, 24), (key289, 24)]

def rawRow19282 : Integer.Sparse Key := [(key289, 24), (key289, 24), (key289, 24), (key288, 24), (key289, 24)]

def rawRow19283 : Integer.Sparse Key := [(key289, 24), (key289, 24), (key289, 24), (key289, 24), (key288, 24)]

def rawRow19284 : Integer.Sparse Key := [(key2416, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2491, 6)]

def rawRow19285 : Integer.Sparse Key := [(key2416, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2416, 6), (key2491, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2491, 6)]

def rawRow19286 : Integer.Sparse Key := [(key2423, 6), (key2416, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2491, 6), (key2423, 6)]

def rawRow19287 : Integer.Sparse Key := [(key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6)]

def rawRow19288 : Integer.Sparse Key := [(key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6)]

def rawRow19289 : Integer.Sparse Key := [(key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6)]

def rawRow19290 : Integer.Sparse Key := [(key2489, 6), (key2491, 6), (key2491, 6), (key2491, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2416, 6), (key2416, 6), (key2416, 6), (key2489, 6)]

def rawRow19291 : Integer.Sparse Key := [(key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2416, 6)]

def rawRow19292 : Integer.Sparse Key := [(key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2416, 6)]

def rawRow19293 : Integer.Sparse Key := [(key2491, 6), (key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2416, 6), (key2416, 6)]

def rawRow19294 : Integer.Sparse Key := [(key1045, 24), (key1045, 24), (key1045, 24), (key1131, 24), (key1131, 24)]

def rawRow19295 : Integer.Sparse Key := [(key1045, 24), (key1045, 24), (key1131, 24), (key1045, 24), (key1131, 24)]

def rawRow19296 : Integer.Sparse Key := [(key1045, 24), (key1045, 24), (key1131, 24), (key1131, 24), (key1045, 24)]

def rawRow19297 : Integer.Sparse Key := [(key1045, 24), (key1131, 24), (key1045, 24), (key1045, 24), (key1131, 24)]

def rawRow19298 : Integer.Sparse Key := [(key1045, 24), (key1131, 24), (key1045, 24), (key1131, 24), (key1045, 24)]

def rawRow19299 : Integer.Sparse Key := [(key1045, 24), (key1131, 24), (key1131, 24), (key1045, 24), (key1045, 24)]

def rawRow19300 : Integer.Sparse Key := [(key1131, 24), (key1045, 24), (key1045, 24), (key1045, 24), (key1131, 24)]

def rawRow19301 : Integer.Sparse Key := [(key1131, 24), (key1045, 24), (key1045, 24), (key1131, 24), (key1045, 24)]

def rawRow19302 : Integer.Sparse Key := [(key1131, 24), (key1045, 24), (key1131, 24), (key1045, 24), (key1045, 24)]

def rawRow19303 : Integer.Sparse Key := [(key1131, 24), (key1131, 24), (key1045, 24), (key1045, 24), (key1045, 24)]

def rawRow19304 : Integer.Sparse Key := [(key2681, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2712, 2), (key2712, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2863, 2), (key2688, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2863, 2)]

def rawRow19305 : Integer.Sparse Key := [(key2681, 2), (key2688, 2), (key2681, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2817, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2817, 2)]

def rawRow19306 : Integer.Sparse Key := [(key2688, 2), (key2681, 2), (key2681, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2863, 2), (key2815, 2), (key2863, 2), (key2712, 2), (key2815, 2), (key2712, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2817, 2), (key2714, 2)]

def rawRow19307 : Integer.Sparse Key := [(key2712, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2712, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2688, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2714, 2), (key2817, 2)]

def rawRow19308 : Integer.Sparse Key := [(key2714, 2), (key2712, 2), (key2714, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2815, 2), (key2712, 2), (key2817, 2), (key2863, 2), (key2817, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2714, 2)]

def rawRow19309 : Integer.Sparse Key := [(key2714, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2681, 2), (key2863, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2712, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2)]

def rawRow19310 : Integer.Sparse Key := [(key2815, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2688, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2712, 2), (key2815, 2)]

def rawRow19311 : Integer.Sparse Key := [(key2817, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2817, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2815, 2), (key2712, 2)]

def rawRow19312 : Integer.Sparse Key := [(key2817, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2712, 2), (key2712, 2), (key2681, 2), (key2681, 2)]

def rawRow19313 : Integer.Sparse Key := [(key2863, 2), (key2863, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2712, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2815, 2), (key2712, 2), (key2712, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2)]

def rawRow19314 : Integer.Sparse Key := [(key2412, 24), (key3031, 24), (key3031, 24), (key3118, 24), (key3118, 24)]

def rawRow19315 : Integer.Sparse Key := [(key2412, 24), (key3031, 24), (key3118, 24), (key3031, 24), (key3118, 24)]

def rawRow19316 : Integer.Sparse Key := [(key2412, 24), (key3031, 24), (key3118, 24), (key3118, 24), (key3031, 24)]

def rawRow19317 : Integer.Sparse Key := [(key2412, 24), (key3118, 24), (key3031, 24), (key3031, 24), (key3118, 24)]

def rawRow19318 : Integer.Sparse Key := [(key2412, 24), (key3118, 24), (key3031, 24), (key3118, 24), (key3031, 24)]

def rawRow19319 : Integer.Sparse Key := [(key2412, 24), (key3118, 24), (key3118, 24), (key3031, 24), (key3031, 24)]

def rawRow19320 : Integer.Sparse Key := [(key2485, 24), (key2412, 24), (key3031, 24), (key3031, 24), (key3118, 24)]

def rawRow19321 : Integer.Sparse Key := [(key2485, 24), (key2412, 24), (key3031, 24), (key3118, 24), (key3031, 24)]

def rawRow19322 : Integer.Sparse Key := [(key2485, 24), (key2412, 24), (key3118, 24), (key3031, 24), (key3031, 24)]

def rawRow19323 : Integer.Sparse Key := [(key2485, 24), (key2485, 24), (key2412, 24), (key3031, 24), (key3031, 24)]

def rawRow19324 : Integer.Sparse Key := [(key1050, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1138, 6)]

def rawRow19325 : Integer.Sparse Key := [(key1050, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1050, 6), (key1138, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1138, 6)]

def rawRow19326 : Integer.Sparse Key := [(key1058, 6), (key1050, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1138, 6), (key1058, 6)]

def rawRow19327 : Integer.Sparse Key := [(key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19328 : Integer.Sparse Key := [(key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6)]

def rawRow19329 : Integer.Sparse Key := [(key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6)]

def rawRow19330 : Integer.Sparse Key := [(key1136, 6), (key1138, 6), (key1138, 6), (key1138, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1050, 6), (key1050, 6), (key1050, 6), (key1136, 6)]

def rawRow19331 : Integer.Sparse Key := [(key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1050, 6)]

def rawRow19332 : Integer.Sparse Key := [(key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1050, 6)]

def rawRow19333 : Integer.Sparse Key := [(key1138, 6), (key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1050, 6), (key1050, 6)]

def rawRow19334 : Integer.Sparse Key := [(key2420, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2504, 4), (key2504, 4)]

def rawRow19335 : Integer.Sparse Key := [(key2427, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2495, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2504, 4), (key2438, 4), (key2504, 4)]

def rawRow19336 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2420, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2420, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2504, 4), (key2504, 4), (key2438, 4)]

def rawRow19337 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2438, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2420, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2495, 4)]

def rawRow19338 : Integer.Sparse Key := [(key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2495, 4), (key2504, 4), (key2495, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2427, 4), (key2495, 4), (key2427, 4)]

def rawRow19339 : Integer.Sparse Key := [(key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2504, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2420, 4), (key2504, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2427, 4)]

def rawRow19340 : Integer.Sparse Key := [(key2495, 4), (key2495, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2504, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2495, 4)]

def rawRow19341 : Integer.Sparse Key := [(key2495, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2427, 4)]

def rawRow19342 : Integer.Sparse Key := [(key2504, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2495, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2427, 4)]

def rawRow19343 : Integer.Sparse Key := [(key2504, 4), (key2504, 4), (key2504, 4), (key2495, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2438, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2420, 4), (key2420, 4)]

def rawRow19344 : Integer.Sparse Key := [(key2413, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2490, 6)]

def rawRow19345 : Integer.Sparse Key := [(key2413, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2413, 6), (key2490, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2490, 6)]

def rawRow19346 : Integer.Sparse Key := [(key2422, 6), (key2413, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2490, 6), (key2422, 6)]

def rawRow19347 : Integer.Sparse Key := [(key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6)]

def rawRow19348 : Integer.Sparse Key := [(key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6)]

def rawRow19349 : Integer.Sparse Key := [(key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6)]

def rawRow19350 : Integer.Sparse Key := [(key2486, 6), (key2490, 6), (key2490, 6), (key2490, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2413, 6), (key2413, 6), (key2413, 6), (key2486, 6)]

def rawRow19351 : Integer.Sparse Key := [(key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2413, 6)]

def rawRow19352 : Integer.Sparse Key := [(key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2413, 6)]

def rawRow19353 : Integer.Sparse Key := [(key2490, 6), (key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2413, 6), (key2413, 6)]

def rawRow19354 : Integer.Sparse Key := [(key2677, 6), (key2677, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3059, 6), (key3059, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3122, 6)]

def rawRow19355 : Integer.Sparse Key := [(key2677, 6), (key2708, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3059, 6), (key3045, 6), (key3059, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3122, 6), (key3059, 6), (key3094, 6)]

def rawRow19356 : Integer.Sparse Key := [(key2677, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key3094, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3045, 6), (key3122, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3094, 6), (key3059, 6)]

def rawRow19357 : Integer.Sparse Key := [(key2708, 6), (key2677, 6), (key2677, 6), (key2708, 6), (key2811, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3059, 6), (key3122, 6), (key3045, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3059, 6), (key3094, 6)]

def rawRow19358 : Integer.Sparse Key := [(key2708, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key2811, 6), (key2677, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3122, 6), (key3094, 6), (key3059, 6), (key3122, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3059, 6)]

def rawRow19359 : Integer.Sparse Key := [(key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key2811, 6), (key2811, 6), (key2677, 6), (key3045, 6), (key3122, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3059, 6), (key3094, 6), (key3094, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3045, 6)]

def rawRow19360 : Integer.Sparse Key := [(key2811, 6), (key2811, 6), (key2811, 6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2861, 6), (key2677, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3059, 6), (key3094, 6)]

def rawRow19361 : Integer.Sparse Key := [(key2811, 6), (key2811, 6), (key2861, 6), (key2811, 6), (key2708, 6), (key2708, 6), (key2861, 6), (key2708, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3059, 6)]

def rawRow19362 : Integer.Sparse Key := [(key2811, 6), (key2861, 6), (key2811, 6), (key2811, 6), (key2708, 6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key2811, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3045, 6)]

def rawRow19363 : Integer.Sparse Key := [(key2861, 6), (key2811, 6), (key2811, 6), (key2811, 6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2811, 6), (key2811, 6), (key2811, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key2677, 6), (key3045, 6), (key3045, 6), (key3045, 6)]

def rawRow19364 : Integer.Sparse Key := [(key1962, 24), (key1962, 24), (key1964, 24), (key1964, 24), (key1964, 24)]

def rawRow19365 : Integer.Sparse Key := [(key1962, 24), (key1964, 24), (key1962, 24), (key1964, 24), (key1964, 24)]

def rawRow19366 : Integer.Sparse Key := [(key1964, 24), (key1962, 24), (key1962, 24), (key1964, 24), (key1964, 24)]

def rawRow19367 : Integer.Sparse Key := [(key1962, 24), (key1964, 24), (key1964, 24), (key1962, 24), (key1964, 24)]

def rawRow19368 : Integer.Sparse Key := [(key1964, 24), (key1962, 24), (key1964, 24), (key1962, 24), (key1964, 24)]

def rawRow19369 : Integer.Sparse Key := [(key1964, 24), (key1964, 24), (key1962, 24), (key1962, 24), (key1964, 24)]

def rawRow19370 : Integer.Sparse Key := [(key1962, 24), (key1964, 24), (key1964, 24), (key1964, 24), (key1962, 24)]

def rawRow19371 : Integer.Sparse Key := [(key1964, 24), (key1962, 24), (key1964, 24), (key1964, 24), (key1962, 24)]

def rawRow19372 : Integer.Sparse Key := [(key1964, 24), (key1964, 24), (key1962, 24), (key1964, 24), (key1962, 24)]

def rawRow19373 : Integer.Sparse Key := [(key1964, 24), (key1964, 24), (key1964, 24), (key1962, 24), (key1962, 24)]

def rawRow19374 : Integer.Sparse Key := [(key3079, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3099, 12)]

def rawRow19375 : Integer.Sparse Key := [(key3084, 12), (key3079, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12)]

def rawRow19376 : Integer.Sparse Key := [(key3084, 12), (key3084, 12), (key3079, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12)]

def rawRow19377 : Integer.Sparse Key := [(key3084, 12), (key3084, 12), (key3099, 12), (key3079, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3099, 12), (key3084, 12)]

def rawRow19378 : Integer.Sparse Key := [(key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3079, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3084, 12)]

def rawRow19379 : Integer.Sparse Key := [(key3099, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3079, 12), (key3099, 12), (key3099, 12), (key3084, 12), (key3084, 12)]

def rawRow19380 : Integer.Sparse Key := [(key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3099, 12), (key3079, 12), (key3084, 12), (key3084, 12), (key3084, 12)]

def rawRow19381 : Integer.Sparse Key := [(key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3079, 12), (key3084, 12), (key3084, 12)]

def rawRow19382 : Integer.Sparse Key := [(key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3079, 12), (key3084, 12)]

def rawRow19383 : Integer.Sparse Key := [(key3099, 12), (key3099, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3079, 12)]

def rawRow19384 : Integer.Sparse Key := [(key1273, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6)]

def rawRow19385 : Integer.Sparse Key := [(key1278, 6), (key1273, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6)]

def rawRow19386 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1273, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6)]

def rawRow19387 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1278, 6), (key1273, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1696, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6)]

def rawRow19388 : Integer.Sparse Key := [(key1696, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1273, 6), (key1278, 6), (key1278, 6), (key1696, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6)]

def rawRow19389 : Integer.Sparse Key := [(key1701, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1273, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6)]

def rawRow19390 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1278, 6), (key1278, 6), (key1273, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6)]

def rawRow19391 : Integer.Sparse Key := [(key1696, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1273, 6), (key1278, 6), (key1696, 6), (key1751, 6), (key1933, 6), (key1953, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6)]

def rawRow19392 : Integer.Sparse Key := [(key1701, 6), (key1696, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1278, 6), (key1273, 6), (key1751, 6), (key1696, 6), (key1953, 6), (key1933, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6)]

def rawRow19393 : Integer.Sparse Key := [(key1696, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1273, 6), (key1953, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6)]

def rawRow19394 : Integer.Sparse Key := [(key1933, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1953, 6), (key1273, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6)]

def rawRow19395 : Integer.Sparse Key := [(key1701, 6), (key1933, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1751, 6), (key1953, 6), (key1278, 6), (key1933, 6), (key1273, 6), (key1696, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6)]

def rawRow19396 : Integer.Sparse Key := [(key1933, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1953, 6), (key1751, 6), (key1933, 6), (key1278, 6), (key1696, 6), (key1273, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6)]

def rawRow19397 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1751, 6), (key1751, 6), (key1953, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1273, 6), (key1696, 6), (key1696, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6)]

def rawRow19398 : Integer.Sparse Key := [(key1701, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1953, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1273, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6)]

def rawRow19399 : Integer.Sparse Key := [(key1933, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1953, 6), (key1751, 6), (key1751, 6), (key1933, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1696, 6), (key1696, 6), (key1273, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6)]

def rawRow19400 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1751, 6), (key1953, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1273, 6), (key1696, 6), (key1696, 6), (key1696, 6)]

def rawRow19401 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1953, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1273, 6), (key1696, 6), (key1696, 6)]

def rawRow19402 : Integer.Sparse Key := [(key1751, 6), (key1953, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1273, 6), (key1696, 6)]

def rawRow19403 : Integer.Sparse Key := [(key1953, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1696, 6), (key1696, 6), (key1696, 6), (key1273, 6)]

def rawRow19404 : Integer.Sparse Key := [(key222, 24), (key494, 24), (key494, 24), (key494, 24), (key548, 24)]

def rawRow19405 : Integer.Sparse Key := [(key222, 24), (key494, 24), (key494, 24), (key548, 24), (key494, 24)]

def rawRow19406 : Integer.Sparse Key := [(key222, 24), (key494, 24), (key548, 24), (key494, 24), (key494, 24)]

def rawRow19407 : Integer.Sparse Key := [(key222, 24), (key548, 24), (key494, 24), (key494, 24), (key494, 24)]

def rawRow19408 : Integer.Sparse Key := [(key494, 24), (key222, 24), (key494, 24), (key494, 24), (key548, 24)]

def rawRow19409 : Integer.Sparse Key := [(key494, 24), (key222, 24), (key494, 24), (key548, 24), (key494, 24)]

def rawRow19410 : Integer.Sparse Key := [(key494, 24), (key222, 24), (key548, 24), (key494, 24), (key494, 24)]

def rawRow19411 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key222, 24), (key494, 24), (key548, 24)]

def rawRow19412 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key222, 24), (key548, 24), (key494, 24)]

def rawRow19413 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key494, 24), (key222, 24), (key548, 24)]

def rawRow19414 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key494, 24), (key548, 24), (key222, 24)]

def rawRow19415 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key548, 24), (key222, 24), (key494, 24)]

def rawRow19416 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key548, 24), (key494, 24), (key222, 24)]

def rawRow19417 : Integer.Sparse Key := [(key494, 24), (key548, 24), (key222, 24), (key494, 24), (key494, 24)]

def rawRow19418 : Integer.Sparse Key := [(key494, 24), (key548, 24), (key494, 24), (key222, 24), (key494, 24)]

def rawRow19419 : Integer.Sparse Key := [(key494, 24), (key548, 24), (key494, 24), (key494, 24), (key222, 24)]

def rawRow19420 : Integer.Sparse Key := [(key548, 24), (key222, 24), (key494, 24), (key494, 24), (key494, 24)]

def rawRow19421 : Integer.Sparse Key := [(key548, 24), (key494, 24), (key222, 24), (key494, 24), (key494, 24)]

def rawRow19422 : Integer.Sparse Key := [(key548, 24), (key494, 24), (key494, 24), (key222, 24), (key494, 24)]

def rawRow19423 : Integer.Sparse Key := [(key548, 24), (key494, 24), (key494, 24), (key494, 24), (key222, 24)]

def rawRow19424 : Integer.Sparse Key := [(key1358, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1374, 2), (key1484, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1513, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1723, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1716, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1937, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1940, 2), (key1949, 2)]

def rawRow19425 : Integer.Sparse Key := [(key1364, 2), (key1358, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1374, 2), (key1364, 2), (key1490, 2), (key1484, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1513, 2), (key1490, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1723, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1949, 2), (key1940, 2)]

def rawRow19426 : Integer.Sparse Key := [(key1364, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1949, 2), (key1940, 2), (key1940, 2), (key1937, 2), (key1937, 2)]

def rawRow19427 : Integer.Sparse Key := [(key1374, 2), (key1374, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1358, 2), (key1358, 2), (key1513, 2), (key1513, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1484, 2), (key1484, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1949, 2), (key1949, 2), (key1949, 2), (key1940, 2), (key1940, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2)]

def rawRow19428 : Integer.Sparse Key := [(key1484, 2), (key1490, 2), (key1490, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1723, 2), (key1937, 2), (key1937, 2), (key1940, 2), (key1358, 2), (key1364, 2), (key1364, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1358, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1374, 2), (key1484, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1513, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1940, 2), (key1949, 2), (key1364, 2), (key1364, 2), (key1374, 2), (key1490, 2), (key1490, 2), (key1513, 2), (key1716, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1723, 2), (key1741, 2)]

def rawRow19429 : Integer.Sparse Key := [(key1490, 2), (key1484, 2), (key1490, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1364, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1949, 2), (key1940, 2), (key1364, 2), (key1374, 2), (key1364, 2), (key1490, 2), (key1513, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1723, 2)]

def rawRow19430 : Integer.Sparse Key := [(key1490, 2), (key1490, 2), (key1484, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1741, 2), (key1741, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1949, 2), (key1937, 2), (key1937, 2), (key1374, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1358, 2), (key1513, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1484, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1949, 2), (key1949, 2), (key1940, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2)]

def rawRow19431 : Integer.Sparse Key := [(key1710, 2), (key1716, 2), (key1937, 2), (key1484, 2), (key1490, 2), (key1710, 2), (key1723, 2), (key1937, 2), (key1940, 2), (key1490, 2), (key1716, 2), (key1723, 2), (key1710, 2), (key1716, 2), (key1937, 2), (key1358, 2), (key1364, 2), (key1710, 2), (key1741, 2), (key1937, 2), (key1949, 2), (key1364, 2), (key1716, 2), (key1741, 2), (key1484, 2), (key1490, 2), (key1710, 2), (key1723, 2), (key1937, 2), (key1940, 2), (key1358, 2), (key1364, 2), (key1710, 2), (key1741, 2), (key1937, 2), (key1949, 2), (key1358, 2), (key1374, 2), (key1484, 2), (key1513, 2), (key1940, 2), (key1949, 2), (key1364, 2), (key1374, 2), (key1490, 2), (key1513, 2), (key1723, 2), (key1741, 2), (key1490, 2), (key1716, 2), (key1723, 2), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1374, 2), (key1490, 2), (key1513, 2), (key1723, 2), (key1741, 2)]

def rawRow19432 : Integer.Sparse Key := [(key1716, 2), (key1710, 2), (key1937, 2), (key1490, 2), (key1484, 2), (key1723, 2), (key1710, 2), (key1940, 2), (key1937, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1741, 2), (key1710, 2), (key1949, 2), (key1937, 2), (key1364, 2), (key1741, 2), (key1716, 2), (key1490, 2), (key1484, 2), (key1723, 2), (key1710, 2), (key1940, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1741, 2), (key1710, 2), (key1949, 2), (key1937, 2), (key1374, 2), (key1358, 2), (key1513, 2), (key1484, 2), (key1949, 2), (key1940, 2), (key1374, 2), (key1364, 2), (key1513, 2), (key1490, 2), (key1741, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1716, 2), (key1374, 2), (key1364, 2), (key1513, 2), (key1490, 2), (key1741, 2), (key1723, 2)]

def rawRow19433 : Integer.Sparse Key := [(key1710, 2), (key1937, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1490, 2), (key1723, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1710, 2), (key1937, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1710, 2), (key1937, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1484, 2), (key1940, 2), (key1358, 2), (key1949, 2), (key1374, 2), (key1513, 2), (key1490, 2), (key1723, 2), (key1364, 2), (key1741, 2), (key1374, 2), (key1513, 2), (key1716, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1490, 2), (key1723, 2), (key1364, 2), (key1741, 2), (key1374, 2), (key1513, 2)]

def rawRow19434 : Integer.Sparse Key := [(key1937, 2), (key1710, 2), (key1716, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1937, 2), (key1710, 2), (key1716, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1723, 2), (key1490, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1741, 2), (key1364, 2), (key1940, 2), (key1484, 2), (key1949, 2), (key1358, 2), (key1513, 2), (key1374, 2), (key1723, 2), (key1490, 2), (key1741, 2), (key1364, 2), (key1513, 2), (key1374, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1723, 2), (key1490, 2), (key1741, 2), (key1364, 2), (key1513, 2), (key1374, 2)]

def rawRow19435 : Integer.Sparse Key := [(key1716, 2), (key1937, 2), (key1710, 2), (key1723, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1484, 2), (key1710, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1358, 2), (key1710, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1723, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1484, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1358, 2), (key1710, 2), (key1513, 2), (key1949, 2), (key1374, 2), (key1940, 2), (key1358, 2), (key1484, 2), (key1513, 2), (key1741, 2), (key1374, 2), (key1723, 2), (key1364, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1513, 2), (key1741, 2), (key1374, 2), (key1723, 2), (key1364, 2), (key1490, 2)]

def rawRow19436 : Integer.Sparse Key := [(key1937, 2), (key1716, 2), (key1710, 2), (key1940, 2), (key1723, 2), (key1937, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1723, 2), (key1716, 2), (key1490, 2), (key1937, 2), (key1716, 2), (key1710, 2), (key1949, 2), (key1741, 2), (key1937, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1741, 2), (key1716, 2), (key1364, 2), (key1940, 2), (key1723, 2), (key1937, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1949, 2), (key1741, 2), (key1937, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1949, 2), (key1513, 2), (key1940, 2), (key1374, 2), (key1484, 2), (key1358, 2), (key1741, 2), (key1513, 2), (key1723, 2), (key1374, 2), (key1490, 2), (key1364, 2), (key1723, 2), (key1716, 2), (key1490, 2), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1513, 2), (key1723, 2), (key1374, 2), (key1490, 2), (key1364, 2)]

def rawRow19437 : Integer.Sparse Key := [(key1723, 2), (key1723, 2), (key1940, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1358, 2), (key1710, 2), (key1710, 2), (key1513, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1949, 2), (key1374, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1940, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1358, 2), (key1358, 2), (key1484, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2)]

def rawRow19438 : Integer.Sparse Key := [(key1723, 2), (key1940, 2), (key1723, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1741, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1358, 2), (key1484, 2), (key1741, 2), (key1513, 2), (key1741, 2), (key1723, 2), (key1374, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1490, 2)]

def rawRow19439 : Integer.Sparse Key := [(key1940, 2), (key1723, 2), (key1723, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1710, 2), (key1710, 2), (key1484, 2), (key1949, 2), (key1741, 2), (key1741, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1949, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1513, 2), (key1940, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1374, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1484, 2), (key1358, 2), (key1741, 2), (key1741, 2), (key1513, 2), (key1723, 2), (key1723, 2), (key1374, 2), (key1716, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1490, 2), (key1364, 2)]

def rawRow19440 : Integer.Sparse Key := [(key1513, 2), (key1513, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1949, 2), (key1949, 2), (key1374, 2), (key1374, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1940, 2), (key1940, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1358, 2), (key1358, 2), (key1358, 2), (key1484, 2), (key1484, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2)]

def rawRow19441 : Integer.Sparse Key := [(key1741, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1358, 2), (key1484, 2), (key1484, 2), (key1710, 2), (key1710, 2)]

def rawRow19442 : Integer.Sparse Key := [(key1741, 2), (key1949, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1513, 2), (key1741, 2), (key1723, 2), (key1940, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1374, 2), (key1723, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1358, 2), (key1484, 2)]

def rawRow19443 : Integer.Sparse Key := [(key1949, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1513, 2), (key1940, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1374, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1716, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1710, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1484, 2), (key1358, 2)]

def rawRow19444 : Integer.Sparse Key := [(key1275, 24), (key1698, 24), (key1698, 24), (key1698, 24), (key1750, 24)]

def rawRow19445 : Integer.Sparse Key := [(key1275, 24), (key1698, 24), (key1698, 24), (key1750, 24), (key1698, 24)]

def rawRow19446 : Integer.Sparse Key := [(key1275, 24), (key1698, 24), (key1750, 24), (key1698, 24), (key1698, 24)]

def rawRow19447 : Integer.Sparse Key := [(key1275, 24), (key1750, 24), (key1698, 24), (key1698, 24), (key1698, 24)]

def rawRow19448 : Integer.Sparse Key := [(key1698, 24), (key1275, 24), (key1698, 24), (key1698, 24), (key1750, 24)]

def rawRow19449 : Integer.Sparse Key := [(key1698, 24), (key1275, 24), (key1698, 24), (key1750, 24), (key1698, 24)]

def rawRow19450 : Integer.Sparse Key := [(key1698, 24), (key1275, 24), (key1750, 24), (key1698, 24), (key1698, 24)]

def rawRow19451 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1275, 24), (key1698, 24), (key1750, 24)]

def rawRow19452 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1275, 24), (key1750, 24), (key1698, 24)]

def rawRow19453 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1698, 24), (key1275, 24), (key1750, 24)]

def rawRow19454 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1698, 24), (key1750, 24), (key1275, 24)]

def rawRow19455 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1750, 24), (key1275, 24), (key1698, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19456 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1750, 24), (key1698, 24), (key1275, 24)]

def rawRow19457 : Integer.Sparse Key := [(key1698, 24), (key1750, 24), (key1275, 24), (key1698, 24), (key1698, 24)]

def rawRow19458 : Integer.Sparse Key := [(key1698, 24), (key1750, 24), (key1698, 24), (key1275, 24), (key1698, 24)]

def rawRow19459 : Integer.Sparse Key := [(key1698, 24), (key1750, 24), (key1698, 24), (key1698, 24), (key1275, 24)]

def rawRow19460 : Integer.Sparse Key := [(key1750, 24), (key1275, 24), (key1698, 24), (key1698, 24), (key1698, 24)]

def rawRow19461 : Integer.Sparse Key := [(key1750, 24), (key1698, 24), (key1275, 24), (key1698, 24), (key1698, 24)]

def rawRow19462 : Integer.Sparse Key := [(key1750, 24), (key1698, 24), (key1698, 24), (key1275, 24), (key1698, 24)]

def rawRow19463 : Integer.Sparse Key := [(key1750, 24), (key1698, 24), (key1698, 24), (key1698, 24), (key1275, 24)]

def rawRow19464 : Integer.Sparse Key := [(key220, 6), (key225, 6), (key225, 6), (key225, 6), (key492, 6), (key497, 6), (key497, 6), (key492, 6), (key497, 6), (key492, 6), (key551, 6), (key497, 6), (key551, 6), (key497, 6), (key497, 6), (key551, 6), (key664, 6), (key664, 6), (key664, 6), (key681, 6)]

def rawRow19465 : Integer.Sparse Key := [(key225, 6), (key220, 6), (key225, 6), (key225, 6), (key497, 6), (key492, 6), (key497, 6), (key497, 6), (key492, 6), (key551, 6), (key492, 6), (key551, 6), (key497, 6), (key497, 6), (key551, 6), (key497, 6), (key664, 6), (key664, 6), (key681, 6), (key664, 6)]

def rawRow19466 : Integer.Sparse Key := [(key225, 6), (key225, 6), (key220, 6), (key225, 6), (key497, 6), (key497, 6), (key492, 6), (key551, 6), (key551, 6), (key497, 6), (key497, 6), (key492, 6), (key492, 6), (key551, 6), (key497, 6), (key497, 6), (key664, 6), (key681, 6), (key664, 6), (key664, 6)]

def rawRow19467 : Integer.Sparse Key := [(key225, 6), (key225, 6), (key225, 6), (key220, 6), (key551, 6), (key551, 6), (key551, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key492, 6), (key492, 6), (key492, 6), (key681, 6), (key664, 6), (key664, 6), (key664, 6)]

def rawRow19468 : Integer.Sparse Key := [(key492, 6), (key497, 6), (key497, 6), (key664, 6), (key220, 6), (key225, 6), (key225, 6), (key492, 6), (key497, 6), (key492, 6), (key551, 6), (key497, 6), (key551, 6), (key664, 6), (key664, 6), (key681, 6), (key225, 6), (key497, 6), (key497, 6), (key551, 6)]

def rawRow19469 : Integer.Sparse Key := [(key497, 6), (key492, 6), (key497, 6), (key664, 6), (key225, 6), (key220, 6), (key225, 6), (key497, 6), (key492, 6), (key551, 6), (key492, 6), (key551, 6), (key497, 6), (key664, 6), (key681, 6), (key664, 6), (key225, 6), (key497, 6), (key551, 6), (key497, 6)]

def rawRow19470 : Integer.Sparse Key := [(key497, 6), (key497, 6), (key492, 6), (key664, 6), (key225, 6), (key225, 6), (key220, 6), (key551, 6), (key551, 6), (key497, 6), (key497, 6), (key492, 6), (key492, 6), (key681, 6), (key664, 6), (key664, 6), (key225, 6), (key551, 6), (key497, 6), (key497, 6)]

def rawRow19471 : Integer.Sparse Key := [(key492, 6), (key497, 6), (key664, 6), (key497, 6), (key492, 6), (key497, 6), (key664, 6), (key220, 6), (key225, 6), (key492, 6), (key551, 6), (key664, 6), (key681, 6), (key225, 6), (key497, 6), (key551, 6), (key497, 6), (key225, 6), (key497, 6), (key551, 6)]

def rawRow19472 : Integer.Sparse Key := [(key497, 6), (key492, 6), (key664, 6), (key497, 6), (key497, 6), (key492, 6), (key664, 6), (key225, 6), (key220, 6), (key551, 6), (key492, 6), (key681, 6), (key664, 6), (key225, 6), (key551, 6), (key497, 6), (key497, 6), (key225, 6), (key551, 6), (key497, 6)]

def rawRow19473 : Integer.Sparse Key := [(key492, 6), (key664, 6), (key497, 6), (key497, 6), (key492, 6), (key664, 6), (key497, 6), (key492, 6), (key664, 6), (key220, 6), (key681, 6), (key225, 6), (key551, 6), (key497, 6), (key225, 6), (key551, 6), (key497, 6), (key497, 6), (key225, 6), (key551, 6)]

def rawRow19474 : Integer.Sparse Key := [(key664, 6), (key492, 6), (key497, 6), (key497, 6), (key664, 6), (key492, 6), (key497, 6), (key664, 6), (key492, 6), (key681, 6), (key220, 6), (key551, 6), (key225, 6), (key497, 6), (key551, 6), (key225, 6), (key497, 6), (key497, 6), (key551, 6), (key225, 6)]

def rawRow19475 : Integer.Sparse Key := [(key497, 6), (key664, 6), (key492, 6), (key497, 6), (key497, 6), (key664, 6), (key492, 6), (key551, 6), (key681, 6), (key225, 6), (key664, 6), (key220, 6), (key492, 6), (key551, 6), (key225, 6), (key497, 6), (key497, 6), (key551, 6), (key225, 6), (key497, 6)]

def rawRow19476 : Integer.Sparse Key := [(key664, 6), (key497, 6), (key492, 6), (key497, 6), (key664, 6), (key497, 6), (key492, 6), (key681, 6), (key551, 6), (key664, 6), (key225, 6), (key492, 6), (key220, 6), (key551, 6), (key497, 6), (key225, 6), (key497, 6), (key551, 6), (key497, 6), (key225, 6)]

def rawRow19477 : Integer.Sparse Key := [(key497, 6), (key497, 6), (key664, 6), (key492, 6), (key551, 6), (key551, 6), (key681, 6), (key225, 6), (key225, 6), (key497, 6), (key497, 6), (key664, 6), (key664, 6), (key220, 6), (key492, 6), (key492, 6), (key551, 6), (key225, 6), (key497, 6), (key497, 6)]

def rawRow19478 : Integer.Sparse Key := [(key497, 6), (key664, 6), (key497, 6), (key492, 6), (key551, 6), (key681, 6), (key551, 6), (key497, 6), (key664, 6), (key225, 6), (key664, 6), (key225, 6), (key497, 6), (key492, 6), (key220, 6), (key492, 6), (key551, 6), (key497, 6), (key225, 6), (key497, 6)]

def rawRow19479 : Integer.Sparse Key := [(key664, 6), (key497, 6), (key497, 6), (key492, 6), (key681, 6), (key551, 6), (key551, 6), (key664, 6), (key497, 6), (key664, 6), (key225, 6), (key497, 6), (key225, 6), (key492, 6), (key492, 6), (key220, 6), (key551, 6), (key497, 6), (key497, 6), (key225, 6)]

def rawRow19480 : Integer.Sparse Key := [(key551, 6), (key551, 6), (key551, 6), (key681, 6), (key225, 6), (key225, 6), (key225, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key664, 6), (key664, 6), (key664, 6), (key220, 6), (key492, 6), (key492, 6), (key492, 6)]

def rawRow19481 : Integer.Sparse Key := [(key551, 6), (key551, 6), (key681, 6), (key551, 6), (key497, 6), (key497, 6), (key664, 6), (key225, 6), (key225, 6), (key497, 6), (key497, 6), (key664, 6), (key664, 6), (key225, 6), (key497, 6), (key497, 6), (key492, 6), (key220, 6), (key492, 6), (key492, 6)]

def rawRow19482 : Integer.Sparse Key := [(key551, 6), (key681, 6), (key551, 6), (key551, 6), (key497, 6), (key664, 6), (key497, 6), (key497, 6), (key664, 6), (key225, 6), (key664, 6), (key225, 6), (key497, 6), (key497, 6), (key225, 6), (key497, 6), (key492, 6), (key492, 6), (key220, 6), (key492, 6)]

def rawRow19483 : Integer.Sparse Key := [(key681, 6), (key551, 6), (key551, 6), (key551, 6), (key664, 6), (key497, 6), (key497, 6), (key664, 6), (key497, 6), (key664, 6), (key225, 6), (key497, 6), (key225, 6), (key497, 6), (key497, 6), (key225, 6), (key492, 6), (key492, 6), (key492, 6), (key220, 6)]

def rawRow19484 : Integer.Sparse Key := [(key1277, 4), (key1277, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1283, 4), (key1700, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1756, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4)]

def rawRow19485 : Integer.Sparse Key := [(key1277, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4), (key1855, 4)]

def rawRow19486 : Integer.Sparse Key := [(key1283, 4), (key1277, 4), (key1277, 4), (key1283, 4), (key1283, 4), (key1277, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1756, 4), (key1706, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4)]

def rawRow19487 : Integer.Sparse Key := [(key1283, 4), (key1283, 4), (key1283, 4), (key1277, 4), (key1277, 4), (key1277, 4), (key1756, 4), (key1756, 4), (key1756, 4), (key1706, 4), (key1706, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow19488 : Integer.Sparse Key := [(key1700, 4), (key1700, 4), (key1706, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1277, 4), (key1283, 4), (key1283, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1756, 4), (key1855, 4), (key1855, 4), (key1886, 4)]

def rawRow19489 : Integer.Sparse Key := [(key1700, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1277, 4), (key1283, 4), (key1277, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1855, 4), (key1886, 4), (key1855, 4)]

def rawRow19490 : Integer.Sparse Key := [(key1706, 4), (key1700, 4), (key1700, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1283, 4), (key1277, 4), (key1277, 4), (key1756, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1283, 4), (key1283, 4), (key1277, 4), (key1756, 4), (key1756, 4), (key1706, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1855, 4), (key1855, 4)]

def rawRow19491 : Integer.Sparse Key := [(key1700, 4), (key1851, 4), (key1855, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1855, 4), (key1277, 4), (key1851, 4), (key1886, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1756, 4), (key1855, 4), (key1886, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1756, 4), (key1855, 4), (key1886, 4), (key1283, 4), (key1706, 4), (key1756, 4)]

def rawRow19492 : Integer.Sparse Key := [(key1700, 4), (key1855, 4), (key1851, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1277, 4), (key1886, 4), (key1851, 4), (key1283, 4), (key1277, 4), (key1756, 4), (key1700, 4), (key1886, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1283, 4), (key1277, 4), (key1756, 4), (key1700, 4), (key1886, 4), (key1855, 4), (key1283, 4), (key1756, 4), (key1706, 4)]

def rawRow19493 : Integer.Sparse Key := [(key1851, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1706, 4), (key1851, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1277, 4), (key1886, 4), (key1700, 4), (key1855, 4), (key1277, 4), (key1886, 4), (key1283, 4), (key1756, 4), (key1700, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1277, 4), (key1886, 4), (key1283, 4), (key1756, 4), (key1706, 4), (key1283, 4), (key1756, 4)]

def rawRow19494 : Integer.Sparse Key := [(key1851, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1706, 4), (key1851, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1886, 4), (key1277, 4), (key1855, 4), (key1700, 4), (key1886, 4), (key1277, 4), (key1756, 4), (key1283, 4), (key1855, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1886, 4), (key1277, 4), (key1756, 4), (key1283, 4), (key1706, 4), (key1756, 4), (key1283, 4)]

def rawRow19495 : Integer.Sparse Key := [(key1855, 4), (key1700, 4), (key1851, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1886, 4), (key1277, 4), (key1851, 4), (key1756, 4), (key1886, 4), (key1283, 4), (key1855, 4), (key1277, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1756, 4), (key1886, 4), (key1283, 4), (key1855, 4), (key1277, 4), (key1700, 4), (key1756, 4), (key1283, 4), (key1706, 4)]

def rawRow19496 : Integer.Sparse Key := [(key1855, 4), (key1851, 4), (key1700, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1700, 4), (key1886, 4), (key1851, 4), (key1277, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1283, 4), (key1700, 4), (key1277, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1283, 4), (key1700, 4), (key1277, 4), (key1756, 4), (key1706, 4), (key1283, 4)]

def rawRow19497 : Integer.Sparse Key := [(key1706, 4), (key1855, 4), (key1855, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1756, 4), (key1886, 4), (key1886, 4), (key1283, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1851, 4), (key1756, 4), (key1756, 4), (key1886, 4), (key1283, 4), (key1283, 4), (key1706, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1700, 4), (key1700, 4)]

def rawRow19498 : Integer.Sparse Key := [(key1855, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1700, 4), (key1886, 4), (key1756, 4), (key1886, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1700, 4), (key1277, 4), (key1700, 4)]

def rawRow19499 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1706, 4), (key1851, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1851, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1277, 4), (key1886, 4), (key1756, 4), (key1756, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1283, 4), (key1700, 4), (key1700, 4), (key1277, 4)]

def rawRow19500 : Integer.Sparse Key := [(key1756, 4), (key1756, 4), (key1756, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1283, 4), (key1283, 4), (key1283, 4), (key1706, 4), (key1706, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1277, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow19501 : Integer.Sparse Key := [(key1756, 4), (key1886, 4), (key1886, 4), (key1756, 4), (key1756, 4), (key1886, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1283, 4), (key1706, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1700, 4)]

def rawRow19502 : Integer.Sparse Key := [(key1886, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1700, 4), (key1851, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1277, 4), (key1700, 4)]

def rawRow19503 : Integer.Sparse Key := [(key1886, 4), (key1886, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1756, 4), (key1855, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1283, 4), (key1851, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1277, 4)]

def rawRow19504 : Integer.Sparse Key := [(key1274, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6)]

def rawRow19505 : Integer.Sparse Key := [(key1278, 6), (key1274, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6)]

def rawRow19506 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1274, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6)]

def rawRow19507 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1278, 6), (key1274, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1697, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6)]

def rawRow19508 : Integer.Sparse Key := [(key1697, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1274, 6), (key1278, 6), (key1278, 6), (key1697, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6)]

def rawRow19509 : Integer.Sparse Key := [(key1701, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1274, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6)]

def rawRow19510 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1278, 6), (key1278, 6), (key1274, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6)]

def rawRow19511 : Integer.Sparse Key := [(key1697, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1274, 6), (key1278, 6), (key1697, 6), (key1751, 6), (key1852, 6), (key1884, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6)]

def rawRow19512 : Integer.Sparse Key := [(key1701, 6), (key1697, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1278, 6), (key1274, 6), (key1751, 6), (key1697, 6), (key1884, 6), (key1852, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6)]

def rawRow19513 : Integer.Sparse Key := [(key1697, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1274, 6), (key1884, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6)]

def rawRow19514 : Integer.Sparse Key := [(key1852, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1884, 6), (key1274, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6)]

def rawRow19515 : Integer.Sparse Key := [(key1701, 6), (key1852, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1751, 6), (key1884, 6), (key1278, 6), (key1852, 6), (key1274, 6), (key1697, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6)]

def rawRow19516 : Integer.Sparse Key := [(key1852, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1884, 6), (key1751, 6), (key1852, 6), (key1278, 6), (key1697, 6), (key1274, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6)]

def rawRow19517 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1751, 6), (key1751, 6), (key1884, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1274, 6), (key1697, 6), (key1697, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6)]

def rawRow19518 : Integer.Sparse Key := [(key1701, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1884, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1274, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6)]

def rawRow19519 : Integer.Sparse Key := [(key1852, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1884, 6), (key1751, 6), (key1751, 6), (key1852, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1697, 6), (key1697, 6), (key1274, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6)]

def rawRow19520 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1751, 6), (key1884, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1274, 6), (key1697, 6), (key1697, 6), (key1697, 6)]

def rawRow19521 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1884, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1274, 6), (key1697, 6), (key1697, 6)]

def rawRow19522 : Integer.Sparse Key := [(key1751, 6), (key1884, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1274, 6), (key1697, 6)]

def rawRow19523 : Integer.Sparse Key := [(key1884, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1697, 6), (key1697, 6), (key1697, 6), (key1274, 6)]

def rawRow19524 : Integer.Sparse Key := [(key1360, 6), (key1360, 6), (key1360, 6), (key1372, 6), (key1486, 6), (key1486, 6), (key1486, 6), (key1511, 6), (key1712, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1721, 6), (key1739, 6)]

def rawRow19525 : Integer.Sparse Key := [(key1360, 6), (key1360, 6), (key1372, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1511, 6), (key1486, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1739, 6), (key1721, 6)]

def rawRow19526 : Integer.Sparse Key := [(key1360, 6), (key1372, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1511, 6), (key1486, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1712, 6), (key1712, 6)]

def rawRow19527 : Integer.Sparse Key := [(key1372, 6), (key1360, 6), (key1360, 6), (key1360, 6), (key1511, 6), (key1486, 6), (key1486, 6), (key1486, 6), (key1739, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6)]

def rawRow19528 : Integer.Sparse Key := [(key1486, 6), (key1712, 6), (key1712, 6), (key1721, 6), (key1360, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1360, 6), (key1372, 6), (key1486, 6), (key1486, 6), (key1511, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1721, 6), (key1739, 6)]

def rawRow19529 : Integer.Sparse Key := [(key1486, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1372, 6), (key1360, 6), (key1486, 6), (key1511, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1739, 6), (key1721, 6)]

def rawRow19530 : Integer.Sparse Key := [(key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1712, 6), (key1372, 6), (key1360, 6), (key1360, 6), (key1511, 6), (key1486, 6), (key1486, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1712, 6), (key1712, 6)]

def rawRow19531 : Integer.Sparse Key := [(key1712, 6), (key1486, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1486, 6), (key1712, 6), (key1721, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1372, 6), (key1486, 6), (key1511, 6), (key1721, 6), (key1739, 6)]

def rawRow19532 : Integer.Sparse Key := [(key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1372, 6), (key1360, 6), (key1511, 6), (key1486, 6), (key1739, 6), (key1721, 6)]

def rawRow19533 : Integer.Sparse Key := [(key1712, 6), (key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1486, 6), (key1721, 6), (key1360, 6), (key1739, 6), (key1372, 6), (key1511, 6)]

def rawRow19534 : Integer.Sparse Key := [(key1712, 6), (key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1721, 6), (key1486, 6), (key1739, 6), (key1360, 6), (key1511, 6), (key1372, 6)]

def rawRow19535 : Integer.Sparse Key := [(key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1511, 6), (key1739, 6), (key1372, 6), (key1721, 6), (key1360, 6), (key1486, 6)]

def rawRow19536 : Integer.Sparse Key := [(key1712, 6), (key1721, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1721, 6), (key1712, 6), (key1486, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1511, 6), (key1721, 6), (key1372, 6), (key1486, 6), (key1360, 6)]

def rawRow19537 : Integer.Sparse Key := [(key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1712, 6), (key1511, 6), (key1739, 6), (key1739, 6), (key1372, 6), (key1721, 6), (key1721, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1712, 6), (key1712, 6)]

def rawRow19538 : Integer.Sparse Key := [(key1721, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1511, 6), (key1739, 6), (key1721, 6), (key1372, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1360, 6), (key1486, 6)]

def rawRow19539 : Integer.Sparse Key := [(key1721, 6), (key1712, 6), (key1712, 6), (key1486, 6), (key1739, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1739, 6), (key1511, 6), (key1721, 6), (key1721, 6), (key1372, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1486, 6), (key1360, 6)]

def rawRow19540 : Integer.Sparse Key := [(key1511, 6), (key1739, 6), (key1739, 6), (key1739, 6), (key1372, 6), (key1721, 6), (key1721, 6), (key1721, 6), (key1360, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6)]

def rawRow19541 : Integer.Sparse Key := [(key1739, 6), (key1511, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1372, 6), (key1721, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1712, 6), (key1712, 6)]

def rawRow19542 : Integer.Sparse Key := [(key1739, 6), (key1739, 6), (key1511, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1372, 6), (key1721, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1360, 6), (key1486, 6)]

def rawRow19543 : Integer.Sparse Key := [(key1739, 6), (key1739, 6), (key1739, 6), (key1511, 6), (key1721, 6), (key1721, 6), (key1721, 6), (key1372, 6), (key1712, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1486, 6), (key1360, 6)]

def rawRow19544 : Integer.Sparse Key := [(key513, 24), (key515, 24), (key515, 24), (key515, 24), (key547, 24)]

def rawRow19545 : Integer.Sparse Key := [(key515, 24), (key513, 24), (key515, 24), (key515, 24), (key547, 24)]

def rawRow19546 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key513, 24), (key515, 24), (key547, 24)]

def rawRow19547 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key515, 24), (key513, 24), (key547, 24)]

def rawRow19548 : Integer.Sparse Key := [(key513, 24), (key515, 24), (key515, 24), (key547, 24), (key515, 24)]

def rawRow19549 : Integer.Sparse Key := [(key515, 24), (key513, 24), (key515, 24), (key547, 24), (key515, 24)]

def rawRow19550 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key513, 24), (key547, 24), (key515, 24)]

def rawRow19551 : Integer.Sparse Key := [(key513, 24), (key515, 24), (key547, 24), (key515, 24), (key515, 24)]

def rawRow19552 : Integer.Sparse Key := [(key515, 24), (key513, 24), (key547, 24), (key515, 24), (key515, 24)]

def rawRow19553 : Integer.Sparse Key := [(key513, 24), (key547, 24), (key515, 24), (key515, 24), (key515, 24)]

def rawRow19554 : Integer.Sparse Key := [(key547, 24), (key513, 24), (key515, 24), (key515, 24), (key515, 24)]

def rawRow19555 : Integer.Sparse Key := [(key515, 24), (key547, 24), (key513, 24), (key515, 24), (key515, 24)]

def rawRow19556 : Integer.Sparse Key := [(key547, 24), (key515, 24), (key513, 24), (key515, 24), (key515, 24)]

def rawRow19557 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key547, 24), (key513, 24), (key515, 24)]

def rawRow19558 : Integer.Sparse Key := [(key515, 24), (key547, 24), (key515, 24), (key513, 24), (key515, 24)]

def rawRow19559 : Integer.Sparse Key := [(key547, 24), (key515, 24), (key515, 24), (key513, 24), (key515, 24)]

def rawRow19560 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key515, 24), (key547, 24), (key513, 24)]

def rawRow19561 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key547, 24), (key515, 24), (key513, 24)]

def rawRow19562 : Integer.Sparse Key := [(key515, 24), (key547, 24), (key515, 24), (key515, 24), (key513, 24)]

def rawRow19563 : Integer.Sparse Key := [(key547, 24), (key515, 24), (key515, 24), (key515, 24), (key513, 24)]

def rawRow19564 : Integer.Sparse Key := [(key1501, 12), (key1501, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1506, 12), (key1733, 12), (key1735, 12), (key1735, 12), (key1735, 12)]

def rawRow19565 : Integer.Sparse Key := [(key1501, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1733, 12), (key1735, 12), (key1735, 12)]

def rawRow19566 : Integer.Sparse Key := [(key1506, 12), (key1501, 12), (key1501, 12), (key1506, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1735, 12), (key1733, 12), (key1735, 12)]

def rawRow19567 : Integer.Sparse Key := [(key1506, 12), (key1506, 12), (key1506, 12), (key1501, 12), (key1501, 12), (key1501, 12), (key1735, 12), (key1735, 12), (key1735, 12), (key1733, 12)]

def rawRow19568 : Integer.Sparse Key := [(key1501, 12), (key1501, 12), (key1506, 12), (key1733, 12), (key1735, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1506, 12), (key1735, 12)]

def rawRow19569 : Integer.Sparse Key := [(key1501, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1733, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1735, 12)]

def rawRow19570 : Integer.Sparse Key := [(key1506, 12), (key1501, 12), (key1501, 12), (key1735, 12), (key1735, 12), (key1733, 12), (key1506, 12), (key1506, 12), (key1501, 12), (key1735, 12)]

def rawRow19571 : Integer.Sparse Key := [(key1501, 12), (key1733, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1506, 12)]

def rawRow19572 : Integer.Sparse Key := [(key1501, 12), (key1735, 12), (key1733, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12)]

def rawRow19573 : Integer.Sparse Key := [(key1733, 12), (key1501, 12), (key1735, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1506, 12)]

def rawRow19574 : Integer.Sparse Key := [(key1733, 12), (key1735, 12), (key1501, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1506, 12)]

def rawRow19575 : Integer.Sparse Key := [(key1735, 12), (key1501, 12), (key1733, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12)]

def rawRow19576 : Integer.Sparse Key := [(key1735, 12), (key1733, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1506, 12)]

def rawRow19577 : Integer.Sparse Key := [(key1506, 12), (key1735, 12), (key1735, 12), (key1501, 12), (key1501, 12), (key1733, 12), (key1506, 12), (key1506, 12), (key1735, 12), (key1501, 12)]

def rawRow19578 : Integer.Sparse Key := [(key1735, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1733, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1501, 12)]

def rawRow19579 : Integer.Sparse Key := [(key1735, 12), (key1735, 12), (key1506, 12), (key1733, 12), (key1501, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1506, 12), (key1501, 12)]

def rawRow19580 : Integer.Sparse Key := [(key1506, 12), (key1506, 12), (key1506, 12), (key1735, 12), (key1735, 12), (key1735, 12), (key1501, 12), (key1501, 12), (key1501, 12), (key1733, 12)]

def rawRow19581 : Integer.Sparse Key := [(key1506, 12), (key1735, 12), (key1735, 12), (key1506, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1501, 12), (key1733, 12), (key1501, 12)]

def rawRow19582 : Integer.Sparse Key := [(key1735, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1733, 12), (key1501, 12), (key1501, 12)]

def rawRow19583 : Integer.Sparse Key := [(key1735, 12), (key1735, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1506, 12), (key1733, 12), (key1501, 12), (key1501, 12), (key1501, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19584 : Integer.Sparse Key := [(key288, 6), (key289, 6), (key289, 6), (key289, 6), (key513, 6), (key515, 6), (key515, 6), (key513, 6), (key515, 6), (key513, 6), (key547, 6), (key515, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key670, 6), (key670, 6), (key670, 6), (key680, 6)]

def rawRow19585 : Integer.Sparse Key := [(key289, 6), (key288, 6), (key289, 6), (key289, 6), (key515, 6), (key513, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key513, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key515, 6), (key670, 6), (key670, 6), (key680, 6), (key670, 6)]

def rawRow19586 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key288, 6), (key289, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key513, 6), (key547, 6), (key515, 6), (key515, 6), (key670, 6), (key680, 6), (key670, 6), (key670, 6)]

def rawRow19587 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key289, 6), (key288, 6), (key547, 6), (key547, 6), (key547, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key513, 6), (key513, 6), (key513, 6), (key680, 6), (key670, 6), (key670, 6), (key670, 6)]

def rawRow19588 : Integer.Sparse Key := [(key513, 6), (key515, 6), (key515, 6), (key547, 6), (key288, 6), (key289, 6), (key289, 6), (key513, 6), (key515, 6), (key513, 6), (key547, 6), (key515, 6), (key547, 6), (key670, 6), (key670, 6), (key680, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6)]

def rawRow19589 : Integer.Sparse Key := [(key515, 6), (key513, 6), (key515, 6), (key547, 6), (key289, 6), (key288, 6), (key289, 6), (key515, 6), (key513, 6), (key547, 6), (key513, 6), (key547, 6), (key515, 6), (key670, 6), (key680, 6), (key670, 6), (key289, 6), (key515, 6), (key547, 6), (key515, 6)]

def rawRow19590 : Integer.Sparse Key := [(key515, 6), (key515, 6), (key513, 6), (key547, 6), (key289, 6), (key289, 6), (key288, 6), (key547, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key513, 6), (key680, 6), (key670, 6), (key670, 6), (key289, 6), (key547, 6), (key515, 6), (key515, 6)]

def rawRow19591 : Integer.Sparse Key := [(key513, 6), (key515, 6), (key547, 6), (key515, 6), (key513, 6), (key515, 6), (key547, 6), (key288, 6), (key289, 6), (key513, 6), (key547, 6), (key670, 6), (key680, 6), (key289, 6), (key515, 6), (key547, 6), (key515, 6), (key289, 6), (key515, 6), (key547, 6)]

def rawRow19592 : Integer.Sparse Key := [(key515, 6), (key513, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key289, 6), (key288, 6), (key547, 6), (key513, 6), (key680, 6), (key670, 6), (key289, 6), (key547, 6), (key515, 6), (key515, 6), (key289, 6), (key547, 6), (key515, 6)]

def rawRow19593 : Integer.Sparse Key := [(key513, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key515, 6), (key513, 6), (key547, 6), (key288, 6), (key680, 6), (key289, 6), (key547, 6), (key515, 6), (key289, 6), (key547, 6), (key515, 6), (key515, 6), (key289, 6), (key547, 6)]

def rawRow19594 : Integer.Sparse Key := [(key547, 6), (key513, 6), (key515, 6), (key515, 6), (key547, 6), (key513, 6), (key515, 6), (key547, 6), (key513, 6), (key680, 6), (key288, 6), (key547, 6), (key289, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6)]

def rawRow19595 : Integer.Sparse Key := [(key515, 6), (key547, 6), (key513, 6), (key515, 6), (key515, 6), (key547, 6), (key513, 6), (key670, 6), (key680, 6), (key289, 6), (key547, 6), (key288, 6), (key513, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6)]

def rawRow19596 : Integer.Sparse Key := [(key547, 6), (key515, 6), (key513, 6), (key515, 6), (key547, 6), (key515, 6), (key513, 6), (key680, 6), (key670, 6), (key547, 6), (key289, 6), (key513, 6), (key288, 6), (key547, 6), (key515, 6), (key289, 6), (key515, 6), (key547, 6), (key515, 6), (key289, 6)]

def rawRow19597 : Integer.Sparse Key := [(key515, 6), (key515, 6), (key547, 6), (key513, 6), (key670, 6), (key670, 6), (key680, 6), (key289, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key547, 6), (key288, 6), (key513, 6), (key513, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6)]

def rawRow19598 : Integer.Sparse Key := [(key515, 6), (key547, 6), (key515, 6), (key513, 6), (key670, 6), (key680, 6), (key670, 6), (key515, 6), (key547, 6), (key289, 6), (key547, 6), (key289, 6), (key515, 6), (key513, 6), (key288, 6), (key513, 6), (key547, 6), (key515, 6), (key289, 6), (key515, 6)]

def rawRow19599 : Integer.Sparse Key := [(key547, 6), (key515, 6), (key515, 6), (key513, 6), (key680, 6), (key670, 6), (key670, 6), (key547, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6), (key289, 6), (key513, 6), (key513, 6), (key288, 6), (key547, 6), (key515, 6), (key515, 6), (key289, 6)]

def rawRow19600 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key670, 6), (key680, 6), (key289, 6), (key289, 6), (key289, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key547, 6), (key547, 6), (key547, 6), (key288, 6), (key513, 6), (key513, 6), (key513, 6)]

def rawRow19601 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key680, 6), (key670, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key513, 6), (key288, 6), (key513, 6), (key513, 6)]

def rawRow19602 : Integer.Sparse Key := [(key670, 6), (key680, 6), (key670, 6), (key670, 6), (key515, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key289, 6), (key515, 6), (key513, 6), (key513, 6), (key288, 6), (key513, 6)]

def rawRow19603 : Integer.Sparse Key := [(key680, 6), (key670, 6), (key670, 6), (key670, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6), (key289, 6), (key515, 6), (key515, 6), (key289, 6), (key513, 6), (key513, 6), (key513, 6), (key288, 6)]

def rawRow19604 : Integer.Sparse Key := [(key1251, 6), (key1259, 6), (key1259, 6), (key1271, 6), (key1526, 6), (key1534, 6), (key1534, 6), (key1604, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1640, 6), (key1679, 6), (key1679, 6), (key1693, 6), (key1894, 6), (key1916, 6), (key1916, 6), (key1930, 6)]

def rawRow19605 : Integer.Sparse Key := [(key1259, 6), (key1251, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1526, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1693, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1930, 6), (key1916, 6)]

def rawRow19606 : Integer.Sparse Key := [(key1259, 6), (key1259, 6), (key1251, 6), (key1271, 6), (key1534, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1640, 6), (key1612, 6), (key1612, 6), (key1604, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1679, 6), (key1894, 6), (key1930, 6), (key1916, 6), (key1916, 6)]

def rawRow19607 : Integer.Sparse Key := [(key1251, 6), (key1259, 6), (key1271, 6), (key1259, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1526, 6), (key1534, 6), (key1604, 6), (key1640, 6), (key1679, 6), (key1693, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1916, 6), (key1894, 6), (key1916, 6), (key1930, 6)]

def rawRow19608 : Integer.Sparse Key := [(key1259, 6), (key1251, 6), (key1271, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1894, 6), (key1930, 6), (key1916, 6)]

def rawRow19609 : Integer.Sparse Key := [(key1251, 6), (key1271, 6), (key1259, 6), (key1259, 6), (key1604, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1526, 6), (key1693, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1640, 6), (key1916, 6), (key1916, 6), (key1894, 6), (key1930, 6)]

def rawRow19610 : Integer.Sparse Key := [(key1271, 6), (key1251, 6), (key1259, 6), (key1259, 6), (key1679, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1693, 6), (key1526, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1534, 6), (key1916, 6), (key1916, 6), (key1930, 6), (key1894, 6)]

def rawRow19611 : Integer.Sparse Key := [(key1259, 6), (key1271, 6), (key1251, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1930, 6), (key1894, 6), (key1916, 6)]

def rawRow19612 : Integer.Sparse Key := [(key1271, 6), (key1259, 6), (key1251, 6), (key1259, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1693, 6), (key1640, 6), (key1679, 6), (key1534, 6), (key1604, 6), (key1526, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1916, 6), (key1930, 6), (key1916, 6), (key1894, 6)]

def rawRow19613 : Integer.Sparse Key := [(key1259, 6), (key1259, 6), (key1271, 6), (key1251, 6), (key1640, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1534, 6), (key1612, 6), (key1612, 6), (key1679, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1604, 6), (key1930, 6), (key1894, 6), (key1916, 6), (key1916, 6)]

def rawRow19614 : Integer.Sparse Key := [(key1259, 6), (key1271, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1693, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1526, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1894, 6), (key1916, 6)]

def rawRow19615 : Integer.Sparse Key := [(key1271, 6), (key1259, 6), (key1259, 6), (key1251, 6), (key1693, 6), (key1640, 6), (key1640, 6), (key1679, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1534, 6), (key1604, 6), (key1604, 6), (key1526, 6), (key1930, 6), (key1916, 6), (key1916, 6), (key1894, 6)]

def rawRow19616 : Integer.Sparse Key := [(key1526, 6), (key1534, 6), (key1534, 6), (key1894, 6), (key1251, 6), (key1259, 6), (key1259, 6), (key1604, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1640, 6), (key1916, 6), (key1916, 6), (key1930, 6), (key1271, 6), (key1679, 6), (key1679, 6), (key1693, 6)]

def rawRow19617 : Integer.Sparse Key := [(key1534, 6), (key1526, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1251, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1930, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1693, 6), (key1679, 6)]

def rawRow19618 : Integer.Sparse Key := [(key1534, 6), (key1534, 6), (key1526, 6), (key1894, 6), (key1259, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1640, 6), (key1612, 6), (key1612, 6), (key1604, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1916, 6), (key1271, 6), (key1693, 6), (key1679, 6), (key1679, 6)]

def rawRow19619 : Integer.Sparse Key := [(key1526, 6), (key1534, 6), (key1894, 6), (key1534, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1251, 6), (key1259, 6), (key1604, 6), (key1640, 6), (key1916, 6), (key1930, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1679, 6), (key1271, 6), (key1679, 6), (key1693, 6)]

def rawRow19620 : Integer.Sparse Key := [(key1534, 6), (key1526, 6), (key1894, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1271, 6), (key1693, 6), (key1679, 6)]

def rawRow19621 : Integer.Sparse Key := [(key1526, 6), (key1894, 6), (key1534, 6), (key1534, 6), (key1604, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1251, 6), (key1930, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1640, 6), (key1679, 6), (key1679, 6), (key1271, 6), (key1693, 6)]

def rawRow19622 : Integer.Sparse Key := [(key1894, 6), (key1526, 6), (key1534, 6), (key1534, 6), (key1916, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1930, 6), (key1251, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1259, 6), (key1679, 6), (key1679, 6), (key1693, 6), (key1271, 6)]

def rawRow19623 : Integer.Sparse Key := [(key1534, 6), (key1894, 6), (key1526, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1693, 6), (key1271, 6), (key1679, 6)]

def rawRow19624 : Integer.Sparse Key := [(key1894, 6), (key1534, 6), (key1526, 6), (key1534, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1930, 6), (key1640, 6), (key1916, 6), (key1259, 6), (key1604, 6), (key1251, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1679, 6), (key1693, 6), (key1679, 6), (key1271, 6)]

def rawRow19625 : Integer.Sparse Key := [(key1534, 6), (key1534, 6), (key1894, 6), (key1526, 6), (key1640, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1259, 6), (key1612, 6), (key1612, 6), (key1916, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1604, 6), (key1693, 6), (key1271, 6), (key1679, 6), (key1679, 6)]

def rawRow19626 : Integer.Sparse Key := [(key1534, 6), (key1894, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1930, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1251, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1271, 6), (key1679, 6)]

def rawRow19627 : Integer.Sparse Key := [(key1894, 6), (key1534, 6), (key1534, 6), (key1526, 6), (key1930, 6), (key1640, 6), (key1640, 6), (key1916, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1259, 6), (key1604, 6), (key1604, 6), (key1251, 6), (key1693, 6), (key1679, 6), (key1679, 6), (key1271, 6)]

def rawRow19628 : Integer.Sparse Key := [(key1604, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1251, 6), (key1259, 6), (key1271, 6), (key1526, 6), (key1534, 6), (key1604, 6), (key1640, 6), (key1679, 6), (key1693, 6), (key1894, 6), (key1916, 6), (key1930, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1640, 6)]

def rawRow19629 : Integer.Sparse Key := [(key1612, 6), (key1604, 6), (key1679, 6), (key1916, 6), (key1259, 6), (key1251, 6), (key1271, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1894, 6), (key1930, 6), (key1916, 6), (key1259, 6), (key1534, 6), (key1640, 6), (key1612, 6)]

def rawRow19630 : Integer.Sparse Key := [(key1604, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1251, 6), (key1271, 6), (key1259, 6), (key1604, 6), (key1679, 6), (key1526, 6), (key1693, 6), (key1534, 6), (key1640, 6), (key1916, 6), (key1894, 6), (key1930, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1640, 6)]

def rawRow19631 : Integer.Sparse Key := [(key1679, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1271, 6), (key1251, 6), (key1259, 6), (key1679, 6), (key1604, 6), (key1693, 6), (key1526, 6), (key1640, 6), (key1534, 6), (key1916, 6), (key1930, 6), (key1894, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1534, 6)]

def rawRow19632 : Integer.Sparse Key := [(key1612, 6), (key1679, 6), (key1604, 6), (key1916, 6), (key1259, 6), (key1271, 6), (key1251, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1930, 6), (key1894, 6), (key1916, 6), (key1259, 6), (key1640, 6), (key1534, 6), (key1612, 6)]

def rawRow19633 : Integer.Sparse Key := [(key1679, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1271, 6), (key1259, 6), (key1251, 6), (key1693, 6), (key1640, 6), (key1679, 6), (key1534, 6), (key1604, 6), (key1526, 6), (key1930, 6), (key1916, 6), (key1894, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1534, 6)]

def rawRow19634 : Integer.Sparse Key := [(key1604, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1526, 6), (key1534, 6), (key1894, 6), (key1251, 6), (key1259, 6), (key1604, 6), (key1640, 6), (key1916, 6), (key1930, 6), (key1271, 6), (key1679, 6), (key1693, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1640, 6)]

def rawRow19635 : Integer.Sparse Key := [(key1612, 6), (key1604, 6), (key1916, 6), (key1679, 6), (key1534, 6), (key1526, 6), (key1894, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1271, 6), (key1693, 6), (key1679, 6), (key1534, 6), (key1259, 6), (key1640, 6), (key1612, 6)]

def rawRow19636 : Integer.Sparse Key := [(key1604, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1526, 6), (key1894, 6), (key1534, 6), (key1604, 6), (key1916, 6), (key1251, 6), (key1930, 6), (key1259, 6), (key1640, 6), (key1679, 6), (key1271, 6), (key1693, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1640, 6)]

def rawRow19637 : Integer.Sparse Key := [(key1916, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, 6), (key1526, 6), (key1534, 6), (key1916, 6), (key1604, 6), (key1930, 6), (key1251, 6), (key1640, 6), (key1259, 6), (key1679, 6), (key1693, 6), (key1271, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1259, 6)]

def rawRow19638 : Integer.Sparse Key := [(key1612, 6), (key1916, 6), (key1604, 6), (key1679, 6), (key1534, 6), (key1894, 6), (key1526, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1693, 6), (key1271, 6), (key1679, 6), (key1534, 6), (key1640, 6), (key1259, 6), (key1612, 6)]

def rawRow19639 : Integer.Sparse Key := [(key1916, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1894, 6), (key1534, 6), (key1526, 6), (key1930, 6), (key1640, 6), (key1916, 6), (key1259, 6), (key1604, 6), (key1251, 6), (key1693, 6), (key1679, 6), (key1271, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1259, 6)]

def rawRow19640 : Integer.Sparse Key := [(key1604, 6), (key1679, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1916, 6), (key1251, 6), (key1271, 6), (key1526, 6), (key1693, 6), (key1894, 6), (key1930, 6), (key1259, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1534, 6), (key1640, 6)]

def rawRow19641 : Integer.Sparse Key := [(key1679, 6), (key1604, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1916, 6), (key1271, 6), (key1251, 6), (key1693, 6), (key1526, 6), (key1930, 6), (key1894, 6), (key1259, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1640, 6), (key1534, 6)]

def rawRow19642 : Integer.Sparse Key := [(key1604, 6), (key1916, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1679, 6), (key1526, 6), (key1894, 6), (key1251, 6), (key1930, 6), (key1271, 6), (key1693, 6), (key1534, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1259, 6), (key1640, 6)]

def rawRow19643 : Integer.Sparse Key := [(key1916, 6), (key1604, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1679, 6), (key1894, 6), (key1526, 6), (key1930, 6), (key1251, 6), (key1693, 6), (key1271, 6), (key1534, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1640, 6), (key1259, 6)]

def rawRow19644 : Integer.Sparse Key := [(key1679, 6), (key1916, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1604, 6), (key1693, 6), (key1930, 6), (key1271, 6), (key1894, 6), (key1251, 6), (key1526, 6), (key1640, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1259, 6), (key1534, 6)]

def rawRow19645 : Integer.Sparse Key := [(key1916, 6), (key1679, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1604, 6), (key1930, 6), (key1693, 6), (key1894, 6), (key1271, 6), (key1526, 6), (key1251, 6), (key1640, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1534, 6), (key1259, 6)]

def rawRow19646 : Integer.Sparse Key := [(key1612, 6), (key1679, 6), (key1916, 6), (key1604, 6), (key1640, 6), (key1693, 6), (key1930, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1251, 6), (key1526, 6), (key1604, 6), (key1640, 6), (key1259, 6), (key1534, 6), (key1612, 6)]

def rawRow19647 : Integer.Sparse Key := [(key1679, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1693, 6), (key1640, 6), (key1930, 6), (key1271, 6), (key1259, 6), (key1679, 6), (key1534, 6), (key1916, 6), (key1894, 6), (key1251, 6), (key1604, 6), (key1526, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1534, 6)]

def rawRow19648 : Integer.Sparse Key := [(key1612, 6), (key1916, 6), (key1679, 6), (key1604, 6), (key1640, 6), (key1930, 6), (key1693, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1526, 6), (key1251, 6), (key1604, 6), (key1640, 6), (key1534, 6), (key1259, 6), (key1612, 6)]

def rawRow19649 : Integer.Sparse Key := [(key1916, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1930, 6), (key1640, 6), (key1693, 6), (key1894, 6), (key1534, 6), (key1916, 6), (key1259, 6), (key1679, 6), (key1271, 6), (key1526, 6), (key1604, 6), (key1251, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1259, 6)]

def rawRow19650 : Integer.Sparse Key := [(key1679, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1693, 6), (key1930, 6), (key1640, 6), (key1679, 6), (key1916, 6), (key1271, 6), (key1894, 6), (key1259, 6), (key1534, 6), (key1604, 6), (key1251, 6), (key1526, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1534, 6)]

def rawRow19651 : Integer.Sparse Key := [(key1916, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1930, 6), (key1693, 6), (key1640, 6), (key1916, 6), (key1679, 6), (key1894, 6), (key1271, 6), (key1534, 6), (key1259, 6), (key1604, 6), (key1526, 6), (key1251, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1259, 6)]

def rawRow19652 : Integer.Sparse Key := [(key1640, 6), (key1640, 6), (key1693, 6), (key1930, 6), (key1259, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1534, 6), (key1612, 6), (key1612, 6), (key1679, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1916, 6), (key1251, 6), (key1526, 6), (key1604, 6), (key1604, 6)]

def rawRow19653 : Integer.Sparse Key := [(key1640, 6), (key1693, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1271, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1894, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1526, 6), (key1604, 6)]

def rawRow19654 : Integer.Sparse Key := [(key1693, 6), (key1640, 6), (key1640, 6), (key1930, 6), (key1271, 6), (key1259, 6), (key1259, 6), (key1679, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1534, 6), (key1916, 6), (key1916, 6), (key1894, 6), (key1251, 6), (key1604, 6), (key1604, 6), (key1526, 6)]

def rawRow19655 : Integer.Sparse Key := [(key1640, 6), (key1640, 6), (key1930, 6), (key1693, 6), (key1534, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1259, 6), (key1612, 6), (key1612, 6), (key1916, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1679, 6), (key1526, 6), (key1251, 6), (key1604, 6), (key1604, 6)]

def rawRow19656 : Integer.Sparse Key := [(key1640, 6), (key1930, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1894, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1271, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1251, 6), (key1604, 6)]

def rawRow19657 : Integer.Sparse Key := [(key1930, 6), (key1640, 6), (key1640, 6), (key1693, 6), (key1894, 6), (key1534, 6), (key1534, 6), (key1916, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1259, 6), (key1679, 6), (key1679, 6), (key1271, 6), (key1526, 6), (key1604, 6), (key1604, 6), (key1251, 6)]

def rawRow19658 : Integer.Sparse Key := [(key1640, 6), (key1693, 6), (key1930, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1251, 6), (key1526, 6), (key1604, 6)]

def rawRow19659 : Integer.Sparse Key := [(key1693, 6), (key1640, 6), (key1930, 6), (key1640, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1271, 6), (key1259, 6), (key1679, 6), (key1534, 6), (key1916, 6), (key1894, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1604, 6), (key1251, 6), (key1604, 6), (key1526, 6)]

def rawRow19660 : Integer.Sparse Key := [(key1640, 6), (key1930, 6), (key1693, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1526, 6), (key1251, 6), (key1604, 6)]

def rawRow19661 : Integer.Sparse Key := [(key1930, 6), (key1640, 6), (key1693, 6), (key1640, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1894, 6), (key1534, 6), (key1916, 6), (key1259, 6), (key1679, 6), (key1271, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1604, 6), (key1526, 6), (key1604, 6), (key1251, 6)]

def rawRow19662 : Integer.Sparse Key := [(key1693, 6), (key1930, 6), (key1640, 6), (key1640, 6), (key1679, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1271, 6), (key1894, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1534, 6), (key1604, 6), (key1604, 6), (key1251, 6), (key1526, 6)]

def rawRow19663 : Integer.Sparse Key := [(key1930, 6), (key1693, 6), (key1640, 6), (key1640, 6), (key1916, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1894, 6), (key1271, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1259, 6), (key1604, 6), (key1604, 6), (key1526, 6), (key1251, 6)]

def rawRow19664 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 24), (key428, 24), (key456, 24)]

def rawRow19665 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 24), (key456, 24), (key428, 24)]

def rawRow19666 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key456, 24), (key428, 24), (key428, 24)]

def rawRow19667 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key377, 24), (key428, 24), (key456, 24)]

def rawRow19668 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key377, 24), (key456, 24), (key428, 24)]

def rawRow19669 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key428, 24), (key377, 24), (key456, 24)]

def rawRow19670 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key428, 24), (key456, 24), (key377, 24)]

def rawRow19671 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key456, 24), (key377, 24), (key428, 24)]

def rawRow19672 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key456, 24), (key428, 24), (key377, 24)]

def rawRow19673 : Integer.Sparse Key := [(key208, 24), (key456, 24), (key377, 24), (key428, 24), (key428, 24)]

def rawRow19674 : Integer.Sparse Key := [(key208, 24), (key456, 24), (key428, 24), (key377, 24), (key428, 24)]

def rawRow19675 : Integer.Sparse Key := [(key208, 24), (key456, 24), (key428, 24), (key428, 24), (key377, 24)]

def rawRow19676 : Integer.Sparse Key := [(key377, 24), (key208, 24), (key428, 24), (key428, 24), (key456, 24)]

def rawRow19677 : Integer.Sparse Key := [(key377, 24), (key208, 24), (key428, 24), (key456, 24), (key428, 24)]

def rawRow19678 : Integer.Sparse Key := [(key377, 24), (key208, 24), (key456, 24), (key428, 24), (key428, 24)]

def rawRow19679 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key208, 24), (key428, 24), (key456, 24)]

def rawRow19680 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key208, 24), (key456, 24), (key428, 24)]

def rawRow19681 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key428, 24), (key208, 24), (key456, 24)]

def rawRow19682 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key428, 24), (key456, 24), (key208, 24)]

def rawRow19683 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key456, 24), (key208, 24), (key428, 24)]

def rawRow19684 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key456, 24), (key428, 24), (key208, 24)]

def rawRow19685 : Integer.Sparse Key := [(key377, 24), (key456, 24), (key208, 24), (key428, 24), (key428, 24)]

def rawRow19686 : Integer.Sparse Key := [(key377, 24), (key456, 24), (key428, 24), (key208, 24), (key428, 24)]

def rawRow19687 : Integer.Sparse Key := [(key377, 24), (key456, 24), (key428, 24), (key428, 24), (key208, 24)]

def rawRow19688 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key377, 24), (key428, 24), (key456, 24)]

def rawRow19689 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key377, 24), (key456, 24), (key428, 24)]

def rawRow19690 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key428, 24), (key377, 24), (key456, 24)]

def rawRow19691 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key428, 24), (key456, 24), (key377, 24)]

def rawRow19692 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key456, 24), (key377, 24), (key428, 24)]

def rawRow19693 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key456, 24), (key428, 24), (key377, 24)]

def rawRow19694 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key208, 24), (key428, 24), (key456, 24)]

def rawRow19695 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key208, 24), (key456, 24), (key428, 24)]

def rawRow19696 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key428, 24), (key208, 24), (key456, 24)]

def rawRow19697 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key428, 24), (key456, 24), (key208, 24)]

def rawRow19698 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key456, 24), (key208, 24), (key428, 24)]

def rawRow19699 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key456, 24), (key428, 24), (key208, 24)]

def rawRow19700 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key208, 24), (key377, 24), (key456, 24)]

def rawRow19701 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key208, 24), (key456, 24), (key377, 24)]

def rawRow19702 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key377, 24), (key208, 24), (key456, 24)]

def rawRow19703 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key377, 24), (key456, 24), (key208, 24)]

def rawRow19704 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key456, 24), (key208, 24), (key377, 24)]

def rawRow19705 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key456, 24), (key377, 24), (key208, 24)]

def rawRow19706 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key208, 24), (key377, 24), (key428, 24)]

def rawRow19707 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key208, 24), (key428, 24), (key377, 24)]

def rawRow19708 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key377, 24), (key208, 24), (key428, 24)]

def rawRow19709 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key377, 24), (key428, 24), (key208, 24)]

def rawRow19710 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key428, 24), (key208, 24), (key377, 24)]

def rawRow19711 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key428, 24), (key377, 24), (key208, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19712 : Integer.Sparse Key := [(key456, 24), (key208, 24), (key377, 24), (key428, 24), (key428, 24)]

def rawRow19713 : Integer.Sparse Key := [(key456, 24), (key208, 24), (key428, 24), (key377, 24), (key428, 24)]

def rawRow19714 : Integer.Sparse Key := [(key456, 24), (key208, 24), (key428, 24), (key428, 24), (key377, 24)]

def rawRow19715 : Integer.Sparse Key := [(key456, 24), (key377, 24), (key208, 24), (key428, 24), (key428, 24)]

def rawRow19716 : Integer.Sparse Key := [(key456, 24), (key377, 24), (key428, 24), (key208, 24), (key428, 24)]

def rawRow19717 : Integer.Sparse Key := [(key456, 24), (key377, 24), (key428, 24), (key428, 24), (key208, 24)]

def rawRow19718 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key208, 24), (key377, 24), (key428, 24)]

def rawRow19719 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key208, 24), (key428, 24), (key377, 24)]

def rawRow19720 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key377, 24), (key208, 24), (key428, 24)]

def rawRow19721 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key377, 24), (key428, 24), (key208, 24)]

def rawRow19722 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key428, 24), (key208, 24), (key377, 24)]

def rawRow19723 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key428, 24), (key377, 24), (key208, 24)]

def rawRow19724 : Integer.Sparse Key := [(key1291, 2), (key1299, 2), (key1299, 2), (key1311, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1327, 2), (key1352, 2), (key1352, 2), (key1355, 2), (key1386, 2), (key1394, 2), (key1394, 2), (key1419, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1445, 2), (key1473, 2), (key1473, 2), (key1481, 2), (key1541, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1557, 2), (key1568, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1634, 2), (key1682, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1684, 2), (key1690, 2), (key1897, 2), (key1897, 2), (key1900, 2), (key1904, 2), (key1904, 2), (key1912, 2), (key1919, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1921, 2), (key1927, 2)]

def rawRow19725 : Integer.Sparse Key := [(key1299, 2), (key1291, 2), (key1299, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1352, 2), (key1355, 2), (key1352, 2), (key1394, 2), (key1386, 2), (key1394, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1473, 2), (key1481, 2), (key1473, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1682, 2), (key1690, 2), (key1684, 2), (key1897, 2), (key1900, 2), (key1897, 2), (key1904, 2), (key1912, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1919, 2), (key1927, 2), (key1921, 2)]

def rawRow19726 : Integer.Sparse Key := [(key1299, 2), (key1299, 2), (key1291, 2), (key1327, 2), (key1327, 2), (key1319, 2), (key1319, 2), (key1311, 2), (key1311, 2), (key1355, 2), (key1352, 2), (key1352, 2), (key1394, 2), (key1394, 2), (key1386, 2), (key1445, 2), (key1445, 2), (key1427, 2), (key1427, 2), (key1419, 2), (key1419, 2), (key1481, 2), (key1473, 2), (key1473, 2), (key1557, 2), (key1557, 2), (key1549, 2), (key1549, 2), (key1541, 2), (key1541, 2), (key1594, 2), (key1594, 2), (key1576, 2), (key1576, 2), (key1568, 2), (key1568, 2), (key1634, 2), (key1634, 2), (key1625, 2), (key1625, 2), (key1617, 2), (key1617, 2), (key1690, 2), (key1690, 2), (key1684, 2), (key1684, 2), (key1682, 2), (key1682, 2), (key1900, 2), (key1897, 2), (key1897, 2), (key1912, 2), (key1904, 2), (key1904, 2), (key1927, 2), (key1927, 2), (key1921, 2), (key1921, 2), (key1919, 2), (key1919, 2)]

def rawRow19727 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1291, 2), (key1299, 2), (key1311, 2), (key1327, 2), (key1352, 2), (key1355, 2), (key1299, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1473, 2), (key1386, 2), (key1394, 2), (key1419, 2), (key1445, 2), (key1473, 2), (key1481, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1568, 2), (key1576, 2), (key1617, 2), (key1625, 2), (key1682, 2), (key1684, 2), (key1541, 2), (key1549, 2), (key1617, 2), (key1634, 2), (key1682, 2), (key1690, 2), (key1541, 2), (key1557, 2), (key1568, 2), (key1594, 2), (key1684, 2), (key1690, 2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2), (key1904, 2), (key1919, 2), (key1921, 2), (key1897, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1900, 2), (key1904, 2), (key1912, 2), (key1921, 2), (key1927, 2)]

def rawRow19728 : Integer.Sparse Key := [(key1319, 2), (key1311, 2), (key1352, 2), (key1299, 2), (key1291, 2), (key1327, 2), (key1311, 2), (key1355, 2), (key1352, 2), (key1299, 2), (key1327, 2), (key1319, 2), (key1427, 2), (key1419, 2), (key1473, 2), (key1394, 2), (key1386, 2), (key1445, 2), (key1419, 2), (key1481, 2), (key1473, 2), (key1394, 2), (key1445, 2), (key1427, 2), (key1576, 2), (key1568, 2), (key1625, 2), (key1617, 2), (key1684, 2), (key1682, 2), (key1549, 2), (key1541, 2), (key1634, 2), (key1617, 2), (key1690, 2), (key1682, 2), (key1557, 2), (key1541, 2), (key1594, 2), (key1568, 2), (key1690, 2), (key1684, 2), (key1557, 2), (key1549, 2), (key1594, 2), (key1576, 2), (key1634, 2), (key1625, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1919, 2), (key1900, 2), (key1897, 2), (key1912, 2), (key1904, 2), (key1927, 2), (key1921, 2)]

def rawRow19729 : Integer.Sparse Key := [(key1311, 2), (key1352, 2), (key1319, 2), (key1311, 2), (key1352, 2), (key1291, 2), (key1355, 2), (key1299, 2), (key1327, 2), (key1319, 2), (key1299, 2), (key1327, 2), (key1419, 2), (key1473, 2), (key1427, 2), (key1419, 2), (key1473, 2), (key1386, 2), (key1481, 2), (key1394, 2), (key1445, 2), (key1427, 2), (key1394, 2), (key1445, 2), (key1617, 2), (key1682, 2), (key1568, 2), (key1684, 2), (key1576, 2), (key1625, 2), (key1617, 2), (key1682, 2), (key1541, 2), (key1690, 2), (key1549, 2), (key1634, 2), (key1568, 2), (key1684, 2), (key1541, 2), (key1690, 2), (key1557, 2), (key1594, 2), (key1576, 2), (key1625, 2), (key1549, 2), (key1634, 2), (key1557, 2), (key1594, 2), (key1919, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1904, 2), (key1921, 2), (key1897, 2), (key1927, 2), (key1900, 2), (key1912, 2)]

def rawRow19730 : Integer.Sparse Key := [(key1352, 2), (key1311, 2), (key1319, 2), (key1352, 2), (key1311, 2), (key1355, 2), (key1291, 2), (key1327, 2), (key1299, 2), (key1319, 2), (key1327, 2), (key1299, 2), (key1473, 2), (key1419, 2), (key1427, 2), (key1473, 2), (key1419, 2), (key1481, 2), (key1386, 2), (key1445, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1394, 2), (key1682, 2), (key1617, 2), (key1684, 2), (key1568, 2), (key1625, 2), (key1576, 2), (key1682, 2), (key1617, 2), (key1690, 2), (key1541, 2), (key1634, 2), (key1549, 2), (key1684, 2), (key1568, 2), (key1690, 2), (key1541, 2), (key1594, 2), (key1557, 2), (key1625, 2), (key1576, 2), (key1634, 2), (key1549, 2), (key1594, 2), (key1557, 2), (key1919, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1921, 2), (key1904, 2), (key1927, 2), (key1897, 2), (key1912, 2), (key1900, 2)]

def rawRow19731 : Integer.Sparse Key := [(key1319, 2), (key1352, 2), (key1311, 2), (key1327, 2), (key1355, 2), (key1299, 2), (key1352, 2), (key1291, 2), (key1311, 2), (key1327, 2), (key1299, 2), (key1319, 2), (key1427, 2), (key1473, 2), (key1419, 2), (key1445, 2), (key1481, 2), (key1394, 2), (key1473, 2), (key1386, 2), (key1419, 2), (key1445, 2), (key1394, 2), (key1427, 2), (key1625, 2), (key1684, 2), (key1576, 2), (key1682, 2), (key1568, 2), (key1617, 2), (key1634, 2), (key1690, 2), (key1549, 2), (key1682, 2), (key1541, 2), (key1617, 2), (key1594, 2), (key1690, 2), (key1557, 2), (key1684, 2), (key1541, 2), (key1568, 2), (key1594, 2), (key1634, 2), (key1557, 2), (key1625, 2), (key1549, 2), (key1576, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1919, 2), (key1912, 2), (key1927, 2), (key1900, 2), (key1921, 2), (key1897, 2), (key1904, 2)]

def rawRow19732 : Integer.Sparse Key := [(key1352, 2), (key1319, 2), (key1311, 2), (key1355, 2), (key1327, 2), (key1352, 2), (key1299, 2), (key1311, 2), (key1291, 2), (key1327, 2), (key1319, 2), (key1299, 2), (key1473, 2), (key1427, 2), (key1419, 2), (key1481, 2), (key1445, 2), (key1473, 2), (key1394, 2), (key1419, 2), (key1386, 2), (key1445, 2), (key1427, 2), (key1394, 2), (key1684, 2), (key1625, 2), (key1682, 2), (key1576, 2), (key1617, 2), (key1568, 2), (key1690, 2), (key1634, 2), (key1682, 2), (key1549, 2), (key1617, 2), (key1541, 2), (key1690, 2), (key1594, 2), (key1684, 2), (key1557, 2), (key1568, 2), (key1541, 2), (key1634, 2), (key1594, 2), (key1625, 2), (key1557, 2), (key1576, 2), (key1549, 2), (key1921, 2), (key1919, 2), (key1904, 2), (key1927, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1912, 2), (key1921, 2), (key1900, 2), (key1904, 2), (key1897, 2)]

def rawRow19733 : Integer.Sparse Key := [(key1327, 2), (key1327, 2), (key1355, 2), (key1299, 2), (key1299, 2), (key1319, 2), (key1319, 2), (key1352, 2), (key1352, 2), (key1291, 2), (key1311, 2), (key1311, 2), (key1445, 2), (key1445, 2), (key1481, 2), (key1394, 2), (key1394, 2), (key1427, 2), (key1427, 2), (key1473, 2), (key1473, 2), (key1386, 2), (key1419, 2), (key1419, 2), (key1594, 2), (key1594, 2), (key1634, 2), (key1634, 2), (key1690, 2), (key1690, 2), (key1557, 2), (key1557, 2), (key1625, 2), (key1625, 2), (key1684, 2), (key1684, 2), (key1549, 2), (key1549, 2), (key1576, 2), (key1576, 2), (key1682, 2), (key1682, 2), (key1541, 2), (key1541, 2), (key1568, 2), (key1568, 2), (key1617, 2), (key1617, 2), (key1912, 2), (key1927, 2), (key1927, 2), (key1900, 2), (key1921, 2), (key1921, 2), (key1897, 2), (key1897, 2), (key1904, 2), (key1904, 2), (key1919, 2), (key1919, 2)]

def rawRow19734 : Integer.Sparse Key := [(key1327, 2), (key1355, 2), (key1327, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1311, 2), (key1291, 2), (key1311, 2), (key1445, 2), (key1481, 2), (key1445, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1419, 2), (key1386, 2), (key1419, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1617, 2), (key1541, 2), (key1568, 2), (key1927, 2), (key1912, 2), (key1927, 2), (key1921, 2), (key1900, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1919, 2), (key1897, 2), (key1904, 2)]

def rawRow19735 : Integer.Sparse Key := [(key1355, 2), (key1327, 2), (key1327, 2), (key1352, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1299, 2), (key1311, 2), (key1311, 2), (key1291, 2), (key1481, 2), (key1445, 2), (key1445, 2), (key1473, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1394, 2), (key1419, 2), (key1419, 2), (key1386, 2), (key1690, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1594, 2), (key1684, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1557, 2), (key1682, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1549, 2), (key1617, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1568, 2), (key1541, 2), (key1927, 2), (key1927, 2), (key1912, 2), (key1921, 2), (key1921, 2), (key1900, 2), (key1919, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1904, 2), (key1897, 2)]

def rawRow19736 : Integer.Sparse Key := [(key1386, 2), (key1394, 2), (key1394, 2), (key1541, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1557, 2), (key1897, 2), (key1897, 2), (key1900, 2), (key1291, 2), (key1299, 2), (key1299, 2), (key1568, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1594, 2), (key1904, 2), (key1904, 2), (key1912, 2), (key1311, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1445, 2), (key1617, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1634, 2), (key1919, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1921, 2), (key1927, 2), (key1352, 2), (key1352, 2), (key1355, 2), (key1473, 2), (key1473, 2), (key1481, 2), (key1682, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1684, 2), (key1690, 2)]

def rawRow19737 : Integer.Sparse Key := [(key1394, 2), (key1386, 2), (key1394, 2), (key1549, 2), (key1541, 2), (key1557, 2), (key1541, 2), (key1557, 2), (key1549, 2), (key1897, 2), (key1900, 2), (key1897, 2), (key1299, 2), (key1291, 2), (key1299, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1904, 2), (key1912, 2), (key1904, 2), (key1319, 2), (key1311, 2), (key1327, 2), (key1311, 2), (key1327, 2), (key1319, 2), (key1427, 2), (key1419, 2), (key1445, 2), (key1419, 2), (key1445, 2), (key1427, 2), (key1625, 2), (key1617, 2), (key1634, 2), (key1617, 2), (key1634, 2), (key1625, 2), (key1921, 2), (key1919, 2), (key1927, 2), (key1919, 2), (key1927, 2), (key1921, 2), (key1352, 2), (key1355, 2), (key1352, 2), (key1473, 2), (key1481, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1690, 2), (key1682, 2), (key1690, 2), (key1684, 2)]

def rawRow19738 : Integer.Sparse Key := [(key1394, 2), (key1394, 2), (key1386, 2), (key1557, 2), (key1557, 2), (key1549, 2), (key1549, 2), (key1541, 2), (key1541, 2), (key1900, 2), (key1897, 2), (key1897, 2), (key1299, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1594, 2), (key1576, 2), (key1576, 2), (key1568, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1904, 2), (key1327, 2), (key1327, 2), (key1319, 2), (key1319, 2), (key1311, 2), (key1311, 2), (key1445, 2), (key1445, 2), (key1427, 2), (key1427, 2), (key1419, 2), (key1419, 2), (key1634, 2), (key1634, 2), (key1625, 2), (key1625, 2), (key1617, 2), (key1617, 2), (key1927, 2), (key1927, 2), (key1921, 2), (key1921, 2), (key1919, 2), (key1919, 2), (key1355, 2), (key1352, 2), (key1352, 2), (key1481, 2), (key1473, 2), (key1473, 2), (key1690, 2), (key1690, 2), (key1684, 2), (key1684, 2), (key1682, 2), (key1682, 2)]

def rawRow19739 : Integer.Sparse Key := [(key1541, 2), (key1549, 2), (key1897, 2), (key1386, 2), (key1394, 2), (key1541, 2), (key1557, 2), (key1897, 2), (key1900, 2), (key1394, 2), (key1549, 2), (key1557, 2), (key1568, 2), (key1576, 2), (key1904, 2), (key1291, 2), (key1299, 2), (key1568, 2), (key1594, 2), (key1904, 2), (key1912, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1419, 2), (key1427, 2), (key1617, 2), (key1625, 2), (key1919, 2), (key1921, 2), (key1311, 2), (key1319, 2), (key1617, 2), (key1634, 2), (key1919, 2), (key1927, 2), (key1311, 2), (key1327, 2), (key1419, 2), (key1445, 2), (key1921, 2), (key1927, 2), (key1319, 2), (key1327, 2), (key1427, 2), (key1445, 2), (key1625, 2), (key1634, 2), (key1473, 2), (key1682, 2), (key1684, 2), (key1352, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1355, 2), (key1473, 2), (key1481, 2), (key1684, 2), (key1690, 2)]

def rawRow19740 : Integer.Sparse Key := [(key1549, 2), (key1541, 2), (key1897, 2), (key1394, 2), (key1386, 2), (key1557, 2), (key1541, 2), (key1900, 2), (key1897, 2), (key1394, 2), (key1557, 2), (key1549, 2), (key1576, 2), (key1568, 2), (key1904, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1427, 2), (key1419, 2), (key1625, 2), (key1617, 2), (key1921, 2), (key1919, 2), (key1319, 2), (key1311, 2), (key1634, 2), (key1617, 2), (key1927, 2), (key1919, 2), (key1327, 2), (key1311, 2), (key1445, 2), (key1419, 2), (key1927, 2), (key1921, 2), (key1327, 2), (key1319, 2), (key1445, 2), (key1427, 2), (key1634, 2), (key1625, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1682, 2), (key1355, 2), (key1352, 2), (key1481, 2), (key1473, 2), (key1690, 2), (key1684, 2)]

def rawRow19741 : Integer.Sparse Key := [(key1541, 2), (key1897, 2), (key1549, 2), (key1541, 2), (key1897, 2), (key1386, 2), (key1900, 2), (key1394, 2), (key1557, 2), (key1549, 2), (key1394, 2), (key1557, 2), (key1568, 2), (key1904, 2), (key1576, 2), (key1568, 2), (key1904, 2), (key1291, 2), (key1912, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1594, 2), (key1617, 2), (key1919, 2), (key1419, 2), (key1921, 2), (key1427, 2), (key1625, 2), (key1617, 2), (key1919, 2), (key1311, 2), (key1927, 2), (key1319, 2), (key1634, 2), (key1419, 2), (key1921, 2), (key1311, 2), (key1927, 2), (key1327, 2), (key1445, 2), (key1427, 2), (key1625, 2), (key1319, 2), (key1634, 2), (key1327, 2), (key1445, 2), (key1682, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1473, 2), (key1684, 2), (key1352, 2), (key1690, 2), (key1355, 2), (key1481, 2)]

def rawRow19742 : Integer.Sparse Key := [(key1897, 2), (key1541, 2), (key1549, 2), (key1897, 2), (key1541, 2), (key1900, 2), (key1386, 2), (key1557, 2), (key1394, 2), (key1549, 2), (key1557, 2), (key1394, 2), (key1904, 2), (key1568, 2), (key1576, 2), (key1904, 2), (key1568, 2), (key1912, 2), (key1291, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1299, 2), (key1919, 2), (key1617, 2), (key1921, 2), (key1419, 2), (key1625, 2), (key1427, 2), (key1919, 2), (key1617, 2), (key1927, 2), (key1311, 2), (key1634, 2), (key1319, 2), (key1921, 2), (key1419, 2), (key1927, 2), (key1311, 2), (key1445, 2), (key1327, 2), (key1625, 2), (key1427, 2), (key1634, 2), (key1319, 2), (key1445, 2), (key1327, 2), (key1682, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1684, 2), (key1473, 2), (key1690, 2), (key1352, 2), (key1481, 2), (key1355, 2)]

def rawRow19743 : Integer.Sparse Key := [(key1549, 2), (key1897, 2), (key1541, 2), (key1557, 2), (key1900, 2), (key1394, 2), (key1897, 2), (key1386, 2), (key1541, 2), (key1557, 2), (key1394, 2), (key1549, 2), (key1576, 2), (key1904, 2), (key1568, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1625, 2), (key1921, 2), (key1427, 2), (key1919, 2), (key1419, 2), (key1617, 2), (key1634, 2), (key1927, 2), (key1319, 2), (key1919, 2), (key1311, 2), (key1617, 2), (key1445, 2), (key1927, 2), (key1327, 2), (key1921, 2), (key1311, 2), (key1419, 2), (key1445, 2), (key1634, 2), (key1327, 2), (key1625, 2), (key1319, 2), (key1427, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1682, 2), (key1481, 2), (key1690, 2), (key1355, 2), (key1684, 2), (key1352, 2), (key1473, 2)]

def rawRow19744 : Integer.Sparse Key := [(key1897, 2), (key1549, 2), (key1541, 2), (key1900, 2), (key1557, 2), (key1897, 2), (key1394, 2), (key1541, 2), (key1386, 2), (key1557, 2), (key1549, 2), (key1394, 2), (key1904, 2), (key1576, 2), (key1568, 2), (key1912, 2), (key1594, 2), (key1904, 2), (key1299, 2), (key1568, 2), (key1291, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1921, 2), (key1625, 2), (key1919, 2), (key1427, 2), (key1617, 2), (key1419, 2), (key1927, 2), (key1634, 2), (key1919, 2), (key1319, 2), (key1617, 2), (key1311, 2), (key1927, 2), (key1445, 2), (key1921, 2), (key1327, 2), (key1419, 2), (key1311, 2), (key1634, 2), (key1445, 2), (key1625, 2), (key1327, 2), (key1427, 2), (key1319, 2), (key1684, 2), (key1682, 2), (key1473, 2), (key1690, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1481, 2), (key1684, 2), (key1355, 2), (key1473, 2), (key1352, 2)]

def rawRow19745 : Integer.Sparse Key := [(key1557, 2), (key1557, 2), (key1900, 2), (key1394, 2), (key1394, 2), (key1549, 2), (key1549, 2), (key1897, 2), (key1897, 2), (key1386, 2), (key1541, 2), (key1541, 2), (key1594, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1299, 2), (key1576, 2), (key1576, 2), (key1904, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1568, 2), (key1445, 2), (key1445, 2), (key1634, 2), (key1634, 2), (key1927, 2), (key1927, 2), (key1327, 2), (key1327, 2), (key1625, 2), (key1625, 2), (key1921, 2), (key1921, 2), (key1319, 2), (key1319, 2), (key1427, 2), (key1427, 2), (key1919, 2), (key1919, 2), (key1311, 2), (key1311, 2), (key1419, 2), (key1419, 2), (key1617, 2), (key1617, 2), (key1481, 2), (key1690, 2), (key1690, 2), (key1355, 2), (key1684, 2), (key1684, 2), (key1352, 2), (key1352, 2), (key1473, 2), (key1473, 2), (key1682, 2), (key1682, 2)]

def rawRow19746 : Integer.Sparse Key := [(key1557, 2), (key1900, 2), (key1557, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1541, 2), (key1386, 2), (key1541, 2), (key1594, 2), (key1912, 2), (key1594, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1568, 2), (key1291, 2), (key1568, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1617, 2), (key1311, 2), (key1419, 2), (key1690, 2), (key1481, 2), (key1690, 2), (key1684, 2), (key1355, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1682, 2), (key1352, 2), (key1473, 2)]

def rawRow19747 : Integer.Sparse Key := [(key1900, 2), (key1557, 2), (key1557, 2), (key1897, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1394, 2), (key1541, 2), (key1541, 2), (key1386, 2), (key1912, 2), (key1594, 2), (key1594, 2), (key1904, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1299, 2), (key1568, 2), (key1568, 2), (key1291, 2), (key1927, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1445, 2), (key1921, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1327, 2), (key1919, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1319, 2), (key1617, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1419, 2), (key1311, 2), (key1690, 2), (key1690, 2), (key1481, 2), (key1684, 2), (key1684, 2), (key1355, 2), (key1682, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1473, 2), (key1352, 2)]

def rawRow19748 : Integer.Sparse Key := [(key1419, 2), (key1427, 2), (key1473, 2), (key1568, 2), (key1576, 2), (key1617, 2), (key1625, 2), (key1682, 2), (key1684, 2), (key1904, 2), (key1919, 2), (key1921, 2), (key1311, 2), (key1319, 2), (key1352, 2), (key1541, 2), (key1549, 2), (key1617, 2), (key1634, 2), (key1682, 2), (key1690, 2), (key1897, 2), (key1919, 2), (key1927, 2), (key1291, 2), (key1299, 2), (key1311, 2), (key1327, 2), (key1352, 2), (key1355, 2), (key1386, 2), (key1394, 2), (key1419, 2), (key1445, 2), (key1473, 2), (key1481, 2), (key1541, 2), (key1557, 2), (key1568, 2), (key1594, 2), (key1684, 2), (key1690, 2), (key1897, 2), (key1900, 2), (key1904, 2), (key1912, 2), (key1921, 2), (key1927, 2), (key1299, 2), (key1319, 2), (key1327, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1549, 2), (key1557, 2), (key1576, 2), (key1594, 2), (key1625, 2), (key1634, 2)]

def rawRow19749 : Integer.Sparse Key := [(key1427, 2), (key1419, 2), (key1473, 2), (key1576, 2), (key1568, 2), (key1625, 2), (key1617, 2), (key1684, 2), (key1682, 2), (key1904, 2), (key1921, 2), (key1919, 2), (key1319, 2), (key1311, 2), (key1352, 2), (key1549, 2), (key1541, 2), (key1634, 2), (key1617, 2), (key1690, 2), (key1682, 2), (key1897, 2), (key1927, 2), (key1919, 2), (key1299, 2), (key1291, 2), (key1327, 2), (key1311, 2), (key1355, 2), (key1352, 2), (key1394, 2), (key1386, 2), (key1445, 2), (key1419, 2), (key1481, 2), (key1473, 2), (key1557, 2), (key1541, 2), (key1594, 2), (key1568, 2), (key1690, 2), (key1684, 2), (key1900, 2), (key1897, 2), (key1912, 2), (key1904, 2), (key1927, 2), (key1921, 2), (key1299, 2), (key1327, 2), (key1319, 2), (key1394, 2), (key1445, 2), (key1427, 2), (key1557, 2), (key1549, 2), (key1594, 2), (key1576, 2), (key1634, 2), (key1625, 2)]

def rawRow19750 : Integer.Sparse Key := [(key1419, 2), (key1473, 2), (key1427, 2), (key1617, 2), (key1682, 2), (key1568, 2), (key1684, 2), (key1576, 2), (key1625, 2), (key1919, 2), (key1904, 2), (key1921, 2), (key1311, 2), (key1352, 2), (key1319, 2), (key1617, 2), (key1682, 2), (key1541, 2), (key1690, 2), (key1549, 2), (key1634, 2), (key1919, 2), (key1897, 2), (key1927, 2), (key1311, 2), (key1352, 2), (key1291, 2), (key1355, 2), (key1299, 2), (key1327, 2), (key1419, 2), (key1473, 2), (key1386, 2), (key1481, 2), (key1394, 2), (key1445, 2), (key1568, 2), (key1684, 2), (key1541, 2), (key1690, 2), (key1557, 2), (key1594, 2), (key1904, 2), (key1921, 2), (key1897, 2), (key1927, 2), (key1900, 2), (key1912, 2), (key1319, 2), (key1299, 2), (key1327, 2), (key1427, 2), (key1394, 2), (key1445, 2), (key1576, 2), (key1625, 2), (key1549, 2), (key1634, 2), (key1557, 2), (key1594, 2)]

def rawRow19751 : Integer.Sparse Key := [(key1473, 2), (key1419, 2), (key1427, 2), (key1682, 2), (key1617, 2), (key1684, 2), (key1568, 2), (key1625, 2), (key1576, 2), (key1919, 2), (key1921, 2), (key1904, 2), (key1352, 2), (key1311, 2), (key1319, 2), (key1682, 2), (key1617, 2), (key1690, 2), (key1541, 2), (key1634, 2), (key1549, 2), (key1919, 2), (key1927, 2), (key1897, 2), (key1352, 2), (key1311, 2), (key1355, 2), (key1291, 2), (key1327, 2), (key1299, 2), (key1473, 2), (key1419, 2), (key1481, 2), (key1386, 2), (key1445, 2), (key1394, 2), (key1684, 2), (key1568, 2), (key1690, 2), (key1541, 2), (key1594, 2), (key1557, 2), (key1921, 2), (key1904, 2), (key1927, 2), (key1897, 2), (key1912, 2), (key1900, 2), (key1319, 2), (key1327, 2), (key1299, 2), (key1427, 2), (key1445, 2), (key1394, 2), (key1625, 2), (key1576, 2), (key1634, 2), (key1549, 2), (key1594, 2), (key1557, 2)]

def rawRow19752 : Integer.Sparse Key := [(key1427, 2), (key1473, 2), (key1419, 2), (key1625, 2), (key1684, 2), (key1576, 2), (key1682, 2), (key1568, 2), (key1617, 2), (key1921, 2), (key1904, 2), (key1919, 2), (key1319, 2), (key1352, 2), (key1311, 2), (key1634, 2), (key1690, 2), (key1549, 2), (key1682, 2), (key1541, 2), (key1617, 2), (key1927, 2), (key1897, 2), (key1919, 2), (key1327, 2), (key1355, 2), (key1299, 2), (key1352, 2), (key1291, 2), (key1311, 2), (key1445, 2), (key1481, 2), (key1394, 2), (key1473, 2), (key1386, 2), (key1419, 2), (key1594, 2), (key1690, 2), (key1557, 2), (key1684, 2), (key1541, 2), (key1568, 2), (key1912, 2), (key1927, 2), (key1900, 2), (key1921, 2), (key1897, 2), (key1904, 2), (key1327, 2), (key1299, 2), (key1319, 2), (key1445, 2), (key1394, 2), (key1427, 2), (key1594, 2), (key1634, 2), (key1557, 2), (key1625, 2), (key1549, 2), (key1576, 2)]

def rawRow19753 : Integer.Sparse Key := [(key1473, 2), (key1427, 2), (key1419, 2), (key1684, 2), (key1625, 2), (key1682, 2), (key1576, 2), (key1617, 2), (key1568, 2), (key1921, 2), (key1919, 2), (key1904, 2), (key1352, 2), (key1319, 2), (key1311, 2), (key1690, 2), (key1634, 2), (key1682, 2), (key1549, 2), (key1617, 2), (key1541, 2), (key1927, 2), (key1919, 2), (key1897, 2), (key1355, 2), (key1327, 2), (key1352, 2), (key1299, 2), (key1311, 2), (key1291, 2), (key1481, 2), (key1445, 2), (key1473, 2), (key1394, 2), (key1419, 2), (key1386, 2), (key1690, 2), (key1594, 2), (key1684, 2), (key1557, 2), (key1568, 2), (key1541, 2), (key1927, 2), (key1912, 2), (key1921, 2), (key1900, 2), (key1904, 2), (key1897, 2), (key1327, 2), (key1319, 2), (key1299, 2), (key1445, 2), (key1427, 2), (key1394, 2), (key1634, 2), (key1594, 2), (key1625, 2), (key1557, 2), (key1576, 2), (key1549, 2)]

def rawRow19754 : Integer.Sparse Key := [(key1568, 2), (key1576, 2), (key1904, 2), (key1419, 2), (key1427, 2), (key1617, 2), (key1625, 2), (key1919, 2), (key1921, 2), (key1473, 2), (key1682, 2), (key1684, 2), (key1541, 2), (key1549, 2), (key1897, 2), (key1311, 2), (key1319, 2), (key1617, 2), (key1634, 2), (key1919, 2), (key1927, 2), (key1352, 2), (key1682, 2), (key1690, 2), (key1386, 2), (key1394, 2), (key1541, 2), (key1557, 2), (key1897, 2), (key1900, 2), (key1291, 2), (key1299, 2), (key1568, 2), (key1594, 2), (key1904, 2), (key1912, 2), (key1311, 2), (key1327, 2), (key1419, 2), (key1445, 2), (key1921, 2), (key1927, 2), (key1352, 2), (key1355, 2), (key1473, 2), (key1481, 2), (key1684, 2), (key1690, 2), (key1394, 2), (key1549, 2), (key1557, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1319, 2), (key1327, 2), (key1427, 2), (key1445, 2), (key1625, 2), (key1634, 2)]

def rawRow19755 : Integer.Sparse Key := [(key1576, 2), (key1568, 2), (key1904, 2), (key1427, 2), (key1419, 2), (key1625, 2), (key1617, 2), (key1921, 2), (key1919, 2), (key1473, 2), (key1684, 2), (key1682, 2), (key1549, 2), (key1541, 2), (key1897, 2), (key1319, 2), (key1311, 2), (key1634, 2), (key1617, 2), (key1927, 2), (key1919, 2), (key1352, 2), (key1690, 2), (key1682, 2), (key1394, 2), (key1386, 2), (key1557, 2), (key1541, 2), (key1900, 2), (key1897, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1327, 2), (key1311, 2), (key1445, 2), (key1419, 2), (key1927, 2), (key1921, 2), (key1355, 2), (key1352, 2), (key1481, 2), (key1473, 2), (key1690, 2), (key1684, 2), (key1394, 2), (key1557, 2), (key1549, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1327, 2), (key1319, 2), (key1445, 2), (key1427, 2), (key1634, 2), (key1625, 2)]

def rawRow19756 : Integer.Sparse Key := [(key1568, 2), (key1904, 2), (key1576, 2), (key1617, 2), (key1919, 2), (key1419, 2), (key1921, 2), (key1427, 2), (key1625, 2), (key1682, 2), (key1473, 2), (key1684, 2), (key1541, 2), (key1897, 2), (key1549, 2), (key1617, 2), (key1919, 2), (key1311, 2), (key1927, 2), (key1319, 2), (key1634, 2), (key1682, 2), (key1352, 2), (key1690, 2), (key1541, 2), (key1897, 2), (key1386, 2), (key1900, 2), (key1394, 2), (key1557, 2), (key1568, 2), (key1904, 2), (key1291, 2), (key1912, 2), (key1299, 2), (key1594, 2), (key1419, 2), (key1921, 2), (key1311, 2), (key1927, 2), (key1327, 2), (key1445, 2), (key1473, 2), (key1684, 2), (key1352, 2), (key1690, 2), (key1355, 2), (key1481, 2), (key1549, 2), (key1394, 2), (key1557, 2), (key1576, 2), (key1299, 2), (key1594, 2), (key1427, 2), (key1625, 2), (key1319, 2), (key1634, 2), (key1327, 2), (key1445, 2)]

def rawRow19757 : Integer.Sparse Key := [(key1904, 2), (key1568, 2), (key1576, 2), (key1919, 2), (key1617, 2), (key1921, 2), (key1419, 2), (key1625, 2), (key1427, 2), (key1682, 2), (key1684, 2), (key1473, 2), (key1897, 2), (key1541, 2), (key1549, 2), (key1919, 2), (key1617, 2), (key1927, 2), (key1311, 2), (key1634, 2), (key1319, 2), (key1682, 2), (key1690, 2), (key1352, 2), (key1897, 2), (key1541, 2), (key1900, 2), (key1386, 2), (key1557, 2), (key1394, 2), (key1904, 2), (key1568, 2), (key1912, 2), (key1291, 2), (key1594, 2), (key1299, 2), (key1921, 2), (key1419, 2), (key1927, 2), (key1311, 2), (key1445, 2), (key1327, 2), (key1684, 2), (key1473, 2), (key1690, 2), (key1352, 2), (key1481, 2), (key1355, 2), (key1549, 2), (key1557, 2), (key1394, 2), (key1576, 2), (key1594, 2), (key1299, 2), (key1625, 2), (key1427, 2), (key1634, 2), (key1319, 2), (key1445, 2), (key1327, 2)]

def rawRow19758 : Integer.Sparse Key := [(key1576, 2), (key1904, 2), (key1568, 2), (key1625, 2), (key1921, 2), (key1427, 2), (key1919, 2), (key1419, 2), (key1617, 2), (key1684, 2), (key1473, 2), (key1682, 2), (key1549, 2), (key1897, 2), (key1541, 2), (key1634, 2), (key1927, 2), (key1319, 2), (key1919, 2), (key1311, 2), (key1617, 2), (key1690, 2), (key1352, 2), (key1682, 2), (key1557, 2), (key1900, 2), (key1394, 2), (key1897, 2), (key1386, 2), (key1541, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1445, 2), (key1927, 2), (key1327, 2), (key1921, 2), (key1311, 2), (key1419, 2), (key1481, 2), (key1690, 2), (key1355, 2), (key1684, 2), (key1352, 2), (key1473, 2), (key1557, 2), (key1394, 2), (key1549, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1445, 2), (key1634, 2), (key1327, 2), (key1625, 2), (key1319, 2), (key1427, 2)]

def rawRow19759 : Integer.Sparse Key := [(key1904, 2), (key1576, 2), (key1568, 2), (key1921, 2), (key1625, 2), (key1919, 2), (key1427, 2), (key1617, 2), (key1419, 2), (key1684, 2), (key1682, 2), (key1473, 2), (key1897, 2), (key1549, 2), (key1541, 2), (key1927, 2), (key1634, 2), (key1919, 2), (key1319, 2), (key1617, 2), (key1311, 2), (key1690, 2), (key1682, 2), (key1352, 2), (key1900, 2), (key1557, 2), (key1897, 2), (key1394, 2), (key1541, 2), (key1386, 2), (key1912, 2), (key1594, 2), (key1904, 2), (key1299, 2), (key1568, 2), (key1291, 2), (key1927, 2), (key1445, 2), (key1921, 2), (key1327, 2), (key1419, 2), (key1311, 2), (key1690, 2), (key1481, 2), (key1684, 2), (key1355, 2), (key1473, 2), (key1352, 2), (key1557, 2), (key1549, 2), (key1394, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1634, 2), (key1445, 2), (key1625, 2), (key1327, 2), (key1427, 2), (key1319, 2)]

def rawRow19760 : Integer.Sparse Key := [(key1617, 2), (key1682, 2), (key1919, 2), (key1419, 2), (key1473, 2), (key1568, 2), (key1684, 2), (key1904, 2), (key1921, 2), (key1427, 2), (key1576, 2), (key1625, 2), (key1617, 2), (key1682, 2), (key1919, 2), (key1311, 2), (key1352, 2), (key1541, 2), (key1690, 2), (key1897, 2), (key1927, 2), (key1319, 2), (key1549, 2), (key1634, 2), (key1419, 2), (key1473, 2), (key1568, 2), (key1684, 2), (key1904, 2), (key1921, 2), (key1311, 2), (key1352, 2), (key1541, 2), (key1690, 2), (key1897, 2), (key1927, 2), (key1291, 2), (key1355, 2), (key1386, 2), (key1481, 2), (key1900, 2), (key1912, 2), (key1299, 2), (key1327, 2), (key1394, 2), (key1445, 2), (key1557, 2), (key1594, 2), (key1427, 2), (key1576, 2), (key1625, 2), (key1319, 2), (key1549, 2), (key1634, 2), (key1299, 2), (key1327, 2), (key1394, 2), (key1445, 2), (key1557, 2), (key1594, 2)]

def rawRow19761 : Integer.Sparse Key := [(key1682, 2), (key1617, 2), (key1919, 2), (key1473, 2), (key1419, 2), (key1684, 2), (key1568, 2), (key1921, 2), (key1904, 2), (key1427, 2), (key1625, 2), (key1576, 2), (key1682, 2), (key1617, 2), (key1919, 2), (key1352, 2), (key1311, 2), (key1690, 2), (key1541, 2), (key1927, 2), (key1897, 2), (key1319, 2), (key1634, 2), (key1549, 2), (key1473, 2), (key1419, 2), (key1684, 2), (key1568, 2), (key1921, 2), (key1904, 2), (key1352, 2), (key1311, 2), (key1690, 2), (key1541, 2), (key1927, 2), (key1897, 2), (key1355, 2), (key1291, 2), (key1481, 2), (key1386, 2), (key1912, 2), (key1900, 2), (key1327, 2), (key1299, 2), (key1445, 2), (key1394, 2), (key1594, 2), (key1557, 2), (key1427, 2), (key1625, 2), (key1576, 2), (key1319, 2), (key1634, 2), (key1549, 2), (key1327, 2), (key1299, 2), (key1445, 2), (key1394, 2), (key1594, 2), (key1557, 2)]

def rawRow19762 : Integer.Sparse Key := [(key1617, 2), (key1919, 2), (key1682, 2), (key1568, 2), (key1904, 2), (key1419, 2), (key1921, 2), (key1473, 2), (key1684, 2), (key1576, 2), (key1427, 2), (key1625, 2), (key1617, 2), (key1919, 2), (key1682, 2), (key1541, 2), (key1897, 2), (key1311, 2), (key1927, 2), (key1352, 2), (key1690, 2), (key1549, 2), (key1319, 2), (key1634, 2), (key1568, 2), (key1904, 2), (key1419, 2), (key1921, 2), (key1473, 2), (key1684, 2), (key1541, 2), (key1897, 2), (key1311, 2), (key1927, 2), (key1352, 2), (key1690, 2), (key1386, 2), (key1900, 2), (key1291, 2), (key1912, 2), (key1355, 2), (key1481, 2), (key1394, 2), (key1557, 2), (key1299, 2), (key1594, 2), (key1327, 2), (key1445, 2), (key1576, 2), (key1427, 2), (key1625, 2), (key1549, 2), (key1319, 2), (key1634, 2), (key1394, 2), (key1557, 2), (key1299, 2), (key1594, 2), (key1327, 2), (key1445, 2)]

def rawRow19763 : Integer.Sparse Key := [(key1919, 2), (key1617, 2), (key1682, 2), (key1904, 2), (key1568, 2), (key1921, 2), (key1419, 2), (key1684, 2), (key1473, 2), (key1576, 2), (key1625, 2), (key1427, 2), (key1919, 2), (key1617, 2), (key1682, 2), (key1897, 2), (key1541, 2), (key1927, 2), (key1311, 2), (key1690, 2), (key1352, 2), (key1549, 2), (key1634, 2), (key1319, 2), (key1904, 2), (key1568, 2), (key1921, 2), (key1419, 2), (key1684, 2), (key1473, 2), (key1897, 2), (key1541, 2), (key1927, 2), (key1311, 2), (key1690, 2), (key1352, 2), (key1900, 2), (key1386, 2), (key1912, 2), (key1291, 2), (key1481, 2), (key1355, 2), (key1557, 2), (key1394, 2), (key1594, 2), (key1299, 2), (key1445, 2), (key1327, 2), (key1576, 2), (key1625, 2), (key1427, 2), (key1549, 2), (key1634, 2), (key1319, 2), (key1557, 2), (key1394, 2), (key1594, 2), (key1299, 2), (key1445, 2), (key1327, 2)]

def rawRow19764 : Integer.Sparse Key := [(key1682, 2), (key1919, 2), (key1617, 2), (key1684, 2), (key1921, 2), (key1473, 2), (key1904, 2), (key1419, 2), (key1568, 2), (key1625, 2), (key1427, 2), (key1576, 2), (key1682, 2), (key1919, 2), (key1617, 2), (key1690, 2), (key1927, 2), (key1352, 2), (key1897, 2), (key1311, 2), (key1541, 2), (key1634, 2), (key1319, 2), (key1549, 2), (key1684, 2), (key1921, 2), (key1473, 2), (key1904, 2), (key1419, 2), (key1568, 2), (key1690, 2), (key1927, 2), (key1352, 2), (key1897, 2), (key1311, 2), (key1541, 2), (key1481, 2), (key1912, 2), (key1355, 2), (key1900, 2), (key1291, 2), (key1386, 2), (key1445, 2), (key1594, 2), (key1327, 2), (key1557, 2), (key1299, 2), (key1394, 2), (key1625, 2), (key1427, 2), (key1576, 2), (key1634, 2), (key1319, 2), (key1549, 2), (key1445, 2), (key1594, 2), (key1327, 2), (key1557, 2), (key1299, 2), (key1394, 2)]

def rawRow19765 : Integer.Sparse Key := [(key1919, 2), (key1682, 2), (key1617, 2), (key1921, 2), (key1684, 2), (key1904, 2), (key1473, 2), (key1568, 2), (key1419, 2), (key1625, 2), (key1576, 2), (key1427, 2), (key1919, 2), (key1682, 2), (key1617, 2), (key1927, 2), (key1690, 2), (key1897, 2), (key1352, 2), (key1541, 2), (key1311, 2), (key1634, 2), (key1549, 2), (key1319, 2), (key1921, 2), (key1684, 2), (key1904, 2), (key1473, 2), (key1568, 2), (key1419, 2), (key1927, 2), (key1690, 2), (key1897, 2), (key1352, 2), (key1541, 2), (key1311, 2), (key1912, 2), (key1481, 2), (key1900, 2), (key1355, 2), (key1386, 2), (key1291, 2), (key1594, 2), (key1445, 2), (key1557, 2), (key1327, 2), (key1394, 2), (key1299, 2), (key1625, 2), (key1576, 2), (key1427, 2), (key1634, 2), (key1549, 2), (key1319, 2), (key1594, 2), (key1445, 2), (key1557, 2), (key1327, 2), (key1394, 2), (key1299, 2)]

def rawRow19766 : Integer.Sparse Key := [(key1625, 2), (key1684, 2), (key1921, 2), (key1427, 2), (key1473, 2), (key1576, 2), (key1682, 2), (key1904, 2), (key1919, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1634, 2), (key1690, 2), (key1927, 2), (key1319, 2), (key1352, 2), (key1549, 2), (key1682, 2), (key1897, 2), (key1919, 2), (key1311, 2), (key1541, 2), (key1617, 2), (key1445, 2), (key1481, 2), (key1594, 2), (key1690, 2), (key1912, 2), (key1927, 2), (key1327, 2), (key1355, 2), (key1557, 2), (key1684, 2), (key1900, 2), (key1921, 2), (key1299, 2), (key1352, 2), (key1394, 2), (key1473, 2), (key1897, 2), (key1904, 2), (key1291, 2), (key1311, 2), (key1386, 2), (key1419, 2), (key1541, 2), (key1568, 2), (key1445, 2), (key1594, 2), (key1634, 2), (key1327, 2), (key1557, 2), (key1625, 2), (key1299, 2), (key1319, 2), (key1394, 2), (key1427, 2), (key1549, 2), (key1576, 2)]

def rawRow19767 : Integer.Sparse Key := [(key1684, 2), (key1625, 2), (key1921, 2), (key1473, 2), (key1427, 2), (key1682, 2), (key1576, 2), (key1919, 2), (key1904, 2), (key1419, 2), (key1617, 2), (key1568, 2), (key1690, 2), (key1634, 2), (key1927, 2), (key1352, 2), (key1319, 2), (key1682, 2), (key1549, 2), (key1919, 2), (key1897, 2), (key1311, 2), (key1617, 2), (key1541, 2), (key1481, 2), (key1445, 2), (key1690, 2), (key1594, 2), (key1927, 2), (key1912, 2), (key1355, 2), (key1327, 2), (key1684, 2), (key1557, 2), (key1921, 2), (key1900, 2), (key1352, 2), (key1299, 2), (key1473, 2), (key1394, 2), (key1904, 2), (key1897, 2), (key1311, 2), (key1291, 2), (key1419, 2), (key1386, 2), (key1568, 2), (key1541, 2), (key1445, 2), (key1634, 2), (key1594, 2), (key1327, 2), (key1625, 2), (key1557, 2), (key1319, 2), (key1299, 2), (key1427, 2), (key1394, 2), (key1576, 2), (key1549, 2)]

def rawRow19768 : Integer.Sparse Key := [(key1625, 2), (key1921, 2), (key1684, 2), (key1576, 2), (key1904, 2), (key1427, 2), (key1919, 2), (key1473, 2), (key1682, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1634, 2), (key1927, 2), (key1690, 2), (key1549, 2), (key1897, 2), (key1319, 2), (key1919, 2), (key1352, 2), (key1682, 2), (key1541, 2), (key1311, 2), (key1617, 2), (key1594, 2), (key1912, 2), (key1445, 2), (key1927, 2), (key1481, 2), (key1690, 2), (key1557, 2), (key1900, 2), (key1327, 2), (key1921, 2), (key1355, 2), (key1684, 2), (key1394, 2), (key1897, 2), (key1299, 2), (key1904, 2), (key1352, 2), (key1473, 2), (key1386, 2), (key1541, 2), (key1291, 2), (key1568, 2), (key1311, 2), (key1419, 2), (key1594, 2), (key1445, 2), (key1634, 2), (key1557, 2), (key1327, 2), (key1625, 2), (key1394, 2), (key1549, 2), (key1299, 2), (key1576, 2), (key1319, 2), (key1427, 2)]

def rawRow19769 : Integer.Sparse Key := [(key1921, 2), (key1625, 2), (key1684, 2), (key1904, 2), (key1576, 2), (key1919, 2), (key1427, 2), (key1682, 2), (key1473, 2), (key1568, 2), (key1617, 2), (key1419, 2), (key1927, 2), (key1634, 2), (key1690, 2), (key1897, 2), (key1549, 2), (key1919, 2), (key1319, 2), (key1682, 2), (key1352, 2), (key1541, 2), (key1617, 2), (key1311, 2), (key1912, 2), (key1594, 2), (key1927, 2), (key1445, 2), (key1690, 2), (key1481, 2), (key1900, 2), (key1557, 2), (key1921, 2), (key1327, 2), (key1684, 2), (key1355, 2), (key1897, 2), (key1394, 2), (key1904, 2), (key1299, 2), (key1473, 2), (key1352, 2), (key1541, 2), (key1386, 2), (key1568, 2), (key1291, 2), (key1419, 2), (key1311, 2), (key1594, 2), (key1634, 2), (key1445, 2), (key1557, 2), (key1625, 2), (key1327, 2), (key1549, 2), (key1394, 2), (key1576, 2), (key1299, 2), (key1427, 2), (key1319, 2)]

def rawRow19770 : Integer.Sparse Key := [(key1684, 2), (key1921, 2), (key1625, 2), (key1682, 2), (key1919, 2), (key1473, 2), (key1904, 2), (key1427, 2), (key1576, 2), (key1617, 2), (key1419, 2), (key1568, 2), (key1690, 2), (key1927, 2), (key1634, 2), (key1682, 2), (key1919, 2), (key1352, 2), (key1897, 2), (key1319, 2), (key1549, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1690, 2), (key1927, 2), (key1481, 2), (key1912, 2), (key1445, 2), (key1594, 2), (key1684, 2), (key1921, 2), (key1355, 2), (key1900, 2), (key1327, 2), (key1557, 2), (key1473, 2), (key1904, 2), (key1352, 2), (key1897, 2), (key1299, 2), (key1394, 2), (key1419, 2), (key1568, 2), (key1311, 2), (key1541, 2), (key1291, 2), (key1386, 2), (key1634, 2), (key1445, 2), (key1594, 2), (key1625, 2), (key1327, 2), (key1557, 2), (key1427, 2), (key1576, 2), (key1319, 2), (key1549, 2), (key1299, 2), (key1394, 2)]

def rawRow19771 : Integer.Sparse Key := [(key1921, 2), (key1684, 2), (key1625, 2), (key1919, 2), (key1682, 2), (key1904, 2), (key1473, 2), (key1576, 2), (key1427, 2), (key1617, 2), (key1568, 2), (key1419, 2), (key1927, 2), (key1690, 2), (key1634, 2), (key1919, 2), (key1682, 2), (key1897, 2), (key1352, 2), (key1549, 2), (key1319, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1927, 2), (key1690, 2), (key1912, 2), (key1481, 2), (key1594, 2), (key1445, 2), (key1921, 2), (key1684, 2), (key1900, 2), (key1355, 2), (key1557, 2), (key1327, 2), (key1904, 2), (key1473, 2), (key1897, 2), (key1352, 2), (key1394, 2), (key1299, 2), (key1568, 2), (key1419, 2), (key1541, 2), (key1311, 2), (key1386, 2), (key1291, 2), (key1634, 2), (key1594, 2), (key1445, 2), (key1625, 2), (key1557, 2), (key1327, 2), (key1576, 2), (key1427, 2), (key1549, 2), (key1319, 2), (key1394, 2), (key1299, 2)]

def rawRow19772 : Integer.Sparse Key := [(key1445, 2), (key1445, 2), (key1481, 2), (key1594, 2), (key1594, 2), (key1634, 2), (key1634, 2), (key1690, 2), (key1690, 2), (key1912, 2), (key1927, 2), (key1927, 2), (key1327, 2), (key1327, 2), (key1355, 2), (key1557, 2), (key1557, 2), (key1625, 2), (key1625, 2), (key1684, 2), (key1684, 2), (key1900, 2), (key1921, 2), (key1921, 2), (key1299, 2), (key1299, 2), (key1319, 2), (key1319, 2), (key1352, 2), (key1352, 2), (key1394, 2), (key1394, 2), (key1427, 2), (key1427, 2), (key1473, 2), (key1473, 2), (key1549, 2), (key1549, 2), (key1576, 2), (key1576, 2), (key1682, 2), (key1682, 2), (key1897, 2), (key1897, 2), (key1904, 2), (key1904, 2), (key1919, 2), (key1919, 2), (key1291, 2), (key1311, 2), (key1311, 2), (key1386, 2), (key1419, 2), (key1419, 2), (key1541, 2), (key1541, 2), (key1568, 2), (key1568, 2), (key1617, 2), (key1617, 2)]

def rawRow19773 : Integer.Sparse Key := [(key1445, 2), (key1481, 2), (key1445, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1927, 2), (key1912, 2), (key1927, 2), (key1327, 2), (key1355, 2), (key1327, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1921, 2), (key1900, 2), (key1921, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1919, 2), (key1897, 2), (key1904, 2), (key1311, 2), (key1291, 2), (key1311, 2), (key1419, 2), (key1386, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1617, 2), (key1541, 2), (key1568, 2)]

def rawRow19774 : Integer.Sparse Key := [(key1481, 2), (key1445, 2), (key1445, 2), (key1690, 2), (key1634, 2), (key1690, 2), (key1594, 2), (key1634, 2), (key1594, 2), (key1927, 2), (key1927, 2), (key1912, 2), (key1355, 2), (key1327, 2), (key1327, 2), (key1684, 2), (key1625, 2), (key1684, 2), (key1557, 2), (key1625, 2), (key1557, 2), (key1921, 2), (key1921, 2), (key1900, 2), (key1352, 2), (key1319, 2), (key1352, 2), (key1299, 2), (key1319, 2), (key1299, 2), (key1473, 2), (key1427, 2), (key1473, 2), (key1394, 2), (key1427, 2), (key1394, 2), (key1682, 2), (key1576, 2), (key1682, 2), (key1549, 2), (key1576, 2), (key1549, 2), (key1919, 2), (key1904, 2), (key1919, 2), (key1897, 2), (key1904, 2), (key1897, 2), (key1311, 2), (key1311, 2), (key1291, 2), (key1419, 2), (key1419, 2), (key1386, 2), (key1617, 2), (key1568, 2), (key1617, 2), (key1541, 2), (key1568, 2), (key1541, 2)]

def rawRow19775 : Integer.Sparse Key := [(key1594, 2), (key1594, 2), (key1912, 2), (key1445, 2), (key1445, 2), (key1634, 2), (key1634, 2), (key1927, 2), (key1927, 2), (key1481, 2), (key1690, 2), (key1690, 2), (key1557, 2), (key1557, 2), (key1900, 2), (key1327, 2), (key1327, 2), (key1625, 2), (key1625, 2), (key1921, 2), (key1921, 2), (key1355, 2), (key1684, 2), (key1684, 2), (key1394, 2), (key1394, 2), (key1549, 2), (key1549, 2), (key1897, 2), (key1897, 2), (key1299, 2), (key1299, 2), (key1576, 2), (key1576, 2), (key1904, 2), (key1904, 2), (key1319, 2), (key1319, 2), (key1427, 2), (key1427, 2), (key1919, 2), (key1919, 2), (key1352, 2), (key1352, 2), (key1473, 2), (key1473, 2), (key1682, 2), (key1682, 2), (key1386, 2), (key1541, 2), (key1541, 2), (key1291, 2), (key1568, 2), (key1568, 2), (key1311, 2), (key1311, 2), (key1419, 2), (key1419, 2), (key1617, 2), (key1617, 2)]

def rawRow19776 : Integer.Sparse Key := [(key1594, 2), (key1912, 2), (key1594, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1690, 2), (key1481, 2), (key1690, 2), (key1557, 2), (key1900, 2), (key1557, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1684, 2), (key1355, 2), (key1684, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1682, 2), (key1352, 2), (key1473, 2), (key1541, 2), (key1386, 2), (key1541, 2), (key1568, 2), (key1291, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1617, 2), (key1311, 2), (key1419, 2)]

def rawRow19777 : Integer.Sparse Key := [(key1912, 2), (key1594, 2), (key1594, 2), (key1927, 2), (key1634, 2), (key1927, 2), (key1445, 2), (key1634, 2), (key1445, 2), (key1690, 2), (key1690, 2), (key1481, 2), (key1900, 2), (key1557, 2), (key1557, 2), (key1921, 2), (key1625, 2), (key1921, 2), (key1327, 2), (key1625, 2), (key1327, 2), (key1684, 2), (key1684, 2), (key1355, 2), (key1897, 2), (key1549, 2), (key1897, 2), (key1394, 2), (key1549, 2), (key1394, 2), (key1904, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1299, 2), (key1919, 2), (key1427, 2), (key1919, 2), (key1319, 2), (key1427, 2), (key1319, 2), (key1682, 2), (key1473, 2), (key1682, 2), (key1352, 2), (key1473, 2), (key1352, 2), (key1541, 2), (key1541, 2), (key1386, 2), (key1568, 2), (key1568, 2), (key1291, 2), (key1617, 2), (key1419, 2), (key1617, 2), (key1311, 2), (key1419, 2), (key1311, 2)]

def rawRow19778 : Integer.Sparse Key := [(key1634, 2), (key1690, 2), (key1927, 2), (key1445, 2), (key1481, 2), (key1594, 2), (key1690, 2), (key1912, 2), (key1927, 2), (key1445, 2), (key1594, 2), (key1634, 2), (key1625, 2), (key1684, 2), (key1921, 2), (key1327, 2), (key1355, 2), (key1557, 2), (key1684, 2), (key1900, 2), (key1921, 2), (key1327, 2), (key1557, 2), (key1625, 2), (key1427, 2), (key1473, 2), (key1576, 2), (key1682, 2), (key1904, 2), (key1919, 2), (key1319, 2), (key1352, 2), (key1549, 2), (key1682, 2), (key1897, 2), (key1919, 2), (key1299, 2), (key1352, 2), (key1394, 2), (key1473, 2), (key1897, 2), (key1904, 2), (key1299, 2), (key1319, 2), (key1394, 2), (key1427, 2), (key1549, 2), (key1576, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1617, 2), (key1291, 2), (key1311, 2), (key1386, 2), (key1419, 2), (key1541, 2), (key1568, 2)]

def rawRow19779 : Integer.Sparse Key := [(key1690, 2), (key1634, 2), (key1927, 2), (key1481, 2), (key1445, 2), (key1690, 2), (key1594, 2), (key1927, 2), (key1912, 2), (key1445, 2), (key1634, 2), (key1594, 2), (key1684, 2), (key1625, 2), (key1921, 2), (key1355, 2), (key1327, 2), (key1684, 2), (key1557, 2), (key1921, 2), (key1900, 2), (key1327, 2), (key1625, 2), (key1557, 2), (key1473, 2), (key1427, 2), (key1682, 2), (key1576, 2), (key1919, 2), (key1904, 2), (key1352, 2), (key1319, 2), (key1682, 2), (key1549, 2), (key1919, 2), (key1897, 2), (key1352, 2), (key1299, 2), (key1473, 2), (key1394, 2), (key1904, 2), (key1897, 2), (key1319, 2), (key1299, 2), (key1427, 2), (key1394, 2), (key1576, 2), (key1549, 2), (key1419, 2), (key1617, 2), (key1568, 2), (key1311, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1291, 2), (key1419, 2), (key1386, 2), (key1568, 2), (key1541, 2)]

def rawRow19780 : Integer.Sparse Key := [(key1634, 2), (key1927, 2), (key1690, 2), (key1594, 2), (key1912, 2), (key1445, 2), (key1927, 2), (key1481, 2), (key1690, 2), (key1594, 2), (key1445, 2), (key1634, 2), (key1625, 2), (key1921, 2), (key1684, 2), (key1557, 2), (key1900, 2), (key1327, 2), (key1921, 2), (key1355, 2), (key1684, 2), (key1557, 2), (key1327, 2), (key1625, 2), (key1576, 2), (key1904, 2), (key1427, 2), (key1919, 2), (key1473, 2), (key1682, 2), (key1549, 2), (key1897, 2), (key1319, 2), (key1919, 2), (key1352, 2), (key1682, 2), (key1394, 2), (key1897, 2), (key1299, 2), (key1904, 2), (key1352, 2), (key1473, 2), (key1394, 2), (key1549, 2), (key1299, 2), (key1576, 2), (key1319, 2), (key1427, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1617, 2), (key1386, 2), (key1541, 2), (key1291, 2), (key1568, 2), (key1311, 2), (key1419, 2)]

def rawRow19781 : Integer.Sparse Key := [(key1927, 2), (key1634, 2), (key1690, 2), (key1912, 2), (key1594, 2), (key1927, 2), (key1445, 2), (key1690, 2), (key1481, 2), (key1594, 2), (key1634, 2), (key1445, 2), (key1921, 2), (key1625, 2), (key1684, 2), (key1900, 2), (key1557, 2), (key1921, 2), (key1327, 2), (key1684, 2), (key1355, 2), (key1557, 2), (key1625, 2), (key1327, 2), (key1904, 2), (key1576, 2), (key1919, 2), (key1427, 2), (key1682, 2), (key1473, 2), (key1897, 2), (key1549, 2), (key1919, 2), (key1319, 2), (key1682, 2), (key1352, 2), (key1897, 2), (key1394, 2), (key1904, 2), (key1299, 2), (key1473, 2), (key1352, 2), (key1549, 2), (key1394, 2), (key1576, 2), (key1299, 2), (key1427, 2), (key1319, 2), (key1568, 2), (key1617, 2), (key1419, 2), (key1541, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1386, 2), (key1568, 2), (key1291, 2), (key1419, 2), (key1311, 2)]

def rawRow19782 : Integer.Sparse Key := [(key1690, 2), (key1927, 2), (key1634, 2), (key1690, 2), (key1927, 2), (key1481, 2), (key1912, 2), (key1445, 2), (key1594, 2), (key1634, 2), (key1445, 2), (key1594, 2), (key1684, 2), (key1921, 2), (key1625, 2), (key1684, 2), (key1921, 2), (key1355, 2), (key1900, 2), (key1327, 2), (key1557, 2), (key1625, 2), (key1327, 2), (key1557, 2), (key1682, 2), (key1919, 2), (key1473, 2), (key1904, 2), (key1427, 2), (key1576, 2), (key1682, 2), (key1919, 2), (key1352, 2), (key1897, 2), (key1319, 2), (key1549, 2), (key1473, 2), (key1904, 2), (key1352, 2), (key1897, 2), (key1299, 2), (key1394, 2), (key1427, 2), (key1576, 2), (key1319, 2), (key1549, 2), (key1299, 2), (key1394, 2), (key1617, 2), (key1419, 2), (key1568, 2), (key1617, 2), (key1311, 2), (key1541, 2), (key1419, 2), (key1568, 2), (key1311, 2), (key1541, 2), (key1291, 2), (key1386, 2)]

def rawRow19783 : Integer.Sparse Key := [(key1927, 2), (key1690, 2), (key1634, 2), (key1927, 2), (key1690, 2), (key1912, 2), (key1481, 2), (key1594, 2), (key1445, 2), (key1634, 2), (key1594, 2), (key1445, 2), (key1921, 2), (key1684, 2), (key1625, 2), (key1921, 2), (key1684, 2), (key1900, 2), (key1355, 2), (key1557, 2), (key1327, 2), (key1625, 2), (key1557, 2), (key1327, 2), (key1919, 2), (key1682, 2), (key1904, 2), (key1473, 2), (key1576, 2), (key1427, 2), (key1919, 2), (key1682, 2), (key1897, 2), (key1352, 2), (key1549, 2), (key1319, 2), (key1904, 2), (key1473, 2), (key1897, 2), (key1352, 2), (key1394, 2), (key1299, 2), (key1576, 2), (key1427, 2), (key1549, 2), (key1319, 2), (key1394, 2), (key1299, 2), (key1617, 2), (key1568, 2), (key1419, 2), (key1617, 2), (key1541, 2), (key1311, 2), (key1568, 2), (key1419, 2), (key1541, 2), (key1311, 2), (key1386, 2), (key1291, 2)]

def rawRow19784 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 24), (key1606, 24), (key1636, 24)]

def rawRow19785 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 24), (key1636, 24), (key1606, 24)]

def rawRow19786 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1636, 24), (key1606, 24), (key1606, 24)]

def rawRow19787 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1528, 24), (key1606, 24), (key1636, 24)]

def rawRow19788 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1528, 24), (key1636, 24), (key1606, 24)]

def rawRow19789 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1606, 24), (key1528, 24), (key1636, 24)]

def rawRow19790 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1606, 24), (key1636, 24), (key1528, 24)]

def rawRow19791 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1636, 24), (key1528, 24), (key1606, 24)]

def rawRow19792 : Integer.Sparse Key := [(key1253, 24), (key1606, 24), (key1636, 24), (key1606, 24), (key1528, 24)]

def rawRow19793 : Integer.Sparse Key := [(key1253, 24), (key1636, 24), (key1528, 24), (key1606, 24), (key1606, 24)]

def rawRow19794 : Integer.Sparse Key := [(key1253, 24), (key1636, 24), (key1606, 24), (key1528, 24), (key1606, 24)]

def rawRow19795 : Integer.Sparse Key := [(key1253, 24), (key1636, 24), (key1606, 24), (key1606, 24), (key1528, 24)]

def rawRow19796 : Integer.Sparse Key := [(key1528, 24), (key1253, 24), (key1606, 24), (key1606, 24), (key1636, 24)]

def rawRow19797 : Integer.Sparse Key := [(key1528, 24), (key1253, 24), (key1606, 24), (key1636, 24), (key1606, 24)]

def rawRow19798 : Integer.Sparse Key := [(key1528, 24), (key1253, 24), (key1636, 24), (key1606, 24), (key1606, 24)]

def rawRow19799 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1253, 24), (key1606, 24), (key1636, 24)]

def rawRow19800 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1253, 24), (key1636, 24), (key1606, 24)]

def rawRow19801 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1606, 24), (key1253, 24), (key1636, 24)]

def rawRow19802 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1606, 24), (key1636, 24), (key1253, 24)]

def rawRow19803 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1636, 24), (key1253, 24), (key1606, 24)]

def rawRow19804 : Integer.Sparse Key := [(key1528, 24), (key1606, 24), (key1636, 24), (key1606, 24), (key1253, 24)]

def rawRow19805 : Integer.Sparse Key := [(key1528, 24), (key1636, 24), (key1253, 24), (key1606, 24), (key1606, 24)]

def rawRow19806 : Integer.Sparse Key := [(key1528, 24), (key1636, 24), (key1606, 24), (key1253, 24), (key1606, 24)]

def rawRow19807 : Integer.Sparse Key := [(key1528, 24), (key1636, 24), (key1606, 24), (key1606, 24), (key1253, 24)]

def rawRow19808 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1528, 24), (key1606, 24), (key1636, 24)]

def rawRow19809 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1528, 24), (key1636, 24), (key1606, 24)]

def rawRow19810 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1606, 24), (key1528, 24), (key1636, 24)]

def rawRow19811 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1606, 24), (key1636, 24), (key1528, 24)]

def rawRow19812 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1636, 24), (key1528, 24), (key1606, 24)]

def rawRow19813 : Integer.Sparse Key := [(key1606, 24), (key1253, 24), (key1636, 24), (key1606, 24), (key1528, 24)]

def rawRow19814 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1253, 24), (key1606, 24), (key1636, 24)]

def rawRow19815 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1253, 24), (key1636, 24), (key1606, 24)]

def rawRow19816 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1606, 24), (key1253, 24), (key1636, 24)]

def rawRow19817 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1606, 24), (key1636, 24), (key1253, 24)]

def rawRow19818 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1636, 24), (key1253, 24), (key1606, 24)]

def rawRow19819 : Integer.Sparse Key := [(key1606, 24), (key1528, 24), (key1636, 24), (key1606, 24), (key1253, 24)]

def rawRow19820 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1253, 24), (key1528, 24), (key1636, 24)]

def rawRow19821 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1253, 24), (key1636, 24), (key1528, 24)]

def rawRow19822 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1528, 24), (key1253, 24), (key1636, 24)]

def rawRow19823 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1528, 24), (key1636, 24), (key1253, 24)]

def rawRow19824 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1636, 24), (key1253, 24), (key1528, 24)]

def rawRow19825 : Integer.Sparse Key := [(key1606, 24), (key1606, 24), (key1636, 24), (key1528, 24), (key1253, 24)]

def rawRow19826 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1253, 24), (key1528, 24), (key1606, 24)]

def rawRow19827 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1253, 24), (key1606, 24), (key1528, 24)]

def rawRow19828 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1528, 24), (key1253, 24), (key1606, 24)]

def rawRow19829 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1528, 24), (key1606, 24), (key1253, 24)]

def rawRow19830 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1606, 24), (key1253, 24), (key1528, 24)]

def rawRow19831 : Integer.Sparse Key := [(key1606, 24), (key1636, 24), (key1606, 24), (key1528, 24), (key1253, 24)]

def rawRow19832 : Integer.Sparse Key := [(key1636, 24), (key1253, 24), (key1528, 24), (key1606, 24), (key1606, 24)]

def rawRow19833 : Integer.Sparse Key := [(key1636, 24), (key1253, 24), (key1606, 24), (key1528, 24), (key1606, 24)]

def rawRow19834 : Integer.Sparse Key := [(key1636, 24), (key1253, 24), (key1606, 24), (key1606, 24), (key1528, 24)]

def rawRow19835 : Integer.Sparse Key := [(key1636, 24), (key1528, 24), (key1253, 24), (key1606, 24), (key1606, 24)]

def rawRow19836 : Integer.Sparse Key := [(key1636, 24), (key1528, 24), (key1606, 24), (key1253, 24), (key1606, 24)]

def rawRow19837 : Integer.Sparse Key := [(key1636, 24), (key1528, 24), (key1606, 24), (key1606, 24), (key1253, 24)]

def rawRow19838 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1253, 24), (key1528, 24), (key1606, 24)]

def rawRow19839 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1253, 24), (key1606, 24), (key1528, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19840 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1528, 24), (key1253, 24), (key1606, 24)]

def rawRow19841 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1528, 24), (key1606, 24), (key1253, 24)]

def rawRow19842 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1606, 24), (key1253, 24), (key1528, 24)]

def rawRow19843 : Integer.Sparse Key := [(key1636, 24), (key1606, 24), (key1606, 24), (key1528, 24), (key1253, 24)]

def rawRow19844 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key23, 6), (key35, 6), (key375, 6), (key381, 6), (key381, 6), (key426, 6), (key432, 6), (key426, 6), (key460, 6), (key432, 6), (key460, 6), (key486, 6), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key659, 6), (key663, 6)]

def rawRow19845 : Integer.Sparse Key := [(key23, 6), (key18, 6), (key23, 6), (key35, 6), (key381, 6), (key375, 6), (key381, 6), (key432, 6), (key426, 6), (key460, 6), (key426, 6), (key460, 6), (key432, 6), (key486, 6), (key490, 6), (key486, 6), (key654, 6), (key659, 6), (key663, 6), (key659, 6)]

def rawRow19846 : Integer.Sparse Key := [(key23, 6), (key23, 6), (key18, 6), (key35, 6), (key381, 6), (key381, 6), (key375, 6), (key460, 6), (key460, 6), (key432, 6), (key432, 6), (key426, 6), (key426, 6), (key490, 6), (key486, 6), (key486, 6), (key654, 6), (key663, 6), (key659, 6), (key659, 6)]

def rawRow19847 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key23, 6), (key426, 6), (key432, 6), (key486, 6), (key375, 6), (key381, 6), (key426, 6), (key460, 6), (key486, 6), (key490, 6), (key381, 6), (key432, 6), (key460, 6), (key659, 6), (key654, 6), (key659, 6), (key663, 6)]

def rawRow19848 : Integer.Sparse Key := [(key23, 6), (key18, 6), (key35, 6), (key23, 6), (key432, 6), (key426, 6), (key486, 6), (key381, 6), (key375, 6), (key460, 6), (key426, 6), (key490, 6), (key486, 6), (key381, 6), (key460, 6), (key432, 6), (key659, 6), (key654, 6), (key663, 6), (key659, 6)]

def rawRow19849 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key23, 6), (key23, 6), (key426, 6), (key486, 6), (key432, 6), (key426, 6), (key486, 6), (key375, 6), (key490, 6), (key381, 6), (key460, 6), (key432, 6), (key381, 6), (key460, 6), (key659, 6), (key659, 6), (key654, 6), (key663, 6)]

def rawRow19850 : Integer.Sparse Key := [(key35, 6), (key18, 6), (key23, 6), (key23, 6), (key486, 6), (key426, 6), (key432, 6), (key486, 6), (key426, 6), (key490, 6), (key375, 6), (key460, 6), (key381, 6), (key432, 6), (key460, 6), (key381, 6), (key659, 6), (key659, 6), (key663, 6), (key654, 6)]

def rawRow19851 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key18, 6), (key23, 6), (key432, 6), (key486, 6), (key426, 6), (key460, 6), (key490, 6), (key381, 6), (key486, 6), (key375, 6), (key426, 6), (key460, 6), (key381, 6), (key432, 6), (key659, 6), (key663, 6), (key654, 6), (key659, 6)]

def rawRow19852 : Integer.Sparse Key := [(key35, 6), (key23, 6), (key18, 6), (key23, 6), (key486, 6), (key432, 6), (key426, 6), (key490, 6), (key460, 6), (key486, 6), (key381, 6), (key426, 6), (key375, 6), (key460, 6), (key432, 6), (key381, 6), (key659, 6), (key663, 6), (key659, 6), (key654, 6)]

def rawRow19853 : Integer.Sparse Key := [(key23, 6), (key23, 6), (key35, 6), (key18, 6), (key460, 6), (key460, 6), (key490, 6), (key381, 6), (key381, 6), (key432, 6), (key432, 6), (key486, 6), (key486, 6), (key375, 6), (key426, 6), (key426, 6), (key663, 6), (key654, 6), (key659, 6), (key659, 6)]

def rawRow19854 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key23, 6), (key18, 6), (key460, 6), (key490, 6), (key460, 6), (key432, 6), (key486, 6), (key381, 6), (key486, 6), (key381, 6), (key432, 6), (key426, 6), (key375, 6), (key426, 6), (key663, 6), (key659, 6), (key654, 6), (key659, 6)]

def rawRow19855 : Integer.Sparse Key := [(key35, 6), (key23, 6), (key23, 6), (key18, 6), (key490, 6), (key460, 6), (key460, 6), (key486, 6), (key432, 6), (key486, 6), (key381, 6), (key432, 6), (key381, 6), (key426, 6), (key426, 6), (key375, 6), (key663, 6), (key659, 6), (key659, 6), (key654, 6)]

def rawRow19856 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key48, 6), (key74, 6), (key206, 6), (key212, 6), (key212, 6), (key426, 6), (key432, 6), (key426, 6), (key460, 6), (key432, 6), (key460, 6), (key659, 6), (key659, 6), (key663, 6), (key218, 6), (key486, 6), (key486, 6), (key490, 6)]

def rawRow19857 : Integer.Sparse Key := [(key48, 6), (key43, 6), (key48, 6), (key74, 6), (key212, 6), (key206, 6), (key212, 6), (key432, 6), (key426, 6), (key460, 6), (key426, 6), (key460, 6), (key432, 6), (key659, 6), (key663, 6), (key659, 6), (key218, 6), (key486, 6), (key490, 6), (key486, 6)]

def rawRow19858 : Integer.Sparse Key := [(key48, 6), (key48, 6), (key43, 6), (key74, 6), (key212, 6), (key212, 6), (key206, 6), (key460, 6), (key460, 6), (key432, 6), (key432, 6), (key426, 6), (key426, 6), (key663, 6), (key659, 6), (key659, 6), (key218, 6), (key490, 6), (key486, 6), (key486, 6)]

def rawRow19859 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key48, 6), (key426, 6), (key432, 6), (key659, 6), (key206, 6), (key212, 6), (key426, 6), (key460, 6), (key659, 6), (key663, 6), (key212, 6), (key432, 6), (key460, 6), (key486, 6), (key218, 6), (key486, 6), (key490, 6)]

def rawRow19860 : Integer.Sparse Key := [(key48, 6), (key43, 6), (key74, 6), (key48, 6), (key432, 6), (key426, 6), (key659, 6), (key212, 6), (key206, 6), (key460, 6), (key426, 6), (key663, 6), (key659, 6), (key212, 6), (key460, 6), (key432, 6), (key486, 6), (key218, 6), (key490, 6), (key486, 6)]

def rawRow19861 : Integer.Sparse Key := [(key43, 6), (key74, 6), (key48, 6), (key48, 6), (key426, 6), (key659, 6), (key432, 6), (key426, 6), (key659, 6), (key206, 6), (key663, 6), (key212, 6), (key460, 6), (key432, 6), (key212, 6), (key460, 6), (key486, 6), (key486, 6), (key218, 6), (key490, 6)]

def rawRow19862 : Integer.Sparse Key := [(key74, 6), (key43, 6), (key48, 6), (key48, 6), (key659, 6), (key426, 6), (key432, 6), (key659, 6), (key426, 6), (key663, 6), (key206, 6), (key460, 6), (key212, 6), (key432, 6), (key460, 6), (key212, 6), (key486, 6), (key486, 6), (key490, 6), (key218, 6)]

def rawRow19863 : Integer.Sparse Key := [(key48, 6), (key74, 6), (key43, 6), (key48, 6), (key432, 6), (key659, 6), (key426, 6), (key460, 6), (key663, 6), (key212, 6), (key659, 6), (key206, 6), (key426, 6), (key460, 6), (key212, 6), (key432, 6), (key486, 6), (key490, 6), (key218, 6), (key486, 6)]

def rawRow19864 : Integer.Sparse Key := [(key74, 6), (key48, 6), (key43, 6), (key48, 6), (key659, 6), (key432, 6), (key426, 6), (key663, 6), (key460, 6), (key659, 6), (key212, 6), (key426, 6), (key206, 6), (key460, 6), (key432, 6), (key212, 6), (key486, 6), (key490, 6), (key486, 6), (key218, 6)]

def rawRow19865 : Integer.Sparse Key := [(key48, 6), (key48, 6), (key74, 6), (key43, 6), (key460, 6), (key460, 6), (key663, 6), (key212, 6), (key212, 6), (key432, 6), (key432, 6), (key659, 6), (key659, 6), (key206, 6), (key426, 6), (key426, 6), (key490, 6), (key218, 6), (key486, 6), (key486, 6)]

def rawRow19866 : Integer.Sparse Key := [(key48, 6), (key74, 6), (key48, 6), (key43, 6), (key460, 6), (key663, 6), (key460, 6), (key432, 6), (key659, 6), (key212, 6), (key659, 6), (key212, 6), (key432, 6), (key426, 6), (key206, 6), (key426, 6), (key490, 6), (key486, 6), (key218, 6), (key486, 6)]

def rawRow19867 : Integer.Sparse Key := [(key74, 6), (key48, 6), (key48, 6), (key43, 6), (key663, 6), (key460, 6), (key460, 6), (key659, 6), (key432, 6), (key659, 6), (key212, 6), (key432, 6), (key212, 6), (key426, 6), (key426, 6), (key206, 6), (key490, 6), (key486, 6), (key486, 6), (key218, 6)]

def rawRow19868 : Integer.Sparse Key := [(key100, 6), (key105, 6), (key115, 6), (key137, 6), (key18, 6), (key23, 6), (key35, 6), (key375, 6), (key381, 6), (key426, 6), (key460, 6), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6), (key212, 6), (key381, 6), (key432, 6), (key460, 6)]

def rawRow19869 : Integer.Sparse Key := [(key105, 6), (key100, 6), (key115, 6), (key137, 6), (key23, 6), (key18, 6), (key35, 6), (key381, 6), (key375, 6), (key460, 6), (key426, 6), (key490, 6), (key486, 6), (key654, 6), (key663, 6), (key659, 6), (key212, 6), (key381, 6), (key460, 6), (key432, 6)]

def rawRow19870 : Integer.Sparse Key := [(key100, 6), (key115, 6), (key105, 6), (key137, 6), (key18, 6), (key35, 6), (key23, 6), (key426, 6), (key486, 6), (key375, 6), (key490, 6), (key381, 6), (key460, 6), (key659, 6), (key654, 6), (key663, 6), (key212, 6), (key432, 6), (key381, 6), (key460, 6)]

def rawRow19871 : Integer.Sparse Key := [(key115, 6), (key100, 6), (key105, 6), (key137, 6), (key35, 6), (key18, 6), (key23, 6), (key486, 6), (key426, 6), (key490, 6), (key375, 6), (key460, 6), (key381, 6), (key659, 6), (key663, 6), (key654, 6), (key212, 6), (key432, 6), (key460, 6), (key381, 6)]

def rawRow19872 : Integer.Sparse Key := [(key105, 6), (key115, 6), (key100, 6), (key137, 6), (key23, 6), (key35, 6), (key18, 6), (key460, 6), (key490, 6), (key381, 6), (key486, 6), (key375, 6), (key426, 6), (key663, 6), (key654, 6), (key659, 6), (key212, 6), (key460, 6), (key381, 6), (key432, 6)]

def rawRow19873 : Integer.Sparse Key := [(key115, 6), (key105, 6), (key100, 6), (key137, 6), (key35, 6), (key23, 6), (key18, 6), (key490, 6), (key460, 6), (key486, 6), (key381, 6), (key426, 6), (key375, 6), (key663, 6), (key659, 6), (key654, 6), (key212, 6), (key460, 6), (key432, 6), (key381, 6)]

def rawRow19874 : Integer.Sparse Key := [(key100, 6), (key105, 6), (key137, 6), (key115, 6), (key43, 6), (key48, 6), (key74, 6), (key206, 6), (key212, 6), (key426, 6), (key460, 6), (key659, 6), (key663, 6), (key218, 6), (key486, 6), (key490, 6), (key381, 6), (key212, 6), (key432, 6), (key460, 6)]

def rawRow19875 : Integer.Sparse Key := [(key105, 6), (key100, 6), (key137, 6), (key115, 6), (key48, 6), (key43, 6), (key74, 6), (key212, 6), (key206, 6), (key460, 6), (key426, 6), (key663, 6), (key659, 6), (key218, 6), (key490, 6), (key486, 6), (key381, 6), (key212, 6), (key460, 6), (key432, 6)]

def rawRow19876 : Integer.Sparse Key := [(key100, 6), (key137, 6), (key105, 6), (key115, 6), (key43, 6), (key74, 6), (key48, 6), (key426, 6), (key659, 6), (key206, 6), (key663, 6), (key212, 6), (key460, 6), (key486, 6), (key218, 6), (key490, 6), (key381, 6), (key432, 6), (key212, 6), (key460, 6)]

def rawRow19877 : Integer.Sparse Key := [(key137, 6), (key100, 6), (key105, 6), (key115, 6), (key74, 6), (key43, 6), (key48, 6), (key659, 6), (key426, 6), (key663, 6), (key206, 6), (key460, 6), (key212, 6), (key486, 6), (key490, 6), (key218, 6), (key381, 6), (key432, 6), (key460, 6), (key212, 6)]

def rawRow19878 : Integer.Sparse Key := [(key105, 6), (key137, 6), (key100, 6), (key115, 6), (key48, 6), (key74, 6), (key43, 6), (key460, 6), (key663, 6), (key212, 6), (key659, 6), (key206, 6), (key426, 6), (key490, 6), (key218, 6), (key486, 6), (key381, 6), (key460, 6), (key212, 6), (key432, 6)]

def rawRow19879 : Integer.Sparse Key := [(key137, 6), (key105, 6), (key100, 6), (key115, 6), (key74, 6), (key48, 6), (key43, 6), (key663, 6), (key460, 6), (key659, 6), (key212, 6), (key426, 6), (key206, 6), (key490, 6), (key486, 6), (key218, 6), (key381, 6), (key460, 6), (key432, 6), (key212, 6)]

def rawRow19880 : Integer.Sparse Key := [(key100, 6), (key115, 6), (key137, 6), (key105, 6), (key100, 6), (key115, 6), (key137, 6), (key18, 6), (key35, 6), (key375, 6), (key490, 6), (key654, 6), (key663, 6), (key212, 6), (key381, 6), (key460, 6), (key432, 6), (key212, 6), (key381, 6), (key460, 6)]

def rawRow19881 : Integer.Sparse Key := [(key115, 6), (key100, 6), (key137, 6), (key105, 6), (key115, 6), (key100, 6), (key137, 6), (key35, 6), (key18, 6), (key490, 6), (key375, 6), (key663, 6), (key654, 6), (key212, 6), (key460, 6), (key381, 6), (key432, 6), (key212, 6), (key460, 6), (key381, 6)]

def rawRow19882 : Integer.Sparse Key := [(key100, 6), (key137, 6), (key115, 6), (key105, 6), (key100, 6), (key137, 6), (key115, 6), (key43, 6), (key74, 6), (key206, 6), (key663, 6), (key218, 6), (key490, 6), (key381, 6), (key212, 6), (key460, 6), (key432, 6), (key381, 6), (key212, 6), (key460, 6)]

def rawRow19883 : Integer.Sparse Key := [(key137, 6), (key100, 6), (key115, 6), (key105, 6), (key137, 6), (key100, 6), (key115, 6), (key74, 6), (key43, 6), (key663, 6), (key206, 6), (key490, 6), (key218, 6), (key381, 6), (key460, 6), (key212, 6), (key432, 6), (key381, 6), (key460, 6), (key212, 6)]

def rawRow19884 : Integer.Sparse Key := [(key115, 6), (key137, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key100, 6), (key196, 6), (key200, 6), (key35, 6), (key74, 6), (key18, 6), (key375, 6), (key460, 6), (key212, 6), (key381, 6), (key432, 6), (key460, 6), (key212, 6), (key381, 6)]

def rawRow19885 : Integer.Sparse Key := [(key137, 6), (key115, 6), (key100, 6), (key105, 6), (key137, 6), (key115, 6), (key100, 6), (key200, 6), (key196, 6), (key74, 6), (key35, 6), (key43, 6), (key206, 6), (key460, 6), (key381, 6), (key212, 6), (key432, 6), (key460, 6), (key381, 6), (key212, 6)]

def rawRow19886 : Integer.Sparse Key := [(key105, 6), (key115, 6), (key137, 6), (key100, 6), (key195, 6), (key196, 6), (key200, 6), (key23, 6), (key35, 6), (key48, 6), (key115, 6), (key74, 6), (key137, 6), (key18, 6), (key375, 6), (key426, 6), (key460, 6), (key212, 6), (key381, 6), (key432, 6)]

def rawRow19887 : Integer.Sparse Key := [(key115, 6), (key105, 6), (key137, 6), (key100, 6), (key196, 6), (key195, 6), (key200, 6), (key35, 6), (key23, 6), (key115, 6), (key48, 6), (key137, 6), (key74, 6), (key18, 6), (key426, 6), (key375, 6), (key460, 6), (key212, 6), (key432, 6), (key381, 6)]

def rawRow19888 : Integer.Sparse Key := [(key105, 6), (key137, 6), (key115, 6), (key100, 6), (key195, 6), (key200, 6), (key196, 6), (key48, 6), (key74, 6), (key23, 6), (key137, 6), (key35, 6), (key115, 6), (key43, 6), (key206, 6), (key426, 6), (key460, 6), (key381, 6), (key212, 6), (key432, 6)]

def rawRow19889 : Integer.Sparse Key := [(key137, 6), (key105, 6), (key115, 6), (key100, 6), (key200, 6), (key195, 6), (key196, 6), (key74, 6), (key48, 6), (key137, 6), (key23, 6), (key115, 6), (key35, 6), (key43, 6), (key426, 6), (key206, 6), (key460, 6), (key381, 6), (key432, 6), (key212, 6)]

def rawRow19890 : Integer.Sparse Key := [(key115, 6), (key137, 6), (key105, 6), (key100, 6), (key196, 6), (key200, 6), (key195, 6), (key115, 6), (key137, 6), (key35, 6), (key74, 6), (key23, 6), (key48, 6), (key100, 6), (key18, 6), (key375, 6), (key460, 6), (key432, 6), (key212, 6), (key381, 6)]

def rawRow19891 : Integer.Sparse Key := [(key137, 6), (key115, 6), (key105, 6), (key100, 6), (key200, 6), (key196, 6), (key195, 6), (key137, 6), (key115, 6), (key74, 6), (key35, 6), (key48, 6), (key23, 6), (key100, 6), (key43, 6), (key206, 6), (key460, 6), (key432, 6), (key381, 6), (key212, 6)]

def rawRow19892 : Integer.Sparse Key := [(key195, 6), (key195, 6), (key196, 6), (key200, 6), (key23, 6), (key23, 6), (key35, 6), (key48, 6), (key48, 6), (key105, 6), (key105, 6), (key115, 6), (key115, 6), (key74, 6), (key137, 6), (key137, 6), (key18, 6), (key375, 6), (key426, 6), (key426, 6)]

def rawRow19893 : Integer.Sparse Key := [(key195, 6), (key196, 6), (key195, 6), (key200, 6), (key23, 6), (key35, 6), (key23, 6), (key105, 6), (key115, 6), (key48, 6), (key115, 6), (key48, 6), (key105, 6), (key137, 6), (key74, 6), (key137, 6), (key18, 6), (key426, 6), (key375, 6), (key426, 6)]

def rawRow19894 : Integer.Sparse Key := [(key196, 6), (key195, 6), (key195, 6), (key200, 6), (key35, 6), (key23, 6), (key23, 6), (key115, 6), (key105, 6), (key115, 6), (key48, 6), (key105, 6), (key48, 6), (key137, 6), (key137, 6), (key74, 6), (key18, 6), (key426, 6), (key426, 6), (key375, 6)]

def rawRow19895 : Integer.Sparse Key := [(key195, 6), (key195, 6), (key200, 6), (key196, 6), (key48, 6), (key48, 6), (key74, 6), (key23, 6), (key23, 6), (key105, 6), (key105, 6), (key137, 6), (key137, 6), (key35, 6), (key115, 6), (key115, 6), (key43, 6), (key206, 6), (key426, 6), (key426, 6)]

def rawRow19896 : Integer.Sparse Key := [(key195, 6), (key200, 6), (key195, 6), (key196, 6), (key48, 6), (key74, 6), (key48, 6), (key105, 6), (key137, 6), (key23, 6), (key137, 6), (key23, 6), (key105, 6), (key115, 6), (key35, 6), (key115, 6), (key43, 6), (key426, 6), (key206, 6), (key426, 6)]

def rawRow19897 : Integer.Sparse Key := [(key200, 6), (key195, 6), (key195, 6), (key196, 6), (key74, 6), (key48, 6), (key48, 6), (key137, 6), (key105, 6), (key137, 6), (key23, 6), (key105, 6), (key23, 6), (key115, 6), (key115, 6), (key35, 6), (key43, 6), (key426, 6), (key426, 6), (key206, 6)]

def rawRow19898 : Integer.Sparse Key := [(key195, 6), (key196, 6), (key200, 6), (key195, 6), (key105, 6), (key115, 6), (key137, 6), (key23, 6), (key35, 6), (key48, 6), (key115, 6), (key74, 6), (key137, 6), (key23, 6), (key48, 6), (key105, 6), (key100, 6), (key18, 6), (key375, 6), (key426, 6)]

def rawRow19899 : Integer.Sparse Key := [(key196, 6), (key195, 6), (key200, 6), (key195, 6), (key115, 6), (key105, 6), (key137, 6), (key35, 6), (key23, 6), (key115, 6), (key48, 6), (key137, 6), (key74, 6), (key23, 6), (key105, 6), (key48, 6), (key100, 6), (key18, 6), (key426, 6), (key375, 6)]

def rawRow19900 : Integer.Sparse Key := [(key195, 6), (key200, 6), (key196, 6), (key195, 6), (key105, 6), (key137, 6), (key115, 6), (key48, 6), (key74, 6), (key23, 6), (key137, 6), (key35, 6), (key115, 6), (key48, 6), (key23, 6), (key105, 6), (key100, 6), (key43, 6), (key206, 6), (key426, 6)]

def rawRow19901 : Integer.Sparse Key := [(key200, 6), (key195, 6), (key196, 6), (key195, 6), (key137, 6), (key105, 6), (key115, 6), (key74, 6), (key48, 6), (key137, 6), (key23, 6), (key115, 6), (key35, 6), (key48, 6), (key105, 6), (key23, 6), (key100, 6), (key43, 6), (key426, 6), (key206, 6)]

def rawRow19902 : Integer.Sparse Key := [(key196, 6), (key200, 6), (key195, 6), (key195, 6), (key115, 6), (key137, 6), (key105, 6), (key115, 6), (key137, 6), (key35, 6), (key74, 6), (key23, 6), (key48, 6), (key105, 6), (key23, 6), (key48, 6), (key100, 6), (key100, 6), (key18, 6), (key375, 6)]

def rawRow19903 : Integer.Sparse Key := [(key200, 6), (key196, 6), (key195, 6), (key195, 6), (key137, 6), (key115, 6), (key105, 6), (key137, 6), (key115, 6), (key74, 6), (key35, 6), (key48, 6), (key23, 6), (key105, 6), (key48, 6), (key23, 6), (key100, 6), (key100, 6), (key43, 6), (key206, 6)]

def rawRow19904 : Integer.Sparse Key := [(key1256, 4), (key1256, 4), (key1261, 4), (key1265, 4), (key1268, 4), (key1268, 4), (key1531, 4), (key1531, 4), (key1536, 4), (key1609, 4), (key1609, 4), (key1642, 4), (key1648, 4), (key1651, 4), (key1648, 4), (key1674, 4), (key1651, 4), (key1674, 4), (key1765, 4), (key1768, 4), (key1768, 4), (key1806, 4), (key1809, 4), (key1806, 4), (key1832, 4), (key1809, 4), (key1832, 4), (key1837, 4), (key1837, 4), (key1848, 4)]

def rawRow19905 : Integer.Sparse Key := [(key1256, 4), (key1261, 4), (key1256, 4), (key1268, 4), (key1265, 4), (key1268, 4), (key1531, 4), (key1536, 4), (key1531, 4), (key1609, 4), (key1642, 4), (key1609, 4), (key1651, 4), (key1648, 4), (key1674, 4), (key1648, 4), (key1674, 4), (key1651, 4), (key1768, 4), (key1765, 4), (key1768, 4), (key1809, 4), (key1806, 4), (key1832, 4), (key1806, 4), (key1832, 4), (key1809, 4), (key1837, 4), (key1848, 4), (key1837, 4)]

def rawRow19906 : Integer.Sparse Key := [(key1261, 4), (key1256, 4), (key1256, 4), (key1268, 4), (key1268, 4), (key1265, 4), (key1536, 4), (key1531, 4), (key1531, 4), (key1642, 4), (key1609, 4), (key1609, 4), (key1674, 4), (key1674, 4), (key1651, 4), (key1651, 4), (key1648, 4), (key1648, 4), (key1768, 4), (key1768, 4), (key1765, 4), (key1832, 4), (key1832, 4), (key1809, 4), (key1809, 4), (key1806, 4), (key1806, 4), (key1848, 4), (key1837, 4), (key1837, 4)]

def rawRow19907 : Integer.Sparse Key := [(key1256, 4), (key1265, 4), (key1268, 4), (key1256, 4), (key1261, 4), (key1268, 4), (key1609, 4), (key1648, 4), (key1651, 4), (key1531, 4), (key1648, 4), (key1674, 4), (key1531, 4), (key1536, 4), (key1609, 4), (key1642, 4), (key1651, 4), (key1674, 4), (key1806, 4), (key1809, 4), (key1837, 4), (key1765, 4), (key1768, 4), (key1806, 4), (key1832, 4), (key1837, 4), (key1848, 4), (key1768, 4), (key1809, 4), (key1832, 4)]

def rawRow19908 : Integer.Sparse Key := [(key1256, 4), (key1268, 4), (key1265, 4), (key1261, 4), (key1256, 4), (key1268, 4), (key1609, 4), (key1651, 4), (key1648, 4), (key1531, 4), (key1674, 4), (key1648, 4), (key1536, 4), (key1531, 4), (key1642, 4), (key1609, 4), (key1674, 4), (key1651, 4), (key1809, 4), (key1806, 4), (key1837, 4), (key1768, 4), (key1765, 4), (key1832, 4), (key1806, 4), (key1848, 4), (key1837, 4), (key1768, 4), (key1832, 4), (key1809, 4)]

def rawRow19909 : Integer.Sparse Key := [(key1265, 4), (key1256, 4), (key1268, 4), (key1256, 4), (key1268, 4), (key1261, 4), (key1648, 4), (key1609, 4), (key1651, 4), (key1648, 4), (key1531, 4), (key1674, 4), (key1609, 4), (key1651, 4), (key1531, 4), (key1674, 4), (key1536, 4), (key1642, 4), (key1806, 4), (key1837, 4), (key1809, 4), (key1806, 4), (key1837, 4), (key1765, 4), (key1848, 4), (key1768, 4), (key1832, 4), (key1809, 4), (key1768, 4), (key1832, 4)]

def rawRow19910 : Integer.Sparse Key := [(key1265, 4), (key1268, 4), (key1256, 4), (key1268, 4), (key1256, 4), (key1261, 4), (key1648, 4), (key1651, 4), (key1609, 4), (key1648, 4), (key1674, 4), (key1531, 4), (key1651, 4), (key1609, 4), (key1674, 4), (key1531, 4), (key1642, 4), (key1536, 4), (key1837, 4), (key1806, 4), (key1809, 4), (key1837, 4), (key1806, 4), (key1848, 4), (key1765, 4), (key1832, 4), (key1768, 4), (key1809, 4), (key1832, 4), (key1768, 4)]

def rawRow19911 : Integer.Sparse Key := [(key1268, 4), (key1256, 4), (key1265, 4), (key1261, 4), (key1268, 4), (key1256, 4), (key1651, 4), (key1609, 4), (key1648, 4), (key1674, 4), (key1531, 4), (key1648, 4), (key1642, 4), (key1674, 4), (key1536, 4), (key1651, 4), (key1531, 4), (key1609, 4), (key1809, 4), (key1837, 4), (key1806, 4), (key1832, 4), (key1848, 4), (key1768, 4), (key1837, 4), (key1765, 4), (key1806, 4), (key1832, 4), (key1768, 4), (key1809, 4)]

def rawRow19912 : Integer.Sparse Key := [(key1268, 4), (key1265, 4), (key1256, 4), (key1268, 4), (key1261, 4), (key1256, 4), (key1651, 4), (key1648, 4), (key1609, 4), (key1674, 4), (key1648, 4), (key1531, 4), (key1674, 4), (key1642, 4), (key1651, 4), (key1536, 4), (key1609, 4), (key1531, 4), (key1837, 4), (key1809, 4), (key1806, 4), (key1848, 4), (key1832, 4), (key1837, 4), (key1768, 4), (key1806, 4), (key1765, 4), (key1832, 4), (key1809, 4), (key1768, 4)]

def rawRow19913 : Integer.Sparse Key := [(key1261, 4), (key1268, 4), (key1268, 4), (key1256, 4), (key1256, 4), (key1265, 4), (key1642, 4), (key1674, 4), (key1674, 4), (key1536, 4), (key1651, 4), (key1651, 4), (key1531, 4), (key1531, 4), (key1609, 4), (key1609, 4), (key1648, 4), (key1648, 4), (key1832, 4), (key1832, 4), (key1848, 4), (key1768, 4), (key1768, 4), (key1809, 4), (key1809, 4), (key1837, 4), (key1837, 4), (key1765, 4), (key1806, 4), (key1806, 4)]

def rawRow19914 : Integer.Sparse Key := [(key1268, 4), (key1261, 4), (key1268, 4), (key1256, 4), (key1265, 4), (key1256, 4), (key1674, 4), (key1642, 4), (key1674, 4), (key1651, 4), (key1536, 4), (key1651, 4), (key1609, 4), (key1648, 4), (key1531, 4), (key1648, 4), (key1531, 4), (key1609, 4), (key1832, 4), (key1848, 4), (key1832, 4), (key1809, 4), (key1837, 4), (key1768, 4), (key1837, 4), (key1768, 4), (key1809, 4), (key1806, 4), (key1765, 4), (key1806, 4)]

def rawRow19915 : Integer.Sparse Key := [(key1268, 4), (key1268, 4), (key1261, 4), (key1265, 4), (key1256, 4), (key1256, 4), (key1674, 4), (key1674, 4), (key1642, 4), (key1651, 4), (key1651, 4), (key1536, 4), (key1648, 4), (key1609, 4), (key1648, 4), (key1531, 4), (key1609, 4), (key1531, 4), (key1848, 4), (key1832, 4), (key1832, 4), (key1837, 4), (key1809, 4), (key1837, 4), (key1768, 4), (key1809, 4), (key1768, 4), (key1806, 4), (key1806, 4), (key1765, 4)]

def rawRow19916 : Integer.Sparse Key := [(key1531, 4), (key1531, 4), (key1536, 4), (key1765, 4), (key1768, 4), (key1768, 4), (key1256, 4), (key1256, 4), (key1261, 4), (key1609, 4), (key1609, 4), (key1642, 4), (key1806, 4), (key1809, 4), (key1806, 4), (key1832, 4), (key1809, 4), (key1832, 4), (key1265, 4), (key1268, 4), (key1268, 4), (key1648, 4), (key1651, 4), (key1648, 4), (key1674, 4), (key1651, 4), (key1674, 4), (key1837, 4), (key1837, 4), (key1848, 4)]

def rawRow19917 : Integer.Sparse Key := [(key1531, 4), (key1536, 4), (key1531, 4), (key1768, 4), (key1765, 4), (key1768, 4), (key1256, 4), (key1261, 4), (key1256, 4), (key1609, 4), (key1642, 4), (key1609, 4), (key1809, 4), (key1806, 4), (key1832, 4), (key1806, 4), (key1832, 4), (key1809, 4), (key1268, 4), (key1265, 4), (key1268, 4), (key1651, 4), (key1648, 4), (key1674, 4), (key1648, 4), (key1674, 4), (key1651, 4), (key1837, 4), (key1848, 4), (key1837, 4)]

def rawRow19918 : Integer.Sparse Key := [(key1536, 4), (key1531, 4), (key1531, 4), (key1768, 4), (key1768, 4), (key1765, 4), (key1261, 4), (key1256, 4), (key1256, 4), (key1642, 4), (key1609, 4), (key1609, 4), (key1832, 4), (key1832, 4), (key1809, 4), (key1809, 4), (key1806, 4), (key1806, 4), (key1268, 4), (key1268, 4), (key1265, 4), (key1674, 4), (key1674, 4), (key1651, 4), (key1651, 4), (key1648, 4), (key1648, 4), (key1848, 4), (key1837, 4), (key1837, 4)]

def rawRow19919 : Integer.Sparse Key := [(key1531, 4), (key1765, 4), (key1768, 4), (key1531, 4), (key1536, 4), (key1768, 4), (key1609, 4), (key1806, 4), (key1809, 4), (key1256, 4), (key1806, 4), (key1832, 4), (key1256, 4), (key1261, 4), (key1609, 4), (key1642, 4), (key1809, 4), (key1832, 4), (key1648, 4), (key1651, 4), (key1837, 4), (key1265, 4), (key1268, 4), (key1648, 4), (key1674, 4), (key1837, 4), (key1848, 4), (key1268, 4), (key1651, 4), (key1674, 4)]

def rawRow19920 : Integer.Sparse Key := [(key1531, 4), (key1768, 4), (key1765, 4), (key1536, 4), (key1531, 4), (key1768, 4), (key1609, 4), (key1809, 4), (key1806, 4), (key1256, 4), (key1832, 4), (key1806, 4), (key1261, 4), (key1256, 4), (key1642, 4), (key1609, 4), (key1832, 4), (key1809, 4), (key1651, 4), (key1648, 4), (key1837, 4), (key1268, 4), (key1265, 4), (key1674, 4), (key1648, 4), (key1848, 4), (key1837, 4), (key1268, 4), (key1674, 4), (key1651, 4)]

def rawRow19921 : Integer.Sparse Key := [(key1765, 4), (key1531, 4), (key1768, 4), (key1531, 4), (key1768, 4), (key1536, 4), (key1806, 4), (key1609, 4), (key1809, 4), (key1806, 4), (key1256, 4), (key1832, 4), (key1609, 4), (key1809, 4), (key1256, 4), (key1832, 4), (key1261, 4), (key1642, 4), (key1648, 4), (key1837, 4), (key1651, 4), (key1648, 4), (key1837, 4), (key1265, 4), (key1848, 4), (key1268, 4), (key1674, 4), (key1651, 4), (key1268, 4), (key1674, 4)]

def rawRow19922 : Integer.Sparse Key := [(key1765, 4), (key1768, 4), (key1531, 4), (key1768, 4), (key1531, 4), (key1536, 4), (key1806, 4), (key1809, 4), (key1609, 4), (key1806, 4), (key1832, 4), (key1256, 4), (key1809, 4), (key1609, 4), (key1832, 4), (key1256, 4), (key1642, 4), (key1261, 4), (key1837, 4), (key1648, 4), (key1651, 4), (key1837, 4), (key1648, 4), (key1848, 4), (key1265, 4), (key1674, 4), (key1268, 4), (key1651, 4), (key1674, 4), (key1268, 4)]

def rawRow19923 : Integer.Sparse Key := [(key1768, 4), (key1531, 4), (key1765, 4), (key1536, 4), (key1768, 4), (key1531, 4), (key1809, 4), (key1609, 4), (key1806, 4), (key1832, 4), (key1256, 4), (key1806, 4), (key1642, 4), (key1832, 4), (key1261, 4), (key1809, 4), (key1256, 4), (key1609, 4), (key1651, 4), (key1837, 4), (key1648, 4), (key1674, 4), (key1848, 4), (key1268, 4), (key1837, 4), (key1265, 4), (key1648, 4), (key1674, 4), (key1268, 4), (key1651, 4)]

def rawRow19924 : Integer.Sparse Key := [(key1768, 4), (key1765, 4), (key1531, 4), (key1768, 4), (key1536, 4), (key1531, 4), (key1809, 4), (key1806, 4), (key1609, 4), (key1832, 4), (key1806, 4), (key1256, 4), (key1832, 4), (key1642, 4), (key1809, 4), (key1261, 4), (key1609, 4), (key1256, 4), (key1837, 4), (key1651, 4), (key1648, 4), (key1848, 4), (key1674, 4), (key1837, 4), (key1268, 4), (key1648, 4), (key1265, 4), (key1674, 4), (key1651, 4), (key1268, 4)]

def rawRow19925 : Integer.Sparse Key := [(key1536, 4), (key1768, 4), (key1768, 4), (key1531, 4), (key1531, 4), (key1765, 4), (key1642, 4), (key1832, 4), (key1832, 4), (key1261, 4), (key1809, 4), (key1809, 4), (key1256, 4), (key1256, 4), (key1609, 4), (key1609, 4), (key1806, 4), (key1806, 4), (key1674, 4), (key1674, 4), (key1848, 4), (key1268, 4), (key1268, 4), (key1651, 4), (key1651, 4), (key1837, 4), (key1837, 4), (key1265, 4), (key1648, 4), (key1648, 4)]

def rawRow19926 : Integer.Sparse Key := [(key1768, 4), (key1536, 4), (key1768, 4), (key1531, 4), (key1765, 4), (key1531, 4), (key1832, 4), (key1642, 4), (key1832, 4), (key1809, 4), (key1261, 4), (key1809, 4), (key1609, 4), (key1806, 4), (key1256, 4), (key1806, 4), (key1256, 4), (key1609, 4), (key1674, 4), (key1848, 4), (key1674, 4), (key1651, 4), (key1837, 4), (key1268, 4), (key1837, 4), (key1268, 4), (key1651, 4), (key1648, 4), (key1265, 4), (key1648, 4)]

def rawRow19927 : Integer.Sparse Key := [(key1768, 4), (key1768, 4), (key1536, 4), (key1765, 4), (key1531, 4), (key1531, 4), (key1832, 4), (key1832, 4), (key1642, 4), (key1809, 4), (key1809, 4), (key1261, 4), (key1806, 4), (key1609, 4), (key1806, 4), (key1256, 4), (key1609, 4), (key1256, 4), (key1848, 4), (key1674, 4), (key1674, 4), (key1837, 4), (key1651, 4), (key1837, 4), (key1268, 4), (key1651, 4), (key1268, 4), (key1648, 4), (key1648, 4), (key1265, 4)]

def rawRow19928 : Integer.Sparse Key := [(key1609, 4), (key1648, 4), (key1651, 4), (key1806, 4), (key1809, 4), (key1837, 4), (key1256, 4), (key1265, 4), (key1268, 4), (key1531, 4), (key1648, 4), (key1674, 4), (key1765, 4), (key1768, 4), (key1806, 4), (key1832, 4), (key1837, 4), (key1848, 4), (key1256, 4), (key1261, 4), (key1268, 4), (key1531, 4), (key1536, 4), (key1609, 4), (key1642, 4), (key1651, 4), (key1674, 4), (key1768, 4), (key1809, 4), (key1832, 4)]

def rawRow19929 : Integer.Sparse Key := [(key1609, 4), (key1651, 4), (key1648, 4), (key1809, 4), (key1806, 4), (key1837, 4), (key1256, 4), (key1268, 4), (key1265, 4), (key1531, 4), (key1674, 4), (key1648, 4), (key1768, 4), (key1765, 4), (key1832, 4), (key1806, 4), (key1848, 4), (key1837, 4), (key1261, 4), (key1256, 4), (key1268, 4), (key1536, 4), (key1531, 4), (key1642, 4), (key1609, 4), (key1674, 4), (key1651, 4), (key1768, 4), (key1832, 4), (key1809, 4)]

def rawRow19930 : Integer.Sparse Key := [(key1648, 4), (key1609, 4), (key1651, 4), (key1806, 4), (key1837, 4), (key1809, 4), (key1265, 4), (key1256, 4), (key1268, 4), (key1648, 4), (key1531, 4), (key1674, 4), (key1806, 4), (key1837, 4), (key1765, 4), (key1848, 4), (key1768, 4), (key1832, 4), (key1256, 4), (key1268, 4), (key1261, 4), (key1609, 4), (key1651, 4), (key1531, 4), (key1674, 4), (key1536, 4), (key1642, 4), (key1809, 4), (key1768, 4), (key1832, 4)]

def rawRow19931 : Integer.Sparse Key := [(key1648, 4), (key1651, 4), (key1609, 4), (key1837, 4), (key1806, 4), (key1809, 4), (key1265, 4), (key1268, 4), (key1256, 4), (key1648, 4), (key1674, 4), (key1531, 4), (key1837, 4), (key1806, 4), (key1848, 4), (key1765, 4), (key1832, 4), (key1768, 4), (key1268, 4), (key1256, 4), (key1261, 4), (key1651, 4), (key1609, 4), (key1674, 4), (key1531, 4), (key1642, 4), (key1536, 4), (key1809, 4), (key1832, 4), (key1768, 4)]

def rawRow19932 : Integer.Sparse Key := [(key1651, 4), (key1609, 4), (key1648, 4), (key1809, 4), (key1837, 4), (key1806, 4), (key1268, 4), (key1256, 4), (key1265, 4), (key1674, 4), (key1531, 4), (key1648, 4), (key1832, 4), (key1848, 4), (key1768, 4), (key1837, 4), (key1765, 4), (key1806, 4), (key1261, 4), (key1268, 4), (key1256, 4), (key1642, 4), (key1674, 4), (key1536, 4), (key1651, 4), (key1531, 4), (key1609, 4), (key1832, 4), (key1768, 4), (key1809, 4)]

def rawRow19933 : Integer.Sparse Key := [(key1651, 4), (key1648, 4), (key1609, 4), (key1837, 4), (key1809, 4), (key1806, 4), (key1268, 4), (key1265, 4), (key1256, 4), (key1674, 4), (key1648, 4), (key1531, 4), (key1848, 4), (key1832, 4), (key1837, 4), (key1768, 4), (key1806, 4), (key1765, 4), (key1268, 4), (key1261, 4), (key1256, 4), (key1674, 4), (key1642, 4), (key1651, 4), (key1536, 4), (key1609, 4), (key1531, 4), (key1832, 4), (key1809, 4), (key1768, 4)]

def rawRow19934 : Integer.Sparse Key := [(key1609, 4), (key1806, 4), (key1809, 4), (key1648, 4), (key1651, 4), (key1837, 4), (key1531, 4), (key1765, 4), (key1768, 4), (key1256, 4), (key1806, 4), (key1832, 4), (key1265, 4), (key1268, 4), (key1648, 4), (key1674, 4), (key1837, 4), (key1848, 4), (key1531, 4), (key1536, 4), (key1768, 4), (key1256, 4), (key1261, 4), (key1609, 4), (key1642, 4), (key1809, 4), (key1832, 4), (key1268, 4), (key1651, 4), (key1674, 4)]

def rawRow19935 : Integer.Sparse Key := [(key1609, 4), (key1809, 4), (key1806, 4), (key1651, 4), (key1648, 4), (key1837, 4), (key1531, 4), (key1768, 4), (key1765, 4), (key1256, 4), (key1832, 4), (key1806, 4), (key1268, 4), (key1265, 4), (key1674, 4), (key1648, 4), (key1848, 4), (key1837, 4), (key1536, 4), (key1531, 4), (key1768, 4), (key1261, 4), (key1256, 4), (key1642, 4), (key1609, 4), (key1832, 4), (key1809, 4), (key1268, 4), (key1674, 4), (key1651, 4)]

def rawRow19936 : Integer.Sparse Key := [(key1806, 4), (key1609, 4), (key1809, 4), (key1648, 4), (key1837, 4), (key1651, 4), (key1765, 4), (key1531, 4), (key1768, 4), (key1806, 4), (key1256, 4), (key1832, 4), (key1648, 4), (key1837, 4), (key1265, 4), (key1848, 4), (key1268, 4), (key1674, 4), (key1531, 4), (key1768, 4), (key1536, 4), (key1609, 4), (key1809, 4), (key1256, 4), (key1832, 4), (key1261, 4), (key1642, 4), (key1651, 4), (key1268, 4), (key1674, 4)]

def rawRow19937 : Integer.Sparse Key := [(key1806, 4), (key1809, 4), (key1609, 4), (key1837, 4), (key1648, 4), (key1651, 4), (key1765, 4), (key1768, 4), (key1531, 4), (key1806, 4), (key1832, 4), (key1256, 4), (key1837, 4), (key1648, 4), (key1848, 4), (key1265, 4), (key1674, 4), (key1268, 4), (key1768, 4), (key1531, 4), (key1536, 4), (key1809, 4), (key1609, 4), (key1832, 4), (key1256, 4), (key1642, 4), (key1261, 4), (key1651, 4), (key1674, 4), (key1268, 4)]

def rawRow19938 : Integer.Sparse Key := [(key1809, 4), (key1609, 4), (key1806, 4), (key1651, 4), (key1837, 4), (key1648, 4), (key1768, 4), (key1531, 4), (key1765, 4), (key1832, 4), (key1256, 4), (key1806, 4), (key1674, 4), (key1848, 4), (key1268, 4), (key1837, 4), (key1265, 4), (key1648, 4), (key1536, 4), (key1768, 4), (key1531, 4), (key1642, 4), (key1832, 4), (key1261, 4), (key1809, 4), (key1256, 4), (key1609, 4), (key1674, 4), (key1268, 4), (key1651, 4)]

def rawRow19939 : Integer.Sparse Key := [(key1809, 4), (key1806, 4), (key1609, 4), (key1837, 4), (key1651, 4), (key1648, 4), (key1768, 4), (key1765, 4), (key1531, 4), (key1832, 4), (key1806, 4), (key1256, 4), (key1848, 4), (key1674, 4), (key1837, 4), (key1268, 4), (key1648, 4), (key1265, 4), (key1768, 4), (key1536, 4), (key1531, 4), (key1832, 4), (key1642, 4), (key1809, 4), (key1261, 4), (key1609, 4), (key1256, 4), (key1674, 4), (key1651, 4), (key1268, 4)]

def rawRow19940 : Integer.Sparse Key := [(key1648, 4), (key1806, 4), (key1837, 4), (key1609, 4), (key1651, 4), (key1809, 4), (key1648, 4), (key1806, 4), (key1837, 4), (key1265, 4), (key1765, 4), (key1848, 4), (key1256, 4), (key1268, 4), (key1531, 4), (key1674, 4), (key1768, 4), (key1832, 4), (key1609, 4), (key1651, 4), (key1809, 4), (key1256, 4), (key1268, 4), (key1531, 4), (key1674, 4), (key1768, 4), (key1832, 4), (key1261, 4), (key1536, 4), (key1642, 4)]

def rawRow19941 : Integer.Sparse Key := [(key1648, 4), (key1837, 4), (key1806, 4), (key1651, 4), (key1609, 4), (key1809, 4), (key1648, 4), (key1837, 4), (key1806, 4), (key1265, 4), (key1848, 4), (key1765, 4), (key1268, 4), (key1256, 4), (key1674, 4), (key1531, 4), (key1832, 4), (key1768, 4), (key1651, 4), (key1609, 4), (key1809, 4), (key1268, 4), (key1256, 4), (key1674, 4), (key1531, 4), (key1832, 4), (key1768, 4), (key1261, 4), (key1642, 4), (key1536, 4)]

def rawRow19942 : Integer.Sparse Key := [(key1806, 4), (key1648, 4), (key1837, 4), (key1609, 4), (key1809, 4), (key1651, 4), (key1806, 4), (key1648, 4), (key1837, 4), (key1765, 4), (key1265, 4), (key1848, 4), (key1531, 4), (key1768, 4), (key1256, 4), (key1832, 4), (key1268, 4), (key1674, 4), (key1609, 4), (key1809, 4), (key1651, 4), (key1531, 4), (key1768, 4), (key1256, 4), (key1832, 4), (key1268, 4), (key1674, 4), (key1536, 4), (key1261, 4), (key1642, 4)]

def rawRow19943 : Integer.Sparse Key := [(key1806, 4), (key1837, 4), (key1648, 4), (key1809, 4), (key1609, 4), (key1651, 4), (key1806, 4), (key1837, 4), (key1648, 4), (key1765, 4), (key1848, 4), (key1265, 4), (key1768, 4), (key1531, 4), (key1832, 4), (key1256, 4), (key1674, 4), (key1268, 4), (key1809, 4), (key1609, 4), (key1651, 4), (key1768, 4), (key1531, 4), (key1832, 4), (key1256, 4), (key1674, 4), (key1268, 4), (key1536, 4), (key1642, 4), (key1261, 4)]

def rawRow19944 : Integer.Sparse Key := [(key1837, 4), (key1648, 4), (key1806, 4), (key1651, 4), (key1809, 4), (key1609, 4), (key1837, 4), (key1648, 4), (key1806, 4), (key1848, 4), (key1265, 4), (key1765, 4), (key1674, 4), (key1832, 4), (key1268, 4), (key1768, 4), (key1256, 4), (key1531, 4), (key1651, 4), (key1809, 4), (key1609, 4), (key1674, 4), (key1832, 4), (key1268, 4), (key1768, 4), (key1256, 4), (key1531, 4), (key1642, 4), (key1261, 4), (key1536, 4)]

def rawRow19945 : Integer.Sparse Key := [(key1837, 4), (key1806, 4), (key1648, 4), (key1809, 4), (key1651, 4), (key1609, 4), (key1837, 4), (key1806, 4), (key1648, 4), (key1848, 4), (key1765, 4), (key1265, 4), (key1832, 4), (key1674, 4), (key1768, 4), (key1268, 4), (key1531, 4), (key1256, 4), (key1809, 4), (key1651, 4), (key1609, 4), (key1832, 4), (key1674, 4), (key1768, 4), (key1268, 4), (key1531, 4), (key1256, 4), (key1642, 4), (key1536, 4), (key1261, 4)]

def rawRow19946 : Integer.Sparse Key := [(key1651, 4), (key1809, 4), (key1837, 4), (key1609, 4), (key1648, 4), (key1806, 4), (key1674, 4), (key1832, 4), (key1848, 4), (key1268, 4), (key1768, 4), (key1837, 4), (key1256, 4), (key1265, 4), (key1531, 4), (key1648, 4), (key1765, 4), (key1806, 4), (key1642, 4), (key1674, 4), (key1832, 4), (key1261, 4), (key1268, 4), (key1536, 4), (key1651, 4), (key1768, 4), (key1809, 4), (key1256, 4), (key1531, 4), (key1609, 4)]

def rawRow19947 : Integer.Sparse Key := [(key1651, 4), (key1837, 4), (key1809, 4), (key1648, 4), (key1609, 4), (key1806, 4), (key1674, 4), (key1848, 4), (key1832, 4), (key1268, 4), (key1837, 4), (key1768, 4), (key1265, 4), (key1256, 4), (key1648, 4), (key1531, 4), (key1806, 4), (key1765, 4), (key1674, 4), (key1642, 4), (key1832, 4), (key1268, 4), (key1261, 4), (key1651, 4), (key1536, 4), (key1809, 4), (key1768, 4), (key1256, 4), (key1609, 4), (key1531, 4)]

def rawRow19948 : Integer.Sparse Key := [(key1809, 4), (key1651, 4), (key1837, 4), (key1609, 4), (key1806, 4), (key1648, 4), (key1832, 4), (key1674, 4), (key1848, 4), (key1768, 4), (key1268, 4), (key1837, 4), (key1531, 4), (key1765, 4), (key1256, 4), (key1806, 4), (key1265, 4), (key1648, 4), (key1642, 4), (key1832, 4), (key1674, 4), (key1536, 4), (key1768, 4), (key1261, 4), (key1809, 4), (key1268, 4), (key1651, 4), (key1531, 4), (key1256, 4), (key1609, 4)]

def rawRow19949 : Integer.Sparse Key := [(key1809, 4), (key1837, 4), (key1651, 4), (key1806, 4), (key1609, 4), (key1648, 4), (key1832, 4), (key1848, 4), (key1674, 4), (key1768, 4), (key1837, 4), (key1268, 4), (key1765, 4), (key1531, 4), (key1806, 4), (key1256, 4), (key1648, 4), (key1265, 4), (key1832, 4), (key1642, 4), (key1674, 4), (key1768, 4), (key1536, 4), (key1809, 4), (key1261, 4), (key1651, 4), (key1268, 4), (key1531, 4), (key1609, 4), (key1256, 4)]

def rawRow19950 : Integer.Sparse Key := [(key1837, 4), (key1651, 4), (key1809, 4), (key1648, 4), (key1806, 4), (key1609, 4), (key1848, 4), (key1674, 4), (key1832, 4), (key1837, 4), (key1268, 4), (key1768, 4), (key1648, 4), (key1806, 4), (key1265, 4), (key1765, 4), (key1256, 4), (key1531, 4), (key1674, 4), (key1832, 4), (key1642, 4), (key1651, 4), (key1809, 4), (key1268, 4), (key1768, 4), (key1261, 4), (key1536, 4), (key1609, 4), (key1256, 4), (key1531, 4)]

def rawRow19951 : Integer.Sparse Key := [(key1837, 4), (key1809, 4), (key1651, 4), (key1806, 4), (key1648, 4), (key1609, 4), (key1848, 4), (key1832, 4), (key1674, 4), (key1837, 4), (key1768, 4), (key1268, 4), (key1806, 4), (key1648, 4), (key1765, 4), (key1265, 4), (key1531, 4), (key1256, 4), (key1832, 4), (key1674, 4), (key1642, 4), (key1809, 4), (key1651, 4), (key1768, 4), (key1268, 4), (key1536, 4), (key1261, 4), (key1609, 4), (key1531, 4), (key1256, 4)]

def rawRow19952 : Integer.Sparse Key := [(key1642, 4), (key1674, 4), (key1674, 4), (key1832, 4), (key1832, 4), (key1848, 4), (key1261, 4), (key1268, 4), (key1268, 4), (key1536, 4), (key1651, 4), (key1651, 4), (key1768, 4), (key1768, 4), (key1809, 4), (key1809, 4), (key1837, 4), (key1837, 4), (key1256, 4), (key1256, 4), (key1265, 4), (key1531, 4), (key1531, 4), (key1609, 4), (key1609, 4), (key1648, 4), (key1648, 4), (key1765, 4), (key1806, 4), (key1806, 4)]

def rawRow19953 : Integer.Sparse Key := [(key1674, 4), (key1642, 4), (key1674, 4), (key1832, 4), (key1848, 4), (key1832, 4), (key1268, 4), (key1261, 4), (key1268, 4), (key1651, 4), (key1536, 4), (key1651, 4), (key1809, 4), (key1837, 4), (key1768, 4), (key1837, 4), (key1768, 4), (key1809, 4), (key1256, 4), (key1265, 4), (key1256, 4), (key1609, 4), (key1648, 4), (key1531, 4), (key1648, 4), (key1531, 4), (key1609, 4), (key1806, 4), (key1765, 4), (key1806, 4)]

def rawRow19954 : Integer.Sparse Key := [(key1674, 4), (key1674, 4), (key1642, 4), (key1848, 4), (key1832, 4), (key1832, 4), (key1268, 4), (key1268, 4), (key1261, 4), (key1651, 4), (key1651, 4), (key1536, 4), (key1837, 4), (key1809, 4), (key1837, 4), (key1768, 4), (key1809, 4), (key1768, 4), (key1265, 4), (key1256, 4), (key1256, 4), (key1648, 4), (key1609, 4), (key1648, 4), (key1531, 4), (key1609, 4), (key1531, 4), (key1806, 4), (key1806, 4), (key1765, 4)]

def rawRow19955 : Integer.Sparse Key := [(key1642, 4), (key1832, 4), (key1832, 4), (key1674, 4), (key1674, 4), (key1848, 4), (key1536, 4), (key1768, 4), (key1768, 4), (key1261, 4), (key1809, 4), (key1809, 4), (key1268, 4), (key1268, 4), (key1651, 4), (key1651, 4), (key1837, 4), (key1837, 4), (key1531, 4), (key1531, 4), (key1765, 4), (key1256, 4), (key1256, 4), (key1609, 4), (key1609, 4), (key1806, 4), (key1806, 4), (key1265, 4), (key1648, 4), (key1648, 4)]

def rawRow19956 : Integer.Sparse Key := [(key1832, 4), (key1642, 4), (key1832, 4), (key1674, 4), (key1848, 4), (key1674, 4), (key1768, 4), (key1536, 4), (key1768, 4), (key1809, 4), (key1261, 4), (key1809, 4), (key1651, 4), (key1837, 4), (key1268, 4), (key1837, 4), (key1268, 4), (key1651, 4), (key1531, 4), (key1765, 4), (key1531, 4), (key1609, 4), (key1806, 4), (key1256, 4), (key1806, 4), (key1256, 4), (key1609, 4), (key1648, 4), (key1265, 4), (key1648, 4)]

def rawRow19957 : Integer.Sparse Key := [(key1832, 4), (key1832, 4), (key1642, 4), (key1848, 4), (key1674, 4), (key1674, 4), (key1768, 4), (key1768, 4), (key1536, 4), (key1809, 4), (key1809, 4), (key1261, 4), (key1837, 4), (key1651, 4), (key1837, 4), (key1268, 4), (key1651, 4), (key1268, 4), (key1765, 4), (key1531, 4), (key1531, 4), (key1806, 4), (key1609, 4), (key1806, 4), (key1256, 4), (key1609, 4), (key1256, 4), (key1648, 4), (key1648, 4), (key1265, 4)]

def rawRow19958 : Integer.Sparse Key := [(key1674, 4), (key1832, 4), (key1848, 4), (key1642, 4), (key1674, 4), (key1832, 4), (key1651, 4), (key1809, 4), (key1837, 4), (key1268, 4), (key1768, 4), (key1837, 4), (key1261, 4), (key1268, 4), (key1536, 4), (key1651, 4), (key1768, 4), (key1809, 4), (key1609, 4), (key1648, 4), (key1806, 4), (key1256, 4), (key1265, 4), (key1531, 4), (key1648, 4), (key1765, 4), (key1806, 4), (key1256, 4), (key1531, 4), (key1609, 4)]

def rawRow19959 : Integer.Sparse Key := [(key1674, 4), (key1848, 4), (key1832, 4), (key1674, 4), (key1642, 4), (key1832, 4), (key1651, 4), (key1837, 4), (key1809, 4), (key1268, 4), (key1837, 4), (key1768, 4), (key1268, 4), (key1261, 4), (key1651, 4), (key1536, 4), (key1809, 4), (key1768, 4), (key1648, 4), (key1609, 4), (key1806, 4), (key1265, 4), (key1256, 4), (key1648, 4), (key1531, 4), (key1806, 4), (key1765, 4), (key1256, 4), (key1609, 4), (key1531, 4)]

def rawRow19960 : Integer.Sparse Key := [(key1832, 4), (key1674, 4), (key1848, 4), (key1642, 4), (key1832, 4), (key1674, 4), (key1809, 4), (key1651, 4), (key1837, 4), (key1768, 4), (key1268, 4), (key1837, 4), (key1536, 4), (key1768, 4), (key1261, 4), (key1809, 4), (key1268, 4), (key1651, 4), (key1609, 4), (key1806, 4), (key1648, 4), (key1531, 4), (key1765, 4), (key1256, 4), (key1806, 4), (key1265, 4), (key1648, 4), (key1531, 4), (key1256, 4), (key1609, 4)]

def rawRow19961 : Integer.Sparse Key := [(key1832, 4), (key1848, 4), (key1674, 4), (key1832, 4), (key1642, 4), (key1674, 4), (key1809, 4), (key1837, 4), (key1651, 4), (key1768, 4), (key1837, 4), (key1268, 4), (key1768, 4), (key1536, 4), (key1809, 4), (key1261, 4), (key1651, 4), (key1268, 4), (key1806, 4), (key1609, 4), (key1648, 4), (key1765, 4), (key1531, 4), (key1806, 4), (key1256, 4), (key1648, 4), (key1265, 4), (key1531, 4), (key1609, 4), (key1256, 4)]

def rawRow19962 : Integer.Sparse Key := [(key1848, 4), (key1674, 4), (key1832, 4), (key1674, 4), (key1832, 4), (key1642, 4), (key1837, 4), (key1651, 4), (key1809, 4), (key1837, 4), (key1268, 4), (key1768, 4), (key1651, 4), (key1809, 4), (key1268, 4), (key1768, 4), (key1261, 4), (key1536, 4), (key1648, 4), (key1806, 4), (key1609, 4), (key1648, 4), (key1806, 4), (key1265, 4), (key1765, 4), (key1256, 4), (key1531, 4), (key1609, 4), (key1256, 4), (key1531, 4)]

def rawRow19963 : Integer.Sparse Key := [(key1848, 4), (key1832, 4), (key1674, 4), (key1832, 4), (key1674, 4), (key1642, 4), (key1837, 4), (key1809, 4), (key1651, 4), (key1837, 4), (key1768, 4), (key1268, 4), (key1809, 4), (key1651, 4), (key1768, 4), (key1268, 4), (key1536, 4), (key1261, 4), (key1806, 4), (key1648, 4), (key1609, 4), (key1806, 4), (key1648, 4), (key1765, 4), (key1265, 4), (key1531, 4), (key1256, 4), (key1609, 4), (key1531, 4), (key1256, 4)]

def rawRow19964 : Integer.Sparse Key := [(key1252, 6), (key1257, 6), (key1257, 6), (key1266, 6), (key1527, 6), (key1532, 6), (key1532, 6), (key1605, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1638, 6), (key1649, 6), (key1649, 6), (key1672, 6), (key1766, 6), (key1807, 6), (key1807, 6), (key1830, 6)]

def rawRow19965 : Integer.Sparse Key := [(key1257, 6), (key1252, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1527, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1672, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1830, 6), (key1807, 6)]

def rawRow19966 : Integer.Sparse Key := [(key1257, 6), (key1257, 6), (key1252, 6), (key1266, 6), (key1532, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1638, 6), (key1610, 6), (key1610, 6), (key1605, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1649, 6), (key1766, 6), (key1830, 6), (key1807, 6), (key1807, 6)]

def rawRow19967 : Integer.Sparse Key := [(key1252, 6), (key1257, 6), (key1266, 6), (key1257, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1527, 6), (key1532, 6), (key1605, 6), (key1638, 6), (key1649, 6), (key1672, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1807, 6), (key1766, 6), (key1807, 6), (key1830, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19968 : Integer.Sparse Key := [(key1257, 6), (key1252, 6), (key1266, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1766, 6), (key1830, 6), (key1807, 6)]

def rawRow19969 : Integer.Sparse Key := [(key1252, 6), (key1266, 6), (key1257, 6), (key1257, 6), (key1605, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1527, 6), (key1672, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1638, 6), (key1807, 6), (key1807, 6), (key1766, 6), (key1830, 6)]

def rawRow19970 : Integer.Sparse Key := [(key1266, 6), (key1252, 6), (key1257, 6), (key1257, 6), (key1649, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1672, 6), (key1527, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1532, 6), (key1807, 6), (key1807, 6), (key1830, 6), (key1766, 6)]

def rawRow19971 : Integer.Sparse Key := [(key1257, 6), (key1266, 6), (key1252, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1830, 6), (key1766, 6), (key1807, 6)]

def rawRow19972 : Integer.Sparse Key := [(key1266, 6), (key1257, 6), (key1252, 6), (key1257, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1672, 6), (key1638, 6), (key1649, 6), (key1532, 6), (key1605, 6), (key1527, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1807, 6), (key1830, 6), (key1807, 6), (key1766, 6)]

def rawRow19973 : Integer.Sparse Key := [(key1257, 6), (key1257, 6), (key1266, 6), (key1252, 6), (key1638, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1532, 6), (key1610, 6), (key1610, 6), (key1649, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1605, 6), (key1830, 6), (key1766, 6), (key1807, 6), (key1807, 6)]

def rawRow19974 : Integer.Sparse Key := [(key1257, 6), (key1266, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1672, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1527, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1766, 6), (key1807, 6)]

def rawRow19975 : Integer.Sparse Key := [(key1266, 6), (key1257, 6), (key1257, 6), (key1252, 6), (key1672, 6), (key1638, 6), (key1638, 6), (key1649, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1532, 6), (key1605, 6), (key1605, 6), (key1527, 6), (key1830, 6), (key1807, 6), (key1807, 6), (key1766, 6)]

def rawRow19976 : Integer.Sparse Key := [(key1527, 6), (key1532, 6), (key1532, 6), (key1766, 6), (key1252, 6), (key1257, 6), (key1257, 6), (key1605, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1638, 6), (key1807, 6), (key1807, 6), (key1830, 6), (key1266, 6), (key1649, 6), (key1649, 6), (key1672, 6)]

def rawRow19977 : Integer.Sparse Key := [(key1532, 6), (key1527, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1252, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1830, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1672, 6), (key1649, 6)]

def rawRow19978 : Integer.Sparse Key := [(key1532, 6), (key1532, 6), (key1527, 6), (key1766, 6), (key1257, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1638, 6), (key1610, 6), (key1610, 6), (key1605, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1807, 6), (key1266, 6), (key1672, 6), (key1649, 6), (key1649, 6)]

def rawRow19979 : Integer.Sparse Key := [(key1527, 6), (key1532, 6), (key1766, 6), (key1532, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1252, 6), (key1257, 6), (key1605, 6), (key1638, 6), (key1807, 6), (key1830, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1649, 6), (key1266, 6), (key1649, 6), (key1672, 6)]

def rawRow19980 : Integer.Sparse Key := [(key1532, 6), (key1527, 6), (key1766, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1266, 6), (key1672, 6), (key1649, 6)]

def rawRow19981 : Integer.Sparse Key := [(key1527, 6), (key1766, 6), (key1532, 6), (key1532, 6), (key1605, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1252, 6), (key1830, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1638, 6), (key1649, 6), (key1649, 6), (key1266, 6), (key1672, 6)]

def rawRow19982 : Integer.Sparse Key := [(key1766, 6), (key1527, 6), (key1532, 6), (key1532, 6), (key1807, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1830, 6), (key1252, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1257, 6), (key1649, 6), (key1649, 6), (key1672, 6), (key1266, 6)]

def rawRow19983 : Integer.Sparse Key := [(key1532, 6), (key1766, 6), (key1527, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1672, 6), (key1266, 6), (key1649, 6)]

def rawRow19984 : Integer.Sparse Key := [(key1766, 6), (key1532, 6), (key1527, 6), (key1532, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1830, 6), (key1638, 6), (key1807, 6), (key1257, 6), (key1605, 6), (key1252, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1649, 6), (key1672, 6), (key1649, 6), (key1266, 6)]

def rawRow19985 : Integer.Sparse Key := [(key1532, 6), (key1532, 6), (key1766, 6), (key1527, 6), (key1638, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1257, 6), (key1610, 6), (key1610, 6), (key1807, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1605, 6), (key1672, 6), (key1266, 6), (key1649, 6), (key1649, 6)]

def rawRow19986 : Integer.Sparse Key := [(key1532, 6), (key1766, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1830, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1252, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1266, 6), (key1649, 6)]

def rawRow19987 : Integer.Sparse Key := [(key1766, 6), (key1532, 6), (key1532, 6), (key1527, 6), (key1830, 6), (key1638, 6), (key1638, 6), (key1807, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1257, 6), (key1605, 6), (key1605, 6), (key1252, 6), (key1672, 6), (key1649, 6), (key1649, 6), (key1266, 6)]

def rawRow19988 : Integer.Sparse Key := [(key1605, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1252, 6), (key1257, 6), (key1266, 6), (key1527, 6), (key1532, 6), (key1605, 6), (key1638, 6), (key1649, 6), (key1672, 6), (key1766, 6), (key1807, 6), (key1830, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1638, 6)]

def rawRow19989 : Integer.Sparse Key := [(key1610, 6), (key1605, 6), (key1649, 6), (key1807, 6), (key1257, 6), (key1252, 6), (key1266, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1766, 6), (key1830, 6), (key1807, 6), (key1257, 6), (key1532, 6), (key1638, 6), (key1610, 6)]

def rawRow19990 : Integer.Sparse Key := [(key1605, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1252, 6), (key1266, 6), (key1257, 6), (key1605, 6), (key1649, 6), (key1527, 6), (key1672, 6), (key1532, 6), (key1638, 6), (key1807, 6), (key1766, 6), (key1830, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1638, 6)]

def rawRow19991 : Integer.Sparse Key := [(key1649, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1266, 6), (key1252, 6), (key1257, 6), (key1649, 6), (key1605, 6), (key1672, 6), (key1527, 6), (key1638, 6), (key1532, 6), (key1807, 6), (key1830, 6), (key1766, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1532, 6)]

def rawRow19992 : Integer.Sparse Key := [(key1610, 6), (key1649, 6), (key1605, 6), (key1807, 6), (key1257, 6), (key1266, 6), (key1252, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1830, 6), (key1766, 6), (key1807, 6), (key1257, 6), (key1638, 6), (key1532, 6), (key1610, 6)]

def rawRow19993 : Integer.Sparse Key := [(key1649, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1266, 6), (key1257, 6), (key1252, 6), (key1672, 6), (key1638, 6), (key1649, 6), (key1532, 6), (key1605, 6), (key1527, 6), (key1830, 6), (key1807, 6), (key1766, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1532, 6)]

def rawRow19994 : Integer.Sparse Key := [(key1605, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1527, 6), (key1532, 6), (key1766, 6), (key1252, 6), (key1257, 6), (key1605, 6), (key1638, 6), (key1807, 6), (key1830, 6), (key1266, 6), (key1649, 6), (key1672, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1638, 6)]

def rawRow19995 : Integer.Sparse Key := [(key1610, 6), (key1605, 6), (key1807, 6), (key1649, 6), (key1532, 6), (key1527, 6), (key1766, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1266, 6), (key1672, 6), (key1649, 6), (key1532, 6), (key1257, 6), (key1638, 6), (key1610, 6)]

def rawRow19996 : Integer.Sparse Key := [(key1605, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1527, 6), (key1766, 6), (key1532, 6), (key1605, 6), (key1807, 6), (key1252, 6), (key1830, 6), (key1257, 6), (key1638, 6), (key1649, 6), (key1266, 6), (key1672, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1638, 6)]

def rawRow19997 : Integer.Sparse Key := [(key1807, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, 6), (key1527, 6), (key1532, 6), (key1807, 6), (key1605, 6), (key1830, 6), (key1252, 6), (key1638, 6), (key1257, 6), (key1649, 6), (key1672, 6), (key1266, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1257, 6)]

def rawRow19998 : Integer.Sparse Key := [(key1610, 6), (key1807, 6), (key1605, 6), (key1649, 6), (key1532, 6), (key1766, 6), (key1527, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1672, 6), (key1266, 6), (key1649, 6), (key1532, 6), (key1638, 6), (key1257, 6), (key1610, 6)]

def rawRow19999 : Integer.Sparse Key := [(key1807, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1766, 6), (key1532, 6), (key1527, 6), (key1830, 6), (key1638, 6), (key1807, 6), (key1257, 6), (key1605, 6), (key1252, 6), (key1672, 6), (key1649, 6), (key1266, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1257, 6)]

def rawRow20000 : Integer.Sparse Key := [(key1605, 6), (key1649, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1807, 6), (key1252, 6), (key1266, 6), (key1527, 6), (key1672, 6), (key1766, 6), (key1830, 6), (key1257, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1532, 6), (key1638, 6)]

def rawRow20001 : Integer.Sparse Key := [(key1649, 6), (key1605, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1807, 6), (key1266, 6), (key1252, 6), (key1672, 6), (key1527, 6), (key1830, 6), (key1766, 6), (key1257, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1638, 6), (key1532, 6)]

def rawRow20002 : Integer.Sparse Key := [(key1605, 6), (key1807, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1649, 6), (key1527, 6), (key1766, 6), (key1252, 6), (key1830, 6), (key1266, 6), (key1672, 6), (key1532, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1257, 6), (key1638, 6)]

def rawRow20003 : Integer.Sparse Key := [(key1807, 6), (key1605, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1649, 6), (key1766, 6), (key1527, 6), (key1830, 6), (key1252, 6), (key1672, 6), (key1266, 6), (key1532, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1638, 6), (key1257, 6)]

def rawRow20004 : Integer.Sparse Key := [(key1649, 6), (key1807, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1605, 6), (key1672, 6), (key1830, 6), (key1266, 6), (key1766, 6), (key1252, 6), (key1527, 6), (key1638, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1257, 6), (key1532, 6)]

def rawRow20005 : Integer.Sparse Key := [(key1807, 6), (key1649, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1605, 6), (key1830, 6), (key1672, 6), (key1766, 6), (key1266, 6), (key1527, 6), (key1252, 6), (key1638, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1532, 6), (key1257, 6)]

def rawRow20006 : Integer.Sparse Key := [(key1610, 6), (key1649, 6), (key1807, 6), (key1605, 6), (key1638, 6), (key1672, 6), (key1830, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1252, 6), (key1527, 6), (key1605, 6), (key1638, 6), (key1257, 6), (key1532, 6), (key1610, 6)]

def rawRow20007 : Integer.Sparse Key := [(key1649, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1672, 6), (key1638, 6), (key1830, 6), (key1266, 6), (key1257, 6), (key1649, 6), (key1532, 6), (key1807, 6), (key1766, 6), (key1252, 6), (key1605, 6), (key1527, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1532, 6)]

def rawRow20008 : Integer.Sparse Key := [(key1610, 6), (key1807, 6), (key1649, 6), (key1605, 6), (key1638, 6), (key1830, 6), (key1672, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1527, 6), (key1252, 6), (key1605, 6), (key1638, 6), (key1532, 6), (key1257, 6), (key1610, 6)]

def rawRow20009 : Integer.Sparse Key := [(key1807, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1830, 6), (key1638, 6), (key1672, 6), (key1766, 6), (key1532, 6), (key1807, 6), (key1257, 6), (key1649, 6), (key1266, 6), (key1527, 6), (key1605, 6), (key1252, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1257, 6)]

def rawRow20010 : Integer.Sparse Key := [(key1649, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1672, 6), (key1830, 6), (key1638, 6), (key1649, 6), (key1807, 6), (key1266, 6), (key1766, 6), (key1257, 6), (key1532, 6), (key1605, 6), (key1252, 6), (key1527, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1532, 6)]

def rawRow20011 : Integer.Sparse Key := [(key1807, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1830, 6), (key1672, 6), (key1638, 6), (key1807, 6), (key1649, 6), (key1766, 6), (key1266, 6), (key1532, 6), (key1257, 6), (key1605, 6), (key1527, 6), (key1252, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1257, 6)]

def rawRow20012 : Integer.Sparse Key := [(key1638, 6), (key1638, 6), (key1672, 6), (key1830, 6), (key1257, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1532, 6), (key1610, 6), (key1610, 6), (key1649, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1807, 6), (key1252, 6), (key1527, 6), (key1605, 6), (key1605, 6)]

def rawRow20013 : Integer.Sparse Key := [(key1638, 6), (key1672, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1266, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1766, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1527, 6), (key1605, 6)]

def rawRow20014 : Integer.Sparse Key := [(key1672, 6), (key1638, 6), (key1638, 6), (key1830, 6), (key1266, 6), (key1257, 6), (key1257, 6), (key1649, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1532, 6), (key1807, 6), (key1807, 6), (key1766, 6), (key1252, 6), (key1605, 6), (key1605, 6), (key1527, 6)]

def rawRow20015 : Integer.Sparse Key := [(key1638, 6), (key1638, 6), (key1830, 6), (key1672, 6), (key1532, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1257, 6), (key1610, 6), (key1610, 6), (key1807, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1649, 6), (key1527, 6), (key1252, 6), (key1605, 6), (key1605, 6)]

def rawRow20016 : Integer.Sparse Key := [(key1638, 6), (key1830, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1766, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1266, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1252, 6), (key1605, 6)]

def rawRow20017 : Integer.Sparse Key := [(key1830, 6), (key1638, 6), (key1638, 6), (key1672, 6), (key1766, 6), (key1532, 6), (key1532, 6), (key1807, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1257, 6), (key1649, 6), (key1649, 6), (key1266, 6), (key1527, 6), (key1605, 6), (key1605, 6), (key1252, 6)]

def rawRow20018 : Integer.Sparse Key := [(key1638, 6), (key1672, 6), (key1830, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1252, 6), (key1527, 6), (key1605, 6)]

def rawRow20019 : Integer.Sparse Key := [(key1672, 6), (key1638, 6), (key1830, 6), (key1638, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1266, 6), (key1257, 6), (key1649, 6), (key1532, 6), (key1807, 6), (key1766, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1605, 6), (key1252, 6), (key1605, 6), (key1527, 6)]

def rawRow20020 : Integer.Sparse Key := [(key1638, 6), (key1830, 6), (key1672, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1527, 6), (key1252, 6), (key1605, 6)]

def rawRow20021 : Integer.Sparse Key := [(key1830, 6), (key1638, 6), (key1672, 6), (key1638, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1766, 6), (key1532, 6), (key1807, 6), (key1257, 6), (key1649, 6), (key1266, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1605, 6), (key1527, 6), (key1605, 6), (key1252, 6)]

def rawRow20022 : Integer.Sparse Key := [(key1672, 6), (key1830, 6), (key1638, 6), (key1638, 6), (key1649, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1266, 6), (key1766, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1532, 6), (key1605, 6), (key1605, 6), (key1252, 6), (key1527, 6)]

def rawRow20023 : Integer.Sparse Key := [(key1830, 6), (key1672, 6), (key1638, 6), (key1638, 6), (key1807, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1766, 6), (key1266, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1257, 6), (key1605, 6), (key1605, 6), (key1527, 6), (key1252, 6)]

def rawRow20024 : Integer.Sparse Key := [(key1293, 6), (key1313, 6), (key1313, 6), (key1323, 6), (key1388, 6), (key1421, 6), (key1421, 6), (key1441, 6), (key1543, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1570, 6), (key1590, 6), (key1619, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1621, 6), (key1630, 6)]

def rawRow20025 : Integer.Sparse Key := [(key1293, 6), (key1313, 6), (key1323, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1441, 6), (key1421, 6), (key1543, 6), (key1553, 6), (key1543, 6), (key1570, 6), (key1590, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1619, 6), (key1630, 6), (key1621, 6)]

def rawRow20026 : Integer.Sparse Key := [(key1293, 6), (key1323, 6), (key1313, 6), (key1313, 6), (key1388, 6), (key1441, 6), (key1421, 6), (key1421, 6), (key1553, 6), (key1543, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1570, 6), (key1630, 6), (key1630, 6), (key1621, 6), (key1621, 6), (key1619, 6), (key1619, 6)]

def rawRow20027 : Integer.Sparse Key := [(key1313, 6), (key1293, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1388, 6), (key1421, 6), (key1441, 6), (key1570, 6), (key1619, 6), (key1621, 6), (key1543, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1590, 6), (key1621, 6), (key1630, 6)]

def rawRow20028 : Integer.Sparse Key := [(key1313, 6), (key1293, 6), (key1323, 6), (key1313, 6), (key1421, 6), (key1388, 6), (key1441, 6), (key1421, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1619, 6), (key1553, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1630, 6), (key1621, 6)]

def rawRow20029 : Integer.Sparse Key := [(key1313, 6), (key1313, 6), (key1293, 6), (key1323, 6), (key1421, 6), (key1421, 6), (key1388, 6), (key1441, 6), (key1619, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1570, 6), (key1621, 6), (key1543, 6), (key1630, 6), (key1553, 6), (key1590, 6)]

def rawRow20030 : Integer.Sparse Key := [(key1313, 6), (key1313, 6), (key1323, 6), (key1293, 6), (key1421, 6), (key1421, 6), (key1441, 6), (key1388, 6), (key1619, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1621, 6), (key1570, 6), (key1630, 6), (key1543, 6), (key1590, 6), (key1553, 6)]

def rawRow20031 : Integer.Sparse Key := [(key1313, 6), (key1323, 6), (key1293, 6), (key1313, 6), (key1421, 6), (key1441, 6), (key1388, 6), (key1421, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1619, 6), (key1590, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1543, 6), (key1570, 6)]

def rawRow20032 : Integer.Sparse Key := [(key1313, 6), (key1323, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1441, 6), (key1421, 6), (key1388, 6), (key1621, 6), (key1619, 6), (key1570, 6), (key1630, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1553, 6), (key1570, 6), (key1543, 6)]

def rawRow20033 : Integer.Sparse Key := [(key1323, 6), (key1293, 6), (key1313, 6), (key1313, 6), (key1441, 6), (key1388, 6), (key1421, 6), (key1421, 6), (key1590, 6), (key1630, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1621, 6), (key1543, 6), (key1543, 6), (key1570, 6), (key1570, 6), (key1619, 6), (key1619, 6)]

def rawRow20034 : Integer.Sparse Key := [(key1323, 6), (key1313, 6), (key1293, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1388, 6), (key1421, 6), (key1630, 6), (key1590, 6), (key1630, 6), (key1621, 6), (key1553, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1619, 6), (key1543, 6), (key1570, 6)]

def rawRow20035 : Integer.Sparse Key := [(key1323, 6), (key1313, 6), (key1313, 6), (key1293, 6), (key1441, 6), (key1421, 6), (key1421, 6), (key1388, 6), (key1630, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1621, 6), (key1553, 6), (key1619, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1570, 6), (key1543, 6)]

def rawRow20036 : Integer.Sparse Key := [(key1388, 6), (key1543, 6), (key1543, 6), (key1553, 6), (key1293, 6), (key1570, 6), (key1570, 6), (key1590, 6), (key1313, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1421, 6), (key1441, 6), (key1619, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1621, 6), (key1630, 6)]

def rawRow20037 : Integer.Sparse Key := [(key1388, 6), (key1543, 6), (key1553, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1590, 6), (key1570, 6), (key1313, 6), (key1323, 6), (key1313, 6), (key1421, 6), (key1441, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1619, 6), (key1630, 6), (key1621, 6)]

def rawRow20038 : Integer.Sparse Key := [(key1388, 6), (key1553, 6), (key1543, 6), (key1543, 6), (key1293, 6), (key1590, 6), (key1570, 6), (key1570, 6), (key1323, 6), (key1313, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1421, 6), (key1630, 6), (key1630, 6), (key1621, 6), (key1621, 6), (key1619, 6), (key1619, 6)]

def rawRow20039 : Integer.Sparse Key := [(key1543, 6), (key1388, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1293, 6), (key1570, 6), (key1590, 6), (key1421, 6), (key1619, 6), (key1621, 6), (key1313, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1441, 6), (key1621, 6), (key1630, 6)]

def rawRow20040 : Integer.Sparse Key := [(key1543, 6), (key1388, 6), (key1553, 6), (key1543, 6), (key1570, 6), (key1293, 6), (key1590, 6), (key1570, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1619, 6), (key1323, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1630, 6), (key1621, 6)]

def rawRow20041 : Integer.Sparse Key := [(key1543, 6), (key1543, 6), (key1388, 6), (key1553, 6), (key1570, 6), (key1570, 6), (key1293, 6), (key1590, 6), (key1619, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1421, 6), (key1621, 6), (key1313, 6), (key1630, 6), (key1323, 6), (key1441, 6)]

def rawRow20042 : Integer.Sparse Key := [(key1543, 6), (key1543, 6), (key1553, 6), (key1388, 6), (key1570, 6), (key1570, 6), (key1590, 6), (key1293, 6), (key1619, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1621, 6), (key1421, 6), (key1630, 6), (key1313, 6), (key1441, 6), (key1323, 6)]

def rawRow20043 : Integer.Sparse Key := [(key1543, 6), (key1553, 6), (key1388, 6), (key1543, 6), (key1570, 6), (key1590, 6), (key1293, 6), (key1570, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1619, 6), (key1441, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1313, 6), (key1421, 6)]

def rawRow20044 : Integer.Sparse Key := [(key1543, 6), (key1553, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1590, 6), (key1570, 6), (key1293, 6), (key1621, 6), (key1619, 6), (key1421, 6), (key1630, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1323, 6), (key1421, 6), (key1313, 6)]

def rawRow20045 : Integer.Sparse Key := [(key1553, 6), (key1388, 6), (key1543, 6), (key1543, 6), (key1590, 6), (key1293, 6), (key1570, 6), (key1570, 6), (key1441, 6), (key1630, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1621, 6), (key1313, 6), (key1313, 6), (key1421, 6), (key1421, 6), (key1619, 6), (key1619, 6)]

def rawRow20046 : Integer.Sparse Key := [(key1553, 6), (key1543, 6), (key1388, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1293, 6), (key1570, 6), (key1630, 6), (key1441, 6), (key1630, 6), (key1621, 6), (key1323, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1619, 6), (key1313, 6), (key1421, 6)]

def rawRow20047 : Integer.Sparse Key := [(key1553, 6), (key1543, 6), (key1543, 6), (key1388, 6), (key1590, 6), (key1570, 6), (key1570, 6), (key1293, 6), (key1630, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1621, 6), (key1323, 6), (key1619, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1421, 6), (key1313, 6)]

def rawRow20048 : Integer.Sparse Key := [(key1421, 6), (key1570, 6), (key1619, 6), (key1621, 6), (key1313, 6), (key1543, 6), (key1619, 6), (key1630, 6), (key1293, 6), (key1313, 6), (key1323, 6), (key1388, 6), (key1421, 6), (key1441, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1590, 6), (key1621, 6), (key1630, 6)]

def rawRow20049 : Integer.Sparse Key := [(key1421, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1619, 6), (key1293, 6), (key1323, 6), (key1313, 6), (key1388, 6), (key1441, 6), (key1421, 6), (key1553, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1630, 6), (key1621, 6)]

def rawRow20050 : Integer.Sparse Key := [(key1421, 6), (key1619, 6), (key1570, 6), (key1621, 6), (key1313, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1293, 6), (key1323, 6), (key1421, 6), (key1388, 6), (key1441, 6), (key1570, 6), (key1621, 6), (key1543, 6), (key1630, 6), (key1553, 6), (key1590, 6)]

def rawRow20051 : Integer.Sparse Key := [(key1421, 6), (key1619, 6), (key1621, 6), (key1570, 6), (key1313, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1323, 6), (key1293, 6), (key1421, 6), (key1441, 6), (key1388, 6), (key1621, 6), (key1570, 6), (key1630, 6), (key1543, 6), (key1590, 6), (key1553, 6)]

def rawRow20052 : Integer.Sparse Key := [(key1421, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1619, 6), (key1323, 6), (key1293, 6), (key1313, 6), (key1441, 6), (key1388, 6), (key1421, 6), (key1590, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1543, 6), (key1570, 6)]

def rawRow20053 : Integer.Sparse Key := [(key1421, 6), (key1621, 6), (key1619, 6), (key1570, 6), (key1313, 6), (key1630, 6), (key1619, 6), (key1543, 6), (key1323, 6), (key1313, 6), (key1293, 6), (key1441, 6), (key1421, 6), (key1388, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1553, 6), (key1570, 6), (key1543, 6)]

def rawRow20054 : Integer.Sparse Key := [(key1570, 6), (key1421, 6), (key1619, 6), (key1621, 6), (key1543, 6), (key1313, 6), (key1619, 6), (key1630, 6), (key1388, 6), (key1543, 6), (key1553, 6), (key1293, 6), (key1570, 6), (key1590, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1441, 6), (key1621, 6), (key1630, 6)]

def rawRow20055 : Integer.Sparse Key := [(key1570, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1619, 6), (key1388, 6), (key1553, 6), (key1543, 6), (key1293, 6), (key1590, 6), (key1570, 6), (key1323, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1630, 6), (key1621, 6)]

def rawRow20056 : Integer.Sparse Key := [(key1570, 6), (key1619, 6), (key1421, 6), (key1621, 6), (key1543, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1388, 6), (key1553, 6), (key1570, 6), (key1293, 6), (key1590, 6), (key1421, 6), (key1621, 6), (key1313, 6), (key1630, 6), (key1323, 6), (key1441, 6)]

def rawRow20057 : Integer.Sparse Key := [(key1570, 6), (key1619, 6), (key1621, 6), (key1421, 6), (key1543, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1553, 6), (key1388, 6), (key1570, 6), (key1590, 6), (key1293, 6), (key1621, 6), (key1421, 6), (key1630, 6), (key1313, 6), (key1441, 6), (key1323, 6)]

def rawRow20058 : Integer.Sparse Key := [(key1570, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1619, 6), (key1553, 6), (key1388, 6), (key1543, 6), (key1590, 6), (key1293, 6), (key1570, 6), (key1441, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1313, 6), (key1421, 6)]

def rawRow20059 : Integer.Sparse Key := [(key1570, 6), (key1621, 6), (key1619, 6), (key1421, 6), (key1543, 6), (key1630, 6), (key1619, 6), (key1313, 6), (key1553, 6), (key1543, 6), (key1388, 6), (key1590, 6), (key1570, 6), (key1293, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1323, 6), (key1421, 6), (key1313, 6)]

def rawRow20060 : Integer.Sparse Key := [(key1619, 6), (key1421, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1421, 6), (key1570, 6), (key1621, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1293, 6), (key1323, 6), (key1388, 6), (key1441, 6), (key1553, 6), (key1590, 6)]

def rawRow20061 : Integer.Sparse Key := [(key1619, 6), (key1421, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1421, 6), (key1621, 6), (key1570, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1323, 6), (key1293, 6), (key1441, 6), (key1388, 6), (key1590, 6), (key1553, 6)]

def rawRow20062 : Integer.Sparse Key := [(key1619, 6), (key1570, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1570, 6), (key1421, 6), (key1621, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1388, 6), (key1553, 6), (key1293, 6), (key1590, 6), (key1323, 6), (key1441, 6)]

def rawRow20063 : Integer.Sparse Key := [(key1619, 6), (key1570, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1570, 6), (key1621, 6), (key1421, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1553, 6), (key1388, 6), (key1590, 6), (key1293, 6), (key1441, 6), (key1323, 6)]

def rawRow20064 : Integer.Sparse Key := [(key1619, 6), (key1621, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1621, 6), (key1421, 6), (key1570, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1441, 6), (key1590, 6), (key1323, 6), (key1553, 6), (key1293, 6), (key1388, 6)]

def rawRow20065 : Integer.Sparse Key := [(key1619, 6), (key1621, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1621, 6), (key1570, 6), (key1421, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1590, 6), (key1441, 6), (key1553, 6), (key1323, 6), (key1388, 6), (key1293, 6)]

def rawRow20066 : Integer.Sparse Key := [(key1621, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1619, 6), (key1441, 6), (key1590, 6), (key1630, 6), (key1323, 6), (key1553, 6), (key1621, 6), (key1293, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1543, 6), (key1570, 6)]

def rawRow20067 : Integer.Sparse Key := [(key1621, 6), (key1421, 6), (key1619, 6), (key1570, 6), (key1630, 6), (key1313, 6), (key1619, 6), (key1543, 6), (key1441, 6), (key1630, 6), (key1590, 6), (key1323, 6), (key1621, 6), (key1553, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1388, 6), (key1570, 6), (key1543, 6)]

def rawRow20068 : Integer.Sparse Key := [(key1621, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1619, 6), (key1590, 6), (key1441, 6), (key1630, 6), (key1553, 6), (key1323, 6), (key1621, 6), (key1388, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1313, 6), (key1421, 6)]

def rawRow20069 : Integer.Sparse Key := [(key1621, 6), (key1570, 6), (key1619, 6), (key1421, 6), (key1630, 6), (key1543, 6), (key1619, 6), (key1313, 6), (key1590, 6), (key1630, 6), (key1441, 6), (key1553, 6), (key1621, 6), (key1323, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1293, 6), (key1421, 6), (key1313, 6)]

def rawRow20070 : Integer.Sparse Key := [(key1621, 6), (key1619, 6), (key1421, 6), (key1570, 6), (key1630, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1441, 6), (key1590, 6), (key1621, 6), (key1323, 6), (key1553, 6), (key1421, 6), (key1570, 6), (key1313, 6), (key1543, 6), (key1293, 6), (key1388, 6)]

def rawRow20071 : Integer.Sparse Key := [(key1621, 6), (key1619, 6), (key1570, 6), (key1421, 6), (key1630, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1590, 6), (key1441, 6), (key1621, 6), (key1553, 6), (key1323, 6), (key1570, 6), (key1421, 6), (key1543, 6), (key1313, 6), (key1388, 6), (key1293, 6)]

def rawRow20072 : Integer.Sparse Key := [(key1441, 6), (key1590, 6), (key1630, 6), (key1630, 6), (key1323, 6), (key1553, 6), (key1621, 6), (key1621, 6), (key1293, 6), (key1313, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1421, 6), (key1543, 6), (key1543, 6), (key1570, 6), (key1570, 6), (key1619, 6), (key1619, 6)]

def rawRow20073 : Integer.Sparse Key := [(key1441, 6), (key1630, 6), (key1590, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1553, 6), (key1621, 6), (key1313, 6), (key1293, 6), (key1313, 6), (key1421, 6), (key1388, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1619, 6), (key1543, 6), (key1570, 6)]

def rawRow20074 : Integer.Sparse Key := [(key1441, 6), (key1630, 6), (key1630, 6), (key1590, 6), (key1323, 6), (key1621, 6), (key1621, 6), (key1553, 6), (key1313, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1421, 6), (key1388, 6), (key1619, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1570, 6), (key1543, 6)]

def rawRow20075 : Integer.Sparse Key := [(key1590, 6), (key1441, 6), (key1630, 6), (key1630, 6), (key1553, 6), (key1323, 6), (key1621, 6), (key1621, 6), (key1388, 6), (key1543, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1570, 6), (key1313, 6), (key1313, 6), (key1421, 6), (key1421, 6), (key1619, 6), (key1619, 6)]

def rawRow20076 : Integer.Sparse Key := [(key1590, 6), (key1630, 6), (key1441, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1323, 6), (key1621, 6), (key1543, 6), (key1388, 6), (key1543, 6), (key1570, 6), (key1293, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1619, 6), (key1313, 6), (key1421, 6)]

def rawRow20077 : Integer.Sparse Key := [(key1590, 6), (key1630, 6), (key1630, 6), (key1441, 6), (key1553, 6), (key1621, 6), (key1621, 6), (key1323, 6), (key1543, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1570, 6), (key1293, 6), (key1619, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1421, 6), (key1313, 6)]

def rawRow20078 : Integer.Sparse Key := [(key1630, 6), (key1441, 6), (key1590, 6), (key1630, 6), (key1621, 6), (key1323, 6), (key1553, 6), (key1621, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1619, 6), (key1293, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1543, 6), (key1570, 6)]

def rawRow20079 : Integer.Sparse Key := [(key1630, 6), (key1441, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1323, 6), (key1621, 6), (key1553, 6), (key1421, 6), (key1619, 6), (key1570, 6), (key1313, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1388, 6), (key1570, 6), (key1543, 6)]

def rawRow20080 : Integer.Sparse Key := [(key1630, 6), (key1590, 6), (key1441, 6), (key1630, 6), (key1621, 6), (key1553, 6), (key1323, 6), (key1621, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1619, 6), (key1388, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1313, 6), (key1421, 6)]

def rawRow20081 : Integer.Sparse Key := [(key1630, 6), (key1590, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1553, 6), (key1621, 6), (key1323, 6), (key1570, 6), (key1619, 6), (key1421, 6), (key1543, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1293, 6), (key1421, 6), (key1313, 6)]

def rawRow20082 : Integer.Sparse Key := [(key1630, 6), (key1630, 6), (key1441, 6), (key1590, 6), (key1621, 6), (key1621, 6), (key1323, 6), (key1553, 6), (key1619, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1421, 6), (key1570, 6), (key1313, 6), (key1543, 6), (key1293, 6), (key1388, 6)]

def rawRow20083 : Integer.Sparse Key := [(key1630, 6), (key1630, 6), (key1590, 6), (key1441, 6), (key1621, 6), (key1621, 6), (key1553, 6), (key1323, 6), (key1619, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1570, 6), (key1421, 6), (key1543, 6), (key1313, 6), (key1388, 6), (key1293, 6)]

def rawRow20084 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key627, 24), (key629, 24), (key640, 24)]

def rawRow20085 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key627, 24), (key629, 24), (key640, 24)]

def rawRow20086 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key626, 24), (key629, 24), (key640, 24)]

def rawRow20087 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key629, 24), (key627, 24), (key640, 24)]

def rawRow20088 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key629, 24), (key627, 24), (key640, 24)]

def rawRow20089 : Integer.Sparse Key := [(key626, 24), (key629, 24), (key627, 24), (key627, 24), (key640, 24)]

def rawRow20090 : Integer.Sparse Key := [(key629, 24), (key626, 24), (key627, 24), (key627, 24), (key640, 24)]

def rawRow20091 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key626, 24), (key627, 24), (key640, 24)]

def rawRow20092 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key626, 24), (key627, 24), (key640, 24)]

def rawRow20093 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key629, 24), (key626, 24), (key640, 24)]

def rawRow20094 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key627, 24), (key626, 24), (key640, 24)]

def rawRow20095 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key627, 24), (key626, 24), (key640, 24)]

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

def rawRow20096 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key627, 24), (key640, 24), (key629, 24)]

def rawRow20097 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key627, 24), (key640, 24), (key629, 24)]

def rawRow20098 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key626, 24), (key640, 24), (key629, 24)]

def rawRow20099 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key640, 24), (key627, 24), (key629, 24)]

def rawRow20100 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key640, 24), (key627, 24), (key629, 24)]

def rawRow20101 : Integer.Sparse Key := [(key626, 24), (key640, 24), (key627, 24), (key627, 24), (key629, 24)]

def rawRow20102 : Integer.Sparse Key := [(key640, 24), (key626, 24), (key627, 24), (key627, 24), (key629, 24)]

def rawRow20103 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key626, 24), (key627, 24), (key629, 24)]

def rawRow20104 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key626, 24), (key627, 24), (key629, 24)]

def rawRow20105 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key640, 24), (key626, 24), (key629, 24)]

def rawRow20106 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key627, 24), (key626, 24), (key629, 24)]

def rawRow20107 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key627, 24), (key626, 24), (key629, 24)]

def rawRow20108 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key629, 24), (key640, 24), (key627, 24)]

def rawRow20109 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key629, 24), (key640, 24), (key627, 24)]

def rawRow20110 : Integer.Sparse Key := [(key626, 24), (key629, 24), (key627, 24), (key640, 24), (key627, 24)]

def rawRow20111 : Integer.Sparse Key := [(key629, 24), (key626, 24), (key627, 24), (key640, 24), (key627, 24)]

def rawRow20112 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key626, 24), (key640, 24), (key627, 24)]

def rawRow20113 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key626, 24), (key640, 24), (key627, 24)]

def rawRow20114 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key640, 24), (key629, 24), (key627, 24)]

def rawRow20115 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key640, 24), (key629, 24), (key627, 24)]

def rawRow20116 : Integer.Sparse Key := [(key626, 24), (key640, 24), (key627, 24), (key629, 24), (key627, 24)]

def rawRow20117 : Integer.Sparse Key := [(key640, 24), (key626, 24), (key627, 24), (key629, 24), (key627, 24)]

def rawRow20118 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key626, 24), (key629, 24), (key627, 24)]

def rawRow20119 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key626, 24), (key629, 24), (key627, 24)]

def rawRow20120 : Integer.Sparse Key := [(key626, 24), (key629, 24), (key640, 24), (key627, 24), (key627, 24)]

def rawRow20121 : Integer.Sparse Key := [(key629, 24), (key626, 24), (key640, 24), (key627, 24), (key627, 24)]

def rawRow20122 : Integer.Sparse Key := [(key626, 24), (key640, 24), (key629, 24), (key627, 24), (key627, 24)]

def rawRow20123 : Integer.Sparse Key := [(key640, 24), (key626, 24), (key629, 24), (key627, 24), (key627, 24)]

def rawRow20124 : Integer.Sparse Key := [(key629, 24), (key640, 24), (key626, 24), (key627, 24), (key627, 24)]

def rawRow20125 : Integer.Sparse Key := [(key640, 24), (key629, 24), (key626, 24), (key627, 24), (key627, 24)]

def rawRow20126 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key640, 24), (key626, 24), (key627, 24)]

def rawRow20127 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key640, 24), (key626, 24), (key627, 24)]

def rawRow20128 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key629, 24), (key626, 24), (key627, 24)]

def rawRow20129 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key629, 24), (key626, 24), (key627, 24)]

def rawRow20130 : Integer.Sparse Key := [(key629, 24), (key640, 24), (key627, 24), (key626, 24), (key627, 24)]

def rawRow20131 : Integer.Sparse Key := [(key640, 24), (key629, 24), (key627, 24), (key626, 24), (key627, 24)]

def rawRow20132 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key629, 24), (key640, 24), (key626, 24)]

def rawRow20133 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key627, 24), (key640, 24), (key626, 24)]

def rawRow20134 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key627, 24), (key640, 24), (key626, 24)]

def rawRow20135 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key640, 24), (key629, 24), (key626, 24)]

def rawRow20136 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key627, 24), (key629, 24), (key626, 24)]

def rawRow20137 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key627, 24), (key629, 24), (key626, 24)]

def rawRow20138 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key640, 24), (key627, 24), (key626, 24)]

def rawRow20139 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key640, 24), (key627, 24), (key626, 24)]

def rawRow20140 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key629, 24), (key627, 24), (key626, 24)]

def rawRow20141 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key629, 24), (key627, 24), (key626, 24)]

def rawRow20142 : Integer.Sparse Key := [(key629, 24), (key640, 24), (key627, 24), (key627, 24), (key626, 24)]

def rawRow20143 : Integer.Sparse Key := [(key640, 24), (key629, 24), (key627, 24), (key627, 24), (key626, 24)]

def rawRow20144 : Integer.Sparse Key := [(key1407, 12), (key1407, 12), (key1411, 12), (key1435, 12), (key1436, 12), (key1436, 12), (key1584, 12), (key1585, 12), (key1585, 12), (key1628, 12)]

def rawRow20145 : Integer.Sparse Key := [(key1407, 12), (key1411, 12), (key1407, 12), (key1436, 12), (key1435, 12), (key1436, 12), (key1585, 12), (key1584, 12), (key1585, 12), (key1628, 12)]

def rawRow20146 : Integer.Sparse Key := [(key1411, 12), (key1407, 12), (key1407, 12), (key1436, 12), (key1436, 12), (key1435, 12), (key1585, 12), (key1585, 12), (key1584, 12), (key1628, 12)]

def rawRow20147 : Integer.Sparse Key := [(key1407, 12), (key1435, 12), (key1436, 12), (key1407, 12), (key1411, 12), (key1436, 12), (key1584, 12), (key1585, 12), (key1628, 12), (key1585, 12)]

def rawRow20148 : Integer.Sparse Key := [(key1407, 12), (key1436, 12), (key1435, 12), (key1411, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1584, 12), (key1628, 12), (key1585, 12)]

def rawRow20149 : Integer.Sparse Key := [(key1435, 12), (key1407, 12), (key1436, 12), (key1407, 12), (key1436, 12), (key1411, 12), (key1584, 12), (key1628, 12), (key1585, 12), (key1585, 12)]

def rawRow20150 : Integer.Sparse Key := [(key1435, 12), (key1436, 12), (key1407, 12), (key1436, 12), (key1407, 12), (key1411, 12), (key1628, 12), (key1584, 12), (key1585, 12), (key1585, 12)]

def rawRow20151 : Integer.Sparse Key := [(key1436, 12), (key1407, 12), (key1435, 12), (key1411, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1628, 12), (key1584, 12), (key1585, 12)]

def rawRow20152 : Integer.Sparse Key := [(key1436, 12), (key1435, 12), (key1407, 12), (key1436, 12), (key1411, 12), (key1407, 12), (key1628, 12), (key1585, 12), (key1584, 12), (key1585, 12)]

def rawRow20153 : Integer.Sparse Key := [(key1411, 12), (key1436, 12), (key1436, 12), (key1407, 12), (key1407, 12), (key1435, 12), (key1585, 12), (key1585, 12), (key1628, 12), (key1584, 12)]

def rawRow20154 : Integer.Sparse Key := [(key1436, 12), (key1411, 12), (key1436, 12), (key1407, 12), (key1435, 12), (key1407, 12), (key1585, 12), (key1628, 12), (key1585, 12), (key1584, 12)]

def rawRow20155 : Integer.Sparse Key := [(key1436, 12), (key1436, 12), (key1411, 12), (key1435, 12), (key1407, 12), (key1407, 12), (key1628, 12), (key1585, 12), (key1585, 12), (key1584, 12)]

def rawRow20156 : Integer.Sparse Key := [(key1407, 12), (key1407, 12), (key1411, 12), (key1584, 12), (key1585, 12), (key1585, 12), (key1435, 12), (key1436, 12), (key1436, 12), (key1628, 12)]

def rawRow20157 : Integer.Sparse Key := [(key1407, 12), (key1411, 12), (key1407, 12), (key1585, 12), (key1584, 12), (key1585, 12), (key1436, 12), (key1435, 12), (key1436, 12), (key1628, 12)]

def rawRow20158 : Integer.Sparse Key := [(key1411, 12), (key1407, 12), (key1407, 12), (key1585, 12), (key1585, 12), (key1584, 12), (key1436, 12), (key1436, 12), (key1435, 12), (key1628, 12)]

def rawRow20159 : Integer.Sparse Key := [(key1407, 12), (key1584, 12), (key1585, 12), (key1407, 12), (key1411, 12), (key1585, 12), (key1435, 12), (key1436, 12), (key1628, 12), (key1436, 12)]

def rawRow20160 : Integer.Sparse Key := [(key1407, 12), (key1585, 12), (key1584, 12), (key1411, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1435, 12), (key1628, 12), (key1436, 12)]

def rawRow20161 : Integer.Sparse Key := [(key1584, 12), (key1407, 12), (key1585, 12), (key1407, 12), (key1585, 12), (key1411, 12), (key1435, 12), (key1628, 12), (key1436, 12), (key1436, 12)]

def rawRow20162 : Integer.Sparse Key := [(key1584, 12), (key1585, 12), (key1407, 12), (key1585, 12), (key1407, 12), (key1411, 12), (key1628, 12), (key1435, 12), (key1436, 12), (key1436, 12)]

def rawRow20163 : Integer.Sparse Key := [(key1585, 12), (key1407, 12), (key1584, 12), (key1411, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1628, 12), (key1435, 12), (key1436, 12)]

def rawRow20164 : Integer.Sparse Key := [(key1585, 12), (key1584, 12), (key1407, 12), (key1585, 12), (key1411, 12), (key1407, 12), (key1628, 12), (key1436, 12), (key1435, 12), (key1436, 12)]

def rawRow20165 : Integer.Sparse Key := [(key1411, 12), (key1585, 12), (key1585, 12), (key1407, 12), (key1407, 12), (key1584, 12), (key1436, 12), (key1436, 12), (key1628, 12), (key1435, 12)]

def rawRow20166 : Integer.Sparse Key := [(key1585, 12), (key1411, 12), (key1585, 12), (key1407, 12), (key1584, 12), (key1407, 12), (key1436, 12), (key1628, 12), (key1436, 12), (key1435, 12)]

def rawRow20167 : Integer.Sparse Key := [(key1585, 12), (key1585, 12), (key1411, 12), (key1584, 12), (key1407, 12), (key1407, 12), (key1628, 12), (key1436, 12), (key1436, 12), (key1435, 12)]

def rawRow20168 : Integer.Sparse Key := [(key1407, 12), (key1435, 12), (key1436, 12), (key1584, 12), (key1585, 12), (key1628, 12), (key1407, 12), (key1411, 12), (key1436, 12), (key1585, 12)]

def rawRow20169 : Integer.Sparse Key := [(key1407, 12), (key1436, 12), (key1435, 12), (key1585, 12), (key1584, 12), (key1628, 12), (key1411, 12), (key1407, 12), (key1436, 12), (key1585, 12)]

def rawRow20170 : Integer.Sparse Key := [(key1435, 12), (key1407, 12), (key1436, 12), (key1584, 12), (key1628, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1411, 12), (key1585, 12)]

def rawRow20171 : Integer.Sparse Key := [(key1435, 12), (key1436, 12), (key1407, 12), (key1628, 12), (key1584, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1411, 12), (key1585, 12)]

def rawRow20172 : Integer.Sparse Key := [(key1436, 12), (key1407, 12), (key1435, 12), (key1585, 12), (key1628, 12), (key1584, 12), (key1411, 12), (key1436, 12), (key1407, 12), (key1585, 12)]

def rawRow20173 : Integer.Sparse Key := [(key1436, 12), (key1435, 12), (key1407, 12), (key1628, 12), (key1585, 12), (key1584, 12), (key1436, 12), (key1411, 12), (key1407, 12), (key1585, 12)]

def rawRow20174 : Integer.Sparse Key := [(key1407, 12), (key1584, 12), (key1585, 12), (key1435, 12), (key1436, 12), (key1628, 12), (key1407, 12), (key1411, 12), (key1585, 12), (key1436, 12)]

def rawRow20175 : Integer.Sparse Key := [(key1407, 12), (key1585, 12), (key1584, 12), (key1436, 12), (key1435, 12), (key1628, 12), (key1411, 12), (key1407, 12), (key1585, 12), (key1436, 12)]

def rawRow20176 : Integer.Sparse Key := [(key1584, 12), (key1407, 12), (key1585, 12), (key1435, 12), (key1628, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1411, 12), (key1436, 12)]

def rawRow20177 : Integer.Sparse Key := [(key1584, 12), (key1585, 12), (key1407, 12), (key1628, 12), (key1435, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1411, 12), (key1436, 12)]

def rawRow20178 : Integer.Sparse Key := [(key1585, 12), (key1407, 12), (key1584, 12), (key1436, 12), (key1628, 12), (key1435, 12), (key1411, 12), (key1585, 12), (key1407, 12), (key1436, 12)]

def rawRow20179 : Integer.Sparse Key := [(key1585, 12), (key1584, 12), (key1407, 12), (key1628, 12), (key1436, 12), (key1435, 12), (key1585, 12), (key1411, 12), (key1407, 12), (key1436, 12)]

def rawRow20180 : Integer.Sparse Key := [(key1435, 12), (key1584, 12), (key1628, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1411, 12)]

def rawRow20181 : Integer.Sparse Key := [(key1435, 12), (key1628, 12), (key1584, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1411, 12)]

def rawRow20182 : Integer.Sparse Key := [(key1584, 12), (key1435, 12), (key1628, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1411, 12)]

def rawRow20183 : Integer.Sparse Key := [(key1584, 12), (key1628, 12), (key1435, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1411, 12)]

def rawRow20184 : Integer.Sparse Key := [(key1628, 12), (key1435, 12), (key1584, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1411, 12)]

def rawRow20185 : Integer.Sparse Key := [(key1628, 12), (key1584, 12), (key1435, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1411, 12)]

def rawRow20186 : Integer.Sparse Key := [(key1436, 12), (key1585, 12), (key1628, 12), (key1407, 12), (key1435, 12), (key1584, 12), (key1411, 12), (key1436, 12), (key1585, 12), (key1407, 12)]

def rawRow20187 : Integer.Sparse Key := [(key1436, 12), (key1628, 12), (key1585, 12), (key1435, 12), (key1407, 12), (key1584, 12), (key1436, 12), (key1411, 12), (key1585, 12), (key1407, 12)]

def rawRow20188 : Integer.Sparse Key := [(key1585, 12), (key1436, 12), (key1628, 12), (key1407, 12), (key1584, 12), (key1435, 12), (key1411, 12), (key1585, 12), (key1436, 12), (key1407, 12)]

def rawRow20189 : Integer.Sparse Key := [(key1585, 12), (key1628, 12), (key1436, 12), (key1584, 12), (key1407, 12), (key1435, 12), (key1585, 12), (key1411, 12), (key1436, 12), (key1407, 12)]

def rawRow20190 : Integer.Sparse Key := [(key1628, 12), (key1436, 12), (key1585, 12), (key1435, 12), (key1584, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1411, 12), (key1407, 12)]

def rawRow20191 : Integer.Sparse Key := [(key1628, 12), (key1585, 12), (key1436, 12), (key1584, 12), (key1435, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1411, 12), (key1407, 12)]

def rawRow20192 : Integer.Sparse Key := [(key1411, 12), (key1436, 12), (key1436, 12), (key1585, 12), (key1585, 12), (key1628, 12), (key1407, 12), (key1407, 12), (key1435, 12), (key1584, 12)]

def rawRow20193 : Integer.Sparse Key := [(key1436, 12), (key1411, 12), (key1436, 12), (key1585, 12), (key1628, 12), (key1585, 12), (key1407, 12), (key1435, 12), (key1407, 12), (key1584, 12)]

def rawRow20194 : Integer.Sparse Key := [(key1436, 12), (key1436, 12), (key1411, 12), (key1628, 12), (key1585, 12), (key1585, 12), (key1435, 12), (key1407, 12), (key1407, 12), (key1584, 12)]

def rawRow20195 : Integer.Sparse Key := [(key1411, 12), (key1585, 12), (key1585, 12), (key1436, 12), (key1436, 12), (key1628, 12), (key1407, 12), (key1407, 12), (key1584, 12), (key1435, 12)]

def rawRow20196 : Integer.Sparse Key := [(key1585, 12), (key1411, 12), (key1585, 12), (key1436, 12), (key1628, 12), (key1436, 12), (key1407, 12), (key1584, 12), (key1407, 12), (key1435, 12)]

def rawRow20197 : Integer.Sparse Key := [(key1585, 12), (key1585, 12), (key1411, 12), (key1628, 12), (key1436, 12), (key1436, 12), (key1584, 12), (key1407, 12), (key1407, 12), (key1435, 12)]

def rawRow20198 : Integer.Sparse Key := [(key1436, 12), (key1585, 12), (key1628, 12), (key1411, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1435, 12), (key1584, 12), (key1407, 12)]

def rawRow20199 : Integer.Sparse Key := [(key1436, 12), (key1628, 12), (key1585, 12), (key1436, 12), (key1411, 12), (key1585, 12), (key1435, 12), (key1407, 12), (key1584, 12), (key1407, 12)]

def rawRow20200 : Integer.Sparse Key := [(key1585, 12), (key1436, 12), (key1628, 12), (key1411, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1584, 12), (key1435, 12), (key1407, 12)]

def rawRow20201 : Integer.Sparse Key := [(key1585, 12), (key1628, 12), (key1436, 12), (key1585, 12), (key1411, 12), (key1436, 12), (key1584, 12), (key1407, 12), (key1435, 12), (key1407, 12)]

def rawRow20202 : Integer.Sparse Key := [(key1628, 12), (key1436, 12), (key1585, 12), (key1436, 12), (key1585, 12), (key1411, 12), (key1435, 12), (key1584, 12), (key1407, 12), (key1407, 12)]

def rawRow20203 : Integer.Sparse Key := [(key1628, 12), (key1585, 12), (key1436, 12), (key1585, 12), (key1436, 12), (key1411, 12), (key1584, 12), (key1435, 12), (key1407, 12), (key1407, 12)]

def rawRow20204 : Integer.Sparse Key := [(key280, 6), (key283, 6), (key283, 6), (key292, 6), (key349, 6), (key352, 6), (key352, 6), (key506, 6), (key509, 6), (key506, 6), (key667, 6), (key509, 6), (key667, 6), (key520, 6), (key520, 6), (key671, 6), (key369, 6), (key541, 6), (key541, 6), (key677, 6)]

def rawRow20205 : Integer.Sparse Key := [(key283, 6), (key280, 6), (key283, 6), (key292, 6), (key352, 6), (key349, 6), (key352, 6), (key509, 6), (key506, 6), (key667, 6), (key506, 6), (key667, 6), (key509, 6), (key520, 6), (key671, 6), (key520, 6), (key369, 6), (key541, 6), (key677, 6), (key541, 6)]

def rawRow20206 : Integer.Sparse Key := [(key283, 6), (key283, 6), (key280, 6), (key292, 6), (key352, 6), (key352, 6), (key349, 6), (key667, 6), (key667, 6), (key509, 6), (key509, 6), (key506, 6), (key506, 6), (key671, 6), (key520, 6), (key520, 6), (key369, 6), (key677, 6), (key541, 6), (key541, 6)]

def rawRow20207 : Integer.Sparse Key := [(key280, 6), (key283, 6), (key292, 6), (key283, 6), (key506, 6), (key509, 6), (key520, 6), (key349, 6), (key352, 6), (key506, 6), (key667, 6), (key520, 6), (key671, 6), (key352, 6), (key509, 6), (key667, 6), (key541, 6), (key369, 6), (key541, 6), (key677, 6)]

def rawRow20208 : Integer.Sparse Key := [(key283, 6), (key280, 6), (key292, 6), (key283, 6), (key509, 6), (key506, 6), (key520, 6), (key352, 6), (key349, 6), (key667, 6), (key506, 6), (key671, 6), (key520, 6), (key352, 6), (key667, 6), (key509, 6), (key541, 6), (key369, 6), (key677, 6), (key541, 6)]

def rawRow20209 : Integer.Sparse Key := [(key280, 6), (key292, 6), (key283, 6), (key283, 6), (key506, 6), (key520, 6), (key509, 6), (key506, 6), (key520, 6), (key349, 6), (key671, 6), (key352, 6), (key667, 6), (key509, 6), (key352, 6), (key667, 6), (key541, 6), (key541, 6), (key369, 6), (key677, 6)]

def rawRow20210 : Integer.Sparse Key := [(key292, 6), (key280, 6), (key283, 6), (key283, 6), (key520, 6), (key506, 6), (key509, 6), (key520, 6), (key506, 6), (key671, 6), (key349, 6), (key667, 6), (key352, 6), (key509, 6), (key667, 6), (key352, 6), (key541, 6), (key541, 6), (key677, 6), (key369, 6)]

def rawRow20211 : Integer.Sparse Key := [(key283, 6), (key292, 6), (key280, 6), (key283, 6), (key509, 6), (key520, 6), (key506, 6), (key667, 6), (key671, 6), (key352, 6), (key520, 6), (key349, 6), (key506, 6), (key667, 6), (key352, 6), (key509, 6), (key541, 6), (key677, 6), (key369, 6), (key541, 6)]

def rawRow20212 : Integer.Sparse Key := [(key292, 6), (key283, 6), (key280, 6), (key283, 6), (key520, 6), (key509, 6), (key506, 6), (key671, 6), (key667, 6), (key520, 6), (key352, 6), (key506, 6), (key349, 6), (key667, 6), (key509, 6), (key352, 6), (key541, 6), (key677, 6), (key541, 6), (key369, 6)]

def rawRow20213 : Integer.Sparse Key := [(key283, 6), (key283, 6), (key292, 6), (key280, 6), (key667, 6), (key667, 6), (key671, 6), (key352, 6), (key352, 6), (key509, 6), (key509, 6), (key520, 6), (key520, 6), (key349, 6), (key506, 6), (key506, 6), (key677, 6), (key369, 6), (key541, 6), (key541, 6)]

def rawRow20214 : Integer.Sparse Key := [(key283, 6), (key292, 6), (key283, 6), (key280, 6), (key667, 6), (key671, 6), (key667, 6), (key509, 6), (key520, 6), (key352, 6), (key520, 6), (key352, 6), (key509, 6), (key506, 6), (key349, 6), (key506, 6), (key677, 6), (key541, 6), (key369, 6), (key541, 6)]

def rawRow20215 : Integer.Sparse Key := [(key292, 6), (key283, 6), (key283, 6), (key280, 6), (key671, 6), (key667, 6), (key667, 6), (key520, 6), (key509, 6), (key520, 6), (key352, 6), (key509, 6), (key352, 6), (key506, 6), (key506, 6), (key349, 6), (key677, 6), (key541, 6), (key541, 6), (key369, 6)]

def rawRow20216 : Integer.Sparse Key := [(key349, 6), (key352, 6), (key352, 6), (key369, 6), (key280, 6), (key283, 6), (key283, 6), (key506, 6), (key509, 6), (key506, 6), (key667, 6), (key509, 6), (key667, 6), (key541, 6), (key541, 6), (key677, 6), (key292, 6), (key520, 6), (key520, 6), (key671, 6)]

def rawRow20217 : Integer.Sparse Key := [(key352, 6), (key349, 6), (key352, 6), (key369, 6), (key283, 6), (key280, 6), (key283, 6), (key509, 6), (key506, 6), (key667, 6), (key506, 6), (key667, 6), (key509, 6), (key541, 6), (key677, 6), (key541, 6), (key292, 6), (key520, 6), (key671, 6), (key520, 6)]

def rawRow20218 : Integer.Sparse Key := [(key352, 6), (key352, 6), (key349, 6), (key369, 6), (key283, 6), (key283, 6), (key280, 6), (key667, 6), (key667, 6), (key509, 6), (key509, 6), (key506, 6), (key506, 6), (key677, 6), (key541, 6), (key541, 6), (key292, 6), (key671, 6), (key520, 6), (key520, 6)]

def rawRow20219 : Integer.Sparse Key := [(key349, 6), (key352, 6), (key369, 6), (key352, 6), (key506, 6), (key509, 6), (key541, 6), (key280, 6), (key283, 6), (key506, 6), (key667, 6), (key541, 6), (key677, 6), (key283, 6), (key509, 6), (key667, 6), (key520, 6), (key292, 6), (key520, 6), (key671, 6)]

def rawRow20220 : Integer.Sparse Key := [(key352, 6), (key349, 6), (key369, 6), (key352, 6), (key509, 6), (key506, 6), (key541, 6), (key283, 6), (key280, 6), (key667, 6), (key506, 6), (key677, 6), (key541, 6), (key283, 6), (key667, 6), (key509, 6), (key520, 6), (key292, 6), (key671, 6), (key520, 6)]

def rawRow20221 : Integer.Sparse Key := [(key349, 6), (key369, 6), (key352, 6), (key352, 6), (key506, 6), (key541, 6), (key509, 6), (key506, 6), (key541, 6), (key280, 6), (key677, 6), (key283, 6), (key667, 6), (key509, 6), (key283, 6), (key667, 6), (key520, 6), (key520, 6), (key292, 6), (key671, 6)]

def rawRow20222 : Integer.Sparse Key := [(key369, 6), (key349, 6), (key352, 6), (key352, 6), (key541, 6), (key506, 6), (key509, 6), (key541, 6), (key506, 6), (key677, 6), (key280, 6), (key667, 6), (key283, 6), (key509, 6), (key667, 6), (key283, 6), (key520, 6), (key520, 6), (key671, 6), (key292, 6)]

def rawRow20223 : Integer.Sparse Key := [(key352, 6), (key369, 6), (key349, 6), (key352, 6), (key509, 6), (key541, 6), (key506, 6), (key667, 6), (key677, 6), (key283, 6), (key541, 6), (key280, 6), (key506, 6), (key667, 6), (key283, 6), (key509, 6), (key520, 6), (key671, 6), (key292, 6), (key520, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow20224 : Integer.Sparse Key := [(key369, 6), (key352, 6), (key349, 6), (key352, 6), (key541, 6), (key509, 6), (key506, 6), (key677, 6), (key667, 6), (key541, 6), (key283, 6), (key506, 6), (key280, 6), (key667, 6), (key509, 6), (key283, 6), (key520, 6), (key671, 6), (key520, 6), (key292, 6)]

def rawRow20225 : Integer.Sparse Key := [(key352, 6), (key352, 6), (key369, 6), (key349, 6), (key667, 6), (key667, 6), (key677, 6), (key283, 6), (key283, 6), (key509, 6), (key509, 6), (key541, 6), (key541, 6), (key280, 6), (key506, 6), (key506, 6), (key671, 6), (key292, 6), (key520, 6), (key520, 6)]

def rawRow20226 : Integer.Sparse Key := [(key352, 6), (key369, 6), (key352, 6), (key349, 6), (key667, 6), (key677, 6), (key667, 6), (key509, 6), (key541, 6), (key283, 6), (key541, 6), (key283, 6), (key509, 6), (key506, 6), (key280, 6), (key506, 6), (key671, 6), (key520, 6), (key292, 6), (key520, 6)]

def rawRow20227 : Integer.Sparse Key := [(key369, 6), (key352, 6), (key352, 6), (key349, 6), (key677, 6), (key667, 6), (key667, 6), (key541, 6), (key509, 6), (key541, 6), (key283, 6), (key509, 6), (key283, 6), (key506, 6), (key506, 6), (key280, 6), (key671, 6), (key520, 6), (key520, 6), (key292, 6)]

def rawRow20228 : Integer.Sparse Key := [(key506, 6), (key509, 6), (key520, 6), (key541, 6), (key280, 6), (key283, 6), (key292, 6), (key349, 6), (key352, 6), (key506, 6), (key667, 6), (key520, 6), (key671, 6), (key369, 6), (key541, 6), (key677, 6), (key283, 6), (key352, 6), (key509, 6), (key667, 6)]

def rawRow20229 : Integer.Sparse Key := [(key509, 6), (key506, 6), (key520, 6), (key541, 6), (key283, 6), (key280, 6), (key292, 6), (key352, 6), (key349, 6), (key667, 6), (key506, 6), (key671, 6), (key520, 6), (key369, 6), (key677, 6), (key541, 6), (key283, 6), (key352, 6), (key667, 6), (key509, 6)]

def rawRow20230 : Integer.Sparse Key := [(key506, 6), (key520, 6), (key509, 6), (key541, 6), (key280, 6), (key292, 6), (key283, 6), (key506, 6), (key520, 6), (key349, 6), (key671, 6), (key352, 6), (key667, 6), (key541, 6), (key369, 6), (key677, 6), (key283, 6), (key509, 6), (key352, 6), (key667, 6)]

def rawRow20231 : Integer.Sparse Key := [(key520, 6), (key506, 6), (key509, 6), (key541, 6), (key292, 6), (key280, 6), (key283, 6), (key520, 6), (key506, 6), (key671, 6), (key349, 6), (key667, 6), (key352, 6), (key541, 6), (key677, 6), (key369, 6), (key283, 6), (key509, 6), (key667, 6), (key352, 6)]

def rawRow20232 : Integer.Sparse Key := [(key509, 6), (key520, 6), (key506, 6), (key541, 6), (key283, 6), (key292, 6), (key280, 6), (key667, 6), (key671, 6), (key352, 6), (key520, 6), (key349, 6), (key506, 6), (key677, 6), (key369, 6), (key541, 6), (key283, 6), (key667, 6), (key352, 6), (key509, 6)]

def rawRow20233 : Integer.Sparse Key := [(key520, 6), (key509, 6), (key506, 6), (key541, 6), (key292, 6), (key283, 6), (key280, 6), (key671, 6), (key667, 6), (key520, 6), (key352, 6), (key506, 6), (key349, 6), (key677, 6), (key541, 6), (key369, 6), (key283, 6), (key667, 6), (key509, 6), (key352, 6)]

def rawRow20234 : Integer.Sparse Key := [(key506, 6), (key509, 6), (key541, 6), (key520, 6), (key349, 6), (key352, 6), (key369, 6), (key280, 6), (key283, 6), (key506, 6), (key667, 6), (key541, 6), (key677, 6), (key292, 6), (key520, 6), (key671, 6), (key352, 6), (key283, 6), (key509, 6), (key667, 6)]

def rawRow20235 : Integer.Sparse Key := [(key509, 6), (key506, 6), (key541, 6), (key520, 6), (key352, 6), (key349, 6), (key369, 6), (key283, 6), (key280, 6), (key667, 6), (key506, 6), (key677, 6), (key541, 6), (key292, 6), (key671, 6), (key520, 6), (key352, 6), (key283, 6), (key667, 6), (key509, 6)]

def rawRow20236 : Integer.Sparse Key := [(key506, 6), (key541, 6), (key509, 6), (key520, 6), (key349, 6), (key369, 6), (key352, 6), (key506, 6), (key541, 6), (key280, 6), (key677, 6), (key283, 6), (key667, 6), (key520, 6), (key292, 6), (key671, 6), (key352, 6), (key509, 6), (key283, 6), (key667, 6)]

def rawRow20237 : Integer.Sparse Key := [(key541, 6), (key506, 6), (key509, 6), (key520, 6), (key369, 6), (key349, 6), (key352, 6), (key541, 6), (key506, 6), (key677, 6), (key280, 6), (key667, 6), (key283, 6), (key520, 6), (key671, 6), (key292, 6), (key352, 6), (key509, 6), (key667, 6), (key283, 6)]

def rawRow20238 : Integer.Sparse Key := [(key509, 6), (key541, 6), (key506, 6), (key520, 6), (key352, 6), (key369, 6), (key349, 6), (key667, 6), (key677, 6), (key283, 6), (key541, 6), (key280, 6), (key506, 6), (key671, 6), (key292, 6), (key520, 6), (key352, 6), (key667, 6), (key283, 6), (key509, 6)]

def rawRow20239 : Integer.Sparse Key := [(key541, 6), (key509, 6), (key506, 6), (key520, 6), (key369, 6), (key352, 6), (key349, 6), (key677, 6), (key667, 6), (key541, 6), (key283, 6), (key506, 6), (key280, 6), (key671, 6), (key520, 6), (key292, 6), (key352, 6), (key667, 6), (key509, 6), (key283, 6)]

def rawRow20240 : Integer.Sparse Key := [(key506, 6), (key520, 6), (key541, 6), (key509, 6), (key506, 6), (key520, 6), (key541, 6), (key280, 6), (key292, 6), (key349, 6), (key671, 6), (key369, 6), (key677, 6), (key283, 6), (key352, 6), (key667, 6), (key509, 6), (key283, 6), (key352, 6), (key667, 6)]

def rawRow20241 : Integer.Sparse Key := [(key520, 6), (key506, 6), (key541, 6), (key509, 6), (key520, 6), (key506, 6), (key541, 6), (key292, 6), (key280, 6), (key671, 6), (key349, 6), (key677, 6), (key369, 6), (key283, 6), (key667, 6), (key352, 6), (key509, 6), (key283, 6), (key667, 6), (key352, 6)]

def rawRow20242 : Integer.Sparse Key := [(key506, 6), (key541, 6), (key520, 6), (key509, 6), (key506, 6), (key541, 6), (key520, 6), (key349, 6), (key369, 6), (key280, 6), (key677, 6), (key292, 6), (key671, 6), (key352, 6), (key283, 6), (key667, 6), (key509, 6), (key352, 6), (key283, 6), (key667, 6)]

def rawRow20243 : Integer.Sparse Key := [(key541, 6), (key506, 6), (key520, 6), (key509, 6), (key541, 6), (key506, 6), (key520, 6), (key369, 6), (key349, 6), (key677, 6), (key280, 6), (key671, 6), (key292, 6), (key352, 6), (key667, 6), (key283, 6), (key509, 6), (key352, 6), (key667, 6), (key283, 6)]

def rawRow20244 : Integer.Sparse Key := [(key520, 6), (key541, 6), (key506, 6), (key509, 6), (key520, 6), (key541, 6), (key506, 6), (key671, 6), (key677, 6), (key292, 6), (key369, 6), (key280, 6), (key349, 6), (key667, 6), (key283, 6), (key352, 6), (key509, 6), (key667, 6), (key283, 6), (key352, 6)]

def rawRow20245 : Integer.Sparse Key := [(key541, 6), (key520, 6), (key506, 6), (key509, 6), (key541, 6), (key520, 6), (key506, 6), (key677, 6), (key671, 6), (key369, 6), (key292, 6), (key349, 6), (key280, 6), (key667, 6), (key352, 6), (key283, 6), (key509, 6), (key667, 6), (key352, 6), (key283, 6)]

def rawRow20246 : Integer.Sparse Key := [(key509, 6), (key520, 6), (key541, 6), (key506, 6), (key667, 6), (key671, 6), (key677, 6), (key283, 6), (key292, 6), (key352, 6), (key520, 6), (key369, 6), (key541, 6), (key280, 6), (key349, 6), (key506, 6), (key667, 6), (key283, 6), (key352, 6), (key509, 6)]

def rawRow20247 : Integer.Sparse Key := [(key520, 6), (key509, 6), (key541, 6), (key506, 6), (key671, 6), (key667, 6), (key677, 6), (key292, 6), (key283, 6), (key520, 6), (key352, 6), (key541, 6), (key369, 6), (key280, 6), (key506, 6), (key349, 6), (key667, 6), (key283, 6), (key509, 6), (key352, 6)]

def rawRow20248 : Integer.Sparse Key := [(key509, 6), (key541, 6), (key520, 6), (key506, 6), (key667, 6), (key677, 6), (key671, 6), (key352, 6), (key369, 6), (key283, 6), (key541, 6), (key292, 6), (key520, 6), (key349, 6), (key280, 6), (key506, 6), (key667, 6), (key352, 6), (key283, 6), (key509, 6)]

def rawRow20249 : Integer.Sparse Key := [(key541, 6), (key509, 6), (key520, 6), (key506, 6), (key677, 6), (key667, 6), (key671, 6), (key369, 6), (key352, 6), (key541, 6), (key283, 6), (key520, 6), (key292, 6), (key349, 6), (key506, 6), (key280, 6), (key667, 6), (key352, 6), (key509, 6), (key283, 6)]

def rawRow20250 : Integer.Sparse Key := [(key520, 6), (key541, 6), (key509, 6), (key506, 6), (key671, 6), (key677, 6), (key667, 6), (key520, 6), (key541, 6), (key292, 6), (key369, 6), (key283, 6), (key352, 6), (key506, 6), (key280, 6), (key349, 6), (key667, 6), (key509, 6), (key283, 6), (key352, 6)]

def rawRow20251 : Integer.Sparse Key := [(key541, 6), (key520, 6), (key509, 6), (key506, 6), (key677, 6), (key671, 6), (key667, 6), (key541, 6), (key520, 6), (key369, 6), (key292, 6), (key352, 6), (key283, 6), (key506, 6), (key349, 6), (key280, 6), (key667, 6), (key509, 6), (key352, 6), (key283, 6)]

def rawRow20252 : Integer.Sparse Key := [(key667, 6), (key667, 6), (key671, 6), (key677, 6), (key283, 6), (key283, 6), (key292, 6), (key352, 6), (key352, 6), (key509, 6), (key509, 6), (key520, 6), (key520, 6), (key369, 6), (key541, 6), (key541, 6), (key280, 6), (key349, 6), (key506, 6), (key506, 6)]

def rawRow20253 : Integer.Sparse Key := [(key667, 6), (key671, 6), (key667, 6), (key677, 6), (key283, 6), (key292, 6), (key283, 6), (key509, 6), (key520, 6), (key352, 6), (key520, 6), (key352, 6), (key509, 6), (key541, 6), (key369, 6), (key541, 6), (key280, 6), (key506, 6), (key349, 6), (key506, 6)]

def rawRow20254 : Integer.Sparse Key := [(key671, 6), (key667, 6), (key667, 6), (key677, 6), (key292, 6), (key283, 6), (key283, 6), (key520, 6), (key509, 6), (key520, 6), (key352, 6), (key509, 6), (key352, 6), (key541, 6), (key541, 6), (key369, 6), (key280, 6), (key506, 6), (key506, 6), (key349, 6)]

def rawRow20255 : Integer.Sparse Key := [(key667, 6), (key667, 6), (key677, 6), (key671, 6), (key352, 6), (key352, 6), (key369, 6), (key283, 6), (key283, 6), (key509, 6), (key509, 6), (key541, 6), (key541, 6), (key292, 6), (key520, 6), (key520, 6), (key349, 6), (key280, 6), (key506, 6), (key506, 6)]

def rawRow20256 : Integer.Sparse Key := [(key667, 6), (key677, 6), (key667, 6), (key671, 6), (key352, 6), (key369, 6), (key352, 6), (key509, 6), (key541, 6), (key283, 6), (key541, 6), (key283, 6), (key509, 6), (key520, 6), (key292, 6), (key520, 6), (key349, 6), (key506, 6), (key280, 6), (key506, 6)]

def rawRow20257 : Integer.Sparse Key := [(key677, 6), (key667, 6), (key667, 6), (key671, 6), (key369, 6), (key352, 6), (key352, 6), (key541, 6), (key509, 6), (key541, 6), (key283, 6), (key509, 6), (key283, 6), (key520, 6), (key520, 6), (key292, 6), (key349, 6), (key506, 6), (key506, 6), (key280, 6)]

def rawRow20258 : Integer.Sparse Key := [(key667, 6), (key671, 6), (key677, 6), (key667, 6), (key509, 6), (key520, 6), (key541, 6), (key283, 6), (key292, 6), (key352, 6), (key520, 6), (key369, 6), (key541, 6), (key283, 6), (key352, 6), (key509, 6), (key506, 6), (key280, 6), (key349, 6), (key506, 6)]

def rawRow20259 : Integer.Sparse Key := [(key671, 6), (key667, 6), (key677, 6), (key667, 6), (key520, 6), (key509, 6), (key541, 6), (key292, 6), (key283, 6), (key520, 6), (key352, 6), (key541, 6), (key369, 6), (key283, 6), (key509, 6), (key352, 6), (key506, 6), (key280, 6), (key506, 6), (key349, 6)]

def rawRow20260 : Integer.Sparse Key := [(key667, 6), (key677, 6), (key671, 6), (key667, 6), (key509, 6), (key541, 6), (key520, 6), (key352, 6), (key369, 6), (key283, 6), (key541, 6), (key292, 6), (key520, 6), (key352, 6), (key283, 6), (key509, 6), (key506, 6), (key349, 6), (key280, 6), (key506, 6)]

def rawRow20261 : Integer.Sparse Key := [(key677, 6), (key667, 6), (key671, 6), (key667, 6), (key541, 6), (key509, 6), (key520, 6), (key369, 6), (key352, 6), (key541, 6), (key283, 6), (key520, 6), (key292, 6), (key352, 6), (key509, 6), (key283, 6), (key506, 6), (key349, 6), (key506, 6), (key280, 6)]

def rawRow20262 : Integer.Sparse Key := [(key671, 6), (key677, 6), (key667, 6), (key667, 6), (key520, 6), (key541, 6), (key509, 6), (key520, 6), (key541, 6), (key292, 6), (key369, 6), (key283, 6), (key352, 6), (key509, 6), (key283, 6), (key352, 6), (key506, 6), (key506, 6), (key280, 6), (key349, 6)]

def rawRow20263 : Integer.Sparse Key := [(key677, 6), (key671, 6), (key667, 6), (key667, 6), (key541, 6), (key520, 6), (key509, 6), (key541, 6), (key520, 6), (key369, 6), (key292, 6), (key352, 6), (key283, 6), (key509, 6), (key352, 6), (key283, 6), (key506, 6), (key506, 6), (key349, 6), (key280, 6)]

def rawRow20264 : Integer.Sparse Key := [(key236, 2), (key241, 2), (key241, 2), (key248, 2), (key253, 2), (key248, 2), (key263, 2), (key253, 2), (key263, 2), (key277, 2), (key277, 2), (key278, 2), (key302, 2), (key307, 2), (key307, 2), (key316, 2), (key321, 2), (key316, 2), (key331, 2), (key321, 2), (key331, 2), (key346, 2), (key346, 2), (key347, 2), (key385, 2), (key390, 2), (key385, 2), (key400, 2), (key390, 2), (key400, 2), (key406, 2), (key411, 2), (key406, 2), (key421, 2), (key411, 2), (key421, 2), (key435, 2), (key445, 2), (key435, 2), (key453, 2), (key445, 2), (key453, 2), (key487, 2), (key488, 2), (key487, 2), (key489, 2), (key488, 2), (key489, 2), (key655, 2), (key655, 2), (key656, 2), (key657, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 2), (key660, 2), (key662, 2), (key661, 2), (key662, 2)]

def rawRow20265 : Integer.Sparse Key := [(key241, 2), (key236, 2), (key241, 2), (key253, 2), (key248, 2), (key263, 2), (key248, 2), (key263, 2), (key253, 2), (key277, 2), (key278, 2), (key277, 2), (key307, 2), (key302, 2), (key307, 2), (key321, 2), (key316, 2), (key331, 2), (key316, 2), (key331, 2), (key321, 2), (key346, 2), (key347, 2), (key346, 2), (key390, 2), (key385, 2), (key400, 2), (key385, 2), (key400, 2), (key390, 2), (key411, 2), (key406, 2), (key421, 2), (key406, 2), (key421, 2), (key411, 2), (key445, 2), (key435, 2), (key453, 2), (key435, 2), (key453, 2), (key445, 2), (key488, 2), (key487, 2), (key489, 2), (key487, 2), (key489, 2), (key488, 2), (key655, 2), (key656, 2), (key655, 2), (key657, 2), (key658, 2), (key657, 2), (key661, 2), (key660, 2), (key662, 2), (key660, 2), (key662, 2), (key661, 2)]

def rawRow20266 : Integer.Sparse Key := [(key241, 2), (key241, 2), (key236, 2), (key263, 2), (key263, 2), (key253, 2), (key253, 2), (key248, 2), (key248, 2), (key278, 2), (key277, 2), (key277, 2), (key307, 2), (key307, 2), (key302, 2), (key331, 2), (key331, 2), (key321, 2), (key321, 2), (key316, 2), (key316, 2), (key347, 2), (key346, 2), (key346, 2), (key400, 2), (key400, 2), (key390, 2), (key390, 2), (key385, 2), (key385, 2), (key421, 2), (key421, 2), (key411, 2), (key411, 2), (key406, 2), (key406, 2), (key453, 2), (key453, 2), (key445, 2), (key445, 2), (key435, 2), (key435, 2), (key489, 2), (key489, 2), (key488, 2), (key488, 2), (key487, 2), (key487, 2), (key656, 2), (key655, 2), (key655, 2), (key658, 2), (key657, 2), (key657, 2), (key662, 2), (key662, 2), (key661, 2), (key661, 2), (key660, 2), (key660, 2)]

def rawRow20267 : Integer.Sparse Key := [(key248, 2), (key253, 2), (key263, 2), (key236, 2), (key241, 2), (key248, 2), (key263, 2), (key277, 2), (key278, 2), (key241, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key346, 2), (key302, 2), (key307, 2), (key316, 2), (key331, 2), (key346, 2), (key347, 2), (key307, 2), (key321, 2), (key331, 2), (key406, 2), (key411, 2), (key435, 2), (key445, 2), (key487, 2), (key488, 2), (key385, 2), (key390, 2), (key435, 2), (key453, 2), (key487, 2), (key489, 2), (key385, 2), (key400, 2), (key406, 2), (key421, 2), (key488, 2), (key489, 2), (key390, 2), (key400, 2), (key411, 2), (key421, 2), (key445, 2), (key453, 2), (key657, 2), (key660, 2), (key661, 2), (key655, 2), (key660, 2), (key662, 2), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key661, 2), (key662, 2)]

def rawRow20268 : Integer.Sparse Key := [(key253, 2), (key248, 2), (key263, 2), (key241, 2), (key236, 2), (key263, 2), (key248, 2), (key278, 2), (key277, 2), (key241, 2), (key263, 2), (key253, 2), (key321, 2), (key316, 2), (key346, 2), (key307, 2), (key302, 2), (key331, 2), (key316, 2), (key347, 2), (key346, 2), (key307, 2), (key331, 2), (key321, 2), (key411, 2), (key406, 2), (key445, 2), (key435, 2), (key488, 2), (key487, 2), (key390, 2), (key385, 2), (key453, 2), (key435, 2), (key489, 2), (key487, 2), (key400, 2), (key385, 2), (key421, 2), (key406, 2), (key489, 2), (key488, 2), (key400, 2), (key390, 2), (key421, 2), (key411, 2), (key453, 2), (key445, 2), (key657, 2), (key661, 2), (key660, 2), (key655, 2), (key662, 2), (key660, 2), (key656, 2), (key655, 2), (key658, 2), (key657, 2), (key662, 2), (key661, 2)]

def rawRow20269 : Integer.Sparse Key := [(key248, 2), (key263, 2), (key253, 2), (key248, 2), (key263, 2), (key236, 2), (key278, 2), (key241, 2), (key263, 2), (key253, 2), (key241, 2), (key263, 2), (key316, 2), (key346, 2), (key321, 2), (key316, 2), (key346, 2), (key302, 2), (key347, 2), (key307, 2), (key331, 2), (key321, 2), (key307, 2), (key331, 2), (key435, 2), (key487, 2), (key406, 2), (key488, 2), (key411, 2), (key445, 2), (key435, 2), (key487, 2), (key385, 2), (key489, 2), (key390, 2), (key453, 2), (key406, 2), (key488, 2), (key385, 2), (key489, 2), (key400, 2), (key421, 2), (key411, 2), (key445, 2), (key390, 2), (key453, 2), (key400, 2), (key421, 2), (key660, 2), (key657, 2), (key661, 2), (key660, 2), (key655, 2), (key662, 2), (key657, 2), (key661, 2), (key655, 2), (key662, 2), (key656, 2), (key658, 2)]

def rawRow20270 : Integer.Sparse Key := [(key263, 2), (key248, 2), (key253, 2), (key263, 2), (key248, 2), (key278, 2), (key236, 2), (key263, 2), (key241, 2), (key253, 2), (key263, 2), (key241, 2), (key346, 2), (key316, 2), (key321, 2), (key346, 2), (key316, 2), (key347, 2), (key302, 2), (key331, 2), (key307, 2), (key321, 2), (key331, 2), (key307, 2), (key487, 2), (key435, 2), (key488, 2), (key406, 2), (key445, 2), (key411, 2), (key487, 2), (key435, 2), (key489, 2), (key385, 2), (key453, 2), (key390, 2), (key488, 2), (key406, 2), (key489, 2), (key385, 2), (key421, 2), (key400, 2), (key445, 2), (key411, 2), (key453, 2), (key390, 2), (key421, 2), (key400, 2), (key660, 2), (key661, 2), (key657, 2), (key660, 2), (key662, 2), (key655, 2), (key661, 2), (key657, 2), (key662, 2), (key655, 2), (key658, 2), (key656, 2)]

def rawRow20271 : Integer.Sparse Key := [(key253, 2), (key263, 2), (key248, 2), (key277, 2), (key278, 2), (key241, 2), (key263, 2), (key236, 2), (key248, 2), (key263, 2), (key241, 2), (key253, 2), (key321, 2), (key346, 2), (key316, 2), (key331, 2), (key347, 2), (key307, 2), (key346, 2), (key302, 2), (key316, 2), (key331, 2), (key307, 2), (key321, 2), (key445, 2), (key488, 2), (key411, 2), (key487, 2), (key406, 2), (key435, 2), (key453, 2), (key489, 2), (key390, 2), (key487, 2), (key385, 2), (key435, 2), (key421, 2), (key489, 2), (key400, 2), (key488, 2), (key385, 2), (key406, 2), (key421, 2), (key453, 2), (key400, 2), (key445, 2), (key390, 2), (key411, 2), (key661, 2), (key657, 2), (key660, 2), (key662, 2), (key655, 2), (key660, 2), (key658, 2), (key662, 2), (key656, 2), (key661, 2), (key655, 2), (key657, 2)]

def rawRow20272 : Integer.Sparse Key := [(key263, 2), (key253, 2), (key248, 2), (key278, 2), (key277, 2), (key263, 2), (key241, 2), (key248, 2), (key236, 2), (key263, 2), (key253, 2), (key241, 2), (key346, 2), (key321, 2), (key316, 2), (key347, 2), (key331, 2), (key346, 2), (key307, 2), (key316, 2), (key302, 2), (key331, 2), (key321, 2), (key307, 2), (key488, 2), (key445, 2), (key487, 2), (key411, 2), (key435, 2), (key406, 2), (key489, 2), (key453, 2), (key487, 2), (key390, 2), (key435, 2), (key385, 2), (key489, 2), (key421, 2), (key488, 2), (key400, 2), (key406, 2), (key385, 2), (key453, 2), (key421, 2), (key445, 2), (key400, 2), (key411, 2), (key390, 2), (key661, 2), (key660, 2), (key657, 2), (key662, 2), (key660, 2), (key655, 2), (key662, 2), (key658, 2), (key661, 2), (key656, 2), (key657, 2), (key655, 2)]

def rawRow20273 : Integer.Sparse Key := [(key277, 2), (key277, 2), (key278, 2), (key241, 2), (key241, 2), (key253, 2), (key253, 2), (key263, 2), (key263, 2), (key236, 2), (key248, 2), (key248, 2), (key331, 2), (key331, 2), (key347, 2), (key307, 2), (key307, 2), (key321, 2), (key321, 2), (key346, 2), (key346, 2), (key302, 2), (key316, 2), (key316, 2), (key421, 2), (key421, 2), (key453, 2), (key453, 2), (key489, 2), (key489, 2), (key400, 2), (key400, 2), (key445, 2), (key445, 2), (key488, 2), (key488, 2), (key390, 2), (key390, 2), (key411, 2), (key411, 2), (key487, 2), (key487, 2), (key385, 2), (key385, 2), (key406, 2), (key406, 2), (key435, 2), (key435, 2), (key658, 2), (key662, 2), (key662, 2), (key656, 2), (key661, 2), (key661, 2), (key655, 2), (key655, 2), (key657, 2), (key657, 2), (key660, 2), (key660, 2)]

def rawRow20274 : Integer.Sparse Key := [(key277, 2), (key278, 2), (key277, 2), (key253, 2), (key263, 2), (key241, 2), (key263, 2), (key241, 2), (key253, 2), (key248, 2), (key236, 2), (key248, 2), (key331, 2), (key347, 2), (key331, 2), (key321, 2), (key346, 2), (key307, 2), (key346, 2), (key307, 2), (key321, 2), (key316, 2), (key302, 2), (key316, 2), (key453, 2), (key489, 2), (key421, 2), (key489, 2), (key421, 2), (key453, 2), (key445, 2), (key488, 2), (key400, 2), (key488, 2), (key400, 2), (key445, 2), (key411, 2), (key487, 2), (key390, 2), (key487, 2), (key390, 2), (key411, 2), (key406, 2), (key435, 2), (key385, 2), (key435, 2), (key385, 2), (key406, 2), (key662, 2), (key658, 2), (key662, 2), (key661, 2), (key656, 2), (key661, 2), (key657, 2), (key660, 2), (key655, 2), (key660, 2), (key655, 2), (key657, 2)]

def rawRow20275 : Integer.Sparse Key := [(key278, 2), (key277, 2), (key277, 2), (key263, 2), (key253, 2), (key263, 2), (key241, 2), (key253, 2), (key241, 2), (key248, 2), (key248, 2), (key236, 2), (key347, 2), (key331, 2), (key331, 2), (key346, 2), (key321, 2), (key346, 2), (key307, 2), (key321, 2), (key307, 2), (key316, 2), (key316, 2), (key302, 2), (key489, 2), (key453, 2), (key489, 2), (key421, 2), (key453, 2), (key421, 2), (key488, 2), (key445, 2), (key488, 2), (key400, 2), (key445, 2), (key400, 2), (key487, 2), (key411, 2), (key487, 2), (key390, 2), (key411, 2), (key390, 2), (key435, 2), (key406, 2), (key435, 2), (key385, 2), (key406, 2), (key385, 2), (key662, 2), (key662, 2), (key658, 2), (key661, 2), (key661, 2), (key656, 2), (key660, 2), (key657, 2), (key660, 2), (key655, 2), (key657, 2), (key655, 2)]

def rawRow20276 : Integer.Sparse Key := [(key302, 2), (key307, 2), (key307, 2), (key316, 2), (key321, 2), (key316, 2), (key346, 2), (key321, 2), (key346, 2), (key331, 2), (key331, 2), (key347, 2), (key236, 2), (key241, 2), (key241, 2), (key406, 2), (key411, 2), (key406, 2), (key421, 2), (key411, 2), (key421, 2), (key657, 2), (key657, 2), (key658, 2), (key248, 2), (key253, 2), (key248, 2), (key263, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key316, 2), (key331, 2), (key321, 2), (key331, 2), (key435, 2), (key445, 2), (key435, 2), (key453, 2), (key445, 2), (key453, 2), (key660, 2), (key661, 2), (key660, 2), (key662, 2), (key661, 2), (key662, 2), (key277, 2), (key277, 2), (key278, 2), (key346, 2), (key346, 2), (key347, 2), (key487, 2), (key488, 2), (key487, 2), (key489, 2), (key488, 2), (key489, 2)]

def rawRow20277 : Integer.Sparse Key := [(key307, 2), (key302, 2), (key307, 2), (key321, 2), (key316, 2), (key346, 2), (key316, 2), (key346, 2), (key321, 2), (key331, 2), (key347, 2), (key331, 2), (key241, 2), (key236, 2), (key241, 2), (key411, 2), (key406, 2), (key421, 2), (key406, 2), (key421, 2), (key411, 2), (key657, 2), (key658, 2), (key657, 2), (key253, 2), (key248, 2), (key263, 2), (key248, 2), (key263, 2), (key253, 2), (key321, 2), (key316, 2), (key331, 2), (key316, 2), (key331, 2), (key321, 2), (key445, 2), (key435, 2), (key453, 2), (key435, 2), (key453, 2), (key445, 2), (key661, 2), (key660, 2), (key662, 2), (key660, 2), (key662, 2), (key661, 2), (key277, 2), (key278, 2), (key277, 2), (key346, 2), (key347, 2), (key346, 2), (key488, 2), (key487, 2), (key489, 2), (key487, 2), (key489, 2), (key488, 2)]

def rawRow20278 : Integer.Sparse Key := [(key307, 2), (key307, 2), (key302, 2), (key346, 2), (key346, 2), (key321, 2), (key321, 2), (key316, 2), (key316, 2), (key347, 2), (key331, 2), (key331, 2), (key241, 2), (key241, 2), (key236, 2), (key421, 2), (key421, 2), (key411, 2), (key411, 2), (key406, 2), (key406, 2), (key658, 2), (key657, 2), (key657, 2), (key263, 2), (key263, 2), (key253, 2), (key253, 2), (key248, 2), (key248, 2), (key331, 2), (key331, 2), (key321, 2), (key321, 2), (key316, 2), (key316, 2), (key453, 2), (key453, 2), (key445, 2), (key445, 2), (key435, 2), (key435, 2), (key662, 2), (key662, 2), (key661, 2), (key661, 2), (key660, 2), (key660, 2), (key278, 2), (key277, 2), (key277, 2), (key347, 2), (key346, 2), (key346, 2), (key489, 2), (key489, 2), (key488, 2), (key488, 2), (key487, 2), (key487, 2)]

def rawRow20279 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key302, 2), (key307, 2), (key316, 2), (key346, 2), (key331, 2), (key347, 2), (key307, 2), (key321, 2), (key346, 2), (key406, 2), (key411, 2), (key421, 2), (key236, 2), (key241, 2), (key406, 2), (key421, 2), (key657, 2), (key658, 2), (key241, 2), (key411, 2), (key421, 2), (key316, 2), (key321, 2), (key435, 2), (key445, 2), (key660, 2), (key661, 2), (key248, 2), (key253, 2), (key435, 2), (key453, 2), (key660, 2), (key662, 2), (key248, 2), (key263, 2), (key316, 2), (key331, 2), (key661, 2), (key662, 2), (key253, 2), (key263, 2), (key321, 2), (key331, 2), (key445, 2), (key453, 2), (key346, 2), (key487, 2), (key488, 2), (key277, 2), (key487, 2), (key489, 2), (key277, 2), (key278, 2), (key346, 2), (key347, 2), (key488, 2), (key489, 2)]

def rawRow20280 : Integer.Sparse Key := [(key321, 2), (key316, 2), (key331, 2), (key307, 2), (key302, 2), (key346, 2), (key316, 2), (key347, 2), (key331, 2), (key307, 2), (key346, 2), (key321, 2), (key411, 2), (key406, 2), (key421, 2), (key241, 2), (key236, 2), (key421, 2), (key406, 2), (key658, 2), (key657, 2), (key241, 2), (key421, 2), (key411, 2), (key321, 2), (key316, 2), (key445, 2), (key435, 2), (key661, 2), (key660, 2), (key253, 2), (key248, 2), (key453, 2), (key435, 2), (key662, 2), (key660, 2), (key263, 2), (key248, 2), (key331, 2), (key316, 2), (key662, 2), (key661, 2), (key263, 2), (key253, 2), (key331, 2), (key321, 2), (key453, 2), (key445, 2), (key346, 2), (key488, 2), (key487, 2), (key277, 2), (key489, 2), (key487, 2), (key278, 2), (key277, 2), (key347, 2), (key346, 2), (key489, 2), (key488, 2)]

def rawRow20281 : Integer.Sparse Key := [(key316, 2), (key331, 2), (key321, 2), (key316, 2), (key331, 2), (key302, 2), (key347, 2), (key307, 2), (key346, 2), (key321, 2), (key307, 2), (key346, 2), (key406, 2), (key421, 2), (key411, 2), (key406, 2), (key421, 2), (key236, 2), (key658, 2), (key241, 2), (key421, 2), (key411, 2), (key241, 2), (key421, 2), (key435, 2), (key660, 2), (key316, 2), (key661, 2), (key321, 2), (key445, 2), (key435, 2), (key660, 2), (key248, 2), (key662, 2), (key253, 2), (key453, 2), (key316, 2), (key661, 2), (key248, 2), (key662, 2), (key263, 2), (key331, 2), (key321, 2), (key445, 2), (key253, 2), (key453, 2), (key263, 2), (key331, 2), (key487, 2), (key346, 2), (key488, 2), (key487, 2), (key277, 2), (key489, 2), (key346, 2), (key488, 2), (key277, 2), (key489, 2), (key278, 2), (key347, 2)]

def rawRow20282 : Integer.Sparse Key := [(key331, 2), (key316, 2), (key321, 2), (key331, 2), (key316, 2), (key347, 2), (key302, 2), (key346, 2), (key307, 2), (key321, 2), (key346, 2), (key307, 2), (key421, 2), (key406, 2), (key411, 2), (key421, 2), (key406, 2), (key658, 2), (key236, 2), (key421, 2), (key241, 2), (key411, 2), (key421, 2), (key241, 2), (key660, 2), (key435, 2), (key661, 2), (key316, 2), (key445, 2), (key321, 2), (key660, 2), (key435, 2), (key662, 2), (key248, 2), (key453, 2), (key253, 2), (key661, 2), (key316, 2), (key662, 2), (key248, 2), (key331, 2), (key263, 2), (key445, 2), (key321, 2), (key453, 2), (key253, 2), (key331, 2), (key263, 2), (key487, 2), (key488, 2), (key346, 2), (key487, 2), (key489, 2), (key277, 2), (key488, 2), (key346, 2), (key489, 2), (key277, 2), (key347, 2), (key278, 2)]

def rawRow20283 : Integer.Sparse Key := [(key321, 2), (key331, 2), (key316, 2), (key346, 2), (key347, 2), (key307, 2), (key331, 2), (key302, 2), (key316, 2), (key346, 2), (key307, 2), (key321, 2), (key411, 2), (key421, 2), (key406, 2), (key657, 2), (key658, 2), (key241, 2), (key421, 2), (key236, 2), (key406, 2), (key421, 2), (key241, 2), (key411, 2), (key445, 2), (key661, 2), (key321, 2), (key660, 2), (key316, 2), (key435, 2), (key453, 2), (key662, 2), (key253, 2), (key660, 2), (key248, 2), (key435, 2), (key331, 2), (key662, 2), (key263, 2), (key661, 2), (key248, 2), (key316, 2), (key331, 2), (key453, 2), (key263, 2), (key445, 2), (key253, 2), (key321, 2), (key488, 2), (key346, 2), (key487, 2), (key489, 2), (key277, 2), (key487, 2), (key347, 2), (key489, 2), (key278, 2), (key488, 2), (key277, 2), (key346, 2)]

def rawRow20284 : Integer.Sparse Key := [(key331, 2), (key321, 2), (key316, 2), (key347, 2), (key346, 2), (key331, 2), (key307, 2), (key316, 2), (key302, 2), (key346, 2), (key321, 2), (key307, 2), (key421, 2), (key411, 2), (key406, 2), (key658, 2), (key657, 2), (key421, 2), (key241, 2), (key406, 2), (key236, 2), (key421, 2), (key411, 2), (key241, 2), (key661, 2), (key445, 2), (key660, 2), (key321, 2), (key435, 2), (key316, 2), (key662, 2), (key453, 2), (key660, 2), (key253, 2), (key435, 2), (key248, 2), (key662, 2), (key331, 2), (key661, 2), (key263, 2), (key316, 2), (key248, 2), (key453, 2), (key331, 2), (key445, 2), (key263, 2), (key321, 2), (key253, 2), (key488, 2), (key487, 2), (key346, 2), (key489, 2), (key487, 2), (key277, 2), (key489, 2), (key347, 2), (key488, 2), (key278, 2), (key346, 2), (key277, 2)]

def rawRow20285 : Integer.Sparse Key := [(key346, 2), (key346, 2), (key347, 2), (key307, 2), (key307, 2), (key321, 2), (key321, 2), (key331, 2), (key331, 2), (key302, 2), (key316, 2), (key316, 2), (key657, 2), (key657, 2), (key658, 2), (key241, 2), (key241, 2), (key411, 2), (key411, 2), (key421, 2), (key421, 2), (key236, 2), (key406, 2), (key406, 2), (key331, 2), (key331, 2), (key453, 2), (key453, 2), (key662, 2), (key662, 2), (key263, 2), (key263, 2), (key445, 2), (key445, 2), (key661, 2), (key661, 2), (key253, 2), (key253, 2), (key321, 2), (key321, 2), (key660, 2), (key660, 2), (key248, 2), (key248, 2), (key316, 2), (key316, 2), (key435, 2), (key435, 2), (key347, 2), (key489, 2), (key489, 2), (key278, 2), (key488, 2), (key488, 2), (key277, 2), (key277, 2), (key346, 2), (key346, 2), (key487, 2), (key487, 2)]

def rawRow20286 : Integer.Sparse Key := [(key346, 2), (key347, 2), (key346, 2), (key321, 2), (key331, 2), (key307, 2), (key331, 2), (key307, 2), (key321, 2), (key316, 2), (key302, 2), (key316, 2), (key657, 2), (key658, 2), (key657, 2), (key411, 2), (key421, 2), (key241, 2), (key421, 2), (key241, 2), (key411, 2), (key406, 2), (key236, 2), (key406, 2), (key453, 2), (key662, 2), (key331, 2), (key662, 2), (key331, 2), (key453, 2), (key445, 2), (key661, 2), (key263, 2), (key661, 2), (key263, 2), (key445, 2), (key321, 2), (key660, 2), (key253, 2), (key660, 2), (key253, 2), (key321, 2), (key316, 2), (key435, 2), (key248, 2), (key435, 2), (key248, 2), (key316, 2), (key489, 2), (key347, 2), (key489, 2), (key488, 2), (key278, 2), (key488, 2), (key346, 2), (key487, 2), (key277, 2), (key487, 2), (key277, 2), (key346, 2)]

def rawRow20287 : Integer.Sparse Key := [(key347, 2), (key346, 2), (key346, 2), (key331, 2), (key321, 2), (key331, 2), (key307, 2), (key321, 2), (key307, 2), (key316, 2), (key316, 2), (key302, 2), (key658, 2), (key657, 2), (key657, 2), (key421, 2), (key411, 2), (key421, 2), (key241, 2), (key411, 2), (key241, 2), (key406, 2), (key406, 2), (key236, 2), (key662, 2), (key453, 2), (key662, 2), (key331, 2), (key453, 2), (key331, 2), (key661, 2), (key445, 2), (key661, 2), (key263, 2), (key445, 2), (key263, 2), (key660, 2), (key321, 2), (key660, 2), (key253, 2), (key321, 2), (key253, 2), (key435, 2), (key316, 2), (key435, 2), (key248, 2), (key316, 2), (key248, 2), (key489, 2), (key489, 2), (key347, 2), (key488, 2), (key488, 2), (key278, 2), (key487, 2), (key346, 2), (key487, 2), (key277, 2), (key346, 2), (key277, 2)]

def rawRow20288 : Integer.Sparse Key := [(key385, 2), (key390, 2), (key400, 2), (key406, 2), (key411, 2), (key435, 2), (key487, 2), (key445, 2), (key488, 2), (key421, 2), (key453, 2), (key489, 2), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key435, 2), (key660, 2), (key445, 2), (key661, 2), (key331, 2), (key453, 2), (key662, 2), (key236, 2), (key241, 2), (key248, 2), (key263, 2), (key277, 2), (key278, 2), (key302, 2), (key307, 2), (key316, 2), (key331, 2), (key346, 2), (key347, 2), (key385, 2), (key400, 2), (key406, 2), (key421, 2), (key488, 2), (key489, 2), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key661, 2), (key662, 2), (key241, 2), (key253, 2), (key263, 2), (key307, 2), (key321, 2), (key331, 2), (key390, 2), (key400, 2), (key411, 2), (key421, 2), (key445, 2), (key453, 2)]

def rawRow20289 : Integer.Sparse Key := [(key390, 2), (key385, 2), (key400, 2), (key411, 2), (key406, 2), (key487, 2), (key435, 2), (key488, 2), (key445, 2), (key421, 2), (key489, 2), (key453, 2), (key253, 2), (key248, 2), (key263, 2), (key321, 2), (key316, 2), (key660, 2), (key435, 2), (key661, 2), (key445, 2), (key331, 2), (key662, 2), (key453, 2), (key241, 2), (key236, 2), (key263, 2), (key248, 2), (key278, 2), (key277, 2), (key307, 2), (key302, 2), (key331, 2), (key316, 2), (key347, 2), (key346, 2), (key400, 2), (key385, 2), (key421, 2), (key406, 2), (key489, 2), (key488, 2), (key656, 2), (key655, 2), (key658, 2), (key657, 2), (key662, 2), (key661, 2), (key241, 2), (key263, 2), (key253, 2), (key307, 2), (key331, 2), (key321, 2), (key400, 2), (key390, 2), (key421, 2), (key411, 2), (key453, 2), (key445, 2)]

def rawRow20290 : Integer.Sparse Key := [(key385, 2), (key400, 2), (key390, 2), (key435, 2), (key445, 2), (key406, 2), (key488, 2), (key411, 2), (key487, 2), (key453, 2), (key421, 2), (key489, 2), (key248, 2), (key263, 2), (key253, 2), (key435, 2), (key445, 2), (key316, 2), (key661, 2), (key321, 2), (key660, 2), (key453, 2), (key331, 2), (key662, 2), (key248, 2), (key263, 2), (key236, 2), (key278, 2), (key241, 2), (key263, 2), (key316, 2), (key346, 2), (key302, 2), (key347, 2), (key307, 2), (key331, 2), (key406, 2), (key488, 2), (key385, 2), (key489, 2), (key400, 2), (key421, 2), (key657, 2), (key661, 2), (key655, 2), (key662, 2), (key656, 2), (key658, 2), (key253, 2), (key241, 2), (key263, 2), (key321, 2), (key307, 2), (key331, 2), (key411, 2), (key445, 2), (key390, 2), (key453, 2), (key400, 2), (key421, 2)]

def rawRow20291 : Integer.Sparse Key := [(key400, 2), (key385, 2), (key390, 2), (key445, 2), (key435, 2), (key488, 2), (key406, 2), (key487, 2), (key411, 2), (key453, 2), (key489, 2), (key421, 2), (key263, 2), (key248, 2), (key253, 2), (key445, 2), (key435, 2), (key661, 2), (key316, 2), (key660, 2), (key321, 2), (key453, 2), (key662, 2), (key331, 2), (key263, 2), (key248, 2), (key278, 2), (key236, 2), (key263, 2), (key241, 2), (key346, 2), (key316, 2), (key347, 2), (key302, 2), (key331, 2), (key307, 2), (key488, 2), (key406, 2), (key489, 2), (key385, 2), (key421, 2), (key400, 2), (key661, 2), (key657, 2), (key662, 2), (key655, 2), (key658, 2), (key656, 2), (key253, 2), (key263, 2), (key241, 2), (key321, 2), (key331, 2), (key307, 2), (key445, 2), (key411, 2), (key453, 2), (key390, 2), (key421, 2), (key400, 2)]

def rawRow20292 : Integer.Sparse Key := [(key390, 2), (key400, 2), (key385, 2), (key487, 2), (key488, 2), (key411, 2), (key445, 2), (key406, 2), (key435, 2), (key489, 2), (key421, 2), (key453, 2), (key253, 2), (key263, 2), (key248, 2), (key660, 2), (key661, 2), (key321, 2), (key445, 2), (key316, 2), (key435, 2), (key662, 2), (key331, 2), (key453, 2), (key277, 2), (key278, 2), (key241, 2), (key263, 2), (key236, 2), (key248, 2), (key331, 2), (key347, 2), (key307, 2), (key346, 2), (key302, 2), (key316, 2), (key421, 2), (key489, 2), (key400, 2), (key488, 2), (key385, 2), (key406, 2), (key658, 2), (key662, 2), (key656, 2), (key661, 2), (key655, 2), (key657, 2), (key263, 2), (key241, 2), (key253, 2), (key331, 2), (key307, 2), (key321, 2), (key421, 2), (key453, 2), (key400, 2), (key445, 2), (key390, 2), (key411, 2)]

def rawRow20293 : Integer.Sparse Key := [(key400, 2), (key390, 2), (key385, 2), (key488, 2), (key487, 2), (key445, 2), (key411, 2), (key435, 2), (key406, 2), (key489, 2), (key453, 2), (key421, 2), (key263, 2), (key253, 2), (key248, 2), (key661, 2), (key660, 2), (key445, 2), (key321, 2), (key435, 2), (key316, 2), (key662, 2), (key453, 2), (key331, 2), (key278, 2), (key277, 2), (key263, 2), (key241, 2), (key248, 2), (key236, 2), (key347, 2), (key331, 2), (key346, 2), (key307, 2), (key316, 2), (key302, 2), (key489, 2), (key421, 2), (key488, 2), (key400, 2), (key406, 2), (key385, 2), (key662, 2), (key658, 2), (key661, 2), (key656, 2), (key657, 2), (key655, 2), (key263, 2), (key253, 2), (key241, 2), (key331, 2), (key321, 2), (key307, 2), (key453, 2), (key421, 2), (key445, 2), (key400, 2), (key411, 2), (key390, 2)]

def rawRow20294 : Integer.Sparse Key := [(key406, 2), (key411, 2), (key421, 2), (key385, 2), (key390, 2), (key435, 2), (key487, 2), (key453, 2), (key489, 2), (key400, 2), (key445, 2), (key488, 2), (key316, 2), (key321, 2), (key331, 2), (key248, 2), (key253, 2), (key435, 2), (key660, 2), (key453, 2), (key662, 2), (key263, 2), (key445, 2), (key661, 2), (key302, 2), (key307, 2), (key316, 2), (key346, 2), (key331, 2), (key347, 2), (key236, 2), (key241, 2), (key406, 2), (key421, 2), (key657, 2), (key658, 2), (key248, 2), (key263, 2), (key316, 2), (key331, 2), (key661, 2), (key662, 2), (key277, 2), (key278, 2), (key346, 2), (key347, 2), (key488, 2), (key489, 2), (key307, 2), (key390, 2), (key400, 2), (key241, 2), (key411, 2), (key421, 2), (key253, 2), (key263, 2), (key321, 2), (key331, 2), (key445, 2), (key453, 2)]

def rawRow20295 : Integer.Sparse Key := [(key411, 2), (key406, 2), (key421, 2), (key390, 2), (key385, 2), (key487, 2), (key435, 2), (key489, 2), (key453, 2), (key400, 2), (key488, 2), (key445, 2), (key321, 2), (key316, 2), (key331, 2), (key253, 2), (key248, 2), (key660, 2), (key435, 2), (key662, 2), (key453, 2), (key263, 2), (key661, 2), (key445, 2), (key307, 2), (key302, 2), (key346, 2), (key316, 2), (key347, 2), (key331, 2), (key241, 2), (key236, 2), (key421, 2), (key406, 2), (key658, 2), (key657, 2), (key263, 2), (key248, 2), (key331, 2), (key316, 2), (key662, 2), (key661, 2), (key278, 2), (key277, 2), (key347, 2), (key346, 2), (key489, 2), (key488, 2), (key307, 2), (key400, 2), (key390, 2), (key241, 2), (key421, 2), (key411, 2), (key263, 2), (key253, 2), (key331, 2), (key321, 2), (key453, 2), (key445, 2)]

def rawRow20296 : Integer.Sparse Key := [(key406, 2), (key421, 2), (key411, 2), (key435, 2), (key453, 2), (key385, 2), (key489, 2), (key390, 2), (key487, 2), (key445, 2), (key400, 2), (key488, 2), (key316, 2), (key331, 2), (key321, 2), (key435, 2), (key453, 2), (key248, 2), (key662, 2), (key253, 2), (key660, 2), (key445, 2), (key263, 2), (key661, 2), (key316, 2), (key331, 2), (key302, 2), (key347, 2), (key307, 2), (key346, 2), (key406, 2), (key421, 2), (key236, 2), (key658, 2), (key241, 2), (key421, 2), (key316, 2), (key661, 2), (key248, 2), (key662, 2), (key263, 2), (key331, 2), (key346, 2), (key488, 2), (key277, 2), (key489, 2), (key278, 2), (key347, 2), (key390, 2), (key307, 2), (key400, 2), (key411, 2), (key241, 2), (key421, 2), (key321, 2), (key445, 2), (key253, 2), (key453, 2), (key263, 2), (key331, 2)]

def rawRow20297 : Integer.Sparse Key := [(key421, 2), (key406, 2), (key411, 2), (key453, 2), (key435, 2), (key489, 2), (key385, 2), (key487, 2), (key390, 2), (key445, 2), (key488, 2), (key400, 2), (key331, 2), (key316, 2), (key321, 2), (key453, 2), (key435, 2), (key662, 2), (key248, 2), (key660, 2), (key253, 2), (key445, 2), (key661, 2), (key263, 2), (key331, 2), (key316, 2), (key347, 2), (key302, 2), (key346, 2), (key307, 2), (key421, 2), (key406, 2), (key658, 2), (key236, 2), (key421, 2), (key241, 2), (key661, 2), (key316, 2), (key662, 2), (key248, 2), (key331, 2), (key263, 2), (key488, 2), (key346, 2), (key489, 2), (key277, 2), (key347, 2), (key278, 2), (key390, 2), (key400, 2), (key307, 2), (key411, 2), (key421, 2), (key241, 2), (key445, 2), (key321, 2), (key453, 2), (key253, 2), (key331, 2), (key263, 2)]

def rawRow20298 : Integer.Sparse Key := [(key411, 2), (key421, 2), (key406, 2), (key487, 2), (key489, 2), (key390, 2), (key453, 2), (key385, 2), (key435, 2), (key488, 2), (key400, 2), (key445, 2), (key321, 2), (key331, 2), (key316, 2), (key660, 2), (key662, 2), (key253, 2), (key453, 2), (key248, 2), (key435, 2), (key661, 2), (key263, 2), (key445, 2), (key346, 2), (key347, 2), (key307, 2), (key331, 2), (key302, 2), (key316, 2), (key657, 2), (key658, 2), (key241, 2), (key421, 2), (key236, 2), (key406, 2), (key331, 2), (key662, 2), (key263, 2), (key661, 2), (key248, 2), (key316, 2), (key347, 2), (key489, 2), (key278, 2), (key488, 2), (key277, 2), (key346, 2), (key400, 2), (key307, 2), (key390, 2), (key421, 2), (key241, 2), (key411, 2), (key331, 2), (key453, 2), (key263, 2), (key445, 2), (key253, 2), (key321, 2)]

def rawRow20299 : Integer.Sparse Key := [(key421, 2), (key411, 2), (key406, 2), (key489, 2), (key487, 2), (key453, 2), (key390, 2), (key435, 2), (key385, 2), (key488, 2), (key445, 2), (key400, 2), (key331, 2), (key321, 2), (key316, 2), (key662, 2), (key660, 2), (key453, 2), (key253, 2), (key435, 2), (key248, 2), (key661, 2), (key445, 2), (key263, 2), (key347, 2), (key346, 2), (key331, 2), (key307, 2), (key316, 2), (key302, 2), (key658, 2), (key657, 2), (key421, 2), (key241, 2), (key406, 2), (key236, 2), (key662, 2), (key331, 2), (key661, 2), (key263, 2), (key316, 2), (key248, 2), (key489, 2), (key347, 2), (key488, 2), (key278, 2), (key346, 2), (key277, 2), (key400, 2), (key390, 2), (key307, 2), (key421, 2), (key411, 2), (key241, 2), (key453, 2), (key331, 2), (key445, 2), (key263, 2), (key321, 2), (key253, 2)]

def rawRow20300 : Integer.Sparse Key := [(key435, 2), (key445, 2), (key453, 2), (key385, 2), (key400, 2), (key406, 2), (key488, 2), (key421, 2), (key489, 2), (key390, 2), (key411, 2), (key487, 2), (key435, 2), (key445, 2), (key453, 2), (key248, 2), (key263, 2), (key316, 2), (key661, 2), (key331, 2), (key662, 2), (key253, 2), (key321, 2), (key660, 2), (key385, 2), (key400, 2), (key406, 2), (key488, 2), (key421, 2), (key489, 2), (key248, 2), (key263, 2), (key316, 2), (key661, 2), (key331, 2), (key662, 2), (key236, 2), (key278, 2), (key302, 2), (key347, 2), (key656, 2), (key658, 2), (key241, 2), (key263, 2), (key307, 2), (key331, 2), (key400, 2), (key421, 2), (key321, 2), (key411, 2), (key445, 2), (key253, 2), (key390, 2), (key453, 2), (key241, 2), (key263, 2), (key307, 2), (key331, 2), (key400, 2), (key421, 2)]

def rawRow20301 : Integer.Sparse Key := [(key445, 2), (key435, 2), (key453, 2), (key400, 2), (key385, 2), (key488, 2), (key406, 2), (key489, 2), (key421, 2), (key390, 2), (key487, 2), (key411, 2), (key445, 2), (key435, 2), (key453, 2), (key263, 2), (key248, 2), (key661, 2), (key316, 2), (key662, 2), (key331, 2), (key253, 2), (key660, 2), (key321, 2), (key400, 2), (key385, 2), (key488, 2), (key406, 2), (key489, 2), (key421, 2), (key263, 2), (key248, 2), (key661, 2), (key316, 2), (key662, 2), (key331, 2), (key278, 2), (key236, 2), (key347, 2), (key302, 2), (key658, 2), (key656, 2), (key263, 2), (key241, 2), (key331, 2), (key307, 2), (key421, 2), (key400, 2), (key321, 2), (key445, 2), (key411, 2), (key253, 2), (key453, 2), (key390, 2), (key263, 2), (key241, 2), (key331, 2), (key307, 2), (key421, 2), (key400, 2)]

def rawRow20302 : Integer.Sparse Key := [(key435, 2), (key453, 2), (key445, 2), (key406, 2), (key421, 2), (key385, 2), (key489, 2), (key400, 2), (key488, 2), (key411, 2), (key390, 2), (key487, 2), (key435, 2), (key453, 2), (key445, 2), (key316, 2), (key331, 2), (key248, 2), (key662, 2), (key263, 2), (key661, 2), (key321, 2), (key253, 2), (key660, 2), (key406, 2), (key421, 2), (key385, 2), (key489, 2), (key400, 2), (key488, 2), (key316, 2), (key331, 2), (key248, 2), (key662, 2), (key263, 2), (key661, 2), (key302, 2), (key347, 2), (key236, 2), (key658, 2), (key278, 2), (key347, 2), (key307, 2), (key400, 2), (key241, 2), (key421, 2), (key263, 2), (key331, 2), (key411, 2), (key321, 2), (key445, 2), (key390, 2), (key253, 2), (key453, 2), (key307, 2), (key400, 2), (key241, 2), (key421, 2), (key263, 2), (key331, 2)]

def rawRow20303 : Integer.Sparse Key := [(key453, 2), (key435, 2), (key445, 2), (key421, 2), (key406, 2), (key489, 2), (key385, 2), (key488, 2), (key400, 2), (key411, 2), (key487, 2), (key390, 2), (key453, 2), (key435, 2), (key445, 2), (key331, 2), (key316, 2), (key662, 2), (key248, 2), (key661, 2), (key263, 2), (key321, 2), (key660, 2), (key253, 2), (key421, 2), (key406, 2), (key489, 2), (key385, 2), (key488, 2), (key400, 2), (key331, 2), (key316, 2), (key662, 2), (key248, 2), (key661, 2), (key263, 2), (key347, 2), (key302, 2), (key658, 2), (key236, 2), (key347, 2), (key278, 2), (key400, 2), (key307, 2), (key421, 2), (key241, 2), (key331, 2), (key263, 2), (key411, 2), (key445, 2), (key321, 2), (key390, 2), (key453, 2), (key253, 2), (key400, 2), (key307, 2), (key421, 2), (key241, 2), (key331, 2), (key263, 2)]

def rawRow20304 : Integer.Sparse Key := [(key445, 2), (key453, 2), (key435, 2), (key488, 2), (key489, 2), (key400, 2), (key421, 2), (key385, 2), (key406, 2), (key487, 2), (key390, 2), (key411, 2), (key445, 2), (key453, 2), (key435, 2), (key661, 2), (key662, 2), (key263, 2), (key331, 2), (key248, 2), (key316, 2), (key660, 2), (key253, 2), (key321, 2), (key488, 2), (key489, 2), (key400, 2), (key421, 2), (key385, 2), (key406, 2), (key661, 2), (key662, 2), (key263, 2), (key331, 2), (key248, 2), (key316, 2), (key656, 2), (key658, 2), (key278, 2), (key347, 2), (key236, 2), (key302, 2), (key331, 2), (key421, 2), (key263, 2), (key400, 2), (key241, 2), (key307, 2), (key445, 2), (key321, 2), (key411, 2), (key453, 2), (key253, 2), (key390, 2), (key331, 2), (key421, 2), (key263, 2), (key400, 2), (key241, 2), (key307, 2)]

def rawRow20305 : Integer.Sparse Key := [(key453, 2), (key445, 2), (key435, 2), (key489, 2), (key488, 2), (key421, 2), (key400, 2), (key406, 2), (key385, 2), (key487, 2), (key411, 2), (key390, 2), (key453, 2), (key445, 2), (key435, 2), (key662, 2), (key661, 2), (key331, 2), (key263, 2), (key316, 2), (key248, 2), (key660, 2), (key321, 2), (key253, 2), (key489, 2), (key488, 2), (key421, 2), (key400, 2), (key406, 2), (key385, 2), (key662, 2), (key661, 2), (key331, 2), (key263, 2), (key316, 2), (key248, 2), (key658, 2), (key656, 2), (key347, 2), (key278, 2), (key302, 2), (key236, 2), (key421, 2), (key331, 2), (key400, 2), (key263, 2), (key307, 2), (key241, 2), (key445, 2), (key411, 2), (key321, 2), (key453, 2), (key390, 2), (key253, 2), (key421, 2), (key331, 2), (key400, 2), (key263, 2), (key307, 2), (key241, 2)]

def rawRow20306 : Integer.Sparse Key := [(key487, 2), (key488, 2), (key489, 2), (key390, 2), (key400, 2), (key411, 2), (key445, 2), (key421, 2), (key453, 2), (key385, 2), (key406, 2), (key435, 2), (key660, 2), (key661, 2), (key662, 2), (key253, 2), (key263, 2), (key321, 2), (key445, 2), (key331, 2), (key453, 2), (key248, 2), (key316, 2), (key435, 2), (key655, 2), (key656, 2), (key657, 2), (key661, 2), (key658, 2), (key662, 2), (key277, 2), (key278, 2), (key346, 2), (key488, 2), (key347, 2), (key489, 2), (key241, 2), (key263, 2), (key307, 2), (key400, 2), (key331, 2), (key421, 2), (key236, 2), (key248, 2), (key302, 2), (key316, 2), (key385, 2), (key406, 2), (key331, 2), (key421, 2), (key453, 2), (key263, 2), (key400, 2), (key445, 2), (key241, 2), (key253, 2), (key307, 2), (key321, 2), (key390, 2), (key411, 2)]

def rawRow20307 : Integer.Sparse Key := [(key488, 2), (key487, 2), (key489, 2), (key400, 2), (key390, 2), (key445, 2), (key411, 2), (key453, 2), (key421, 2), (key385, 2), (key435, 2), (key406, 2), (key661, 2), (key660, 2), (key662, 2), (key263, 2), (key253, 2), (key445, 2), (key321, 2), (key453, 2), (key331, 2), (key248, 2), (key435, 2), (key316, 2), (key656, 2), (key655, 2), (key661, 2), (key657, 2), (key662, 2), (key658, 2), (key278, 2), (key277, 2), (key488, 2), (key346, 2), (key489, 2), (key347, 2), (key263, 2), (key241, 2), (key400, 2), (key307, 2), (key421, 2), (key331, 2), (key248, 2), (key236, 2), (key316, 2), (key302, 2), (key406, 2), (key385, 2), (key331, 2), (key453, 2), (key421, 2), (key263, 2), (key445, 2), (key400, 2), (key253, 2), (key241, 2), (key321, 2), (key307, 2), (key411, 2), (key390, 2)]

def rawRow20308 : Integer.Sparse Key := [(key487, 2), (key489, 2), (key488, 2), (key411, 2), (key421, 2), (key390, 2), (key453, 2), (key400, 2), (key445, 2), (key406, 2), (key385, 2), (key435, 2), (key660, 2), (key662, 2), (key661, 2), (key321, 2), (key331, 2), (key253, 2), (key453, 2), (key263, 2), (key445, 2), (key316, 2), (key248, 2), (key435, 2), (key657, 2), (key658, 2), (key655, 2), (key662, 2), (key656, 2), (key661, 2), (key346, 2), (key347, 2), (key277, 2), (key489, 2), (key278, 2), (key488, 2), (key307, 2), (key331, 2), (key241, 2), (key421, 2), (key263, 2), (key400, 2), (key302, 2), (key316, 2), (key236, 2), (key406, 2), (key248, 2), (key316, 2), (key421, 2), (key331, 2), (key453, 2), (key400, 2), (key263, 2), (key445, 2), (key307, 2), (key390, 2), (key241, 2), (key411, 2), (key253, 2), (key321, 2)]

def rawRow20309 : Integer.Sparse Key := [(key489, 2), (key487, 2), (key488, 2), (key421, 2), (key411, 2), (key453, 2), (key390, 2), (key445, 2), (key400, 2), (key406, 2), (key435, 2), (key385, 2), (key662, 2), (key660, 2), (key661, 2), (key331, 2), (key321, 2), (key453, 2), (key253, 2), (key445, 2), (key263, 2), (key316, 2), (key435, 2), (key248, 2), (key658, 2), (key657, 2), (key662, 2), (key655, 2), (key661, 2), (key656, 2), (key347, 2), (key346, 2), (key489, 2), (key277, 2), (key488, 2), (key278, 2), (key331, 2), (key307, 2), (key421, 2), (key241, 2), (key400, 2), (key263, 2), (key316, 2), (key302, 2), (key406, 2), (key236, 2), (key316, 2), (key248, 2), (key421, 2), (key453, 2), (key331, 2), (key400, 2), (key445, 2), (key263, 2), (key390, 2), (key307, 2), (key411, 2), (key241, 2), (key321, 2), (key253, 2)]

def rawRow20310 : Integer.Sparse Key := [(key488, 2), (key489, 2), (key487, 2), (key445, 2), (key453, 2), (key400, 2), (key421, 2), (key390, 2), (key411, 2), (key435, 2), (key385, 2), (key406, 2), (key661, 2), (key662, 2), (key660, 2), (key445, 2), (key453, 2), (key263, 2), (key331, 2), (key253, 2), (key321, 2), (key435, 2), (key248, 2), (key316, 2), (key661, 2), (key662, 2), (key656, 2), (key658, 2), (key655, 2), (key657, 2), (key488, 2), (key489, 2), (key278, 2), (key347, 2), (key277, 2), (key346, 2), (key400, 2), (key421, 2), (key263, 2), (key331, 2), (key241, 2), (key307, 2), (key385, 2), (key406, 2), (key248, 2), (key316, 2), (key236, 2), (key302, 2), (key453, 2), (key331, 2), (key421, 2), (key445, 2), (key263, 2), (key400, 2), (key321, 2), (key411, 2), (key253, 2), (key390, 2), (key241, 2), (key307, 2)]

def rawRow20311 : Integer.Sparse Key := [(key489, 2), (key488, 2), (key487, 2), (key453, 2), (key445, 2), (key421, 2), (key400, 2), (key411, 2), (key390, 2), (key435, 2), (key406, 2), (key385, 2), (key662, 2), (key661, 2), (key660, 2), (key453, 2), (key445, 2), (key331, 2), (key263, 2), (key321, 2), (key253, 2), (key435, 2), (key316, 2), (key248, 2), (key662, 2), (key661, 2), (key658, 2), (key656, 2), (key657, 2), (key655, 2), (key489, 2), (key488, 2), (key347, 2), (key278, 2), (key346, 2), (key277, 2), (key421, 2), (key400, 2), (key331, 2), (key263, 2), (key307, 2), (key241, 2), (key406, 2), (key385, 2), (key316, 2), (key248, 2), (key302, 2), (key236, 2), (key453, 2), (key421, 2), (key331, 2), (key445, 2), (key400, 2), (key263, 2), (key411, 2), (key321, 2), (key390, 2), (key253, 2), (key307, 2), (key241, 2)]

def rawRow20312 : Integer.Sparse Key := [(key655, 2), (key655, 2), (key656, 2), (key657, 2), (key657, 2), (key660, 2), (key660, 2), (key661, 2), (key661, 2), (key658, 2), (key662, 2), (key662, 2), (key277, 2), (key277, 2), (key278, 2), (key346, 2), (key346, 2), (key487, 2), (key487, 2), (key488, 2), (key488, 2), (key347, 2), (key489, 2), (key489, 2), (key241, 2), (key241, 2), (key253, 2), (key253, 2), (key263, 2), (key263, 2), (key307, 2), (key307, 2), (key390, 2), (key390, 2), (key400, 2), (key400, 2), (key321, 2), (key321, 2), (key411, 2), (key411, 2), (key445, 2), (key445, 2), (key331, 2), (key331, 2), (key421, 2), (key421, 2), (key453, 2), (key453, 2), (key236, 2), (key248, 2), (key248, 2), (key302, 2), (key316, 2), (key316, 2), (key385, 2), (key385, 2), (key406, 2), (key406, 2), (key435, 2), (key435, 2)]

def rawRow20313 : Integer.Sparse Key := [(key655, 2), (key656, 2), (key655, 2), (key660, 2), (key661, 2), (key657, 2), (key661, 2), (key657, 2), (key660, 2), (key662, 2), (key658, 2), (key662, 2), (key277, 2), (key278, 2), (key277, 2), (key487, 2), (key488, 2), (key346, 2), (key488, 2), (key346, 2), (key487, 2), (key489, 2), (key347, 2), (key489, 2), (key253, 2), (key263, 2), (key241, 2), (key263, 2), (key241, 2), (key253, 2), (key390, 2), (key400, 2), (key307, 2), (key400, 2), (key307, 2), (key390, 2), (key411, 2), (key445, 2), (key321, 2), (key445, 2), (key321, 2), (key411, 2), (key421, 2), (key453, 2), (key331, 2), (key453, 2), (key331, 2), (key421, 2), (key248, 2), (key236, 2), (key248, 2), (key316, 2), (key302, 2), (key316, 2), (key406, 2), (key435, 2), (key385, 2), (key435, 2), (key385, 2), (key406, 2)]

def rawRow20314 : Integer.Sparse Key := [(key656, 2), (key655, 2), (key655, 2), (key661, 2), (key660, 2), (key661, 2), (key657, 2), (key660, 2), (key657, 2), (key662, 2), (key662, 2), (key658, 2), (key278, 2), (key277, 2), (key277, 2), (key488, 2), (key487, 2), (key488, 2), (key346, 2), (key487, 2), (key346, 2), (key489, 2), (key489, 2), (key347, 2), (key263, 2), (key253, 2), (key263, 2), (key241, 2), (key253, 2), (key241, 2), (key400, 2), (key390, 2), (key400, 2), (key307, 2), (key390, 2), (key307, 2), (key445, 2), (key411, 2), (key445, 2), (key321, 2), (key411, 2), (key321, 2), (key453, 2), (key421, 2), (key453, 2), (key331, 2), (key421, 2), (key331, 2), (key248, 2), (key248, 2), (key236, 2), (key316, 2), (key316, 2), (key302, 2), (key435, 2), (key406, 2), (key435, 2), (key385, 2), (key406, 2), (key385, 2)]

def rawRow20315 : Integer.Sparse Key := [(key657, 2), (key657, 2), (key658, 2), (key655, 2), (key655, 2), (key660, 2), (key660, 2), (key662, 2), (key662, 2), (key656, 2), (key661, 2), (key661, 2), (key346, 2), (key346, 2), (key347, 2), (key277, 2), (key277, 2), (key487, 2), (key487, 2), (key489, 2), (key489, 2), (key278, 2), (key488, 2), (key488, 2), (key307, 2), (key307, 2), (key321, 2), (key321, 2), (key331, 2), (key331, 2), (key241, 2), (key241, 2), (key411, 2), (key411, 2), (key421, 2), (key421, 2), (key253, 2), (key253, 2), (key390, 2), (key390, 2), (key453, 2), (key453, 2), (key263, 2), (key263, 2), (key400, 2), (key400, 2), (key445, 2), (key445, 2), (key302, 2), (key316, 2), (key316, 2), (key236, 2), (key406, 2), (key406, 2), (key248, 2), (key248, 2), (key316, 2), (key316, 2), (key435, 2), (key435, 2)]

def rawRow20316 : Integer.Sparse Key := [(key657, 2), (key658, 2), (key657, 2), (key660, 2), (key662, 2), (key655, 2), (key662, 2), (key655, 2), (key660, 2), (key661, 2), (key656, 2), (key661, 2), (key346, 2), (key347, 2), (key346, 2), (key487, 2), (key489, 2), (key277, 2), (key489, 2), (key277, 2), (key487, 2), (key488, 2), (key278, 2), (key488, 2), (key321, 2), (key331, 2), (key307, 2), (key331, 2), (key307, 2), (key321, 2), (key411, 2), (key421, 2), (key241, 2), (key421, 2), (key241, 2), (key411, 2), (key390, 2), (key453, 2), (key253, 2), (key453, 2), (key253, 2), (key390, 2), (key400, 2), (key445, 2), (key263, 2), (key445, 2), (key263, 2), (key400, 2), (key316, 2), (key302, 2), (key316, 2), (key406, 2), (key236, 2), (key406, 2), (key316, 2), (key435, 2), (key248, 2), (key435, 2), (key248, 2), (key316, 2)]

def rawRow20317 : Integer.Sparse Key := [(key658, 2), (key657, 2), (key657, 2), (key662, 2), (key660, 2), (key662, 2), (key655, 2), (key660, 2), (key655, 2), (key661, 2), (key661, 2), (key656, 2), (key347, 2), (key346, 2), (key346, 2), (key489, 2), (key487, 2), (key489, 2), (key277, 2), (key487, 2), (key277, 2), (key488, 2), (key488, 2), (key278, 2), (key331, 2), (key321, 2), (key331, 2), (key307, 2), (key321, 2), (key307, 2), (key421, 2), (key411, 2), (key421, 2), (key241, 2), (key411, 2), (key241, 2), (key453, 2), (key390, 2), (key453, 2), (key253, 2), (key390, 2), (key253, 2), (key445, 2), (key400, 2), (key445, 2), (key263, 2), (key400, 2), (key263, 2), (key316, 2), (key316, 2), (key302, 2), (key406, 2), (key406, 2), (key236, 2), (key435, 2), (key316, 2), (key435, 2), (key248, 2), (key316, 2), (key248, 2)]

def rawRow20318 : Integer.Sparse Key := [(key660, 2), (key661, 2), (key662, 2), (key655, 2), (key656, 2), (key657, 2), (key661, 2), (key658, 2), (key662, 2), (key655, 2), (key657, 2), (key660, 2), (key487, 2), (key488, 2), (key489, 2), (key277, 2), (key278, 2), (key346, 2), (key488, 2), (key347, 2), (key489, 2), (key277, 2), (key346, 2), (key487, 2), (key390, 2), (key400, 2), (key411, 2), (key445, 2), (key421, 2), (key453, 2), (key253, 2), (key263, 2), (key321, 2), (key445, 2), (key331, 2), (key453, 2), (key241, 2), (key263, 2), (key307, 2), (key400, 2), (key331, 2), (key421, 2), (key241, 2), (key253, 2), (key307, 2), (key390, 2), (key321, 2), (key411, 2), (key385, 2), (key406, 2), (key435, 2), (key248, 2), (key316, 2), (key435, 2), (key236, 2), (key248, 2), (key302, 2), (key316, 2), (key385, 2), (key406, 2)]

def rawRow20319 : Integer.Sparse Key := [(key661, 2), (key660, 2), (key662, 2), (key656, 2), (key655, 2), (key661, 2), (key657, 2), (key662, 2), (key658, 2), (key655, 2), (key660, 2), (key657, 2), (key488, 2), (key487, 2), (key489, 2), (key278, 2), (key277, 2), (key488, 2), (key346, 2), (key489, 2), (key347, 2), (key277, 2), (key487, 2), (key346, 2), (key400, 2), (key390, 2), (key445, 2), (key411, 2), (key453, 2), (key421, 2), (key263, 2), (key253, 2), (key445, 2), (key321, 2), (key453, 2), (key331, 2), (key263, 2), (key241, 2), (key400, 2), (key307, 2), (key421, 2), (key331, 2), (key253, 2), (key241, 2), (key390, 2), (key307, 2), (key411, 2), (key321, 2), (key385, 2), (key435, 2), (key406, 2), (key248, 2), (key435, 2), (key316, 2), (key248, 2), (key236, 2), (key316, 2), (key302, 2), (key406, 2), (key385, 2)]

def rawRow20320 : Integer.Sparse Key := [(key660, 2), (key662, 2), (key661, 2), (key657, 2), (key658, 2), (key655, 2), (key662, 2), (key656, 2), (key661, 2), (key657, 2), (key655, 2), (key660, 2), (key487, 2), (key489, 2), (key488, 2), (key346, 2), (key347, 2), (key277, 2), (key489, 2), (key278, 2), (key488, 2), (key346, 2), (key277, 2), (key487, 2), (key411, 2), (key421, 2), (key390, 2), (key453, 2), (key400, 2), (key445, 2), (key321, 2), (key331, 2), (key253, 2), (key453, 2), (key263, 2), (key445, 2), (key307, 2), (key331, 2), (key241, 2), (key421, 2), (key263, 2), (key400, 2), (key307, 2), (key321, 2), (key241, 2), (key411, 2), (key253, 2), (key390, 2), (key406, 2), (key385, 2), (key435, 2), (key316, 2), (key248, 2), (key435, 2), (key302, 2), (key316, 2), (key236, 2), (key406, 2), (key248, 2), (key316, 2)]

def rawRow20321 : Integer.Sparse Key := [(key662, 2), (key660, 2), (key661, 2), (key658, 2), (key657, 2), (key662, 2), (key655, 2), (key661, 2), (key656, 2), (key657, 2), (key660, 2), (key655, 2), (key489, 2), (key487, 2), (key488, 2), (key347, 2), (key346, 2), (key489, 2), (key277, 2), (key488, 2), (key278, 2), (key346, 2), (key487, 2), (key277, 2), (key421, 2), (key411, 2), (key453, 2), (key390, 2), (key445, 2), (key400, 2), (key331, 2), (key321, 2), (key453, 2), (key253, 2), (key445, 2), (key263, 2), (key331, 2), (key307, 2), (key421, 2), (key241, 2), (key400, 2), (key263, 2), (key321, 2), (key307, 2), (key411, 2), (key241, 2), (key390, 2), (key253, 2), (key406, 2), (key435, 2), (key385, 2), (key316, 2), (key435, 2), (key248, 2), (key316, 2), (key302, 2), (key406, 2), (key236, 2), (key316, 2), (key248, 2)]

def rawRow20322 : Integer.Sparse Key := [(key661, 2), (key662, 2), (key660, 2), (key661, 2), (key662, 2), (key656, 2), (key658, 2), (key655, 2), (key657, 2), (key660, 2), (key655, 2), (key657, 2), (key488, 2), (key489, 2), (key487, 2), (key488, 2), (key489, 2), (key278, 2), (key347, 2), (key277, 2), (key346, 2), (key487, 2), (key277, 2), (key346, 2), (key445, 2), (key453, 2), (key400, 2), (key421, 2), (key390, 2), (key411, 2), (key445, 2), (key453, 2), (key263, 2), (key331, 2), (key253, 2), (key321, 2), (key400, 2), (key421, 2), (key263, 2), (key331, 2), (key241, 2), (key307, 2), (key390, 2), (key411, 2), (key253, 2), (key321, 2), (key241, 2), (key307, 2), (key435, 2), (key385, 2), (key406, 2), (key435, 2), (key248, 2), (key316, 2), (key385, 2), (key406, 2), (key248, 2), (key316, 2), (key236, 2), (key302, 2)]

def rawRow20323 : Integer.Sparse Key := [(key662, 2), (key661, 2), (key660, 2), (key662, 2), (key661, 2), (key658, 2), (key656, 2), (key657, 2), (key655, 2), (key660, 2), (key657, 2), (key655, 2), (key489, 2), (key488, 2), (key487, 2), (key489, 2), (key488, 2), (key347, 2), (key278, 2), (key346, 2), (key277, 2), (key487, 2), (key346, 2), (key277, 2), (key453, 2), (key445, 2), (key421, 2), (key400, 2), (key411, 2), (key390, 2), (key453, 2), (key445, 2), (key331, 2), (key263, 2), (key321, 2), (key253, 2), (key421, 2), (key400, 2), (key331, 2), (key263, 2), (key307, 2), (key241, 2), (key411, 2), (key390, 2), (key321, 2), (key253, 2), (key307, 2), (key241, 2), (key435, 2), (key406, 2), (key385, 2), (key435, 2), (key316, 2), (key248, 2), (key406, 2), (key385, 2), (key316, 2), (key248, 2), (key302, 2), (key236, 2)]

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

def rawRow190 : Integer.Sparse Key := [(key2798, -2), (key2786, 1), (key2794, 1), (key2920, 2), (key2809, -1), (key2860, -1), (key2923, -1), (key2927, -1), (key2835, 1), (key2885, 1), (key2644, 2), (key2632, -1), (key2640, -1), (key3023, -2), (key2706, 1), (key2860, 1), (key3026, 1), (key3030, 1), (key2732, -1), (key2885, -1), (key2660, -2), (key2616, 1), (key2640, 1), (key2747, 2), (key2667, -1), (key2735, -1), (key2960, -1), (key3000, -1), (key2943, 1), (key2998, 1), (key2641, 1), (key2653, 1), (key2618, -1), (key2648, -1), (key2728, -1), (key2747, -1), (key2673, 1), (key2737, 1), (key2831, 1), (key2904, 1), (key2795, -1), (key2897, -1)]

def rawRow191 : Integer.Sparse Key := [(key2798, -2), (key2794, 1), (key2786, 1), (key2920, 2), (key2860, -1), (key2809, -1), (key2927, -1), (key2923, -1), (key2885, 1), (key2835, 1), (key2644, 2), (key2640, -1), (key2632, -1), (key3023, -2), (key2860, 1), (key2706, 1), (key3030, 1), (key3026, 1), (key2885, -1), (key2732, -1), (key2660, -2), (key2640, 1), (key2616, 1), (key2747, 2), (key2735, -1), (key2667, -1), (key3000, -1), (key2960, -1), (key2998, 1), (key2943, 1), (key2653, 1), (key2641, 1), (key2648, -1), (key2618, -1), (key2747, -1), (key2728, -1), (key2737, 1), (key2673, 1), (key2904, 1), (key2831, 1), (key2897, -1), (key2795, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow192 : Integer.Sparse Key := [(key2809, -2), (key2829, 1), (key2835, 1), (key2786, 2), (key2870, -1), (key2923, -1), (key2794, -1), (key2798, -1), (key2860, 1), (key2920, 1), (key2706, 2), (key2726, -1), (key2732, -1), (key2632, -2), (key2870, 1), (key3026, 1), (key2640, 1), (key2644, 1), (key2860, -1), (key3023, -1), (key2671, -2), (key2726, 1), (key2758, 1), (key2612, 2), (key2948, -1), (key2960, -1), (key2646, -1), (key2653, -1), (key2735, 1), (key2747, 1), (key2667, 1), (key2673, 1), (key2782, -1), (key2795, -1), (key2612, -1), (key2618, -1), (key2805, 1), (key2831, 1), (key2628, 1), (key2641, 1), (key2702, -1), (key2728, -1)]

def rawRow193 : Integer.Sparse Key := [(key2809, -2), (key2835, 1), (key2829, 1), (key2786, 2), (key2923, -1), (key2870, -1), (key2798, -1), (key2794, -1), (key2920, 1), (key2860, 1), (key2706, 2), (key2732, -1), (key2726, -1), (key2632, -2), (key3026, 1), (key2870, 1), (key2644, 1), (key2640, 1), (key3023, -1), (key2860, -1), (key2671, -2), (key2758, 1), (key2726, 1), (key2616, 2), (key2960, -1), (key2948, -1), (key2653, -1), (key2646, -1), (key2747, 1), (key2735, 1), (key2673, 1), (key2667, 1), (key2795, -1), (key2782, -1), (key2618, -1), (key2612, -1), (key2831, 1), (key2805, 1), (key2641, 1), (key2628, 1), (key2728, -1), (key2702, -1)]

def rawRow194 : Integer.Sparse Key := [(key2835, -2), (key2809, 1), (key2829, 1), (key2923, 2), (key2786, -1), (key2870, -1), (key2920, -1), (key2927, -1), (key2798, 1), (key2885, 1), (key2732, 2), (key2706, -1), (key2726, -1), (key3026, -2), (key2632, 1), (key2870, 1), (key3023, 1), (key3030, 1), (key2644, -1), (key2885, -1), (key2758, -2), (key2671, 1), (key2726, 1), (key3017, 2), (key2616, -1), (key2829, -1), (key2747, -1), (key3000, -1), (key2653, 1), (key2998, 1), (key2795, 1), (key2943, 1), (key2673, -1), (key2938, -1), (key2831, -1), (key2960, -1), (key2618, 1), (key2950, 1), (key2728, 1), (key2983, 1), (key2641, -1), (key2976, -1)]

def rawRow195 : Integer.Sparse Key := [(key2835, -2), (key2829, 1), (key2809, 1), (key2923, 2), (key2870, -1), (key2786, -1), (key2927, -1), (key2920, -1), (key2885, 1), (key2798, 1), (key2732, 2), (key2726, -1), (key2706, -1), (key3026, -2), (key2870, 1), (key2632, 1), (key3030, 1), (key3023, 1), (key2885, -1), (key2644, -1), (key2758, -2), (key2726, 1), (key2671, 1), (key3017, 2), (key2829, -1), (key2616, -1), (key3000, -1), (key2747, -1), (key2998, 1), (key2653, 1), (key2943, 1), (key2795, 1), (key2938, -1), (key2673, -1), (key2960, -1), (key2831, -1), (key2950, 1), (key2618, 1), (key2983, 1), (key2728, 1), (key2976, -1), (key2641, -1)]

def rawRow196 : Integer.Sparse Key := [(key2920, -2), (key2923, 1), (key2927, 1), (key2798, 2), (key2835, -1), (key2885, -1), (key2786, -1), (key2794, -1), (key2809, 1), (key2860, 1), (key3023, 2), (key3026, -1), (key3030, -1), (key2644, -2), (key2732, 1), (key2885, 1), (key2632, 1), (key2640, 1), (key2706, -1), (key2860, -1), (key3010, -2), (key3017, 1), (key3030, 1), (key2660, 2), (key2758, -1), (key2927, -1), (key2616, -1), (key2640, -1), (key2671, 1), (key2794, 1), (key2728, 1), (key2747, 1), (key2831, -1), (key2904, -1), (key2641, -1), (key2653, -1), (key2795, 1), (key2897, 1), (key2618, 1), (key2648, 1), (key2673, -1), (key2737, -1)]

def rawRow197 : Integer.Sparse Key := [(key2920, -2), (key2927, 1), (key2923, 1), (key2798, 2), (key2885, -1), (key2835, -1), (key2794, -1), (key2786, -1), (key2860, 1), (key2809, 1), (key3023, 2), (key3030, -1), (key3026, -1), (key2644, -2), (key2885, 1), (key2732, 1), (key2640, 1), (key2632, 1), (key2860, -1), (key2706, -1), (key3010, -2), (key3030, 1), (key3017, 1), (key2660, 2), (key2927, -1), (key2758, -1), (key2640, -1), (key2616, -1), (key2794, 1), (key2671, 1), (key2747, 1), (key2728, 1), (key2904, -1), (key2831, -1), (key2653, -1), (key2641, -1), (key2897, 1), (key2795, 1), (key2648, 1), (key2618, 1), (key2737, -1), (key2673, -1)]

def rawRow198 : Integer.Sparse Key := [(key2923, -2), (key2920, 1), (key2927, 1), (key2835, 2), (key2798, -1), (key2885, -1), (key2809, -1), (key2829, -1), (key2786, 1), (key2870, 1), (key3026, 2), (key3023, -1), (key3030, -1), (key2732, -2), (key2644, 1), (key2885, 1), (key2706, 1), (key2726, 1), (key2632, -1), (key2870, -1), (key3017, -2), (key3010, 1), (key3030, 1), (key2758, 2), (key2660, -1), (key2927, -1), (key2671, -1), (key2726, -1), (key2616, 1), (key2829, 1), (key2831, 1), (key2960, 1), (key2728, -1), (key2983, -1), (key2795, -1), (key2943, -1), (key2641, 1), (key2976, 1), (key2673, 1), (key2938, 1), (key2618, -1), (key2950, -1)]

def rawRow199 : Integer.Sparse Key := [(key2923, -2), (key2927, 1), (key2920, 1), (key2835, 2), (key2885, -1), (key2798, -1), (key2829, -1), (key2809, -1), (key2870, 1), (key2786, 1), (key3026, 2), (key3030, -1), (key3023, -1), (key2732, -2), (key2885, 1), (key2644, 1), (key2726, 1), (key2706, 1), (key2870, -1), (key2632, -1), (key3017, -2), (key3030, 1), (key3010, 1), (key2758, 2), (key2927, -1), (key2660, -1), (key2726, -1), (key2671, -1), (key2829, 1), (key2616, 1), (key2960, 1), (key2831, 1), (key2983, -1), (key2728, -1), (key2943, -1), (key2795, -1), (key2976, 1), (key2641, 1), (key2938, 1), (key2673, 1), (key2950, -1), (key2618, -1)]

def rawRow200 : Integer.Sparse Key := [(key3008, -2), (key3010, 1), (key3010, 1), (key3012, 2), (key3023, -1), (key3023, -1), (key3017, -1), (key3017, -1), (key3026, 1), (key3026, 1), (key2658, 2), (key2660, -1), (key2660, -1), (key2753, -2), (key2920, 1), (key2920, 1), (key2758, 1), (key2758, 1), (key2923, -1), (key2923, -1), (key2621, -2), (key2644, 1), (key2644, 1), (key2676, 2), (key2798, -1), (key2798, -1), (key2732, -1), (key2732, -1), (key2835, 1), (key2835, 1), (key2616, 1), (key2616, 1), (key2632, -1), (key2632, -1), (key2671, -1), (key2671, -1), (key2786, 1), (key2786, 1), (key2706, 1), (key2706, 1), (key2809, -1), (key2809, -1)]

def rawRow201 : Integer.Sparse Key := [(key3010, -2), (key3008, 1), (key3010, 1), (key3023, 2), (key3012, -1), (key3023, -1), (key3026, -1), (key3030, -1), (key3017, 1), (key3030, 1), (key2660, 2), (key2658, -1), (key2660, -1), (key2920, -2), (key2753, 1), (key2920, 1), (key2923, 1), (key2927, 1), (key2758, -1), (key2927, -1), (key2644, -2), (key2621, 1), (key2644, 1), (key2798, 2), (key2676, -1), (key2798, -1), (key2835, -1), (key2885, -1), (key2732, 1), (key2885, 1), (key2632, 1), (key2640, 1), (key2616, -1), (key2640, -1), (key2786, -1), (key2794, -1), (key2671, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2706, -1), (key2860, -1)]

def rawRow202 : Integer.Sparse Key := [(key3010, -2), (key3010, 1), (key3008, 1), (key3023, 2), (key3023, -1), (key3012, -1), (key3030, -1), (key3026, -1), (key3030, 1), (key3017, 1), (key2660, 2), (key2660, -1), (key2658, -1), (key2920, -2), (key2920, 1), (key2753, 1), (key2927, 1), (key2923, 1), (key2927, -1), (key2758, -1), (key2644, -2), (key2644, 1), (key2621, 1), (key2798, 2), (key2798, -1), (key2676, -1), (key2885, -1), (key2835, -1), (key2885, 1), (key2732, 1), (key2640, 1), (key2632, 1), (key2640, -1), (key2616, -1), (key2794, -1), (key2786, -1), (key2794, 1), (key2671, 1), (key2860, 1), (key2809, 1), (key2860, -1), (key2706, -1)]

def rawRow203 : Integer.Sparse Key := [(key3012, -2), (key3017, 1), (key3017, 1), (key3008, 2), (key3026, -1), (key3026, -1), (key3010, -1), (key3010, -1), (key3023, 1), (key3023, 1), (key2753, 2), (key2758, -1), (key2758, -1), (key2658, -2), (key2923, 1), (key2923, 1), (key2660, 1), (key2660, 1), (key2920, -1), (key2920, -1), (key2676, -2), (key2732, 1), (key2732, 1), (key2621, 2), (key2835, -1), (key2835, -1), (key2644, -1), (key2644, -1), (key2798, 1), (key2798, 1), (key2671, 1), (key2671, 1), (key2706, -1), (key2706, -1), (key2616, -1), (key2616, -1), (key2809, 1), (key2809, 1), (key2632, 1), (key2632, 1), (key2786, -1), (key2786, -1)]

def rawRow204 : Integer.Sparse Key := [(key3017, -2), (key3012, 1), (key3017, 1), (key3026, 2), (key3008, -1), (key3026, -1), (key3023, -1), (key3030, -1), (key3010, 1), (key3030, 1), (key2758, 2), (key2753, -1), (key2758, -1), (key2923, -2), (key2658, 1), (key2923, 1), (key2920, 1), (key2927, 1), (key2660, -1), (key2927, -1), (key2732, -2), (key2676, 1), (key2732, 1), (key2835, 2), (key2621, -1), (key2835, -1), (key2798, -1), (key2885, -1), (key2644, 1), (key2885, 1), (key2706, 1), (key2726, 1), (key2671, -1), (key2726, -1), (key2809, -1), (key2829, -1), (key2616, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2632, -1), (key2870, -1)]

def rawRow205 : Integer.Sparse Key := [(key3017, -2), (key3017, 1), (key3012, 1), (key3026, 2), (key3026, -1), (key3008, -1), (key3030, -1), (key3023, -1), (key3030, 1), (key3010, 1), (key2758, 2), (key2758, -1), (key2753, -1), (key2923, -2), (key2923, 1), (key2658, 1), (key2927, 1), (key2920, 1), (key2927, -1), (key2660, -1), (key2732, -2), (key2732, 1), (key2676, 1), (key2835, 2), (key2835, -1), (key2621, -1), (key2885, -1), (key2798, -1), (key2885, 1), (key2644, 1), (key2726, 1), (key2706, 1), (key2726, -1), (key2671, -1), (key2829, -1), (key2809, -1), (key2829, 1), (key2616, 1), (key2870, 1), (key2786, 1), (key2870, -1), (key2632, -1)]

def rawRow206 : Integer.Sparse Key := [(key3023, -2), (key3026, 1), (key3030, 1), (key3010, 2), (key3017, -1), (key3030, -1), (key3008, -1), (key3010, -1), (key3012, 1), (key3023, 1), (key2920, 2), (key2923, -1), (key2927, -1), (key2660, -2), (key2758, 1), (key2927, 1), (key2658, 1), (key2660, 1), (key2753, -1), (key2920, -1), (key2798, -2), (key2835, 1), (key2885, 1), (key2644, 2), (key2732, -1), (key2885, -1), (key2621, -1), (key2644, -1), (key2676, 1), (key2798, 1), (key2786, 1), (key2794, 1), (key2809, -1), (key2860, -1), (key2632, -1), (key2640, -1), (key2706, 1), (key2860, 1), (key2616, 1), (key2640, 1), (key2671, -1), (key2794, -1)]

def rawRow207 : Integer.Sparse Key := [(key3023, -2), (key3030, 1), (key3026, 1), (key3010, 2), (key3030, -1), (key3017, -1), (key3010, -1), (key3008, -1), (key3023, 1), (key3012, 1), (key2920, 2), (key2927, -1), (key2923, -1), (key2660, -2), (key2927, 1), (key2758, 1), (key2660, 1), (key2658, 1), (key2920, -1), (key2753, -1), (key2798, -2), (key2885, 1), (key2835, 1), (key2644, 2), (key2885, -1), (key2732, -1), (key2644, -1), (key2621, -1), (key2798, 1), (key2676, 1), (key2794, 1), (key2786, 1), (key2860, -1), (key2809, -1), (key2640, -1), (key2632, -1), (key2860, 1), (key2706, 1), (key2640, 1), (key2616, 1), (key2794, -1), (key2671, -1)]

def rawRow208 : Integer.Sparse Key := [(key3026, -2), (key3023, 1), (key3030, 1), (key3017, 2), (key3010, -1), (key3030, -1), (key3012, -1), (key3017, -1), (key3008, 1), (key3026, 1), (key2923, 2), (key2920, -1), (key2927, -1), (key2758, -2), (key2660, 1), (key2927, 1), (key2753, 1), (key2758, 1), (key2658, -1), (key2923, -1), (key2835, -2), (key2798, 1), (key2885, 1), (key2732, 2), (key2644, -1), (key2885, -1), (key2676, -1), (key2732, -1), (key2621, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2786, -1), (key2870, -1), (key2706, -1), (key2726, -1), (key2632, 1), (key2870, 1), (key2671, 1), (key2726, 1), (key2616, -1), (key2829, -1)]

def rawRow209 : Integer.Sparse Key := [(key3026, -2), (key3030, 1), (key3023, 1), (key3017, 2), (key3030, -1), (key3010, -1), (key3017, -1), (key3012, -1), (key3026, 1), (key3008, 1), (key2923, 2), (key2927, -1), (key2920, -1), (key2758, -2), (key2927, 1), (key2660, 1), (key2758, 1), (key2753, 1), (key2923, -1), (key2658, -1), (key2835, -2), (key2885, 1), (key2798, 1), (key2732, 2), (key2885, -1), (key2644, -1), (key2732, -1), (key2676, -1), (key2835, 1), (key2621, 1), (key2829, 1), (key2809, 1), (key2870, -1), (key2786, -1), (key2726, -1), (key2706, -1), (key2870, 1), (key2632, 1), (key2726, 1), (key2671, 1), (key2829, -1), (key2616, -1)]

def rawRow210 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2614, 2), (key2624, 1), (key2630, 1), (key2630, -1), (key2638, -1), (key2657, -2), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2669, -2), (key2698, -1), (key2704, -1), (key2704, 1), (key2724, 1), (key2752, 2), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2784, 1), (key2792, 1), (key2801, 1), (key2807, 1), (key2807, -1), (key2827, -1), (key2918, -1), (key2919, -1), (key2918, 1), (key2922, 1), (key3007, 2), (key3007, -1), (key3009, -1), (key3011, -2), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3021, -1), (key3025, -1)]

def rawRow211 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2614, 2), (key2630, 1), (key2624, 1), (key2638, -1), (key2630, -1), (key2657, -2), (key2659, 1), (key2657, 1), (key2669, 1), (key2663, 1), (key2669, -2), (key2704, -1), (key2698, -1), (key2724, 1), (key2704, 1), (key2752, 2), (key2757, -1), (key2752, -1), (key2784, -1), (key2778, -1), (key2792, 1), (key2784, 1), (key2807, 1), (key2801, 1), (key2827, -1), (key2807, -1), (key2919, -1), (key2918, -1), (key2922, 1), (key2918, 1), (key3007, 2), (key3009, -1), (key3007, -1), (key3011, -2), (key3016, 1), (key3011, 1), (key3022, 1), (key3021, 1), (key3025, -1), (key3021, -1)]

def rawRow212 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2608, 2), (key2638, 1), (key2638, 1), (key2624, -1), (key2624, -1), (key2659, -2), (key2657, 1), (key2657, 1), (key2669, 1), (key2669, 1), (key2663, -2), (key2724, -1), (key2724, -1), (key2698, 1), (key2698, 1), (key2757, 2), (key2752, -1), (key2752, -1), (key2792, -1), (key2792, -1), (key2778, 1), (key2778, 1), (key2827, 1), (key2827, 1), (key2801, -1), (key2801, -1), (key2922, -1), (key2922, -1), (key2919, 1), (key2919, 1), (key3009, 2), (key3007, -1), (key3007, -1), (key3016, -2), (key3011, 1), (key3011, 1), (key3025, 1), (key3025, 1), (key3022, -1), (key3022, -1)]

def rawRow213 : Integer.Sparse Key := [(key2624, -1), (key2630, -1), (key2638, 2), (key2608, 1), (key2614, 1), (key2657, -1), (key2659, -1), (key2614, -2), (key2630, 1), (key2638, 1), (key2698, 1), (key2704, 1), (key2752, -2), (key2663, -1), (key2669, -1), (key2752, 1), (key2757, 1), (key2669, 2), (key2704, -1), (key2724, -1), (key2801, -1), (key2807, -1), (key2918, 1), (key2919, 1), (key2778, 1), (key2784, 1), (key2918, -1), (key2922, -1), (key2784, -1), (key2792, -1), (key2807, 1), (key2827, 1), (key3011, 2), (key3021, -1), (key3022, -1), (key3007, -2), (key3021, 1), (key3025, 1), (key3007, 1), (key3009, 1), (key3011, -1), (key3016, -1)]

def rawRow214 : Integer.Sparse Key := [(key2630, -1), (key2624, -1), (key2638, 2), (key2614, 1), (key2608, 1), (key2659, -1), (key2657, -1), (key2614, -2), (key2638, 1), (key2630, 1), (key2704, 1), (key2698, 1), (key2752, -2), (key2669, -1), (key2663, -1), (key2757, 1), (key2752, 1), (key2669, 2), (key2724, -1), (key2704, -1), (key2807, -1), (key2801, -1), (key2919, 1), (key2918, 1), (key2784, 1), (key2778, 1), (key2922, -1), (key2918, -1), (key2792, -1), (key2784, -1), (key2827, 1), (key2807, 1), (key3011, 2), (key3022, -1), (key3021, -1), (key3007, -2), (key3025, 1), (key3021, 1), (key3009, 1), (key3007, 1), (key3016, -1), (key3011, -1)]

def rawRow215 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2624, 2), (key2657, 1), (key2659, 1), (key2608, -1), (key2624, -1), (key2638, -2), (key2614, 1), (key2630, 1), (key2704, 1), (key2752, 1), (key2698, -2), (key2724, -1), (key2757, -1), (key2663, 1), (key2698, 1), (key2724, 2), (key2669, -1), (key2704, -1), (key2858, -1), (key2919, -1), (key2801, 1), (key2851, 1), (key2868, 1), (key2922, 1), (key2778, -1), (key2851, -1), (key2827, -1), (key2868, -1), (key2792, 1), (key2858, 1), (key3022, 2), (key3011, -1), (key3021, -1), (key3025, -2), (key3007, 1), (key3021, 1), (key3016, 1), (key3025, 1), (key3009, -1), (key3022, -1)]

def rawRow216 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2624, 2), (key2659, 1), (key2657, 1), (key2624, -1), (key2608, -1), (key2638, -2), (key2630, 1), (key2614, 1), (key2752, 1), (key2704, 1), (key2698, -2), (key2757, -1), (key2724, -1), (key2698, 1), (key2663, 1), (key2724, 2), (key2704, -1), (key2669, -1), (key2919, -1), (key2858, -1), (key2851, 1), (key2801, 1), (key2922, 1), (key2868, 1), (key2851, -1), (key2778, -1), (key2868, -1), (key2827, -1), (key2858, 1), (key2792, 1), (key3022, 2), (key3021, -1), (key3011, -1), (key3025, -2), (key3021, 1), (key3007, 1), (key3025, 1), (key3016, 1), (key3022, -1), (key3009, -1)]

def rawRow217 : Integer.Sparse Key := [(key2657, -1), (key2657, -1), (key2659, 2), (key2614, 1), (key2614, 1), (key2638, -1), (key2638, -1), (key2608, -2), (key2624, 1), (key2624, 1), (key2724, 1), (key2724, 1), (key2757, -2), (key2669, -1), (key2669, -1), (key2752, 1), (key2752, 1), (key2663, 2), (key2698, -1), (key2698, -1), (key2827, -1), (key2827, -1), (key2922, 1), (key2922, 1), (key2792, 1), (key2792, 1), (key2919, -1), (key2919, -1), (key2778, -1), (key2778, -1), (key2801, 1), (key2801, 1), (key3016, 2), (key3025, -1), (key3025, -1), (key3009, -2), (key3022, 1), (key3022, 1), (key3007, 1), (key3007, 1), (key3011, -1), (key3011, -1)]

def rawRow218 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2657, 2), (key2630, 1), (key2638, 1), (key2614, -1), (key2630, -1), (key2624, -2), (key2608, 1), (key2624, 1), (key2724, 1), (key2757, 1), (key2724, -2), (key2704, -1), (key2752, -1), (key2669, 1), (key2704, 1), (key2698, 2), (key2663, -1), (key2698, -1), (key2868, -1), (key2922, -1), (key2827, 1), (key2868, 1), (key2858, 1), (key2919, 1), (key2792, -1), (key2858, -1), (key2801, -1), (key2851, -1), (key2778, 1), (key2851, 1), (key3025, 2), (key3016, -1), (key3025, -1), (key3022, -2), (key3009, 1), (key3022, 1), (key3011, 1), (key3021, 1), (key3007, -1), (key3021, -1)]

def rawRow219 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2657, 2), (key2638, 1), (key2630, 1), (key2630, -1), (key2614, -1), (key2624, -2), (key2624, 1), (key2608, 1), (key2757, 1), (key2724, 1), (key2724, -2), (key2752, -1), (key2704, -1), (key2704, 1), (key2669, 1), (key2698, 2), (key2698, -1), (key2663, -1), (key2922, -1), (key2868, -1), (key2868, 1), (key2827, 1), (key2919, 1), (key2858, 1), (key2858, -1), (key2792, -1), (key2851, -1), (key2801, -1), (key2851, 1), (key2778, 1), (key3025, 2), (key3025, -1), (key3016, -1), (key3022, -2), (key3022, 1), (key3009, 1), (key3021, 1), (key3011, 1), (key3021, -1), (key3007, -1)]

def rawRow220 : Integer.Sparse Key := [(key2663, -1), (key2669, -1), (key2669, 2), (key2698, 1), (key2704, 1), (key2704, -1), (key2752, -1), (key2724, -2), (key2724, 1), (key2757, 1), (key2608, 1), (key2614, 1), (key2614, -2), (key2801, -1), (key2807, -1), (key2807, 1), (key2827, 1), (key3011, 2), (key3011, -1), (key3016, -1), (key2624, -1), (key2630, -1), (key2630, 1), (key2638, 1), (key2698, 1), (key2704, 1), (key2704, -1), (key2724, -1), (key3021, -1), (key3022, -1), (key3021, 1), (key3025, 1), (key2657, 2), (key2657, -1), (key2659, -1), (key2752, -2), (key2752, 1), (key2757, 1), (key2918, 1), (key2919, 1), (key2918, -1), (key2922, -1)]

def rawRow221 : Integer.Sparse Key := [(key2669, -1), (key2663, -1), (key2669, 2), (key2704, 1), (key2698, 1), (key2752, -1), (key2704, -1), (key2724, -2), (key2757, 1), (key2724, 1), (key2614, 1), (key2608, 1), (key2614, -2), (key2807, -1), (key2801, -1), (key2827, 1), (key2807, 1), (key3011, 2), (key3016, -1), (key3011, -1), (key2630, -1), (key2624, -1), (key2638, 1), (key2630, 1), (key2704, 1), (key2698, 1), (key2724, -1), (key2704, -1), (key3022, -1), (key3021, -1), (key3025, 1), (key3021, 1), (key2657, 2), (key2659, -1), (key2657, -1), (key2752, -2), (key2757, 1), (key2752, 1), (key2919, 1), (key2918, 1), (key2922, -1), (key2918, -1)]

def rawRow222 : Integer.Sparse Key := [(key2669, -1), (key2669, -1), (key2663, 2), (key2752, 1), (key2752, 1), (key2698, -1), (key2698, -1), (key2757, -2), (key2724, 1), (key2724, 1), (key2614, 1), (key2614, 1), (key2608, -2), (key2827, -1), (key2827, -1), (key2801, 1), (key2801, 1), (key3016, 2), (key3011, -1), (key3011, -1), (key2638, -1), (key2638, -1), (key2624, 1), (key2624, 1), (key2724, 1), (key2724, 1), (key2698, -1), (key2698, -1), (key3025, -1), (key3025, -1), (key3022, 1), (key3022, 1), (key2659, 2), (key2657, -1), (key2657, -1), (key2757, -2), (key2752, 1), (key2752, 1), (key2922, 1), (key2922, 1), (key2919, -1), (key2919, -1)]

def rawRow223 : Integer.Sparse Key := [(key2698, -1), (key2704, -1), (key2724, 2), (key2663, 1), (key2669, 1), (key2724, -1), (key2757, -1), (key2669, -2), (key2704, 1), (key2752, 1), (key2801, 1), (key2807, 1), (key2827, -2), (key2608, -1), (key2614, -1), (key3011, 1), (key3016, 1), (key2614, 2), (key2807, -1), (key2827, -1), (key2698, -1), (key2704, -1), (key3021, 1), (key3022, 1), (key2624, 1), (key2630, 1), (key3021, -1), (key3025, -1), (key2630, -1), (key2638, -1), (key2704, 1), (key2724, 1), (key2752, 2), (key2918, -1), (key2919, -1), (key2657, -2), (key2918, 1), (key2922, 1), (key2657, 1), (key2659, 1), (key2752, -1), (key2757, -1)]

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

def rawRow1893 : Integer.Sparse Key := [(key2380, -2), (key2380, -2), (key2380, -2), (key2374, 1), (key2374, 1), (key2374, 1), (key2374, 1), (key2374, 1), (key2374, 1), (key2505, 2), (key2505, 2), (key2505, 2), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2553, -1), (key2553, -1), (key2553, -1), (key2553, -1), (key2553, -1), (key2553, -1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1)]

def rawRow1894 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2917, -2), (key2878, 1), (key2884, 1), (key2878, 1), (key2926, 1), (key2884, 1), (key2926, 1), (key2374, 2), (key2374, 2), (key2391, 2), (key2535, -1), (key2542, -1), (key2535, -1), (key2553, -1), (key2542, -1), (key2553, -1), (key2374, -1), (key2380, -1), (key2374, -1), (key2391, -1), (key2380, -1), (key2391, -1), (key2468, 1), (key2481, 1), (key2468, 1), (key2505, 1), (key2481, 1), (key2505, 1)]

def rawRow1895 : Integer.Sparse Key := [(key2847, -2), (key2917, -2), (key2847, -2), (key2884, 1), (key2878, 1), (key2926, 1), (key2878, 1), (key2926, 1), (key2884, 1), (key2374, 2), (key2391, 2), (key2374, 2), (key2542, -1), (key2535, -1), (key2553, -1), (key2535, -1), (key2553, -1), (key2542, -1), (key2380, -1), (key2374, -1), (key2391, -1), (key2374, -1), (key2391, -1), (key2380, -1), (key2481, 1), (key2468, 1), (key2505, 1), (key2468, 1), (key2505, 1), (key2481, 1)]

def rawRow1896 : Integer.Sparse Key := [(key2917, -2), (key2847, -2), (key2847, -2), (key2926, 1), (key2926, 1), (key2884, 1), (key2884, 1), (key2878, 1), (key2878, 1), (key2391, 2), (key2374, 2), (key2374, 2), (key2553, -1), (key2553, -1), (key2542, -1), (key2542, -1), (key2535, -1), (key2535, -1), (key2391, -1), (key2391, -1), (key2380, -1), (key2380, -1), (key2374, -1), (key2374, -1), (key2505, 1), (key2505, 1), (key2481, 1), (key2481, 1), (key2468, 1), (key2468, 1)]

def rawRow1897 : Integer.Sparse Key := [(key2775, -2), (key2884, -2), (key2884, -2), (key2770, 1), (key2770, 1), (key2847, 1), (key2847, 1), (key2878, 1), (key2878, 1), (key3006, 2), (key3029, 2), (key3029, 2), (key2591, -1), (key2591, -1), (key2770, -1), (key2770, -1), (key2878, -1), (key2878, -1), (key2439, -1), (key2439, -1), (key2505, -1), (key2505, -1), (key2553, -1), (key2553, -1), (key2380, 1), (key2380, 1), (key2408, 1), (key2408, 1), (key2537, 1), (key2537, 1)]

def rawRow1898 : Integer.Sparse Key := [(key2884, -2), (key2775, -2), (key2884, -2), (key2847, 1), (key2878, 1), (key2770, 1), (key2878, 1), (key2770, 1), (key2847, 1), (key3029, 2), (key3006, 2), (key3029, 2), (key2770, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2505, -1), (key2553, -1), (key2439, -1), (key2553, -1), (key2439, -1), (key2505, -1), (key2408, 1), (key2537, 1), (key2380, 1), (key2537, 1), (key2380, 1), (key2408, 1)]

def rawRow1899 : Integer.Sparse Key := [(key2884, -2), (key2884, -2), (key2775, -2), (key2878, 1), (key2847, 1), (key2878, 1), (key2770, 1), (key2847, 1), (key2770, 1), (key3029, 2), (key3029, 2), (key3006, 2), (key2878, -1), (key2770, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2591, -1), (key2553, -1), (key2505, -1), (key2553, -1), (key2439, -1), (key2505, -1), (key2439, -1), (key2537, 1), (key2408, 1), (key2537, 1), (key2380, 1), (key2408, 1), (key2380, 1)]

def rawRow1900 : Integer.Sparse Key := [(key3020, -2), (key3020, -2), (key3020, -2), (key3029, 1), (key3029, 1), (key3029, 1), (key3029, 1), (key3029, 1), (key3029, 1), (key2596, 2), (key2596, 2), (key2596, 2), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1)]

def rawRow1901 : Integer.Sparse Key := [(key3006, -2), (key3029, -2), (key3029, -2), (key3006, 1), (key3006, 1), (key3020, 1), (key3020, 1), (key3029, 1), (key3029, 1), (key2775, 2), (key2884, 2), (key2884, 2), (key2596, -1), (key2596, -1), (key2775, -1), (key2775, -1), (key2884, -1), (key2884, -1), (key2770, -1), (key2770, -1), (key2847, -1), (key2847, -1), (key2878, -1), (key2878, -1), (key2591, 1), (key2591, 1), (key2770, 1), (key2770, 1), (key2878, 1), (key2878, 1)]

def rawRow1902 : Integer.Sparse Key := [(key3029, -2), (key3006, -2), (key3029, -2), (key3020, 1), (key3029, 1), (key3006, 1), (key3029, 1), (key3006, 1), (key3020, 1), (key2884, 2), (key2775, 2), (key2884, 2), (key2775, -1), (key2884, -1), (key2596, -1), (key2884, -1), (key2596, -1), (key2775, -1), (key2847, -1), (key2878, -1), (key2770, -1), (key2878, -1), (key2770, -1), (key2847, -1), (key2770, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2770, 1)]

def rawRow1903 : Integer.Sparse Key := [(key3029, -2), (key3029, -2), (key3006, -2), (key3029, 1), (key3020, 1), (key3029, 1), (key3006, 1), (key3020, 1), (key3006, 1), (key2884, 2), (key2884, 2), (key2775, 2), (key2884, -1), (key2775, -1), (key2884, -1), (key2596, -1), (key2775, -1), (key2596, -1), (key2878, -1), (key2847, -1), (key2878, -1), (key2770, -1), (key2847, -1), (key2770, -1), (key2878, 1), (key2770, 1), (key2878, 1), (key2591, 1), (key2770, 1), (key2591, 1)]

def rawRow1904 : Integer.Sparse Key := [(key2353, -2), (key2359, -2), (key2359, -2), (key2359, 6), (key2448, 2), (key2454, 2), (key2454, 2), (key2454, -2), (key2454, -2), (key2515, -2), (key2566, -6), (key2566, 2), (key2566, 2), (key2578, 2)]

def rawRow1905 : Integer.Sparse Key := [(key2359, -2), (key2353, -2), (key2359, -2), (key2359, 6), (key2454, 2), (key2448, 2), (key2454, 2), (key2454, -2), (key2515, -2), (key2454, -2), (key2566, -6), (key2566, 2), (key2578, 2), (key2566, 2)]

def rawRow1906 : Integer.Sparse Key := [(key2359, -2), (key2359, -2), (key2353, -2), (key2359, 6), (key2454, 2), (key2454, 2), (key2448, 2), (key2515, -2), (key2454, -2), (key2454, -2), (key2566, -6), (key2578, 2), (key2566, 2), (key2566, 2)]

def rawRow1907 : Integer.Sparse Key := [(key2359, -2), (key2359, -2), (key2359, -2), (key2353, 6), (key2515, 2), (key2515, 2), (key2515, 2), (key2448, -2), (key2448, -2), (key2448, -2), (key2578, -6), (key2566, 2), (key2566, 2), (key2566, 2)]

def rawRow1908 : Integer.Sparse Key := [(key2448, -2), (key2454, -2), (key2454, -2), (key2515, 6), (key2353, 2), (key2359, 2), (key2359, 2), (key2566, -2), (key2566, -2), (key2578, -2), (key2359, -6), (key2454, 2), (key2454, 2), (key2515, 2)]

def rawRow1909 : Integer.Sparse Key := [(key2454, -2), (key2448, -2), (key2454, -2), (key2515, 6), (key2359, 2), (key2353, 2), (key2359, 2), (key2566, -2), (key2578, -2), (key2566, -2), (key2359, -6), (key2454, 2), (key2515, 2), (key2454, 2)]

def rawRow1910 : Integer.Sparse Key := [(key2454, -2), (key2454, -2), (key2448, -2), (key2515, 6), (key2359, 2), (key2359, 2), (key2353, 2), (key2578, -2), (key2566, -2), (key2566, -2), (key2359, -6), (key2515, 2), (key2454, 2), (key2454, 2)]

def rawRow1911 : Integer.Sparse Key := [(key2454, -2), (key2454, -2), (key2515, -2), (key2448, 6), (key2566, 2), (key2566, 2), (key2578, 2), (key2353, -2), (key2448, -2), (key2448, -2), (key2515, -6), (key2359, 2), (key2454, 2), (key2454, 2)]

def rawRow1912 : Integer.Sparse Key := [(key2454, -2), (key2515, -2), (key2454, -2), (key2448, 6), (key2566, 2), (key2578, 2), (key2566, 2), (key2448, -2), (key2353, -2), (key2448, -2), (key2515, -6), (key2454, 2), (key2359, 2), (key2454, 2)]

def rawRow1913 : Integer.Sparse Key := [(key2515, -2), (key2454, -2), (key2454, -2), (key2448, 6), (key2578, 2), (key2566, 2), (key2566, 2), (key2448, -2), (key2448, -2), (key2353, -2), (key2515, -6), (key2454, 2), (key2454, 2), (key2359, 2)]

def rawRow1914 : Integer.Sparse Key := [(key2566, -2), (key2566, -2), (key2566, -2), (key2578, 6), (key2359, 2), (key2359, 2), (key2359, 2), (key2515, -2), (key2515, -2), (key2515, -2), (key2353, -6), (key2448, 2), (key2448, 2), (key2448, 2)]

def rawRow1915 : Integer.Sparse Key := [(key2566, -2), (key2566, -2), (key2578, -2), (key2566, 6), (key2454, 2), (key2454, 2), (key2515, 2), (key2359, -2), (key2454, -2), (key2454, -2), (key2448, -6), (key2353, 2), (key2448, 2), (key2448, 2)]

def rawRow1916 : Integer.Sparse Key := [(key2566, -2), (key2578, -2), (key2566, -2), (key2566, 6), (key2454, 2), (key2515, 2), (key2454, 2), (key2454, -2), (key2359, -2), (key2454, -2), (key2448, -6), (key2448, 2), (key2353, 2), (key2448, 2)]

def rawRow1917 : Integer.Sparse Key := [(key2578, -2), (key2566, -2), (key2566, -2), (key2566, 6), (key2515, 2), (key2454, 2), (key2454, 2), (key2454, -2), (key2454, -2), (key2359, -2), (key2448, -6), (key2448, 2), (key2448, 2), (key2353, 2)]

def rawRow1918 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2932, -2), (key2770, 1), (key2773, 1), (key2770, 1), (key2932, 1), (key2773, 1), (key2932, 1), (key2847, 2), (key2847, 2), (key2969, 2), (key2847, -1), (key2890, -1), (key2847, -1), (key2969, -1), (key2890, -1), (key2969, -1), (key2878, -1), (key2881, -1), (key2878, -1), (key2990, -1), (key2881, -1), (key2990, -1), (key2878, 1), (key2911, 1), (key2878, 1), (key2990, 1), (key2911, 1), (key2990, 1)]

def rawRow1919 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2770, -2), (key2773, 1), (key2770, 1), (key2932, 1), (key2770, 1), (key2932, 1), (key2773, 1), (key2847, 2), (key2969, 2), (key2847, 2), (key2890, -1), (key2847, -1), (key2969, -1), (key2847, -1), (key2969, -1), (key2890, -1), (key2881, -1), (key2878, -1), (key2990, -1), (key2878, -1), (key2990, -1), (key2881, -1), (key2911, 1), (key2878, 1), (key2990, 1), (key2878, 1), (key2990, 1), (key2911, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1920 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2770, -2), (key2932, 1), (key2932, 1), (key2773, 1), (key2773, 1), (key2770, 1), (key2770, 1), (key2969, 2), (key2847, 2), (key2847, 2), (key2969, -1), (key2969, -1), (key2890, -1), (key2890, -1), (key2847, -1), (key2847, -1), (key2990, -1), (key2990, -1), (key2881, -1), (key2881, -1), (key2878, -1), (key2878, -1), (key2990, 1), (key2990, 1), (key2911, 1), (key2911, 1), (key2878, 1), (key2878, 1)]

def rawRow1921 : Integer.Sparse Key := [(key2773, -2), (key2773, -2), (key2773, -2), (key2770, 1), (key2770, 1), (key2770, 1), (key2770, 1), (key2770, 1), (key2770, 1), (key2890, 2), (key2890, 2), (key2890, 2), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2911, -1), (key2911, -1), (key2911, -1), (key2911, -1), (key2911, -1), (key2911, -1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1)]

def rawRow1922 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2969, -2), (key2878, 1), (key2881, 1), (key2878, 1), (key2990, 1), (key2881, 1), (key2990, 1), (key2770, 2), (key2770, 2), (key2932, 2), (key2878, -1), (key2911, -1), (key2878, -1), (key2990, -1), (key2911, -1), (key2990, -1), (key2770, -1), (key2773, -1), (key2770, -1), (key2932, -1), (key2773, -1), (key2932, -1), (key2847, 1), (key2890, 1), (key2847, 1), (key2969, 1), (key2890, 1), (key2969, 1)]

def rawRow1923 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2847, -2), (key2881, 1), (key2878, 1), (key2990, 1), (key2878, 1), (key2990, 1), (key2881, 1), (key2770, 2), (key2932, 2), (key2770, 2), (key2911, -1), (key2878, -1), (key2990, -1), (key2878, -1), (key2990, -1), (key2911, -1), (key2773, -1), (key2770, -1), (key2932, -1), (key2770, -1), (key2932, -1), (key2773, -1), (key2890, 1), (key2847, 1), (key2969, 1), (key2847, 1), (key2969, 1), (key2890, 1)]

def rawRow1924 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2847, -2), (key2990, 1), (key2990, 1), (key2881, 1), (key2881, 1), (key2878, 1), (key2878, 1), (key2932, 2), (key2770, 2), (key2770, 2), (key2990, -1), (key2990, -1), (key2911, -1), (key2911, -1), (key2878, -1), (key2878, -1), (key2932, -1), (key2932, -1), (key2773, -1), (key2773, -1), (key2770, -1), (key2770, -1), (key2969, 1), (key2969, 1), (key2890, 1), (key2890, 1), (key2847, 1), (key2847, 1)]

def rawRow1925 : Integer.Sparse Key := [(key2594, -2), (key2881, -2), (key2881, -2), (key2591, 1), (key2591, 1), (key2847, 1), (key2847, 1), (key2878, 1), (key2878, 1), (key2601, 2), (key2911, 2), (key2911, 2), (key2591, -1), (key2591, -1), (key2770, -1), (key2770, -1), (key2878, -1), (key2878, -1), (key2601, -1), (key2601, -1), (key2890, -1), (key2890, -1), (key2911, -1), (key2911, -1), (key2594, 1), (key2594, 1), (key2773, 1), (key2773, 1), (key2881, 1), (key2881, 1)]

def rawRow1926 : Integer.Sparse Key := [(key2881, -2), (key2594, -2), (key2881, -2), (key2847, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2847, 1), (key2911, 2), (key2601, 2), (key2911, 2), (key2770, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2890, -1), (key2911, -1), (key2601, -1), (key2911, -1), (key2601, -1), (key2890, -1), (key2773, 1), (key2881, 1), (key2594, 1), (key2881, 1), (key2594, 1), (key2773, 1)]

def rawRow1927 : Integer.Sparse Key := [(key2881, -2), (key2881, -2), (key2594, -2), (key2878, 1), (key2847, 1), (key2878, 1), (key2591, 1), (key2847, 1), (key2591, 1), (key2911, 2), (key2911, 2), (key2601, 2), (key2878, -1), (key2770, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2591, -1), (key2911, -1), (key2890, -1), (key2911, -1), (key2601, -1), (key2890, -1), (key2601, -1), (key2881, 1), (key2773, 1), (key2881, 1), (key2594, 1), (key2773, 1), (key2594, 1)]

def rawRow1928 : Integer.Sparse Key := [(key2890, -2), (key2890, -2), (key2890, -2), (key2911, 1), (key2911, 1), (key2911, 1), (key2911, 1), (key2911, 1), (key2911, 1), (key2773, 2), (key2773, 2), (key2773, 2), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1)]

def rawRow1929 : Integer.Sparse Key := [(key2601, -2), (key2911, -2), (key2911, -2), (key2601, 1), (key2601, 1), (key2890, 1), (key2890, 1), (key2911, 1), (key2911, 1), (key2594, 2), (key2881, 2), (key2881, 2), (key2594, -1), (key2594, -1), (key2773, -1), (key2773, -1), (key2881, -1), (key2881, -1), (key2591, -1), (key2591, -1), (key2847, -1), (key2847, -1), (key2878, -1), (key2878, -1), (key2591, 1), (key2591, 1), (key2770, 1), (key2770, 1), (key2878, 1), (key2878, 1)]

def rawRow1930 : Integer.Sparse Key := [(key2911, -2), (key2601, -2), (key2911, -2), (key2890, 1), (key2911, 1), (key2601, 1), (key2911, 1), (key2601, 1), (key2890, 1), (key2881, 2), (key2594, 2), (key2881, 2), (key2773, -1), (key2881, -1), (key2594, -1), (key2881, -1), (key2594, -1), (key2773, -1), (key2847, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2847, -1), (key2770, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2770, 1)]

def rawRow1931 : Integer.Sparse Key := [(key2911, -2), (key2911, -2), (key2601, -2), (key2911, 1), (key2890, 1), (key2911, 1), (key2601, 1), (key2890, 1), (key2601, 1), (key2881, 2), (key2881, 2), (key2594, 2), (key2881, -1), (key2773, -1), (key2881, -1), (key2594, -1), (key2773, -1), (key2594, -1), (key2878, -1), (key2847, -1), (key2878, -1), (key2591, -1), (key2847, -1), (key2591, -1), (key2878, 1), (key2770, 1), (key2878, 1), (key2591, 1), (key2770, 1), (key2591, 1)]

def rawRow1932 : Integer.Sparse Key := [(key1249, -6), (key1249, 2), (key1249, 2), (key1262, 2), (key1524, 6), (key1524, -2), (key1524, -2), (key1762, -2), (key1602, -2), (key1602, -2), (key1645, -2), (key1602, 2), (key1602, 2), (key1803, 2)]

def rawRow1933 : Integer.Sparse Key := [(key1249, -6), (key1249, 2), (key1262, 2), (key1249, 2), (key1524, 6), (key1524, -2), (key1762, -2), (key1524, -2), (key1602, -2), (key1645, -2), (key1602, -2), (key1602, 2), (key1803, 2), (key1602, 2)]

def rawRow1934 : Integer.Sparse Key := [(key1249, -6), (key1262, 2), (key1249, 2), (key1249, 2), (key1524, 6), (key1762, -2), (key1524, -2), (key1524, -2), (key1645, -2), (key1602, -2), (key1602, -2), (key1803, 2), (key1602, 2), (key1602, 2)]

def rawRow1935 : Integer.Sparse Key := [(key1262, -6), (key1249, 2), (key1249, 2), (key1249, 2), (key1762, 6), (key1524, -2), (key1524, -2), (key1524, -2), (key1803, -2), (key1803, -2), (key1803, -2), (key1645, 2), (key1645, 2), (key1645, 2)]

def rawRow1936 : Integer.Sparse Key := [(key1524, -6), (key1602, 2), (key1602, 2), (key1645, 2), (key1249, 6), (key1602, -2), (key1602, -2), (key1803, -2), (key1249, -2), (key1249, -2), (key1262, -2), (key1524, 2), (key1524, 2), (key1762, 2)]

def rawRow1937 : Integer.Sparse Key := [(key1524, -6), (key1602, 2), (key1645, 2), (key1602, 2), (key1249, 6), (key1602, -2), (key1803, -2), (key1602, -2), (key1249, -2), (key1262, -2), (key1249, -2), (key1524, 2), (key1762, 2), (key1524, 2)]

def rawRow1938 : Integer.Sparse Key := [(key1524, -6), (key1645, 2), (key1602, 2), (key1602, 2), (key1249, 6), (key1803, -2), (key1602, -2), (key1602, -2), (key1262, -2), (key1249, -2), (key1249, -2), (key1762, 2), (key1524, 2), (key1524, 2)]

def rawRow1939 : Integer.Sparse Key := [(key1645, -6), (key1524, 2), (key1602, 2), (key1602, 2), (key1803, 6), (key1249, -2), (key1602, -2), (key1602, -2), (key1762, -2), (key1803, -2), (key1803, -2), (key1262, 2), (key1645, 2), (key1645, 2)]

def rawRow1940 : Integer.Sparse Key := [(key1645, -6), (key1602, 2), (key1524, 2), (key1602, 2), (key1803, 6), (key1602, -2), (key1249, -2), (key1602, -2), (key1803, -2), (key1762, -2), (key1803, -2), (key1645, 2), (key1262, 2), (key1645, 2)]

def rawRow1941 : Integer.Sparse Key := [(key1645, -6), (key1602, 2), (key1602, 2), (key1524, 2), (key1803, 6), (key1602, -2), (key1602, -2), (key1249, -2), (key1803, -2), (key1803, -2), (key1762, -2), (key1645, 2), (key1645, 2), (key1262, 2)]

def rawRow1942 : Integer.Sparse Key := [(key1762, -6), (key1803, 2), (key1803, 2), (key1803, 2), (key1262, 6), (key1645, -2), (key1645, -2), (key1645, -2), (key1249, -2), (key1249, -2), (key1249, -2), (key1524, 2), (key1524, 2), (key1524, 2)]

def rawRow1943 : Integer.Sparse Key := [(key1803, -6), (key1762, 2), (key1803, 2), (key1803, 2), (key1645, 6), (key1262, -2), (key1645, -2), (key1645, -2), (key1524, -2), (key1602, -2), (key1602, -2), (key1249, 2), (key1602, 2), (key1602, 2)]

def rawRow1944 : Integer.Sparse Key := [(key1803, -6), (key1803, 2), (key1762, 2), (key1803, 2), (key1645, 6), (key1645, -2), (key1262, -2), (key1645, -2), (key1602, -2), (key1524, -2), (key1602, -2), (key1602, 2), (key1249, 2), (key1602, 2)]

def rawRow1945 : Integer.Sparse Key := [(key1803, -6), (key1803, 2), (key1803, 2), (key1762, 2), (key1645, 6), (key1645, -2), (key1645, -2), (key1262, -2), (key1602, -2), (key1602, -2), (key1524, -2), (key1602, 2), (key1602, 2), (key1249, 2)]

def rawRow1946 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2584, 1), (key2588, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2599, 1), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, -1), (key2767, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2930, -1), (key2840, -1), (key2844, -1), (key2840, -1), (key2888, -1), (key2844, -1), (key2888, -1), (key2840, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2967, 1)]

def rawRow1947 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2588, 1), (key2584, 1), (key2599, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2767, 2), (key2763, 2), (key2767, 2), (key2767, -1), (key2763, -1), (key2930, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2844, -1), (key2840, -1), (key2888, -1), (key2840, -1), (key2888, -1), (key2844, -1), (key2844, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2844, 1)]

def rawRow1948 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2599, 1), (key2599, 1), (key2588, 1), (key2588, 1), (key2584, 1), (key2584, 1), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, -1), (key2930, -1), (key2767, -1), (key2767, -1), (key2763, -1), (key2763, -1), (key2888, -1), (key2888, -1), (key2844, -1), (key2844, -1), (key2840, -1), (key2840, -1), (key2967, 1), (key2967, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1)]

def rawRow1949 : Integer.Sparse Key := [(key2599, -2), (key2599, -2), (key2599, -2), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2930, 2), (key2930, 2), (key2930, 2), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2767, -1), (key2967, -1), (key2967, -1), (key2967, -1), (key2967, -1), (key2967, -1), (key2967, -1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1)]

def rawRow1950 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2840, 1), (key2844, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2888, 1), (key2584, 2), (key2588, 2), (key2588, 2), (key2840, -1), (key2844, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2584, -1), (key2588, -1), (key2584, -1), (key2599, -1), (key2588, -1), (key2599, -1), (key2763, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2930, 1)]

def rawRow1951 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2844, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2588, 2), (key2584, 2), (key2588, 2), (key2844, -1), (key2840, -1), (key2967, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2588, -1), (key2584, -1), (key2599, -1), (key2584, -1), (key2599, -1), (key2588, -1), (key2767, 1), (key2763, 1), (key2930, 1), (key2763, 1), (key2930, 1), (key2767, 1)]

def rawRow1952 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2588, 2), (key2588, 2), (key2584, 2), (key2967, -1), (key2967, -1), (key2844, -1), (key2844, -1), (key2840, -1), (key2840, -1), (key2599, -1), (key2599, -1), (key2588, -1), (key2588, -1), (key2584, -1), (key2584, -1), (key2930, 1), (key2930, 1), (key2767, 1), (key2767, 1), (key2763, 1), (key2763, 1)]

def rawRow1953 : Integer.Sparse Key := [(key2888, -2), (key2888, -2), (key2909, -2), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2967, 2), (key2967, 2), (key2988, 2), (key2588, -1), (key2588, -1), (key2844, -1), (key2844, -1), (key2875, -1), (key2875, -1), (key2930, -1), (key2930, -1), (key2967, -1), (key2967, -1), (key2988, -1), (key2988, -1), (key2599, 1), (key2599, 1), (key2888, 1), (key2888, 1), (key2909, 1), (key2909, 1)]

def rawRow1954 : Integer.Sparse Key := [(key2888, -2), (key2909, -2), (key2888, -2), (key2844, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2967, 2), (key2988, 2), (key2967, 2), (key2844, -1), (key2875, -1), (key2588, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2967, -1), (key2988, -1), (key2930, -1), (key2988, -1), (key2930, -1), (key2967, -1), (key2888, 1), (key2909, 1), (key2599, 1), (key2909, 1), (key2599, 1), (key2888, 1)]

def rawRow1955 : Integer.Sparse Key := [(key2909, -2), (key2888, -2), (key2888, -2), (key2875, 1), (key2844, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2767, 1), (key2988, 2), (key2967, 2), (key2967, 2), (key2875, -1), (key2844, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2988, -1), (key2967, -1), (key2988, -1), (key2930, -1), (key2967, -1), (key2930, -1), (key2909, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2599, 1)]

def rawRow1956 : Integer.Sparse Key := [(key2930, -2), (key2930, -2), (key2930, -2), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2599, 2), (key2599, 2), (key2599, 2), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2888, -1), (key2588, -1), (key2588, -1), (key2588, -1), (key2588, -1), (key2588, -1), (key2588, -1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1)]

def rawRow1957 : Integer.Sparse Key := [(key2967, -2), (key2967, -2), (key2988, -2), (key2930, 1), (key2930, 1), (key2967, 1), (key2967, 1), (key2988, 1), (key2988, 1), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, -1), (key2599, -1), (key2888, -1), (key2888, -1), (key2909, -1), (key2909, -1), (key2767, -1), (key2767, -1), (key2844, -1), (key2844, -1), (key2875, -1), (key2875, -1), (key2588, 1), (key2588, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1)]

def rawRow1958 : Integer.Sparse Key := [(key2967, -2), (key2988, -2), (key2967, -2), (key2967, 1), (key2988, 1), (key2930, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2888, 2), (key2909, 2), (key2888, 2), (key2888, -1), (key2909, -1), (key2599, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2844, -1), (key2875, -1), (key2767, -1), (key2875, -1), (key2767, -1), (key2844, -1), (key2844, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2844, 1)]

def rawRow1959 : Integer.Sparse Key := [(key2988, -2), (key2967, -2), (key2967, -2), (key2988, 1), (key2967, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2930, 1), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, -1), (key2888, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2599, -1), (key2875, -1), (key2844, -1), (key2875, -1), (key2767, -1), (key2844, -1), (key2767, -1), (key2875, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2588, 1)]

def rawRow1960 : Integer.Sparse Key := [(key972, -2), (key977, -2), (key977, -2), (key977, 6), (key1086, 2), (key1091, 2), (key1091, 2), (key1091, -2), (key1091, -2), (key1181, -2), (key1162, -6), (key1162, 2), (key1162, 2), (key1218, 2)]

def rawRow1961 : Integer.Sparse Key := [(key977, -2), (key972, -2), (key977, -2), (key977, 6), (key1091, 2), (key1086, 2), (key1091, 2), (key1091, -2), (key1181, -2), (key1091, -2), (key1162, -6), (key1162, 2), (key1218, 2), (key1162, 2)]

def rawRow1962 : Integer.Sparse Key := [(key977, -2), (key977, -2), (key972, -2), (key977, 6), (key1091, 2), (key1091, 2), (key1086, 2), (key1181, -2), (key1091, -2), (key1091, -2), (key1162, -6), (key1218, 2), (key1162, 2), (key1162, 2)]

def rawRow1963 : Integer.Sparse Key := [(key977, -2), (key977, -2), (key977, -2), (key972, 6), (key1181, 2), (key1181, 2), (key1181, 2), (key1086, -2), (key1086, -2), (key1086, -2), (key1218, -6), (key1162, 2), (key1162, 2), (key1162, 2)]

def rawRow1964 : Integer.Sparse Key := [(key1086, -2), (key1091, -2), (key1091, -2), (key1162, 6), (key972, 2), (key977, 2), (key977, 2), (key1162, -2), (key1162, -2), (key1218, -2), (key977, -6), (key1091, 2), (key1091, 2), (key1181, 2)]

def rawRow1965 : Integer.Sparse Key := [(key1091, -2), (key1086, -2), (key1091, -2), (key1162, 6), (key977, 2), (key972, 2), (key977, 2), (key1162, -2), (key1218, -2), (key1162, -2), (key977, -6), (key1091, 2), (key1181, 2), (key1091, 2)]

def rawRow1966 : Integer.Sparse Key := [(key1091, -2), (key1091, -2), (key1086, -2), (key1162, 6), (key977, 2), (key977, 2), (key972, 2), (key1218, -2), (key1162, -2), (key1162, -2), (key977, -6), (key1181, 2), (key1091, 2), (key1091, 2)]

def rawRow1967 : Integer.Sparse Key := [(key1091, -2), (key1091, -2), (key1162, -2), (key1086, 6), (key1181, 2), (key1181, 2), (key1218, 2), (key972, -2), (key1086, -2), (key1086, -2), (key1181, -6), (key977, 2), (key1091, 2), (key1091, 2)]

def rawRow1968 : Integer.Sparse Key := [(key1091, -2), (key1162, -2), (key1091, -2), (key1086, 6), (key1181, 2), (key1218, 2), (key1181, 2), (key1086, -2), (key972, -2), (key1086, -2), (key1181, -6), (key1091, 2), (key977, 2), (key1091, 2)]

def rawRow1969 : Integer.Sparse Key := [(key1162, -2), (key1091, -2), (key1091, -2), (key1086, 6), (key1218, 2), (key1181, 2), (key1181, 2), (key1086, -2), (key1086, -2), (key972, -2), (key1181, -6), (key1091, 2), (key1091, 2), (key977, 2)]

def rawRow1970 : Integer.Sparse Key := [(key1181, -2), (key1181, -2), (key1181, -2), (key1218, 6), (key977, 2), (key977, 2), (key977, 2), (key1162, -2), (key1162, -2), (key1162, -2), (key972, -6), (key1086, 2), (key1086, 2), (key1086, 2)]

def rawRow1971 : Integer.Sparse Key := [(key1181, -2), (key1181, -2), (key1218, -2), (key1181, 6), (key1091, 2), (key1091, 2), (key1162, 2), (key977, -2), (key1091, -2), (key1091, -2), (key1086, -6), (key972, 2), (key1086, 2), (key1086, 2)]

def rawRow1972 : Integer.Sparse Key := [(key1181, -2), (key1218, -2), (key1181, -2), (key1181, 6), (key1091, 2), (key1162, 2), (key1091, 2), (key1091, -2), (key977, -2), (key1091, -2), (key1086, -6), (key1086, 2), (key972, 2), (key1086, 2)]

def rawRow1973 : Integer.Sparse Key := [(key1218, -2), (key1181, -2), (key1181, -2), (key1181, 6), (key1162, 2), (key1091, 2), (key1091, 2), (key1091, -2), (key1091, -2), (key977, -2), (key1086, -6), (key1086, 2), (key1086, 2), (key972, 2)]

def rawRow1974 : Integer.Sparse Key := [(key2369, -6), (key2369, 2), (key2369, 2), (key2384, 2), (key2397, 6), (key2397, -2), (key2397, -2), (key2431, -2), (key2463, -2), (key2463, -2), (key2474, -2), (key2463, 2), (key2463, 2), (key2497, 2)]

def rawRow1975 : Integer.Sparse Key := [(key2369, -6), (key2369, 2), (key2384, 2), (key2369, 2), (key2397, 6), (key2397, -2), (key2431, -2), (key2397, -2), (key2463, -2), (key2474, -2), (key2463, -2), (key2463, 2), (key2497, 2), (key2463, 2)]

def rawRow1976 : Integer.Sparse Key := [(key2369, -6), (key2384, 2), (key2369, 2), (key2369, 2), (key2397, 6), (key2431, -2), (key2397, -2), (key2397, -2), (key2474, -2), (key2463, -2), (key2463, -2), (key2497, 2), (key2463, 2), (key2463, 2)]

def rawRow1977 : Integer.Sparse Key := [(key2384, -6), (key2369, 2), (key2369, 2), (key2369, 2), (key2431, 6), (key2397, -2), (key2397, -2), (key2397, -2), (key2497, -2), (key2497, -2), (key2497, -2), (key2474, 2), (key2474, 2), (key2474, 2)]

def rawRow1978 : Integer.Sparse Key := [(key2397, -6), (key2463, 2), (key2463, 2), (key2474, 2), (key2369, 6), (key2463, -2), (key2463, -2), (key2497, -2), (key2369, -2), (key2369, -2), (key2384, -2), (key2397, 2), (key2397, 2), (key2431, 2)]

def rawRow1979 : Integer.Sparse Key := [(key2397, -6), (key2463, 2), (key2474, 2), (key2463, 2), (key2369, 6), (key2463, -2), (key2497, -2), (key2463, -2), (key2369, -2), (key2384, -2), (key2369, -2), (key2397, 2), (key2431, 2), (key2397, 2)]

def rawRow1980 : Integer.Sparse Key := [(key2397, -6), (key2474, 2), (key2463, 2), (key2463, 2), (key2369, 6), (key2497, -2), (key2463, -2), (key2463, -2), (key2384, -2), (key2369, -2), (key2369, -2), (key2431, 2), (key2397, 2), (key2397, 2)]

def rawRow1981 : Integer.Sparse Key := [(key2474, -6), (key2397, 2), (key2463, 2), (key2463, 2), (key2497, 6), (key2369, -2), (key2463, -2), (key2463, -2), (key2431, -2), (key2497, -2), (key2497, -2), (key2384, 2), (key2474, 2), (key2474, 2)]

def rawRow1982 : Integer.Sparse Key := [(key2474, -6), (key2463, 2), (key2397, 2), (key2463, 2), (key2497, 6), (key2463, -2), (key2369, -2), (key2463, -2), (key2497, -2), (key2431, -2), (key2497, -2), (key2474, 2), (key2384, 2), (key2474, 2)]

def rawRow1983 : Integer.Sparse Key := [(key2474, -6), (key2463, 2), (key2463, 2), (key2397, 2), (key2497, 6), (key2463, -2), (key2463, -2), (key2369, -2), (key2497, -2), (key2497, -2), (key2431, -2), (key2474, 2), (key2474, 2), (key2384, 2)]

def rawRow1984 : Integer.Sparse Key := [(key2431, -6), (key2497, 2), (key2497, 2), (key2497, 2), (key2384, 6), (key2474, -2), (key2474, -2), (key2474, -2), (key2369, -2), (key2369, -2), (key2369, -2), (key2397, 2), (key2397, 2), (key2397, 2)]

def rawRow1985 : Integer.Sparse Key := [(key2497, -6), (key2431, 2), (key2497, 2), (key2497, 2), (key2474, 6), (key2384, -2), (key2474, -2), (key2474, -2), (key2397, -2), (key2463, -2), (key2463, -2), (key2369, 2), (key2463, 2), (key2463, 2)]

def rawRow1986 : Integer.Sparse Key := [(key2497, -6), (key2497, 2), (key2431, 2), (key2497, 2), (key2474, 6), (key2474, -2), (key2384, -2), (key2474, -2), (key2463, -2), (key2397, -2), (key2463, -2), (key2463, 2), (key2369, 2), (key2463, 2)]

def rawRow1987 : Integer.Sparse Key := [(key2497, -6), (key2497, 2), (key2497, 2), (key2431, 2), (key2474, 6), (key2474, -2), (key2474, -2), (key2384, -2), (key2463, -2), (key2463, -2), (key2397, -2), (key2463, 2), (key2463, 2), (key2369, 2)]

def rawRow1988 : Integer.Sparse Key := [(key1527, -1), (key1532, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1766, -1), (key1532, 2), (key1532, 2), (key1766, 2), (key1605, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1610, -1), (key1649, -1), (key1610, -1), (key1807, -1), (key1649, -1), (key1807, -1), (key1638, -2), (key1638, -2), (key1830, -2), (key1638, 1), (key1672, 1), (key1638, 1), (key1830, 1), (key1672, 1), (key1830, 1)]

def rawRow1989 : Integer.Sparse Key := [(key1532, -1), (key1527, -1), (key1766, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1532, 2), (key1766, 2), (key1532, 2), (key1610, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1649, -1), (key1610, -1), (key1807, -1), (key1610, -1), (key1807, -1), (key1649, -1), (key1638, -2), (key1830, -2), (key1638, -2), (key1672, 1), (key1638, 1), (key1830, 1), (key1638, 1), (key1830, 1), (key1672, 1)]

def rawRow1990 : Integer.Sparse Key := [(key1766, -1), (key1766, -1), (key1532, -1), (key1532, -1), (key1527, -1), (key1527, -1), (key1766, 2), (key1532, 2), (key1532, 2), (key1807, 1), (key1807, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1807, -1), (key1807, -1), (key1649, -1), (key1649, -1), (key1610, -1), (key1610, -1), (key1830, -2), (key1638, -2), (key1638, -2), (key1830, 1), (key1830, 1), (key1672, 1), (key1672, 1), (key1638, 1), (key1638, 1)]

def rawRow1991 : Integer.Sparse Key := [(key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1527, 2), (key1527, 2), (key1527, 2), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1605, -1), (key1605, -1), (key1605, -1), (key1605, -1), (key1605, -1), (key1605, -1), (key1672, -2), (key1672, -2), (key1672, -2), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1)]

def rawRow1992 : Integer.Sparse Key := [(key1605, -1), (key1610, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1807, -1), (key1638, 2), (key1638, 2), (key1830, 2), (key1527, 1), (key1532, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1766, 1), (key1638, -1), (key1672, -1), (key1638, -1), (key1830, -1), (key1672, -1), (key1830, -1), (key1532, -2), (key1532, -2), (key1766, -2), (key1610, 1), (key1649, 1), (key1610, 1), (key1807, 1), (key1649, 1), (key1807, 1)]

def rawRow1993 : Integer.Sparse Key := [(key1610, -1), (key1605, -1), (key1807, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1638, 2), (key1830, 2), (key1638, 2), (key1532, 1), (key1527, 1), (key1766, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1672, -1), (key1638, -1), (key1830, -1), (key1638, -1), (key1830, -1), (key1672, -1), (key1532, -2), (key1766, -2), (key1532, -2), (key1649, 1), (key1610, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1649, 1)]

def rawRow1994 : Integer.Sparse Key := [(key1807, -1), (key1807, -1), (key1610, -1), (key1610, -1), (key1605, -1), (key1605, -1), (key1830, 2), (key1638, 2), (key1638, 2), (key1766, 1), (key1766, 1), (key1532, 1), (key1532, 1), (key1527, 1), (key1527, 1), (key1830, -1), (key1830, -1), (key1672, -1), (key1672, -1), (key1638, -1), (key1638, -1), (key1766, -2), (key1532, -2), (key1532, -2), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1)]

def rawRow1995 : Integer.Sparse Key := [(key1257, -1), (key1257, -1), (key1610, -1), (key1610, -1), (key1638, -1), (key1638, -1), (key1252, 2), (key1605, 2), (key1605, 2), (key1266, 1), (key1266, 1), (key1649, 1), (key1649, 1), (key1672, 1), (key1672, 1), (key1252, -1), (key1252, -1), (key1527, -1), (key1527, -1), (key1605, -1), (key1605, -1), (key1266, -2), (key1649, -2), (key1649, -2), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1)]

def rawRow1996 : Integer.Sparse Key := [(key1610, -1), (key1638, -1), (key1257, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1605, 2), (key1252, 2), (key1605, 2), (key1649, 1), (key1672, 1), (key1266, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1527, -1), (key1605, -1), (key1252, -1), (key1605, -1), (key1252, -1), (key1527, -1), (key1649, -2), (key1266, -2), (key1649, -2), (key1532, 1), (key1610, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1532, 1)]

def rawRow1997 : Integer.Sparse Key := [(key1638, -1), (key1610, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1257, -1), (key1605, 2), (key1605, 2), (key1252, 2), (key1672, 1), (key1649, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1266, 1), (key1605, -1), (key1527, -1), (key1605, -1), (key1252, -1), (key1527, -1), (key1252, -1), (key1649, -2), (key1649, -2), (key1266, -2), (key1610, 1), (key1532, 1), (key1610, 1), (key1257, 1), (key1532, 1), (key1257, 1)]

def rawRow1998 : Integer.Sparse Key := [(key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1672, 2), (key1672, 2), (key1672, 2), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1638, -1), (key1638, -1), (key1638, -1), (key1638, -1), (key1638, -1), (key1638, -1), (key1527, -2), (key1527, -2), (key1527, -2), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1)]

def rawRow1999 : Integer.Sparse Key := [(key1266, -1), (key1266, -1), (key1649, -1), (key1649, -1), (key1672, -1), (key1672, -1), (key1266, 2), (key1649, 2), (key1649, 2), (key1257, 1), (key1257, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1257, -1), (key1257, -1), (key1532, -1), (key1532, -1), (key1610, -1), (key1610, -1), (key1252, -2), (key1605, -2), (key1605, -2), (key1252, 1), (key1252, 1), (key1527, 1), (key1527, 1), (key1605, 1), (key1605, 1)]

def rawRow2000 : Integer.Sparse Key := [(key1649, -1), (key1672, -1), (key1266, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1649, 2), (key1266, 2), (key1649, 2), (key1610, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1532, -1), (key1610, -1), (key1257, -1), (key1610, -1), (key1257, -1), (key1532, -1), (key1605, -2), (key1252, -2), (key1605, -2), (key1527, 1), (key1605, 1), (key1252, 1), (key1605, 1), (key1252, 1), (key1527, 1)]

def rawRow2001 : Integer.Sparse Key := [(key1672, -1), (key1649, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1266, -1), (key1649, 2), (key1649, 2), (key1266, 2), (key1638, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1610, -1), (key1532, -1), (key1610, -1), (key1257, -1), (key1532, -1), (key1257, -1), (key1605, -2), (key1605, -2), (key1252, -2), (key1605, 1), (key1527, 1), (key1605, 1), (key1252, 1), (key1527, 1), (key1252, 1)]

def rawRow2002 : Integer.Sparse Key := [(key3034, -2), (key3041, -2), (key3041, -2), (key3037, 2), (key3041, 2), (key3041, 2), (key3121, 2), (key3133, 2), (key3133, 2), (key3133, -6), (key3129, -2), (key3139, -2), (key3139, -2), (key3139, 6)]

def rawRow2003 : Integer.Sparse Key := [(key3041, -2), (key3034, -2), (key3041, -2), (key3041, 2), (key3037, 2), (key3041, 2), (key3133, 2), (key3121, 2), (key3133, 2), (key3133, -6), (key3139, -2), (key3129, -2), (key3139, -2), (key3139, 6)]

def rawRow2004 : Integer.Sparse Key := [(key3041, -2), (key3041, -2), (key3034, -2), (key3041, 2), (key3041, 2), (key3037, 2), (key3133, 2), (key3133, 2), (key3121, 2), (key3133, -6), (key3139, -2), (key3139, -2), (key3129, -2), (key3139, 6)]

def rawRow2005 : Integer.Sparse Key := [(key3037, -2), (key3037, -2), (key3037, -2), (key3034, 2), (key3034, 2), (key3034, 2), (key3133, 2), (key3133, 2), (key3133, 2), (key3121, -6), (key3139, -2), (key3139, -2), (key3139, -2), (key3129, 6)]

def rawRow2006 : Integer.Sparse Key := [(key3121, -2), (key3133, -2), (key3133, -2), (key3129, 2), (key3139, 2), (key3139, 2), (key3034, 2), (key3041, 2), (key3041, 2), (key3139, -6), (key3037, -2), (key3041, -2), (key3041, -2), (key3133, 6)]

def rawRow2007 : Integer.Sparse Key := [(key3133, -2), (key3121, -2), (key3133, -2), (key3139, 2), (key3129, 2), (key3139, 2), (key3041, 2), (key3034, 2), (key3041, 2), (key3139, -6), (key3041, -2), (key3037, -2), (key3041, -2), (key3133, 6)]

def rawRow2008 : Integer.Sparse Key := [(key3133, -2), (key3133, -2), (key3121, -2), (key3139, 2), (key3139, 2), (key3129, 2), (key3041, 2), (key3041, 2), (key3034, 2), (key3139, -6), (key3041, -2), (key3041, -2), (key3037, -2), (key3133, 6)]

def rawRow2009 : Integer.Sparse Key := [(key3037, -2), (key3037, -2), (key3129, -2), (key3034, 2), (key3034, 2), (key3121, 2), (key3041, 2), (key3041, 2), (key3139, 2), (key3034, -6), (key3041, -2), (key3041, -2), (key3133, -2), (key3037, 6)]

def rawRow2010 : Integer.Sparse Key := [(key3037, -2), (key3129, -2), (key3037, -2), (key3034, 2), (key3121, 2), (key3034, 2), (key3041, 2), (key3139, 2), (key3041, 2), (key3034, -6), (key3041, -2), (key3133, -2), (key3041, -2), (key3037, 6)]

def rawRow2011 : Integer.Sparse Key := [(key3129, -2), (key3037, -2), (key3037, -2), (key3121, 2), (key3034, 2), (key3034, 2), (key3139, 2), (key3041, 2), (key3041, 2), (key3034, -6), (key3133, -2), (key3041, -2), (key3041, -2), (key3037, 6)]

def rawRow2012 : Integer.Sparse Key := [(key3133, -2), (key3133, -2), (key3133, -2), (key3139, 2), (key3139, 2), (key3139, 2), (key3037, 2), (key3037, 2), (key3037, 2), (key3129, -6), (key3034, -2), (key3034, -2), (key3034, -2), (key3121, 6)]

def rawRow2013 : Integer.Sparse Key := [(key3041, -2), (key3041, -2), (key3139, -2), (key3041, 2), (key3041, 2), (key3133, 2), (key3037, 2), (key3037, 2), (key3129, 2), (key3037, -6), (key3034, -2), (key3034, -2), (key3121, -2), (key3034, 6)]

def rawRow2014 : Integer.Sparse Key := [(key3041, -2), (key3139, -2), (key3041, -2), (key3041, 2), (key3133, 2), (key3041, 2), (key3037, 2), (key3129, 2), (key3037, 2), (key3037, -6), (key3034, -2), (key3121, -2), (key3034, -2), (key3034, 6)]

def rawRow2015 : Integer.Sparse Key := [(key3139, -2), (key3041, -2), (key3041, -2), (key3133, 2), (key3041, 2), (key3041, 2), (key3129, 2), (key3037, 2), (key3037, 2), (key3037, -6), (key3121, -2), (key3034, -2), (key3034, -2), (key3034, 6)]

def rawRow2016 : Integer.Sparse Key := [(key1252, -2), (key1257, -2), (key1257, -2), (key1252, 1), (key1257, 1), (key1252, 1), (key1266, 1), (key1257, 1), (key1266, 1), (key1527, 2), (key1532, 2), (key1532, 2), (key1527, -1), (key1532, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1766, -1), (key1605, -1), (key1610, -1), (key1605, -1), (key1649, -1), (key1610, -1), (key1649, -1), (key1605, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1807, 1)]

def rawRow2017 : Integer.Sparse Key := [(key1257, -2), (key1252, -2), (key1257, -2), (key1257, 1), (key1252, 1), (key1266, 1), (key1252, 1), (key1266, 1), (key1257, 1), (key1532, 2), (key1527, 2), (key1532, 2), (key1532, -1), (key1527, -1), (key1766, -1), (key1527, -1), (key1766, -1), (key1532, -1), (key1610, -1), (key1605, -1), (key1649, -1), (key1605, -1), (key1649, -1), (key1610, -1), (key1610, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1610, 1)]

def rawRow2018 : Integer.Sparse Key := [(key1257, -2), (key1257, -2), (key1252, -2), (key1266, 1), (key1266, 1), (key1257, 1), (key1257, 1), (key1252, 1), (key1252, 1), (key1532, 2), (key1532, 2), (key1527, 2), (key1766, -1), (key1766, -1), (key1532, -1), (key1532, -1), (key1527, -1), (key1527, -1), (key1649, -1), (key1649, -1), (key1610, -1), (key1610, -1), (key1605, -1), (key1605, -1), (key1807, 1), (key1807, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1)]

def rawRow2019 : Integer.Sparse Key := [(key1266, -2), (key1266, -2), (key1266, -2), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1766, 2), (key1766, 2), (key1766, 2), (key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1532, -1), (key1807, -1), (key1807, -1), (key1807, -1), (key1807, -1), (key1807, -1), (key1807, -1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1)]

def rawRow2020 : Integer.Sparse Key := [(key1527, -2), (key1532, -2), (key1532, -2), (key1605, 1), (key1610, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1649, 1), (key1252, 2), (key1257, 2), (key1257, 2), (key1605, -1), (key1610, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1807, -1), (key1252, -1), (key1257, -1), (key1252, -1), (key1266, -1), (key1257, -1), (key1266, -1), (key1527, 1), (key1532, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1766, 1)]

def rawRow2021 : Integer.Sparse Key := [(key1532, -2), (key1527, -2), (key1532, -2), (key1610, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1257, 2), (key1252, 2), (key1257, 2), (key1610, -1), (key1605, -1), (key1807, -1), (key1605, -1), (key1807, -1), (key1610, -1), (key1257, -1), (key1252, -1), (key1266, -1), (key1252, -1), (key1266, -1), (key1257, -1), (key1532, 1), (key1527, 1), (key1766, 1), (key1527, 1), (key1766, 1), (key1532, 1)]

def rawRow2022 : Integer.Sparse Key := [(key1532, -2), (key1532, -2), (key1527, -2), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1257, 2), (key1257, 2), (key1252, 2), (key1807, -1), (key1807, -1), (key1610, -1), (key1610, -1), (key1605, -1), (key1605, -1), (key1266, -1), (key1266, -1), (key1257, -1), (key1257, -1), (key1252, -1), (key1252, -1), (key1766, 1), (key1766, 1), (key1532, 1), (key1532, 1), (key1527, 1), (key1527, 1)]

def rawRow2023 : Integer.Sparse Key := [(key1649, -2), (key1649, -2), (key1672, -2), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1807, 2), (key1807, 2), (key1830, 2), (key1257, -1), (key1257, -1), (key1610, -1), (key1610, -1), (key1638, -1), (key1638, -1), (key1766, -1), (key1766, -1), (key1807, -1), (key1807, -1), (key1830, -1), (key1830, -1), (key1266, 1), (key1266, 1), (key1649, 1), (key1649, 1), (key1672, 1), (key1672, 1)]

def rawRow2024 : Integer.Sparse Key := [(key1649, -2), (key1672, -2), (key1649, -2), (key1610, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1807, 2), (key1830, 2), (key1807, 2), (key1610, -1), (key1638, -1), (key1257, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1807, -1), (key1830, -1), (key1766, -1), (key1830, -1), (key1766, -1), (key1807, -1), (key1649, 1), (key1672, 1), (key1266, 1), (key1672, 1), (key1266, 1), (key1649, 1)]

def rawRow2025 : Integer.Sparse Key := [(key1672, -2), (key1649, -2), (key1649, -2), (key1638, 1), (key1610, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1532, 1), (key1830, 2), (key1807, 2), (key1807, 2), (key1638, -1), (key1610, -1), (key1638, -1), (key1257, -1), (key1610, -1), (key1257, -1), (key1830, -1), (key1807, -1), (key1830, -1), (key1766, -1), (key1807, -1), (key1766, -1), (key1672, 1), (key1649, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1266, 1)]

def rawRow2026 : Integer.Sparse Key := [(key1766, -2), (key1766, -2), (key1766, -2), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1266, 2), (key1266, 2), (key1266, 2), (key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1649, -1), (key1257, -1), (key1257, -1), (key1257, -1), (key1257, -1), (key1257, -1), (key1257, -1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1)]

def rawRow2027 : Integer.Sparse Key := [(key1807, -2), (key1807, -2), (key1830, -2), (key1766, 1), (key1766, 1), (key1807, 1), (key1807, 1), (key1830, 1), (key1830, 1), (key1649, 2), (key1649, 2), (key1672, 2), (key1266, -1), (key1266, -1), (key1649, -1), (key1649, -1), (key1672, -1), (key1672, -1), (key1532, -1), (key1532, -1), (key1610, -1), (key1610, -1), (key1638, -1), (key1638, -1), (key1257, 1), (key1257, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1)]

def rawRow2028 : Integer.Sparse Key := [(key1807, -2), (key1830, -2), (key1807, -2), (key1807, 1), (key1830, 1), (key1766, 1), (key1830, 1), (key1766, 1), (key1807, 1), (key1649, 2), (key1672, 2), (key1649, 2), (key1649, -1), (key1672, -1), (key1266, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1610, -1), (key1638, -1), (key1532, -1), (key1638, -1), (key1532, -1), (key1610, -1), (key1610, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1610, 1)]

def rawRow2029 : Integer.Sparse Key := [(key1830, -2), (key1807, -2), (key1807, -2), (key1830, 1), (key1807, 1), (key1830, 1), (key1766, 1), (key1807, 1), (key1766, 1), (key1672, 2), (key1649, 2), (key1649, 2), (key1672, -1), (key1649, -1), (key1672, -1), (key1266, -1), (key1649, -1), (key1266, -1), (key1638, -1), (key1610, -1), (key1638, -1), (key1532, -1), (key1610, -1), (key1532, -1), (key1638, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1257, 1)]

def rawRow2030 : Integer.Sparse Key := [(key971, -2), (key975, -2), (key975, -2), (key975, 6), (key1085, 2), (key1089, 2), (key1089, 2), (key1089, -2), (key1089, -2), (key1179, -2), (key1161, -6), (key1161, 2), (key1161, 2), (key1217, 2)]

def rawRow2031 : Integer.Sparse Key := [(key975, -2), (key971, -2), (key975, -2), (key975, 6), (key1089, 2), (key1085, 2), (key1089, 2), (key1089, -2), (key1179, -2), (key1089, -2), (key1161, -6), (key1161, 2), (key1217, 2), (key1161, 2)]

def rawRow2032 : Integer.Sparse Key := [(key975, -2), (key975, -2), (key971, -2), (key975, 6), (key1089, 2), (key1089, 2), (key1085, 2), (key1179, -2), (key1089, -2), (key1089, -2), (key1161, -6), (key1217, 2), (key1161, 2), (key1161, 2)]

def rawRow2033 : Integer.Sparse Key := [(key975, -2), (key975, -2), (key975, -2), (key971, 6), (key1179, 2), (key1179, 2), (key1179, 2), (key1085, -2), (key1085, -2), (key1085, -2), (key1217, -6), (key1161, 2), (key1161, 2), (key1161, 2)]

def rawRow2034 : Integer.Sparse Key := [(key1085, -2), (key1089, -2), (key1089, -2), (key1161, 6), (key971, 2), (key975, 2), (key975, 2), (key1161, -2), (key1161, -2), (key1217, -2), (key975, -6), (key1089, 2), (key1089, 2), (key1179, 2)]

def rawRow2035 : Integer.Sparse Key := [(key1089, -2), (key1085, -2), (key1089, -2), (key1161, 6), (key975, 2), (key971, 2), (key975, 2), (key1161, -2), (key1217, -2), (key1161, -2), (key975, -6), (key1089, 2), (key1179, 2), (key1089, 2)]

def rawRow2036 : Integer.Sparse Key := [(key1089, -2), (key1089, -2), (key1085, -2), (key1161, 6), (key975, 2), (key975, 2), (key971, 2), (key1217, -2), (key1161, -2), (key1161, -2), (key975, -6), (key1179, 2), (key1089, 2), (key1089, 2)]

def rawRow2037 : Integer.Sparse Key := [(key1089, -2), (key1089, -2), (key1161, -2), (key1085, 6), (key1179, 2), (key1179, 2), (key1217, 2), (key971, -2), (key1085, -2), (key1085, -2), (key1179, -6), (key975, 2), (key1089, 2), (key1089, 2)]

def rawRow2038 : Integer.Sparse Key := [(key1089, -2), (key1161, -2), (key1089, -2), (key1085, 6), (key1179, 2), (key1217, 2), (key1179, 2), (key1085, -2), (key971, -2), (key1085, -2), (key1179, -6), (key1089, 2), (key975, 2), (key1089, 2)]

def rawRow2039 : Integer.Sparse Key := [(key1161, -2), (key1089, -2), (key1089, -2), (key1085, 6), (key1217, 2), (key1179, 2), (key1179, 2), (key1085, -2), (key1085, -2), (key971, -2), (key1179, -6), (key1089, 2), (key1089, 2), (key975, 2)]

def rawRow2040 : Integer.Sparse Key := [(key1179, -2), (key1179, -2), (key1179, -2), (key1217, 6), (key975, 2), (key975, 2), (key975, 2), (key1161, -2), (key1161, -2), (key1161, -2), (key971, -6), (key1085, 2), (key1085, 2), (key1085, 2)]

def rawRow2041 : Integer.Sparse Key := [(key1179, -2), (key1179, -2), (key1217, -2), (key1179, 6), (key1089, 2), (key1089, 2), (key1161, 2), (key975, -2), (key1089, -2), (key1089, -2), (key1085, -6), (key971, 2), (key1085, 2), (key1085, 2)]

def rawRow2042 : Integer.Sparse Key := [(key1179, -2), (key1217, -2), (key1179, -2), (key1179, 6), (key1089, 2), (key1161, 2), (key1089, 2), (key1089, -2), (key975, -2), (key1089, -2), (key1085, -6), (key1085, 2), (key971, 2), (key1085, 2)]

def rawRow2043 : Integer.Sparse Key := [(key1217, -2), (key1179, -2), (key1179, -2), (key1179, 6), (key1161, 2), (key1089, 2), (key1089, 2), (key1089, -2), (key1089, -2), (key975, -2), (key1085, -6), (key1085, 2), (key1085, 2), (key971, 2)]

def rawRow2044 : Integer.Sparse Key := [(key2591, -2), (key2591, -2), (key2601, -2), (key2591, 1), (key2594, 1), (key2591, 1), (key2601, 1), (key2594, 1), (key2601, 1), (key2847, 2), (key2847, 2), (key2890, 2), (key2847, -1), (key2890, -1), (key2847, -1), (key2969, -1), (key2890, -1), (key2969, -1), (key2878, -1), (key2881, -1), (key2878, -1), (key2911, -1), (key2881, -1), (key2911, -1), (key2878, 1), (key2911, 1), (key2878, 1), (key2990, 1), (key2911, 1), (key2990, 1)]

def rawRow2045 : Integer.Sparse Key := [(key2591, -2), (key2601, -2), (key2591, -2), (key2594, 1), (key2591, 1), (key2601, 1), (key2591, 1), (key2601, 1), (key2594, 1), (key2847, 2), (key2890, 2), (key2847, 2), (key2890, -1), (key2847, -1), (key2969, -1), (key2847, -1), (key2969, -1), (key2890, -1), (key2881, -1), (key2878, -1), (key2911, -1), (key2878, -1), (key2911, -1), (key2881, -1), (key2911, 1), (key2878, 1), (key2990, 1), (key2878, 1), (key2990, 1), (key2911, 1)]

def rawRow2046 : Integer.Sparse Key := [(key2601, -2), (key2591, -2), (key2591, -2), (key2601, 1), (key2601, 1), (key2594, 1), (key2594, 1), (key2591, 1), (key2591, 1), (key2890, 2), (key2847, 2), (key2847, 2), (key2969, -1), (key2969, -1), (key2890, -1), (key2890, -1), (key2847, -1), (key2847, -1), (key2911, -1), (key2911, -1), (key2881, -1), (key2881, -1), (key2878, -1), (key2878, -1), (key2990, 1), (key2990, 1), (key2911, 1), (key2911, 1), (key2878, 1), (key2878, 1)]

def rawRow2047 : Integer.Sparse Key := [(key2594, -2), (key2594, -2), (key2594, -2), (key2591, 1), (key2591, 1), (key2591, 1), (key2591, 1), (key2591, 1), (key2591, 1), (key2969, 2), (key2969, 2), (key2969, 2), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2847, -1), (key2990, -1), (key2990, -1), (key2990, -1), (key2990, -1), (key2990, -1), (key2990, -1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1), (key2881, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2048 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2890, -2), (key2878, 1), (key2881, 1), (key2878, 1), (key2911, 1), (key2881, 1), (key2911, 1), (key2591, 2), (key2591, 2), (key2601, 2), (key2878, -1), (key2911, -1), (key2878, -1), (key2990, -1), (key2911, -1), (key2990, -1), (key2591, -1), (key2594, -1), (key2591, -1), (key2601, -1), (key2594, -1), (key2601, -1), (key2847, 1), (key2890, 1), (key2847, 1), (key2969, 1), (key2890, 1), (key2969, 1)]

def rawRow2049 : Integer.Sparse Key := [(key2847, -2), (key2890, -2), (key2847, -2), (key2881, 1), (key2878, 1), (key2911, 1), (key2878, 1), (key2911, 1), (key2881, 1), (key2591, 2), (key2601, 2), (key2591, 2), (key2911, -1), (key2878, -1), (key2990, -1), (key2878, -1), (key2990, -1), (key2911, -1), (key2594, -1), (key2591, -1), (key2601, -1), (key2591, -1), (key2601, -1), (key2594, -1), (key2890, 1), (key2847, 1), (key2969, 1), (key2847, 1), (key2969, 1), (key2890, 1)]

def rawRow2050 : Integer.Sparse Key := [(key2890, -2), (key2847, -2), (key2847, -2), (key2911, 1), (key2911, 1), (key2881, 1), (key2881, 1), (key2878, 1), (key2878, 1), (key2601, 2), (key2591, 2), (key2591, 2), (key2990, -1), (key2990, -1), (key2911, -1), (key2911, -1), (key2878, -1), (key2878, -1), (key2601, -1), (key2601, -1), (key2594, -1), (key2594, -1), (key2591, -1), (key2591, -1), (key2969, 1), (key2969, 1), (key2890, 1), (key2890, 1), (key2847, 1), (key2847, 1)]

def rawRow2051 : Integer.Sparse Key := [(key2773, -2), (key2881, -2), (key2881, -2), (key2770, 1), (key2770, 1), (key2847, 1), (key2847, 1), (key2878, 1), (key2878, 1), (key2932, 2), (key2990, 2), (key2990, 2), (key2591, -1), (key2591, -1), (key2770, -1), (key2770, -1), (key2878, -1), (key2878, -1), (key2932, -1), (key2932, -1), (key2969, -1), (key2969, -1), (key2990, -1), (key2990, -1), (key2594, 1), (key2594, 1), (key2773, 1), (key2773, 1), (key2881, 1), (key2881, 1)]

def rawRow2052 : Integer.Sparse Key := [(key2881, -2), (key2773, -2), (key2881, -2), (key2847, 1), (key2878, 1), (key2770, 1), (key2878, 1), (key2770, 1), (key2847, 1), (key2990, 2), (key2932, 2), (key2990, 2), (key2770, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2969, -1), (key2990, -1), (key2932, -1), (key2990, -1), (key2932, -1), (key2969, -1), (key2773, 1), (key2881, 1), (key2594, 1), (key2881, 1), (key2594, 1), (key2773, 1)]

def rawRow2053 : Integer.Sparse Key := [(key2881, -2), (key2881, -2), (key2773, -2), (key2878, 1), (key2847, 1), (key2878, 1), (key2770, 1), (key2847, 1), (key2770, 1), (key2990, 2), (key2990, 2), (key2932, 2), (key2878, -1), (key2770, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2591, -1), (key2990, -1), (key2969, -1), (key2990, -1), (key2932, -1), (key2969, -1), (key2932, -1), (key2881, 1), (key2773, 1), (key2881, 1), (key2594, 1), (key2773, 1), (key2594, 1)]

def rawRow2054 : Integer.Sparse Key := [(key2969, -2), (key2969, -2), (key2969, -2), (key2990, 1), (key2990, 1), (key2990, 1), (key2990, 1), (key2990, 1), (key2990, 1), (key2594, 2), (key2594, 2), (key2594, 2), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1)]

def rawRow2055 : Integer.Sparse Key := [(key2932, -2), (key2990, -2), (key2990, -2), (key2932, 1), (key2932, 1), (key2969, 1), (key2969, 1), (key2990, 1), (key2990, 1), (key2773, 2), (key2881, 2), (key2881, 2), (key2594, -1), (key2594, -1), (key2773, -1), (key2773, -1), (key2881, -1), (key2881, -1), (key2770, -1), (key2770, -1), (key2847, -1), (key2847, -1), (key2878, -1), (key2878, -1), (key2591, 1), (key2591, 1), (key2770, 1), (key2770, 1), (key2878, 1), (key2878, 1)]

def rawRow2056 : Integer.Sparse Key := [(key2990, -2), (key2932, -2), (key2990, -2), (key2969, 1), (key2990, 1), (key2932, 1), (key2990, 1), (key2932, 1), (key2969, 1), (key2881, 2), (key2773, 2), (key2881, 2), (key2773, -1), (key2881, -1), (key2594, -1), (key2881, -1), (key2594, -1), (key2773, -1), (key2847, -1), (key2878, -1), (key2770, -1), (key2878, -1), (key2770, -1), (key2847, -1), (key2770, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2770, 1)]

def rawRow2057 : Integer.Sparse Key := [(key2990, -2), (key2990, -2), (key2932, -2), (key2990, 1), (key2969, 1), (key2990, 1), (key2932, 1), (key2969, 1), (key2932, 1), (key2881, 2), (key2881, 2), (key2773, 2), (key2881, -1), (key2773, -1), (key2881, -1), (key2594, -1), (key2773, -1), (key2594, -1), (key2878, -1), (key2847, -1), (key2878, -1), (key2770, -1), (key2847, -1), (key2770, -1), (key2878, 1), (key2770, 1), (key2878, 1), (key2591, 1), (key2770, 1), (key2591, 1)]

def rawRow2058 : Integer.Sparse Key := [(key2354, -2), (key2358, -2), (key2358, -2), (key2358, 6), (key2449, 2), (key2453, 2), (key2453, 2), (key2453, -2), (key2453, -2), (key2529, -2), (key2514, -6), (key2514, 2), (key2514, 2), (key2559, 2)]

def rawRow2059 : Integer.Sparse Key := [(key2358, -2), (key2354, -2), (key2358, -2), (key2358, 6), (key2453, 2), (key2449, 2), (key2453, 2), (key2453, -2), (key2529, -2), (key2453, -2), (key2514, -6), (key2514, 2), (key2559, 2), (key2514, 2)]

def rawRow2060 : Integer.Sparse Key := [(key2358, -2), (key2358, -2), (key2354, -2), (key2358, 6), (key2453, 2), (key2453, 2), (key2449, 2), (key2529, -2), (key2453, -2), (key2453, -2), (key2514, -6), (key2559, 2), (key2514, 2), (key2514, 2)]

def rawRow2061 : Integer.Sparse Key := [(key2358, -2), (key2358, -2), (key2358, -2), (key2354, 6), (key2529, 2), (key2529, 2), (key2529, 2), (key2449, -2), (key2449, -2), (key2449, -2), (key2559, -6), (key2514, 2), (key2514, 2), (key2514, 2)]

def rawRow2062 : Integer.Sparse Key := [(key2449, -2), (key2453, -2), (key2453, -2), (key2514, 6), (key2354, 2), (key2358, 2), (key2358, 2), (key2514, -2), (key2514, -2), (key2559, -2), (key2358, -6), (key2453, 2), (key2453, 2), (key2529, 2)]

def rawRow2063 : Integer.Sparse Key := [(key2453, -2), (key2449, -2), (key2453, -2), (key2514, 6), (key2358, 2), (key2354, 2), (key2358, 2), (key2514, -2), (key2559, -2), (key2514, -2), (key2358, -6), (key2453, 2), (key2529, 2), (key2453, 2)]

def rawRow2064 : Integer.Sparse Key := [(key2453, -2), (key2453, -2), (key2449, -2), (key2514, 6), (key2358, 2), (key2358, 2), (key2354, 2), (key2559, -2), (key2514, -2), (key2514, -2), (key2358, -6), (key2529, 2), (key2453, 2), (key2453, 2)]

def rawRow2065 : Integer.Sparse Key := [(key2453, -2), (key2453, -2), (key2514, -2), (key2449, 6), (key2529, 2), (key2529, 2), (key2559, 2), (key2354, -2), (key2449, -2), (key2449, -2), (key2529, -6), (key2358, 2), (key2453, 2), (key2453, 2)]

def rawRow2066 : Integer.Sparse Key := [(key2453, -2), (key2514, -2), (key2453, -2), (key2449, 6), (key2529, 2), (key2559, 2), (key2529, 2), (key2449, -2), (key2354, -2), (key2449, -2), (key2529, -6), (key2453, 2), (key2358, 2), (key2453, 2)]

def rawRow2067 : Integer.Sparse Key := [(key2514, -2), (key2453, -2), (key2453, -2), (key2449, 6), (key2559, 2), (key2529, 2), (key2529, 2), (key2449, -2), (key2449, -2), (key2354, -2), (key2529, -6), (key2453, 2), (key2453, 2), (key2358, 2)]

def rawRow2068 : Integer.Sparse Key := [(key2529, -2), (key2529, -2), (key2529, -2), (key2559, 6), (key2358, 2), (key2358, 2), (key2358, 2), (key2514, -2), (key2514, -2), (key2514, -2), (key2354, -6), (key2449, 2), (key2449, 2), (key2449, 2)]

def rawRow2069 : Integer.Sparse Key := [(key2529, -2), (key2529, -2), (key2559, -2), (key2529, 6), (key2453, 2), (key2453, 2), (key2514, 2), (key2358, -2), (key2453, -2), (key2453, -2), (key2449, -6), (key2354, 2), (key2449, 2), (key2449, 2)]

def rawRow2070 : Integer.Sparse Key := [(key2529, -2), (key2559, -2), (key2529, -2), (key2529, 6), (key2453, 2), (key2514, 2), (key2453, 2), (key2453, -2), (key2358, -2), (key2453, -2), (key2449, -6), (key2449, 2), (key2354, 2), (key2449, 2)]

def rawRow2071 : Integer.Sparse Key := [(key2559, -2), (key2529, -2), (key2529, -2), (key2529, 6), (key2514, 2), (key2453, 2), (key2453, 2), (key2453, -2), (key2453, -2), (key2358, -2), (key2449, -6), (key2449, 2), (key2449, 2), (key2354, 2)]

def rawRow2072 : Integer.Sparse Key := [(key2353, -2), (key2356, -2), (key2356, -2), (key2356, 6), (key2448, 2), (key2451, 2), (key2451, 2), (key2451, -2), (key2451, -2), (key2513, -2), (key2527, -6), (key2527, 2), (key2527, 2), (key2558, 2)]

def rawRow2073 : Integer.Sparse Key := [(key2356, -2), (key2353, -2), (key2356, -2), (key2356, 6), (key2451, 2), (key2448, 2), (key2451, 2), (key2451, -2), (key2513, -2), (key2451, -2), (key2527, -6), (key2527, 2), (key2558, 2), (key2527, 2)]

def rawRow2074 : Integer.Sparse Key := [(key2356, -2), (key2356, -2), (key2353, -2), (key2356, 6), (key2451, 2), (key2451, 2), (key2448, 2), (key2513, -2), (key2451, -2), (key2451, -2), (key2527, -6), (key2558, 2), (key2527, 2), (key2527, 2)]

def rawRow2075 : Integer.Sparse Key := [(key2356, -2), (key2356, -2), (key2356, -2), (key2353, 6), (key2513, 2), (key2513, 2), (key2513, 2), (key2448, -2), (key2448, -2), (key2448, -2), (key2558, -6), (key2527, 2), (key2527, 2), (key2527, 2)]

def rawRow2076 : Integer.Sparse Key := [(key2448, -2), (key2451, -2), (key2451, -2), (key2513, 6), (key2353, 2), (key2356, 2), (key2356, 2), (key2527, -2), (key2527, -2), (key2558, -2), (key2356, -6), (key2451, 2), (key2451, 2), (key2513, 2)]

def rawRow2077 : Integer.Sparse Key := [(key2451, -2), (key2448, -2), (key2451, -2), (key2513, 6), (key2356, 2), (key2353, 2), (key2356, 2), (key2527, -2), (key2558, -2), (key2527, -2), (key2356, -6), (key2451, 2), (key2513, 2), (key2451, 2)]

def rawRow2078 : Integer.Sparse Key := [(key2451, -2), (key2451, -2), (key2448, -2), (key2513, 6), (key2356, 2), (key2356, 2), (key2353, 2), (key2558, -2), (key2527, -2), (key2527, -2), (key2356, -6), (key2513, 2), (key2451, 2), (key2451, 2)]

def rawRow2079 : Integer.Sparse Key := [(key2451, -2), (key2451, -2), (key2513, -2), (key2448, 6), (key2527, 2), (key2527, 2), (key2558, 2), (key2353, -2), (key2448, -2), (key2448, -2), (key2513, -6), (key2356, 2), (key2451, 2), (key2451, 2)]

def rawRow2080 : Integer.Sparse Key := [(key2451, -2), (key2513, -2), (key2451, -2), (key2448, 6), (key2527, 2), (key2558, 2), (key2527, 2), (key2448, -2), (key2353, -2), (key2448, -2), (key2513, -6), (key2451, 2), (key2356, 2), (key2451, 2)]

def rawRow2081 : Integer.Sparse Key := [(key2513, -2), (key2451, -2), (key2451, -2), (key2448, 6), (key2558, 2), (key2527, 2), (key2527, 2), (key2448, -2), (key2448, -2), (key2353, -2), (key2513, -6), (key2451, 2), (key2451, 2), (key2356, 2)]

def rawRow2082 : Integer.Sparse Key := [(key2527, -2), (key2527, -2), (key2527, -2), (key2558, 6), (key2356, 2), (key2356, 2), (key2356, 2), (key2513, -2), (key2513, -2), (key2513, -2), (key2353, -6), (key2448, 2), (key2448, 2), (key2448, 2)]

def rawRow2083 : Integer.Sparse Key := [(key2527, -2), (key2527, -2), (key2558, -2), (key2527, 6), (key2451, 2), (key2451, 2), (key2513, 2), (key2356, -2), (key2451, -2), (key2451, -2), (key2448, -6), (key2353, 2), (key2448, 2), (key2448, 2)]

def rawRow2084 : Integer.Sparse Key := [(key2527, -2), (key2558, -2), (key2527, -2), (key2527, 6), (key2451, 2), (key2513, 2), (key2451, 2), (key2451, -2), (key2356, -2), (key2451, -2), (key2448, -6), (key2448, 2), (key2353, 2), (key2448, 2)]

def rawRow2085 : Integer.Sparse Key := [(key2558, -2), (key2527, -2), (key2527, -2), (key2527, 6), (key2513, 2), (key2451, 2), (key2451, 2), (key2451, -2), (key2451, -2), (key2356, -2), (key2448, -6), (key2448, 2), (key2448, 2), (key2353, 2)]

def rawRow2086 : Integer.Sparse Key := [(key2786, -2), (key2786, -2), (key2939, -2), (key2794, 1), (key2796, 1), (key2794, 1), (key2944, 1), (key2796, 1), (key2944, 1), (key2809, 2), (key2809, 2), (key2951, 2), (key2860, -1), (key2898, -1), (key2860, -1), (key2977, -1), (key2898, -1), (key2977, -1), (key2829, -1), (key2832, -1), (key2829, -1), (key2961, -1), (key2832, -1), (key2961, -1), (key2870, 1), (key2905, 1), (key2870, 1), (key2984, 1), (key2905, 1), (key2984, 1)]

def rawRow2087 : Integer.Sparse Key := [(key2786, -2), (key2939, -2), (key2786, -2), (key2796, 1), (key2794, 1), (key2944, 1), (key2794, 1), (key2944, 1), (key2796, 1), (key2809, 2), (key2951, 2), (key2809, 2), (key2898, -1), (key2860, -1), (key2977, -1), (key2860, -1), (key2977, -1), (key2898, -1), (key2832, -1), (key2829, -1), (key2961, -1), (key2829, -1), (key2961, -1), (key2832, -1), (key2905, 1), (key2870, 1), (key2984, 1), (key2870, 1), (key2984, 1), (key2905, 1)]

def rawRow2088 : Integer.Sparse Key := [(key2939, -2), (key2786, -2), (key2786, -2), (key2944, 1), (key2944, 1), (key2796, 1), (key2796, 1), (key2794, 1), (key2794, 1), (key2951, 2), (key2809, 2), (key2809, 2), (key2977, -1), (key2977, -1), (key2898, -1), (key2898, -1), (key2860, -1), (key2860, -1), (key2961, -1), (key2961, -1), (key2832, -1), (key2832, -1), (key2829, -1), (key2829, -1), (key2984, 1), (key2984, 1), (key2905, 1), (key2905, 1), (key2870, 1), (key2870, 1)]

def rawRow2089 : Integer.Sparse Key := [(key2671, -2), (key2794, -2), (key2944, -2), (key2671, 1), (key2674, 1), (key2786, 1), (key2939, 1), (key2796, 1), (key2944, 1), (key2706, 2), (key2860, 2), (key2977, 2), (key2706, -1), (key2738, -1), (key2809, -1), (key2951, -1), (key2898, -1), (key2977, -1), (key2726, -1), (key2729, -1), (key2870, -1), (key2984, -1), (key2883, -1), (key2992, -1), (key2726, 1), (key2748, 1), (key2829, 1), (key2961, 1), (key2913, 1), (key2992, 1)]

def rawRow2090 : Integer.Sparse Key := [(key2671, -2), (key2944, -2), (key2794, -2), (key2674, 1), (key2671, 1), (key2939, 1), (key2786, 1), (key2944, 1), (key2796, 1), (key2706, 2), (key2977, 2), (key2860, 2), (key2738, -1), (key2706, -1), (key2951, -1), (key2809, -1), (key2977, -1), (key2898, -1), (key2729, -1), (key2726, -1), (key2984, -1), (key2870, -1), (key2992, -1), (key2883, -1), (key2748, 1), (key2726, 1), (key2961, 1), (key2829, 1), (key2992, 1), (key2913, 1)]

def rawRow2091 : Integer.Sparse Key := [(key2794, -2), (key2671, -2), (key2944, -2), (key2786, 1), (key2796, 1), (key2671, 1), (key2944, 1), (key2674, 1), (key2939, 1), (key2860, 2), (key2706, 2), (key2977, 2), (key2809, -1), (key2898, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2870, -1), (key2883, -1), (key2726, -1), (key2992, -1), (key2729, -1), (key2984, -1), (key2829, 1), (key2913, 1), (key2726, 1), (key2992, 1), (key2748, 1), (key2961, 1)]

def rawRow2092 : Integer.Sparse Key := [(key2794, -2), (key2944, -2), (key2671, -2), (key2796, 1), (key2786, 1), (key2944, 1), (key2671, 1), (key2939, 1), (key2674, 1), (key2860, 2), (key2977, 2), (key2706, 2), (key2898, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2951, -1), (key2738, -1), (key2883, -1), (key2870, -1), (key2992, -1), (key2726, -1), (key2984, -1), (key2729, -1), (key2913, 1), (key2829, 1), (key2992, 1), (key2726, 1), (key2961, 1), (key2748, 1)]

def rawRow2093 : Integer.Sparse Key := [(key2944, -2), (key2671, -2), (key2794, -2), (key2939, 1), (key2944, 1), (key2674, 1), (key2796, 1), (key2671, 1), (key2786, 1), (key2977, 2), (key2706, 2), (key2860, 2), (key2951, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2706, -1), (key2809, -1), (key2984, -1), (key2992, -1), (key2729, -1), (key2883, -1), (key2726, -1), (key2870, -1), (key2961, 1), (key2992, 1), (key2748, 1), (key2913, 1), (key2726, 1), (key2829, 1)]

def rawRow2094 : Integer.Sparse Key := [(key2944, -2), (key2794, -2), (key2671, -2), (key2944, 1), (key2939, 1), (key2796, 1), (key2674, 1), (key2786, 1), (key2671, 1), (key2977, 2), (key2860, 2), (key2706, 2), (key2977, -1), (key2951, -1), (key2898, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2992, -1), (key2984, -1), (key2883, -1), (key2729, -1), (key2870, -1), (key2726, -1), (key2992, 1), (key2961, 1), (key2913, 1), (key2748, 1), (key2829, 1), (key2726, 1)]

def rawRow2095 : Integer.Sparse Key := [(key2809, -2), (key2809, -2), (key2951, -2), (key2829, 1), (key2832, 1), (key2829, 1), (key2961, 1), (key2832, 1), (key2961, 1), (key2786, 2), (key2786, 2), (key2939, 2), (key2870, -1), (key2905, -1), (key2870, -1), (key2984, -1), (key2905, -1), (key2984, -1), (key2794, -1), (key2796, -1), (key2794, -1), (key2944, -1), (key2796, -1), (key2944, -1), (key2860, 1), (key2898, 1), (key2860, 1), (key2977, 1), (key2898, 1), (key2977, 1)]

def rawRow2096 : Integer.Sparse Key := [(key2809, -2), (key2951, -2), (key2809, -2), (key2832, 1), (key2829, 1), (key2961, 1), (key2829, 1), (key2961, 1), (key2832, 1), (key2786, 2), (key2939, 2), (key2786, 2), (key2905, -1), (key2870, -1), (key2984, -1), (key2870, -1), (key2984, -1), (key2905, -1), (key2796, -1), (key2794, -1), (key2944, -1), (key2794, -1), (key2944, -1), (key2796, -1), (key2898, 1), (key2860, 1), (key2977, 1), (key2860, 1), (key2977, 1), (key2898, 1)]

def rawRow2097 : Integer.Sparse Key := [(key2951, -2), (key2809, -2), (key2809, -2), (key2961, 1), (key2961, 1), (key2832, 1), (key2832, 1), (key2829, 1), (key2829, 1), (key2939, 2), (key2786, 2), (key2786, 2), (key2984, -1), (key2984, -1), (key2905, -1), (key2905, -1), (key2870, -1), (key2870, -1), (key2944, -1), (key2944, -1), (key2796, -1), (key2796, -1), (key2794, -1), (key2794, -1), (key2977, 1), (key2977, 1), (key2898, 1), (key2898, 1), (key2860, 1), (key2860, 1)]

def rawRow2098 : Integer.Sparse Key := [(key2616, -2), (key2829, -2), (key2961, -2), (key2616, 1), (key2619, 1), (key2809, 1), (key2951, 1), (key2832, 1), (key2961, 1), (key2632, 2), (key2870, 2), (key2984, 2), (key2632, -1), (key2649, -1), (key2786, -1), (key2939, -1), (key2905, -1), (key2984, -1), (key2640, -1), (key2642, -1), (key2860, -1), (key2977, -1), (key2883, -1), (key2992, -1), (key2640, 1), (key2654, 1), (key2794, 1), (key2944, 1), (key2913, 1), (key2992, 1)]

def rawRow2099 : Integer.Sparse Key := [(key2616, -2), (key2961, -2), (key2829, -2), (key2619, 1), (key2616, 1), (key2951, 1), (key2809, 1), (key2961, 1), (key2832, 1), (key2632, 2), (key2984, 2), (key2870, 2), (key2649, -1), (key2632, -1), (key2939, -1), (key2786, -1), (key2984, -1), (key2905, -1), (key2642, -1), (key2640, -1), (key2977, -1), (key2860, -1), (key2992, -1), (key2883, -1), (key2654, 1), (key2640, 1), (key2944, 1), (key2794, 1), (key2992, 1), (key2913, 1)]

def rawRow2100 : Integer.Sparse Key := [(key2829, -2), (key2616, -2), (key2961, -2), (key2809, 1), (key2832, 1), (key2616, 1), (key2961, 1), (key2619, 1), (key2951, 1), (key2870, 2), (key2632, 2), (key2984, 2), (key2786, -1), (key2905, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2860, -1), (key2883, -1), (key2640, -1), (key2992, -1), (key2642, -1), (key2977, -1), (key2794, 1), (key2913, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2944, 1)]

def rawRow2101 : Integer.Sparse Key := [(key2829, -2), (key2961, -2), (key2616, -2), (key2832, 1), (key2809, 1), (key2961, 1), (key2616, 1), (key2951, 1), (key2619, 1), (key2870, 2), (key2984, 2), (key2632, 2), (key2905, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2939, -1), (key2649, -1), (key2883, -1), (key2860, -1), (key2992, -1), (key2640, -1), (key2977, -1), (key2642, -1), (key2913, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2944, 1), (key2654, 1)]

def rawRow2102 : Integer.Sparse Key := [(key2961, -2), (key2616, -2), (key2829, -2), (key2951, 1), (key2961, 1), (key2619, 1), (key2832, 1), (key2616, 1), (key2809, 1), (key2984, 2), (key2632, 2), (key2870, 2), (key2939, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2632, -1), (key2786, -1), (key2977, -1), (key2992, -1), (key2642, -1), (key2883, -1), (key2640, -1), (key2860, -1), (key2944, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2640, 1), (key2794, 1)]

def rawRow2103 : Integer.Sparse Key := [(key2961, -2), (key2829, -2), (key2616, -2), (key2961, 1), (key2951, 1), (key2832, 1), (key2619, 1), (key2809, 1), (key2616, 1), (key2984, 2), (key2870, 2), (key2632, 2), (key2984, -1), (key2939, -1), (key2905, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2992, -1), (key2977, -1), (key2883, -1), (key2642, -1), (key2860, -1), (key2640, -1), (key2992, 1), (key2944, 1), (key2913, 1), (key2654, 1), (key2794, 1), (key2640, 1)]

def rawRow2104 : Integer.Sparse Key := [(key2706, -2), (key2860, -2), (key2977, -2), (key2726, 1), (key2729, 1), (key2870, 1), (key2984, 1), (key2883, 1), (key2992, 1), (key2671, 2), (key2794, 2), (key2944, 2), (key2726, -1), (key2748, -1), (key2829, -1), (key2961, -1), (key2913, -1), (key2992, -1), (key2671, -1), (key2674, -1), (key2786, -1), (key2939, -1), (key2796, -1), (key2944, -1), (key2706, 1), (key2738, 1), (key2809, 1), (key2951, 1), (key2898, 1), (key2977, 1)]

def rawRow2105 : Integer.Sparse Key := [(key2706, -2), (key2977, -2), (key2860, -2), (key2729, 1), (key2726, 1), (key2984, 1), (key2870, 1), (key2992, 1), (key2883, 1), (key2671, 2), (key2944, 2), (key2794, 2), (key2748, -1), (key2726, -1), (key2961, -1), (key2829, -1), (key2992, -1), (key2913, -1), (key2674, -1), (key2671, -1), (key2939, -1), (key2786, -1), (key2944, -1), (key2796, -1), (key2738, 1), (key2706, 1), (key2951, 1), (key2809, 1), (key2977, 1), (key2898, 1)]

def rawRow2106 : Integer.Sparse Key := [(key2860, -2), (key2706, -2), (key2977, -2), (key2870, 1), (key2883, 1), (key2726, 1), (key2992, 1), (key2729, 1), (key2984, 1), (key2794, 2), (key2671, 2), (key2944, 2), (key2829, -1), (key2913, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2786, -1), (key2796, -1), (key2671, -1), (key2944, -1), (key2674, -1), (key2939, -1), (key2809, 1), (key2898, 1), (key2706, 1), (key2977, 1), (key2738, 1), (key2951, 1)]

def rawRow2107 : Integer.Sparse Key := [(key2860, -2), (key2977, -2), (key2706, -2), (key2883, 1), (key2870, 1), (key2992, 1), (key2726, 1), (key2984, 1), (key2729, 1), (key2794, 2), (key2944, 2), (key2671, 2), (key2913, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2961, -1), (key2748, -1), (key2796, -1), (key2786, -1), (key2944, -1), (key2671, -1), (key2939, -1), (key2674, -1), (key2898, 1), (key2809, 1), (key2977, 1), (key2706, 1), (key2951, 1), (key2738, 1)]

def rawRow2108 : Integer.Sparse Key := [(key2977, -2), (key2706, -2), (key2860, -2), (key2984, 1), (key2992, 1), (key2729, 1), (key2883, 1), (key2726, 1), (key2870, 1), (key2944, 2), (key2671, 2), (key2794, 2), (key2961, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2726, -1), (key2829, -1), (key2939, -1), (key2944, -1), (key2674, -1), (key2796, -1), (key2671, -1), (key2786, -1), (key2951, 1), (key2977, 1), (key2738, 1), (key2898, 1), (key2706, 1), (key2809, 1)]

def rawRow2109 : Integer.Sparse Key := [(key2977, -2), (key2860, -2), (key2706, -2), (key2992, 1), (key2984, 1), (key2883, 1), (key2729, 1), (key2870, 1), (key2726, 1), (key2944, 2), (key2794, 2), (key2671, 2), (key2992, -1), (key2961, -1), (key2913, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2944, -1), (key2939, -1), (key2796, -1), (key2674, -1), (key2786, -1), (key2671, -1), (key2977, 1), (key2951, 1), (key2898, 1), (key2738, 1), (key2809, 1), (key2706, 1)]

def rawRow2110 : Integer.Sparse Key := [(key2632, -2), (key2870, -2), (key2984, -2), (key2640, 1), (key2642, 1), (key2860, 1), (key2977, 1), (key2883, 1), (key2992, 1), (key2616, 2), (key2829, 2), (key2961, 2), (key2640, -1), (key2654, -1), (key2794, -1), (key2944, -1), (key2913, -1), (key2992, -1), (key2616, -1), (key2619, -1), (key2809, -1), (key2951, -1), (key2832, -1), (key2961, -1), (key2632, 1), (key2649, 1), (key2786, 1), (key2939, 1), (key2905, 1), (key2984, 1)]

def rawRow2111 : Integer.Sparse Key := [(key2632, -2), (key2984, -2), (key2870, -2), (key2642, 1), (key2640, 1), (key2977, 1), (key2860, 1), (key2992, 1), (key2883, 1), (key2616, 2), (key2961, 2), (key2829, 2), (key2654, -1), (key2640, -1), (key2944, -1), (key2794, -1), (key2992, -1), (key2913, -1), (key2619, -1), (key2616, -1), (key2951, -1), (key2809, -1), (key2961, -1), (key2832, -1), (key2649, 1), (key2632, 1), (key2939, 1), (key2786, 1), (key2984, 1), (key2905, 1)]

def rawRow2112 : Integer.Sparse Key := [(key2870, -2), (key2632, -2), (key2984, -2), (key2860, 1), (key2883, 1), (key2640, 1), (key2992, 1), (key2642, 1), (key2977, 1), (key2829, 2), (key2616, 2), (key2961, 2), (key2794, -1), (key2913, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2809, -1), (key2832, -1), (key2616, -1), (key2961, -1), (key2619, -1), (key2951, -1), (key2786, 1), (key2905, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2939, 1)]

def rawRow2113 : Integer.Sparse Key := [(key2870, -2), (key2984, -2), (key2632, -2), (key2883, 1), (key2860, 1), (key2992, 1), (key2640, 1), (key2977, 1), (key2642, 1), (key2829, 2), (key2961, 2), (key2616, 2), (key2913, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2944, -1), (key2654, -1), (key2832, -1), (key2809, -1), (key2961, -1), (key2616, -1), (key2951, -1), (key2619, -1), (key2905, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2939, 1), (key2649, 1)]

def rawRow2114 : Integer.Sparse Key := [(key2984, -2), (key2632, -2), (key2870, -2), (key2977, 1), (key2992, 1), (key2642, 1), (key2883, 1), (key2640, 1), (key2860, 1), (key2961, 2), (key2616, 2), (key2829, 2), (key2944, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2640, -1), (key2794, -1), (key2951, -1), (key2961, -1), (key2619, -1), (key2832, -1), (key2616, -1), (key2809, -1), (key2939, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2632, 1), (key2786, 1)]

def rawRow2115 : Integer.Sparse Key := [(key2984, -2), (key2870, -2), (key2632, -2), (key2992, 1), (key2977, 1), (key2883, 1), (key2642, 1), (key2860, 1), (key2640, 1), (key2961, 2), (key2829, 2), (key2616, 2), (key2992, -1), (key2944, -1), (key2913, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2961, -1), (key2951, -1), (key2832, -1), (key2619, -1), (key2809, -1), (key2616, -1), (key2984, 1), (key2939, 1), (key2905, 1), (key2649, 1), (key2786, 1), (key2632, 1)]

def rawRow2116 : Integer.Sparse Key := [(key1288, -6), (key1308, 2), (key1308, 2), (key1334, 2), (key1383, 6), (key1538, -2), (key1538, -2), (key1769, -2), (key1416, -2), (key1416, -2), (key1452, -2), (key1565, 2), (key1565, 2), (key1785, 2)]

def rawRow2117 : Integer.Sparse Key := [(key1288, -6), (key1308, 2), (key1334, 2), (key1308, 2), (key1383, 6), (key1538, -2), (key1769, -2), (key1538, -2), (key1416, -2), (key1452, -2), (key1416, -2), (key1565, 2), (key1785, 2), (key1565, 2)]

def rawRow2118 : Integer.Sparse Key := [(key1288, -6), (key1334, 2), (key1308, 2), (key1308, 2), (key1383, 6), (key1769, -2), (key1538, -2), (key1538, -2), (key1452, -2), (key1416, -2), (key1416, -2), (key1785, 2), (key1565, 2), (key1565, 2)]

def rawRow2119 : Integer.Sparse Key := [(key1308, -6), (key1288, 2), (key1308, 2), (key1334, 2), (key1538, 6), (key1383, -2), (key1538, -2), (key1769, -2), (key1565, -2), (key1614, -2), (key1652, -2), (key1416, 2), (key1614, 2), (key1810, 2)]

def rawRow2120 : Integer.Sparse Key := [(key1308, -6), (key1288, 2), (key1334, 2), (key1308, 2), (key1538, 6), (key1383, -2), (key1769, -2), (key1538, -2), (key1565, -2), (key1652, -2), (key1614, -2), (key1416, 2), (key1810, 2), (key1614, 2)]

def rawRow2121 : Integer.Sparse Key := [(key1308, -6), (key1308, 2), (key1288, 2), (key1334, 2), (key1538, 6), (key1538, -2), (key1383, -2), (key1769, -2), (key1614, -2), (key1565, -2), (key1652, -2), (key1614, 2), (key1416, 2), (key1810, 2)]

def rawRow2122 : Integer.Sparse Key := [(key1308, -6), (key1308, 2), (key1334, 2), (key1288, 2), (key1538, 6), (key1538, -2), (key1769, -2), (key1383, -2), (key1614, -2), (key1652, -2), (key1565, -2), (key1614, 2), (key1810, 2), (key1416, 2)]

def rawRow2123 : Integer.Sparse Key := [(key1308, -6), (key1334, 2), (key1288, 2), (key1308, 2), (key1538, 6), (key1769, -2), (key1383, -2), (key1538, -2), (key1652, -2), (key1565, -2), (key1614, -2), (key1810, 2), (key1416, 2), (key1614, 2)]

def rawRow2124 : Integer.Sparse Key := [(key1308, -6), (key1334, 2), (key1308, 2), (key1288, 2), (key1538, 6), (key1769, -2), (key1538, -2), (key1383, -2), (key1652, -2), (key1614, -2), (key1565, -2), (key1810, 2), (key1614, 2), (key1416, 2)]

def rawRow2125 : Integer.Sparse Key := [(key1383, -6), (key1416, 2), (key1416, 2), (key1452, 2), (key1288, 6), (key1565, -2), (key1565, -2), (key1785, -2), (key1308, -2), (key1308, -2), (key1334, -2), (key1538, 2), (key1538, 2), (key1769, 2)]

def rawRow2126 : Integer.Sparse Key := [(key1383, -6), (key1416, 2), (key1452, 2), (key1416, 2), (key1288, 6), (key1565, -2), (key1785, -2), (key1565, -2), (key1308, -2), (key1334, -2), (key1308, -2), (key1538, 2), (key1769, 2), (key1538, 2)]

def rawRow2127 : Integer.Sparse Key := [(key1383, -6), (key1452, 2), (key1416, 2), (key1416, 2), (key1288, 6), (key1785, -2), (key1565, -2), (key1565, -2), (key1334, -2), (key1308, -2), (key1308, -2), (key1769, 2), (key1538, 2), (key1538, 2)]

def rawRow2128 : Integer.Sparse Key := [(key1416, -6), (key1383, 2), (key1416, 2), (key1452, 2), (key1565, 6), (key1288, -2), (key1565, -2), (key1785, -2), (key1538, -2), (key1614, -2), (key1652, -2), (key1308, 2), (key1614, 2), (key1810, 2)]

def rawRow2129 : Integer.Sparse Key := [(key1416, -6), (key1383, 2), (key1452, 2), (key1416, 2), (key1565, 6), (key1288, -2), (key1785, -2), (key1565, -2), (key1538, -2), (key1652, -2), (key1614, -2), (key1308, 2), (key1810, 2), (key1614, 2)]

def rawRow2130 : Integer.Sparse Key := [(key1416, -6), (key1416, 2), (key1383, 2), (key1452, 2), (key1565, 6), (key1565, -2), (key1288, -2), (key1785, -2), (key1614, -2), (key1538, -2), (key1652, -2), (key1614, 2), (key1308, 2), (key1810, 2)]

def rawRow2131 : Integer.Sparse Key := [(key1416, -6), (key1416, 2), (key1452, 2), (key1383, 2), (key1565, 6), (key1565, -2), (key1785, -2), (key1288, -2), (key1614, -2), (key1652, -2), (key1538, -2), (key1614, 2), (key1810, 2), (key1308, 2)]

def rawRow2132 : Integer.Sparse Key := [(key1416, -6), (key1452, 2), (key1383, 2), (key1416, 2), (key1565, 6), (key1785, -2), (key1288, -2), (key1565, -2), (key1652, -2), (key1538, -2), (key1614, -2), (key1810, 2), (key1308, 2), (key1614, 2)]

def rawRow2133 : Integer.Sparse Key := [(key1416, -6), (key1452, 2), (key1416, 2), (key1383, 2), (key1565, 6), (key1785, -2), (key1565, -2), (key1288, -2), (key1652, -2), (key1614, -2), (key1538, -2), (key1810, 2), (key1614, 2), (key1308, 2)]

def rawRow2134 : Integer.Sparse Key := [(key1538, -6), (key1565, 2), (key1614, 2), (key1652, 2), (key1308, 6), (key1416, -2), (key1614, -2), (key1810, -2), (key1288, -2), (key1308, -2), (key1334, -2), (key1383, 2), (key1538, 2), (key1769, 2)]

def rawRow2135 : Integer.Sparse Key := [(key1538, -6), (key1565, 2), (key1652, 2), (key1614, 2), (key1308, 6), (key1416, -2), (key1810, -2), (key1614, -2), (key1288, -2), (key1334, -2), (key1308, -2), (key1383, 2), (key1769, 2), (key1538, 2)]

def rawRow2136 : Integer.Sparse Key := [(key1538, -6), (key1614, 2), (key1565, 2), (key1652, 2), (key1308, 6), (key1614, -2), (key1416, -2), (key1810, -2), (key1308, -2), (key1288, -2), (key1334, -2), (key1538, 2), (key1383, 2), (key1769, 2)]

def rawRow2137 : Integer.Sparse Key := [(key1538, -6), (key1614, 2), (key1652, 2), (key1565, 2), (key1308, 6), (key1614, -2), (key1810, -2), (key1416, -2), (key1308, -2), (key1334, -2), (key1288, -2), (key1538, 2), (key1769, 2), (key1383, 2)]

def rawRow2138 : Integer.Sparse Key := [(key1538, -6), (key1652, 2), (key1565, 2), (key1614, 2), (key1308, 6), (key1810, -2), (key1416, -2), (key1614, -2), (key1334, -2), (key1288, -2), (key1308, -2), (key1769, 2), (key1383, 2), (key1538, 2)]

def rawRow2139 : Integer.Sparse Key := [(key1538, -6), (key1652, 2), (key1614, 2), (key1565, 2), (key1308, 6), (key1810, -2), (key1614, -2), (key1416, -2), (key1334, -2), (key1308, -2), (key1288, -2), (key1769, 2), (key1538, 2), (key1383, 2)]

def rawRow2140 : Integer.Sparse Key := [(key1565, -6), (key1538, 2), (key1614, 2), (key1652, 2), (key1416, 6), (key1308, -2), (key1614, -2), (key1810, -2), (key1383, -2), (key1416, -2), (key1452, -2), (key1288, 2), (key1565, 2), (key1785, 2)]

def rawRow2141 : Integer.Sparse Key := [(key1565, -6), (key1538, 2), (key1652, 2), (key1614, 2), (key1416, 6), (key1308, -2), (key1810, -2), (key1614, -2), (key1383, -2), (key1452, -2), (key1416, -2), (key1288, 2), (key1785, 2), (key1565, 2)]

def rawRow2142 : Integer.Sparse Key := [(key1565, -6), (key1614, 2), (key1538, 2), (key1652, 2), (key1416, 6), (key1614, -2), (key1308, -2), (key1810, -2), (key1416, -2), (key1383, -2), (key1452, -2), (key1565, 2), (key1288, 2), (key1785, 2)]

def rawRow2143 : Integer.Sparse Key := [(key1565, -6), (key1614, 2), (key1652, 2), (key1538, 2), (key1416, 6), (key1614, -2), (key1810, -2), (key1308, -2), (key1416, -2), (key1452, -2), (key1383, -2), (key1565, 2), (key1785, 2), (key1288, 2)]

def rawRow2144 : Integer.Sparse Key := [(key1565, -6), (key1652, 2), (key1538, 2), (key1614, 2), (key1416, 6), (key1810, -2), (key1308, -2), (key1614, -2), (key1452, -2), (key1383, -2), (key1416, -2), (key1785, 2), (key1288, 2), (key1565, 2)]

def rawRow2145 : Integer.Sparse Key := [(key1565, -6), (key1652, 2), (key1614, 2), (key1538, 2), (key1416, 6), (key1810, -2), (key1614, -2), (key1308, -2), (key1452, -2), (key1416, -2), (key1383, -2), (key1785, 2), (key1565, 2), (key1288, 2)]

def rawRow2146 : Integer.Sparse Key := [(key2609, -2), (key2613, -2), (key2613, -2), (key2625, 1), (key2629, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2647, 1), (key2664, 2), (key2668, 2), (key2668, 2), (key2779, -1), (key2783, -1), (key2779, -1), (key2937, -1), (key2783, -1), (key2937, -1), (key2699, -1), (key2703, -1), (key2699, -1), (key2736, -1), (key2703, -1), (key2736, -1), (key2802, 1), (key2806, 1), (key2802, 1), (key2949, 1), (key2806, 1), (key2949, 1)]

def rawRow2147 : Integer.Sparse Key := [(key2613, -2), (key2609, -2), (key2613, -2), (key2629, 1), (key2625, 1), (key2647, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2668, 2), (key2664, 2), (key2668, 2), (key2783, -1), (key2779, -1), (key2937, -1), (key2779, -1), (key2937, -1), (key2783, -1), (key2703, -1), (key2699, -1), (key2736, -1), (key2699, -1), (key2736, -1), (key2703, -1), (key2806, 1), (key2802, 1), (key2949, 1), (key2802, 1), (key2949, 1), (key2806, 1)]

def rawRow2148 : Integer.Sparse Key := [(key2613, -2), (key2613, -2), (key2609, -2), (key2647, 1), (key2647, 1), (key2629, 1), (key2629, 1), (key2625, 1), (key2625, 1), (key2668, 2), (key2668, 2), (key2664, 2), (key2937, -1), (key2937, -1), (key2783, -1), (key2783, -1), (key2779, -1), (key2779, -1), (key2736, -1), (key2736, -1), (key2703, -1), (key2703, -1), (key2699, -1), (key2699, -1), (key2949, 1), (key2949, 1), (key2806, 1), (key2806, 1), (key2802, 1), (key2802, 1)]

def rawRow2149 : Integer.Sparse Key := [(key2625, -2), (key2629, -2), (key2637, -2), (key2609, 1), (key2613, 1), (key2625, 1), (key2647, 1), (key2637, 1), (key2652, 1), (key2779, 2), (key2783, 2), (key2791, 2), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2699, 1), (key2703, 1), (key2852, 1), (key2973, 1), (key2857, 1), (key2975, 1)]

def rawRow2150 : Integer.Sparse Key := [(key2629, -2), (key2625, -2), (key2637, -2), (key2613, 1), (key2609, 1), (key2647, 1), (key2625, 1), (key2652, 1), (key2637, 1), (key2783, 2), (key2779, 2), (key2791, 2), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2703, 1), (key2699, 1), (key2973, 1), (key2852, 1), (key2975, 1), (key2857, 1)]

def rawRow2151 : Integer.Sparse Key := [(key2625, -2), (key2637, -2), (key2629, -2), (key2625, 1), (key2637, 1), (key2609, 1), (key2652, 1), (key2613, 1), (key2647, 1), (key2779, 2), (key2791, 2), (key2783, 2), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2852, 1), (key2857, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2973, 1)]

def rawRow2152 : Integer.Sparse Key := [(key2637, -2), (key2625, -2), (key2629, -2), (key2637, 1), (key2625, 1), (key2652, 1), (key2609, 1), (key2647, 1), (key2613, 1), (key2791, 2), (key2779, 2), (key2783, 2), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2857, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2973, 1), (key2703, 1)]

def rawRow2153 : Integer.Sparse Key := [(key2629, -2), (key2637, -2), (key2625, -2), (key2647, 1), (key2652, 1), (key2613, 1), (key2637, 1), (key2609, 1), (key2625, 1), (key2783, 2), (key2791, 2), (key2779, 2), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2973, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2699, 1), (key2852, 1)]

def rawRow2154 : Integer.Sparse Key := [(key2637, -2), (key2629, -2), (key2625, -2), (key2652, 1), (key2647, 1), (key2637, 1), (key2613, 1), (key2625, 1), (key2609, 1), (key2791, 2), (key2783, 2), (key2779, 2), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2975, 1), (key2973, 1), (key2857, 1), (key2703, 1), (key2852, 1), (key2699, 1)]

def rawRow2155 : Integer.Sparse Key := [(key2664, -2), (key2668, -2), (key2668, -2), (key2699, 1), (key2703, 1), (key2699, 1), (key2736, 1), (key2703, 1), (key2736, 1), (key2609, 2), (key2613, 2), (key2613, 2), (key2802, -1), (key2806, -1), (key2802, -1), (key2949, -1), (key2806, -1), (key2949, -1), (key2625, -1), (key2629, -1), (key2625, -1), (key2647, -1), (key2629, -1), (key2647, -1), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1)]

def rawRow2156 : Integer.Sparse Key := [(key2668, -2), (key2664, -2), (key2668, -2), (key2703, 1), (key2699, 1), (key2736, 1), (key2699, 1), (key2736, 1), (key2703, 1), (key2613, 2), (key2609, 2), (key2613, 2), (key2806, -1), (key2802, -1), (key2949, -1), (key2802, -1), (key2949, -1), (key2806, -1), (key2629, -1), (key2625, -1), (key2647, -1), (key2625, -1), (key2647, -1), (key2629, -1), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1)]

def rawRow2157 : Integer.Sparse Key := [(key2668, -2), (key2668, -2), (key2664, -2), (key2736, 1), (key2736, 1), (key2703, 1), (key2703, 1), (key2699, 1), (key2699, 1), (key2613, 2), (key2613, 2), (key2609, 2), (key2949, -1), (key2949, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2647, -1), (key2647, -1), (key2629, -1), (key2629, -1), (key2625, -1), (key2625, -1), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1)]

def rawRow2158 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2664, 1), (key2668, 1), (key2699, 1), (key2736, 1), (key2723, 1), (key2746, 1), (key2802, 2), (key2806, 2), (key2826, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1)]

def rawRow2159 : Integer.Sparse Key := [(key2703, -2), (key2699, -2), (key2723, -2), (key2668, 1), (key2664, 1), (key2736, 1), (key2699, 1), (key2746, 1), (key2723, 1), (key2806, 2), (key2802, 2), (key2826, 2), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1)]

def rawRow2160 : Integer.Sparse Key := [(key2699, -2), (key2723, -2), (key2703, -2), (key2699, 1), (key2723, 1), (key2664, 1), (key2746, 1), (key2668, 1), (key2736, 1), (key2802, 2), (key2826, 2), (key2806, 2), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1)]

def rawRow2161 : Integer.Sparse Key := [(key2723, -2), (key2699, -2), (key2703, -2), (key2723, 1), (key2699, 1), (key2746, 1), (key2664, 1), (key2736, 1), (key2668, 1), (key2826, 2), (key2802, 2), (key2806, 2), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1)]

def rawRow2162 : Integer.Sparse Key := [(key2703, -2), (key2723, -2), (key2699, -2), (key2736, 1), (key2746, 1), (key2668, 1), (key2723, 1), (key2664, 1), (key2699, 1), (key2806, 2), (key2826, 2), (key2802, 2), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1)]

def rawRow2163 : Integer.Sparse Key := [(key2723, -2), (key2703, -2), (key2699, -2), (key2746, 1), (key2736, 1), (key2723, 1), (key2668, 1), (key2699, 1), (key2664, 1), (key2826, 2), (key2806, 2), (key2802, 2), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1)]

def rawRow2164 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, -2), (key2802, 1), (key2806, 1), (key2852, 1), (key2894, 1), (key2857, 1), (key2896, 1), (key2625, 2), (key2629, 2), (key2637, 2), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1)]

def rawRow2165 : Integer.Sparse Key := [(key2783, -2), (key2779, -2), (key2791, -2), (key2806, 1), (key2802, 1), (key2894, 1), (key2852, 1), (key2896, 1), (key2857, 1), (key2629, 2), (key2625, 2), (key2637, 2), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1)]

def rawRow2166 : Integer.Sparse Key := [(key2779, -2), (key2791, -2), (key2783, -2), (key2852, 1), (key2857, 1), (key2802, 1), (key2896, 1), (key2806, 1), (key2894, 1), (key2625, 2), (key2637, 2), (key2629, 2), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1)]

def rawRow2167 : Integer.Sparse Key := [(key2791, -2), (key2779, -2), (key2783, -2), (key2857, 1), (key2852, 1), (key2896, 1), (key2802, 1), (key2894, 1), (key2806, 1), (key2637, 2), (key2625, 2), (key2629, 2), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1)]

def rawRow2168 : Integer.Sparse Key := [(key2783, -2), (key2791, -2), (key2779, -2), (key2894, 1), (key2896, 1), (key2806, 1), (key2857, 1), (key2802, 1), (key2852, 1), (key2629, 2), (key2637, 2), (key2625, 2), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1)]

def rawRow2169 : Integer.Sparse Key := [(key2791, -2), (key2783, -2), (key2779, -2), (key2896, 1), (key2894, 1), (key2857, 1), (key2806, 1), (key2852, 1), (key2802, 1), (key2637, 2), (key2629, 2), (key2625, 2), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1)]

def rawRow2170 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2826, -2), (key2779, 1), (key2783, 1), (key2852, 1), (key2894, 1), (key2867, 1), (key2903, 1), (key2699, 2), (key2703, 2), (key2723, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1)]

def rawRow2171 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2826, -2), (key2783, 1), (key2779, 1), (key2894, 1), (key2852, 1), (key2903, 1), (key2867, 1), (key2703, 2), (key2699, 2), (key2723, 2), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1)]

def rawRow2172 : Integer.Sparse Key := [(key2802, -2), (key2826, -2), (key2806, -2), (key2852, 1), (key2867, 1), (key2779, 1), (key2903, 1), (key2783, 1), (key2894, 1), (key2699, 2), (key2723, 2), (key2703, 2), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1)]

def rawRow2173 : Integer.Sparse Key := [(key2826, -2), (key2802, -2), (key2806, -2), (key2867, 1), (key2852, 1), (key2903, 1), (key2779, 1), (key2894, 1), (key2783, 1), (key2723, 2), (key2699, 2), (key2703, 2), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1)]

def rawRow2174 : Integer.Sparse Key := [(key2806, -2), (key2826, -2), (key2802, -2), (key2894, 1), (key2903, 1), (key2783, 1), (key2867, 1), (key2779, 1), (key2852, 1), (key2703, 2), (key2723, 2), (key2699, 2), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1)]

def rawRow2175 : Integer.Sparse Key := [(key2826, -2), (key2806, -2), (key2802, -2), (key2903, 1), (key2894, 1), (key2867, 1), (key2783, 1), (key2852, 1), (key2779, 1), (key2723, 2), (key2703, 2), (key2699, 2), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2176 : Integer.Sparse Key := [(key994, -2), (key999, -2), (key999, -2), (key1013, 6), (key1029, 2), (key1034, 2), (key1034, 2), (key1121, -2), (key1121, -2), (key1197, -2), (key1069, -6), (key1148, 2), (key1148, 2), (key1210, 2)]

def rawRow2177 : Integer.Sparse Key := [(key999, -2), (key994, -2), (key999, -2), (key1013, 6), (key1034, 2), (key1029, 2), (key1034, 2), (key1121, -2), (key1197, -2), (key1121, -2), (key1069, -6), (key1148, 2), (key1210, 2), (key1148, 2)]

def rawRow2178 : Integer.Sparse Key := [(key999, -2), (key999, -2), (key994, -2), (key1013, 6), (key1034, 2), (key1034, 2), (key1029, 2), (key1197, -2), (key1121, -2), (key1121, -2), (key1069, -6), (key1210, 2), (key1148, 2), (key1148, 2)]

def rawRow2179 : Integer.Sparse Key := [(key994, -2), (key999, -2), (key1013, -2), (key999, 6), (key1107, 2), (key1112, 2), (key1121, 2), (key1034, -2), (key1112, -2), (key1191, -2), (key1148, -6), (key1069, 2), (key1148, 2), (key1210, 2)]

def rawRow2180 : Integer.Sparse Key := [(key999, -2), (key994, -2), (key1013, -2), (key999, 6), (key1112, 2), (key1107, 2), (key1121, 2), (key1034, -2), (key1191, -2), (key1112, -2), (key1148, -6), (key1069, 2), (key1210, 2), (key1148, 2)]

def rawRow2181 : Integer.Sparse Key := [(key994, -2), (key1013, -2), (key999, -2), (key999, 6), (key1107, 2), (key1121, 2), (key1112, 2), (key1112, -2), (key1034, -2), (key1191, -2), (key1148, -6), (key1148, 2), (key1069, 2), (key1210, 2)]

def rawRow2182 : Integer.Sparse Key := [(key1013, -2), (key994, -2), (key999, -2), (key999, 6), (key1121, 2), (key1107, 2), (key1112, 2), (key1112, -2), (key1191, -2), (key1034, -2), (key1148, -6), (key1148, 2), (key1210, 2), (key1069, 2)]

def rawRow2183 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key994, -2), (key999, 6), (key1112, 2), (key1121, 2), (key1107, 2), (key1191, -2), (key1034, -2), (key1112, -2), (key1148, -6), (key1210, 2), (key1069, 2), (key1148, 2)]

def rawRow2184 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key994, -2), (key999, 6), (key1121, 2), (key1112, 2), (key1107, 2), (key1191, -2), (key1112, -2), (key1034, -2), (key1148, -6), (key1210, 2), (key1148, 2), (key1069, 2)]

def rawRow2185 : Integer.Sparse Key := [(key1029, -2), (key1034, -2), (key1034, -2), (key1069, 6), (key994, 2), (key999, 2), (key999, 2), (key1148, -2), (key1148, -2), (key1210, -2), (key1013, -6), (key1121, 2), (key1121, 2), (key1197, 2)]

def rawRow2186 : Integer.Sparse Key := [(key1034, -2), (key1029, -2), (key1034, -2), (key1069, 6), (key999, 2), (key994, 2), (key999, 2), (key1148, -2), (key1210, -2), (key1148, -2), (key1013, -6), (key1121, 2), (key1197, 2), (key1121, 2)]

def rawRow2187 : Integer.Sparse Key := [(key1034, -2), (key1034, -2), (key1029, -2), (key1069, 6), (key999, 2), (key999, 2), (key994, 2), (key1210, -2), (key1148, -2), (key1148, -2), (key1013, -6), (key1197, 2), (key1121, 2), (key1121, 2)]

def rawRow2188 : Integer.Sparse Key := [(key1029, -2), (key1034, -2), (key1069, -2), (key1034, 6), (key1107, 2), (key1112, 2), (key1148, 2), (key999, -2), (key1112, -2), (key1191, -2), (key1121, -6), (key1013, 2), (key1121, 2), (key1197, 2)]

def rawRow2189 : Integer.Sparse Key := [(key1034, -2), (key1029, -2), (key1069, -2), (key1034, 6), (key1112, 2), (key1107, 2), (key1148, 2), (key999, -2), (key1191, -2), (key1112, -2), (key1121, -6), (key1013, 2), (key1197, 2), (key1121, 2)]

def rawRow2190 : Integer.Sparse Key := [(key1029, -2), (key1069, -2), (key1034, -2), (key1034, 6), (key1107, 2), (key1148, 2), (key1112, 2), (key1112, -2), (key999, -2), (key1191, -2), (key1121, -6), (key1121, 2), (key1013, 2), (key1197, 2)]

def rawRow2191 : Integer.Sparse Key := [(key1069, -2), (key1029, -2), (key1034, -2), (key1034, 6), (key1148, 2), (key1107, 2), (key1112, 2), (key1112, -2), (key1191, -2), (key999, -2), (key1121, -6), (key1121, 2), (key1197, 2), (key1013, 2)]

def rawRow2192 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1029, -2), (key1034, 6), (key1112, 2), (key1148, 2), (key1107, 2), (key1191, -2), (key999, -2), (key1112, -2), (key1121, -6), (key1197, 2), (key1013, 2), (key1121, 2)]

def rawRow2193 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1029, -2), (key1034, 6), (key1148, 2), (key1112, 2), (key1107, 2), (key1191, -2), (key1112, -2), (key999, -2), (key1121, -6), (key1197, 2), (key1121, 2), (key1013, 2)]

def rawRow2194 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1121, -2), (key1148, 6), (key994, 2), (key999, 2), (key1013, 2), (key1069, -2), (key1148, -2), (key1210, -2), (key999, -6), (key1034, 2), (key1112, 2), (key1191, 2)]

def rawRow2195 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1121, -2), (key1148, 6), (key999, 2), (key994, 2), (key1013, 2), (key1069, -2), (key1210, -2), (key1148, -2), (key999, -6), (key1034, 2), (key1191, 2), (key1112, 2)]

def rawRow2196 : Integer.Sparse Key := [(key1107, -2), (key1121, -2), (key1112, -2), (key1148, 6), (key994, 2), (key1013, 2), (key999, 2), (key1148, -2), (key1069, -2), (key1210, -2), (key999, -6), (key1112, 2), (key1034, 2), (key1191, 2)]

def rawRow2197 : Integer.Sparse Key := [(key1121, -2), (key1107, -2), (key1112, -2), (key1148, 6), (key1013, 2), (key994, 2), (key999, 2), (key1148, -2), (key1210, -2), (key1069, -2), (key999, -6), (key1112, 2), (key1191, 2), (key1034, 2)]

def rawRow2198 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1107, -2), (key1148, 6), (key999, 2), (key1013, 2), (key994, 2), (key1210, -2), (key1069, -2), (key1148, -2), (key999, -6), (key1191, 2), (key1034, 2), (key1112, 2)]

def rawRow2199 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1107, -2), (key1148, 6), (key1013, 2), (key999, 2), (key994, 2), (key1210, -2), (key1148, -2), (key1069, -2), (key999, -6), (key1191, 2), (key1112, 2), (key1034, 2)]

def rawRow2200 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1148, -2), (key1121, 6), (key1029, 2), (key1034, 2), (key1069, 2), (key1013, -2), (key1121, -2), (key1197, -2), (key1034, -6), (key999, 2), (key1112, 2), (key1191, 2)]

def rawRow2201 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1148, -2), (key1121, 6), (key1034, 2), (key1029, 2), (key1069, 2), (key1013, -2), (key1197, -2), (key1121, -2), (key1034, -6), (key999, 2), (key1191, 2), (key1112, 2)]

def rawRow2202 : Integer.Sparse Key := [(key1107, -2), (key1148, -2), (key1112, -2), (key1121, 6), (key1029, 2), (key1069, 2), (key1034, 2), (key1121, -2), (key1013, -2), (key1197, -2), (key1034, -6), (key1112, 2), (key999, 2), (key1191, 2)]

def rawRow2203 : Integer.Sparse Key := [(key1148, -2), (key1107, -2), (key1112, -2), (key1121, 6), (key1069, 2), (key1029, 2), (key1034, 2), (key1121, -2), (key1197, -2), (key1013, -2), (key1034, -6), (key1112, 2), (key1191, 2), (key999, 2)]

def rawRow2204 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1107, -2), (key1121, 6), (key1034, 2), (key1069, 2), (key1029, 2), (key1197, -2), (key1013, -2), (key1121, -2), (key1034, -6), (key1191, 2), (key999, 2), (key1112, 2)]

def rawRow2205 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1107, -2), (key1121, 6), (key1069, 2), (key1034, 2), (key1029, 2), (key1197, -2), (key1121, -2), (key1013, -2), (key1034, -6), (key1191, 2), (key1112, 2), (key999, 2)]

def rawRow2206 : Integer.Sparse Key := [(key2607, -6), (key2623, 2), (key2623, 2), (key2634, 2), (key2662, 6), (key2697, -2), (key2697, -2), (key2720, -2), (key2777, -2), (key2777, -2), (key2788, -2), (key2800, 2), (key2800, 2), (key2823, 2)]

def rawRow2207 : Integer.Sparse Key := [(key2607, -6), (key2623, 2), (key2634, 2), (key2623, 2), (key2662, 6), (key2697, -2), (key2720, -2), (key2697, -2), (key2777, -2), (key2788, -2), (key2777, -2), (key2800, 2), (key2823, 2), (key2800, 2)]

def rawRow2208 : Integer.Sparse Key := [(key2607, -6), (key2634, 2), (key2623, 2), (key2623, 2), (key2662, 6), (key2720, -2), (key2697, -2), (key2697, -2), (key2788, -2), (key2777, -2), (key2777, -2), (key2823, 2), (key2800, 2), (key2800, 2)]

def rawRow2209 : Integer.Sparse Key := [(key2623, -6), (key2607, 2), (key2623, 2), (key2634, 2), (key2697, 6), (key2662, -2), (key2697, -2), (key2720, -2), (key2800, -2), (key2850, -2), (key2854, -2), (key2777, 2), (key2850, 2), (key2864, 2)]

def rawRow2210 : Integer.Sparse Key := [(key2623, -6), (key2607, 2), (key2634, 2), (key2623, 2), (key2697, 6), (key2662, -2), (key2720, -2), (key2697, -2), (key2800, -2), (key2854, -2), (key2850, -2), (key2777, 2), (key2864, 2), (key2850, 2)]

def rawRow2211 : Integer.Sparse Key := [(key2623, -6), (key2623, 2), (key2607, 2), (key2634, 2), (key2697, 6), (key2697, -2), (key2662, -2), (key2720, -2), (key2850, -2), (key2800, -2), (key2854, -2), (key2850, 2), (key2777, 2), (key2864, 2)]

def rawRow2212 : Integer.Sparse Key := [(key2623, -6), (key2623, 2), (key2634, 2), (key2607, 2), (key2697, 6), (key2697, -2), (key2720, -2), (key2662, -2), (key2850, -2), (key2854, -2), (key2800, -2), (key2850, 2), (key2864, 2), (key2777, 2)]

def rawRow2213 : Integer.Sparse Key := [(key2623, -6), (key2634, 2), (key2607, 2), (key2623, 2), (key2697, 6), (key2720, -2), (key2662, -2), (key2697, -2), (key2854, -2), (key2800, -2), (key2850, -2), (key2864, 2), (key2777, 2), (key2850, 2)]

def rawRow2214 : Integer.Sparse Key := [(key2623, -6), (key2634, 2), (key2623, 2), (key2607, 2), (key2697, 6), (key2720, -2), (key2697, -2), (key2662, -2), (key2854, -2), (key2850, -2), (key2800, -2), (key2864, 2), (key2850, 2), (key2777, 2)]

def rawRow2215 : Integer.Sparse Key := [(key2662, -6), (key2777, 2), (key2777, 2), (key2788, 2), (key2607, 6), (key2800, -2), (key2800, -2), (key2823, -2), (key2623, -2), (key2623, -2), (key2634, -2), (key2697, 2), (key2697, 2), (key2720, 2)]

def rawRow2216 : Integer.Sparse Key := [(key2662, -6), (key2777, 2), (key2788, 2), (key2777, 2), (key2607, 6), (key2800, -2), (key2823, -2), (key2800, -2), (key2623, -2), (key2634, -2), (key2623, -2), (key2697, 2), (key2720, 2), (key2697, 2)]

def rawRow2217 : Integer.Sparse Key := [(key2662, -6), (key2788, 2), (key2777, 2), (key2777, 2), (key2607, 6), (key2823, -2), (key2800, -2), (key2800, -2), (key2634, -2), (key2623, -2), (key2623, -2), (key2720, 2), (key2697, 2), (key2697, 2)]

def rawRow2218 : Integer.Sparse Key := [(key2777, -6), (key2662, 2), (key2777, 2), (key2788, 2), (key2800, 6), (key2607, -2), (key2800, -2), (key2823, -2), (key2697, -2), (key2850, -2), (key2854, -2), (key2623, 2), (key2850, 2), (key2864, 2)]

def rawRow2219 : Integer.Sparse Key := [(key2777, -6), (key2662, 2), (key2788, 2), (key2777, 2), (key2800, 6), (key2607, -2), (key2823, -2), (key2800, -2), (key2697, -2), (key2854, -2), (key2850, -2), (key2623, 2), (key2864, 2), (key2850, 2)]

def rawRow2220 : Integer.Sparse Key := [(key2777, -6), (key2777, 2), (key2662, 2), (key2788, 2), (key2800, 6), (key2800, -2), (key2607, -2), (key2823, -2), (key2850, -2), (key2697, -2), (key2854, -2), (key2850, 2), (key2623, 2), (key2864, 2)]

def rawRow2221 : Integer.Sparse Key := [(key2777, -6), (key2777, 2), (key2788, 2), (key2662, 2), (key2800, 6), (key2800, -2), (key2823, -2), (key2607, -2), (key2850, -2), (key2854, -2), (key2697, -2), (key2850, 2), (key2864, 2), (key2623, 2)]

def rawRow2222 : Integer.Sparse Key := [(key2777, -6), (key2788, 2), (key2662, 2), (key2777, 2), (key2800, 6), (key2823, -2), (key2607, -2), (key2800, -2), (key2854, -2), (key2697, -2), (key2850, -2), (key2864, 2), (key2623, 2), (key2850, 2)]

def rawRow2223 : Integer.Sparse Key := [(key2777, -6), (key2788, 2), (key2777, 2), (key2662, 2), (key2800, 6), (key2823, -2), (key2800, -2), (key2607, -2), (key2854, -2), (key2850, -2), (key2697, -2), (key2864, 2), (key2850, 2), (key2623, 2)]

def rawRow2224 : Integer.Sparse Key := [(key2697, -6), (key2800, 2), (key2850, 2), (key2854, 2), (key2623, 6), (key2777, -2), (key2850, -2), (key2864, -2), (key2607, -2), (key2623, -2), (key2634, -2), (key2662, 2), (key2697, 2), (key2720, 2)]

def rawRow2225 : Integer.Sparse Key := [(key2697, -6), (key2800, 2), (key2854, 2), (key2850, 2), (key2623, 6), (key2777, -2), (key2864, -2), (key2850, -2), (key2607, -2), (key2634, -2), (key2623, -2), (key2662, 2), (key2720, 2), (key2697, 2)]

def rawRow2226 : Integer.Sparse Key := [(key2697, -6), (key2850, 2), (key2800, 2), (key2854, 2), (key2623, 6), (key2850, -2), (key2777, -2), (key2864, -2), (key2623, -2), (key2607, -2), (key2634, -2), (key2697, 2), (key2662, 2), (key2720, 2)]

def rawRow2227 : Integer.Sparse Key := [(key2697, -6), (key2850, 2), (key2854, 2), (key2800, 2), (key2623, 6), (key2850, -2), (key2864, -2), (key2777, -2), (key2623, -2), (key2634, -2), (key2607, -2), (key2697, 2), (key2720, 2), (key2662, 2)]

def rawRow2228 : Integer.Sparse Key := [(key2697, -6), (key2854, 2), (key2800, 2), (key2850, 2), (key2623, 6), (key2864, -2), (key2777, -2), (key2850, -2), (key2634, -2), (key2607, -2), (key2623, -2), (key2720, 2), (key2662, 2), (key2697, 2)]

def rawRow2229 : Integer.Sparse Key := [(key2697, -6), (key2854, 2), (key2850, 2), (key2800, 2), (key2623, 6), (key2864, -2), (key2850, -2), (key2777, -2), (key2634, -2), (key2623, -2), (key2607, -2), (key2720, 2), (key2697, 2), (key2662, 2)]

def rawRow2230 : Integer.Sparse Key := [(key2800, -6), (key2697, 2), (key2850, 2), (key2854, 2), (key2777, 6), (key2623, -2), (key2850, -2), (key2864, -2), (key2662, -2), (key2777, -2), (key2788, -2), (key2607, 2), (key2800, 2), (key2823, 2)]

def rawRow2231 : Integer.Sparse Key := [(key2800, -6), (key2697, 2), (key2854, 2), (key2850, 2), (key2777, 6), (key2623, -2), (key2864, -2), (key2850, -2), (key2662, -2), (key2788, -2), (key2777, -2), (key2607, 2), (key2823, 2), (key2800, 2)]

def rawRow2232 : Integer.Sparse Key := [(key2800, -6), (key2850, 2), (key2697, 2), (key2854, 2), (key2777, 6), (key2850, -2), (key2623, -2), (key2864, -2), (key2777, -2), (key2662, -2), (key2788, -2), (key2800, 2), (key2607, 2), (key2823, 2)]

def rawRow2233 : Integer.Sparse Key := [(key2800, -6), (key2850, 2), (key2854, 2), (key2697, 2), (key2777, 6), (key2850, -2), (key2864, -2), (key2623, -2), (key2777, -2), (key2788, -2), (key2662, -2), (key2800, 2), (key2823, 2), (key2607, 2)]

def rawRow2234 : Integer.Sparse Key := [(key2800, -6), (key2854, 2), (key2697, 2), (key2850, 2), (key2777, 6), (key2864, -2), (key2623, -2), (key2850, -2), (key2788, -2), (key2662, -2), (key2777, -2), (key2823, 2), (key2607, 2), (key2800, 2)]

def rawRow2235 : Integer.Sparse Key := [(key2800, -6), (key2854, 2), (key2850, 2), (key2697, 2), (key2777, 6), (key2864, -2), (key2850, -2), (key2623, -2), (key2788, -2), (key2777, -2), (key2662, -2), (key2823, 2), (key2800, 2), (key2607, 2)]

def rawRow2236 : Integer.Sparse Key := [(key1542, -1), (key1547, -1), (key1542, -1), (key1773, -1), (key1547, -1), (key1773, -1), (key1555, 2), (key1555, 2), (key1779, 2), (key1569, 1), (key1574, 1), (key1569, 1), (key1789, 1), (key1574, 1), (key1789, 1), (key1623, -1), (key1658, -1), (key1623, -1), (key1816, -1), (key1658, -1), (key1816, -1), (key1592, -2), (key1592, -2), (key1797, -2), (key1632, 1), (key1666, 1), (key1632, 1), (key1824, 1), (key1666, 1), (key1824, 1)]

def rawRow2237 : Integer.Sparse Key := [(key1547, -1), (key1542, -1), (key1773, -1), (key1542, -1), (key1773, -1), (key1547, -1), (key1555, 2), (key1779, 2), (key1555, 2), (key1574, 1), (key1569, 1), (key1789, 1), (key1569, 1), (key1789, 1), (key1574, 1), (key1658, -1), (key1623, -1), (key1816, -1), (key1623, -1), (key1816, -1), (key1658, -1), (key1592, -2), (key1797, -2), (key1592, -2), (key1666, 1), (key1632, 1), (key1824, 1), (key1632, 1), (key1824, 1), (key1666, 1)]

def rawRow2266 : Integer.Sparse Key := [(key3062, -2), (key3071, -2), (key3071, -2), (key3067, 2), (key3073, 2), (key3073, 2), (key3097, 2), (key3108, 2), (key3108, 2), (key3135, -6), (key3104, -2), (key3111, -2), (key3111, -2), (key3137, 6)]

end MUB6.Certificate.GramRows

end OAI
end


