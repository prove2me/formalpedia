-- Prove2me | Definitions.Def_OAIQ106E048
-- name    : OAIQ106E048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:02:21.622297+00:00
-- url     : https://prove2.me/theorems/26f16a74-6ac9-41a3-aeb0-0b2edffb2faa
-- title:
--   Definitions bundle OAIQ106E048 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1487 declarations of OpenAI's Lean: 1487 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow16187`, `OAI.MUB6.Certificate.GramRows.rawRow16188`, `OAI.MUB6.Certificate.GramRows.rawRow16189`, `OAI.MUB6.Certificate.GramRows.rawRow1619`, `OAI.MUB6.Certificate.GramRows.rawRow16190`, `OAI.MUB6.Certificate.GramRows.rawRow16191`, `OAI.MUB6.Certificate.GramRows.rawRow16192`, `OAI.MUB6.Certificate.GramRows.rawRow16193`, `OAI.MUB6.Certificate.GramRows.rawRow16194`, `OAI.MUB6.Certificate.GramRows.rawRow16195`, `OAI.MUB6.Certificate.GramRows.rawRow16196`, `OAI.MUB6.Certificate.GramRows.rawRow16197`, `OAI.MUB6.Certificate.GramRows.rawRow16198`, `OAI.MUB6.Certificate.GramRows.rawRow16199`, `OAI.MUB6.Certificate.GramRows.rawRow162`, `OAI.MUB6.Certificate.GramRows.rawRow1620`, `OAI.MUB6.Certificate.GramRows.rawRow16200`, `OAI.MUB6.Certificate.GramRows.rawRow16201`, `OAI.MUB6.Certificate.GramRows.rawRow16202`, `OAI.MUB6.Certificate.GramRows.rawRow16203`, `OAI.MUB6.Certificate.GramRows.rawRow16204`, `OAI.MUB6.Certificate.GramRows.rawRow16205`, `OAI.MUB6.Certificate.GramRows.rawRow16206`, `OAI.MUB6.Certificate.GramRows.rawRow16207`, `OAI.MUB6.Certificate.GramRows.rawRow16208`, `OAI.MUB6.Certificate.GramRows.rawRow16209`, `OAI.MUB6.Certificate.GramRows.rawRow1621`, `OAI.MUB6.Certificate.GramRows.rawRow16210`, `OAI.MUB6.Certificate.GramRows.rawRow16211`, `OAI.MUB6.Certificate.GramRows.rawRow16212`, `OAI.MUB6.Certificate.GramRows.rawRow16213`, `OAI.MUB6.Certificate.GramRows.rawRow16214`, `OAI.MUB6.Certificate.GramRows.rawRow16215`, `OAI.MUB6.Certificate.GramRows.rawRow16216`, `OAI.MUB6.Certificate.GramRows.rawRow16217`, `OAI.MUB6.Certificate.GramRows.rawRow16218`, `OAI.MUB6.Certificate.GramRows.rawRow16219`, `OAI.MUB6.Certificate.GramRows.rawRow1622`, `OAI.MUB6.Certificate.GramRows.rawRow16220`, `OAI.MUB6.Certificate.GramRows.rawRow16221` and 1447 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block150`, `MutuallyUnbiased_GramRows_Block151`, `MutuallyUnbiased_GramRows_Block152`, `MutuallyUnbiased_GramRows_Block153`, `MutuallyUnbiased_GramRows_Block154`, `MutuallyUnbiased_GramRows_Block155`, `MutuallyUnbiased_GramRows_Block156`, `MutuallyUnbiased_GramRows_Block157`, `MutuallyUnbiased_GramRows_Block158`, `MutuallyUnbiased_GramRows_Block159`, `MutuallyUnbiased_GramRows_Block160`, `MutuallyUnbiased_GramRows_Block2`, `MutuallyUnbiased_GramRows_Block36`, `MutuallyUnbiased_GramRows_Block37`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval16_9_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval17_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_12_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_6_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9_e`.
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

def rawRow17 : Integer.Sparse Key := [(key335, -1), (key335, -1), (key340, 2), (key305, 1), (key305, 1), (key328, -1), (key328, -1), (key302, -2), (key316, 1), (key316, 1), (key578, 1), (key578, 1), (key583, -2), (key239, -1), (key239, -1), (key418, 1), (key418, 1), (key236, 2), (key406, -1), (key406, -1), (key328, -1), (key328, -1), (key601, 1), (key601, 1), (key260, 1), (key260, 1), (key595, -1), (key595, -1), (key248, -1), (key248, -1), (key316, 1), (key316, 1), (key340, 2), (key475, -1), (key475, -1), (key271, -2), (key469, 1), (key469, 1), (key267, 1), (key267, 1), (key335, -1), (key335, -1)]

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

def rawRow16187 : Integer.Sparse Key := [(key2535, -2), (key2553, -2), (key2537, -2), (key2542, 6), (key2402, -2), (key2439, -2), (key2408, -2), (key2468, 2), (key2505, 2), (key2374, 2), (key2553, 2), (key2380, 2), (key2537, 2), (key2481, -2), (key2391, -2), (key2542, -2), (key2770, 6), (key2847, -2), (key2591, -2), (key2878, -2)]

def rawRow16188 : Integer.Sparse Key := [(key2553, -2), (key2535, -2), (key2537, -2), (key2542, 6), (key2439, -2), (key2402, -2), (key2408, -2), (key2505, 2), (key2468, 2), (key2553, 2), (key2374, 2), (key2537, 2), (key2380, 2), (key2481, -2), (key2542, -2), (key2391, -2), (key2770, 6), (key2847, -2), (key2878, -2), (key2591, -2)]

def rawRow16189 : Integer.Sparse Key := [(key2537, -2), (key2553, -2), (key2535, -2), (key2542, 6), (key2408, -2), (key2439, -2), (key2402, -2), (key2537, 2), (key2553, 2), (key2380, 2), (key2505, 2), (key2374, 2), (key2468, 2), (key2542, -2), (key2391, -2), (key2481, -2), (key2770, 6), (key2878, -2), (key2591, -2), (key2847, -2)]

def rawRow16190 : Integer.Sparse Key := [(key2553, -2), (key2537, -2), (key2535, -2), (key2542, 6), (key2439, -2), (key2408, -2), (key2402, -2), (key2553, 2), (key2537, 2), (key2505, 2), (key2380, 2), (key2468, 2), (key2374, 2), (key2542, -2), (key2481, -2), (key2391, -2), (key2770, 6), (key2878, -2), (key2847, -2), (key2591, -2)]

def rawRow16191 : Integer.Sparse Key := [(key2535, -2), (key2542, -2), (key2553, -2), (key2537, 6), (key2468, -2), (key2481, -2), (key2505, -2), (key2374, 2), (key2391, 2), (key2402, 2), (key2542, 2), (key2439, 2), (key2553, 2), (key2380, -2), (key2408, -2), (key2537, -2), (key2847, 6), (key2591, -2), (key2770, -2), (key2878, -2)]

def rawRow16192 : Integer.Sparse Key := [(key2542, -2), (key2535, -2), (key2553, -2), (key2537, 6), (key2481, -2), (key2468, -2), (key2505, -2), (key2391, 2), (key2374, 2), (key2542, 2), (key2402, 2), (key2553, 2), (key2439, 2), (key2380, -2), (key2537, -2), (key2408, -2), (key2847, 6), (key2591, -2), (key2878, -2), (key2770, -2)]

def rawRow16193 : Integer.Sparse Key := [(key2535, -2), (key2553, -2), (key2542, -2), (key2537, 6), (key2468, -2), (key2505, -2), (key2481, -2), (key2402, 2), (key2439, 2), (key2374, 2), (key2553, 2), (key2391, 2), (key2542, 2), (key2408, -2), (key2380, -2), (key2537, -2), (key2847, 6), (key2770, -2), (key2591, -2), (key2878, -2)]

def rawRow16194 : Integer.Sparse Key := [(key2553, -2), (key2535, -2), (key2542, -2), (key2537, 6), (key2505, -2), (key2468, -2), (key2481, -2), (key2439, 2), (key2402, 2), (key2553, 2), (key2374, 2), (key2542, 2), (key2391, 2), (key2408, -2), (key2537, -2), (key2380, -2), (key2847, 6), (key2770, -2), (key2878, -2), (key2591, -2)]

def rawRow16195 : Integer.Sparse Key := [(key2542, -2), (key2553, -2), (key2535, -2), (key2537, 6), (key2481, -2), (key2505, -2), (key2468, -2), (key2542, 2), (key2553, 2), (key2391, 2), (key2439, 2), (key2374, 2), (key2402, 2), (key2537, -2), (key2380, -2), (key2408, -2), (key2847, 6), (key2878, -2), (key2591, -2), (key2770, -2)]

def rawRow16196 : Integer.Sparse Key := [(key2553, -2), (key2542, -2), (key2535, -2), (key2537, 6), (key2505, -2), (key2481, -2), (key2468, -2), (key2553, 2), (key2542, 2), (key2439, 2), (key2391, 2), (key2402, 2), (key2374, 2), (key2537, -2), (key2408, -2), (key2380, -2), (key2847, 6), (key2878, -2), (key2770, -2), (key2591, -2)]

def rawRow16197 : Integer.Sparse Key := [(key2537, -2), (key2542, -2), (key2553, -2), (key2535, 6), (key2537, -2), (key2542, -2), (key2553, -2), (key2380, 2), (key2391, 2), (key2408, 2), (key2481, 2), (key2439, 2), (key2505, 2), (key2374, -2), (key2402, -2), (key2468, -2), (key2878, 6), (key2591, -2), (key2770, -2), (key2847, -2)]

def rawRow16198 : Integer.Sparse Key := [(key2542, -2), (key2537, -2), (key2553, -2), (key2535, 6), (key2542, -2), (key2537, -2), (key2553, -2), (key2391, 2), (key2380, 2), (key2481, 2), (key2408, 2), (key2505, 2), (key2439, 2), (key2374, -2), (key2468, -2), (key2402, -2), (key2878, 6), (key2591, -2), (key2847, -2), (key2770, -2)]

def rawRow16199 : Integer.Sparse Key := [(key2537, -2), (key2553, -2), (key2542, -2), (key2535, 6), (key2537, -2), (key2553, -2), (key2542, -2), (key2408, 2), (key2439, 2), (key2380, 2), (key2505, 2), (key2391, 2), (key2481, 2), (key2402, -2), (key2374, -2), (key2468, -2), (key2878, 6), (key2770, -2), (key2591, -2), (key2847, -2)]

def rawRow16200 : Integer.Sparse Key := [(key2553, -2), (key2537, -2), (key2542, -2), (key2535, 6), (key2553, -2), (key2537, -2), (key2542, -2), (key2439, 2), (key2408, 2), (key2505, 2), (key2380, 2), (key2481, 2), (key2391, 2), (key2402, -2), (key2468, -2), (key2374, -2), (key2878, 6), (key2770, -2), (key2847, -2), (key2591, -2)]

def rawRow16201 : Integer.Sparse Key := [(key2542, -2), (key2553, -2), (key2537, -2), (key2535, 6), (key2542, -2), (key2553, -2), (key2537, -2), (key2481, 2), (key2505, 2), (key2391, 2), (key2439, 2), (key2380, 2), (key2408, 2), (key2468, -2), (key2374, -2), (key2402, -2), (key2878, 6), (key2847, -2), (key2591, -2), (key2770, -2)]

def rawRow16202 : Integer.Sparse Key := [(key2553, -2), (key2542, -2), (key2537, -2), (key2535, 6), (key2553, -2), (key2542, -2), (key2537, -2), (key2505, 2), (key2481, 2), (key2439, 2), (key2391, 2), (key2408, 2), (key2380, 2), (key2468, -2), (key2402, -2), (key2374, -2), (key2878, 6), (key2847, -2), (key2770, -2), (key2591, -2)]

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

def rawRow16311 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2621, 2), (key2835, 2), (key2835, 2), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key3026, -1), (key3026, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, -1), (key2885, -1), (key2658, 2), (key2923, 2), (key2923, 2), (key2660, -1), (key2660, -1), (key2758, -1), (key2758, -1), (key2927, -1), (key2927, -1)]

def rawRow16312 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2835, 2), (key2621, 2), (key2835, 2), (key2870, -1), (key3026, -1), (key2632, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2923, 2), (key2658, 2), (key2923, 2), (key2758, -1), (key2927, -1), (key2660, -1), (key2927, -1), (key2660, -1), (key2758, -1)]

def rawRow16313 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key2835, 2), (key2835, 2), (key2621, 2), (key3026, -1), (key2870, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2644, -1), (key2923, 2), (key2923, 2), (key2658, 2), (key2927, -1), (key2758, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2660, -1)]

def rawRow16314 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2640, -1), (key2644, -1), (key2860, -1), (key2885, -1), (key3023, -1), (key3030, -1), (key2632, 2), (key2644, 2), (key2706, 2), (key2732, 2), (key3023, 2), (key3026, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1), (key2660, 2), (key2920, 2), (key2927, 2), (key2658, -1), (key2660, -1), (key2753, -1), (key2758, -1), (key2920, -1), (key2923, -1)]

def rawRow16315 : Integer.Sparse Key := [(key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2644, -1), (key2640, -1), (key2885, -1), (key2860, -1), (key3030, -1), (key3023, -1), (key2644, 2), (key2632, 2), (key2732, 2), (key2706, 2), (key3026, 2), (key3023, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1), (key2660, 2), (key2927, 2), (key2920, 2), (key2660, -1), (key2658, -1), (key2758, -1), (key2753, -1), (key2923, -1), (key2920, -1)]

def rawRow16316 : Integer.Sparse Key := [(key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2860, -1), (key3023, -1), (key2640, -1), (key3030, -1), (key2644, -1), (key2885, -1), (key2706, 2), (key3023, 2), (key2632, 2), (key3026, 2), (key2644, 2), (key2732, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2920, 2), (key2660, 2), (key2927, 2), (key2753, -1), (key2920, -1), (key2658, -1), (key2923, -1), (key2660, -1), (key2758, -1)]

def rawRow16317 : Integer.Sparse Key := [(key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key3023, -1), (key2860, -1), (key3030, -1), (key2640, -1), (key2885, -1), (key2644, -1), (key3023, 2), (key2706, 2), (key3026, 2), (key2632, 2), (key2732, 2), (key2644, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1), (key2920, 2), (key2927, 2), (key2660, 2), (key2920, -1), (key2753, -1), (key2923, -1), (key2658, -1), (key2758, -1), (key2660, -1)]

def rawRow16318 : Integer.Sparse Key := [(key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2885, -1), (key3030, -1), (key2644, -1), (key3023, -1), (key2640, -1), (key2860, -1), (key2732, 2), (key3026, 2), (key2644, 2), (key3023, 2), (key2632, 2), (key2706, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1), (key2927, 2), (key2660, 2), (key2920, 2), (key2758, -1), (key2923, -1), (key2660, -1), (key2920, -1), (key2658, -1), (key2753, -1)]

def rawRow16319 : Integer.Sparse Key := [(key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key3030, -1), (key2885, -1), (key3023, -1), (key2644, -1), (key2860, -1), (key2640, -1), (key3026, 2), (key2732, 2), (key3023, 2), (key2644, 2), (key2706, 2), (key2632, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2927, 2), (key2920, 2), (key2660, 2), (key2923, -1), (key2758, -1), (key2920, -1), (key2660, -1), (key2753, -1), (key2658, -1)]

def rawRow16320 : Integer.Sparse Key := [(key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2641, 2), (key2976, 2), (key2976, 2), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2), (key2660, -1), (key2660, -1), (key2758, -1), (key2758, -1), (key2927, -1), (key2927, -1), (key2621, 2), (key2835, 2), (key2835, 2), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, -1), (key2885, -1)]

def rawRow16321 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2976, 2), (key2641, 2), (key2976, 2), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2758, -1), (key2927, -1), (key2660, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2835, 2), (key2621, 2), (key2835, 2), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2732, -1)]

def rawRow16322 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2976, 2), (key2976, 2), (key2641, 2), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2927, -1), (key2758, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2660, -1), (key2835, 2), (key2835, 2), (key2621, 2), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2644, -1)]

def rawRow16323 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2628, 2), (key2702, 2), (key2972, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1), (key2644, 2), (key2798, 2), (key2885, 2), (key2621, -1), (key2644, -1), (key2676, -1), (key2732, -1), (key2798, -1), (key2835, -1)]

def rawRow16324 : Integer.Sparse Key := [(key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2628, 2), (key2972, 2), (key2702, 2), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1), (key2644, 2), (key2885, 2), (key2798, 2), (key2644, -1), (key2621, -1), (key2732, -1), (key2676, -1), (key2835, -1), (key2798, -1)]

def rawRow16325 : Integer.Sparse Key := [(key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2702, 2), (key2628, 2), (key2972, 2), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2798, 2), (key2644, 2), (key2885, 2), (key2676, -1), (key2798, -1), (key2621, -1), (key2835, -1), (key2644, -1), (key2732, -1)]

def rawRow16326 : Integer.Sparse Key := [(key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2702, 2), (key2972, 2), (key2628, 2), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1), (key2798, 2), (key2885, 2), (key2644, 2), (key2798, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2732, -1), (key2644, -1)]

def rawRow16327 : Integer.Sparse Key := [(key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2972, 2), (key2628, 2), (key2702, 2), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1), (key2885, 2), (key2644, 2), (key2798, 2), (key2732, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2621, -1), (key2676, -1)]

def rawRow16328 : Integer.Sparse Key := [(key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2972, 2), (key2702, 2), (key2628, 2), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2885, 2), (key2798, 2), (key2644, 2), (key2835, -1), (key2732, -1), (key2798, -1), (key2644, -1), (key2676, -1), (key2621, -1)]

def rawRow16329 : Integer.Sparse Key := [(key2646, -1), (key2648, -1), (key2893, -1), (key2997, -1), (key2904, -1), (key3000, -1), (key2653, 2), (key2897, 2), (key2998, 2), (key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2628, 2), (key2648, 2), (key2782, 2), (key2938, 2), (key2904, 2), (key2983, 2), (key2641, -1), (key2653, -1), (key2795, -1), (key2943, -1), (key2897, -1), (key2976, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1)]

def rawRow16330 : Integer.Sparse Key := [(key2648, -1), (key2646, -1), (key2997, -1), (key2893, -1), (key3000, -1), (key2904, -1), (key2653, 2), (key2998, 2), (key2897, 2), (key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2648, 2), (key2628, 2), (key2938, 2), (key2782, 2), (key2983, 2), (key2904, 2), (key2653, -1), (key2641, -1), (key2943, -1), (key2795, -1), (key2976, -1), (key2897, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1)]

def rawRow16331 : Integer.Sparse Key := [(key2893, -1), (key2904, -1), (key2646, -1), (key3000, -1), (key2648, -1), (key2997, -1), (key2897, 2), (key2653, 2), (key2998, 2), (key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2782, 2), (key2904, 2), (key2628, 2), (key2983, 2), (key2648, 2), (key2938, 2), (key2795, -1), (key2897, -1), (key2641, -1), (key2976, -1), (key2653, -1), (key2943, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1)]

def rawRow16332 : Integer.Sparse Key := [(key2904, -1), (key2893, -1), (key3000, -1), (key2646, -1), (key2997, -1), (key2648, -1), (key2897, 2), (key2998, 2), (key2653, 2), (key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key2904, 2), (key2782, 2), (key2983, 2), (key2628, 2), (key2938, 2), (key2648, 2), (key2897, -1), (key2795, -1), (key2976, -1), (key2641, -1), (key2943, -1), (key2653, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1)]

def rawRow16333 : Integer.Sparse Key := [(key2997, -1), (key3000, -1), (key2648, -1), (key2904, -1), (key2646, -1), (key2893, -1), (key2998, 2), (key2653, 2), (key2897, 2), (key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2938, 2), (key2983, 2), (key2648, 2), (key2904, 2), (key2628, 2), (key2782, 2), (key2943, -1), (key2976, -1), (key2653, -1), (key2897, -1), (key2641, -1), (key2795, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1)]

def rawRow16334 : Integer.Sparse Key := [(key3000, -1), (key2997, -1), (key2904, -1), (key2648, -1), (key2893, -1), (key2646, -1), (key2998, 2), (key2897, 2), (key2653, 2), (key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2983, 2), (key2938, 2), (key2904, 2), (key2648, 2), (key2782, 2), (key2628, 2), (key2976, -1), (key2943, -1), (key2897, -1), (key2653, -1), (key2795, -1), (key2641, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1)]

def rawRow16335 : Integer.Sparse Key := [(key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2648, 2), (key2737, 2), (key2997, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2), (key2618, -1), (key2648, -1), (key2673, -1), (key2938, -1), (key2737, -1), (key2950, -1), (key2632, 2), (key2786, 2), (key2870, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1)]

def rawRow16336 : Integer.Sparse Key := [(key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2648, 2), (key2997, 2), (key2737, 2), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2), (key2648, -1), (key2618, -1), (key2938, -1), (key2673, -1), (key2950, -1), (key2737, -1), (key2632, 2), (key2870, 2), (key2786, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1)]

def rawRow16337 : Integer.Sparse Key := [(key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2737, 2), (key2648, 2), (key2997, 2), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2), (key2673, -1), (key2737, -1), (key2618, -1), (key2950, -1), (key2648, -1), (key2938, -1), (key2786, 2), (key2632, 2), (key2870, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1)]

def rawRow16338 : Integer.Sparse Key := [(key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2737, 2), (key2997, 2), (key2648, 2), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2), (key2737, -1), (key2673, -1), (key2950, -1), (key2618, -1), (key2938, -1), (key2648, -1), (key2786, 2), (key2870, 2), (key2632, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1)]

def rawRow16339 : Integer.Sparse Key := [(key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2997, 2), (key2648, 2), (key2737, 2), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2), (key2938, -1), (key2950, -1), (key2648, -1), (key2737, -1), (key2618, -1), (key2673, -1), (key2870, 2), (key2632, 2), (key2786, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1)]

def rawRow16340 : Integer.Sparse Key := [(key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2997, 2), (key2737, 2), (key2648, 2), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2), (key2950, -1), (key2938, -1), (key2737, -1), (key2648, -1), (key2673, -1), (key2618, -1), (key2870, 2), (key2786, 2), (key2632, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1)]

def rawRow16341 : Integer.Sparse Key := [(key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2646, 2), (key2735, 2), (key2893, 2), (key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2618, 2), (key2641, 2), (key2673, 2), (key2795, 2), (key2728, 2), (key2831, 2), (key2612, -1), (key2628, -1), (key2667, -1), (key2782, -1), (key2702, -1), (key2805, -1), (key2640, 2), (key2794, 2), (key2860, 2), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, -1), (key2809, -1)]

def rawRow16342 : Integer.Sparse Key := [(key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2646, 2), (key2893, 2), (key2735, 2), (key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2641, 2), (key2618, 2), (key2795, 2), (key2673, 2), (key2831, 2), (key2728, 2), (key2628, -1), (key2612, -1), (key2782, -1), (key2667, -1), (key2805, -1), (key2702, -1), (key2640, 2), (key2860, 2), (key2794, 2), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, -1), (key2786, -1)]

def rawRow16343 : Integer.Sparse Key := [(key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2735, 2), (key2646, 2), (key2893, 2), (key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2673, 2), (key2728, 2), (key2618, 2), (key2831, 2), (key2641, 2), (key2795, 2), (key2667, -1), (key2702, -1), (key2612, -1), (key2805, -1), (key2628, -1), (key2782, -1), (key2794, 2), (key2640, 2), (key2860, 2), (key2671, -1), (key2786, -1), (key2616, -1), (key2809, -1), (key2632, -1), (key2706, -1)]

def rawRow16344 : Integer.Sparse Key := [(key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2735, 2), (key2893, 2), (key2646, 2), (key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2728, 2), (key2673, 2), (key2831, 2), (key2618, 2), (key2795, 2), (key2641, 2), (key2702, -1), (key2667, -1), (key2805, -1), (key2612, -1), (key2782, -1), (key2628, -1), (key2794, 2), (key2860, 2), (key2640, 2), (key2786, -1), (key2671, -1), (key2809, -1), (key2616, -1), (key2706, -1), (key2632, -1)]

def rawRow16345 : Integer.Sparse Key := [(key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2893, 2), (key2646, 2), (key2735, 2), (key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2795, 2), (key2831, 2), (key2641, 2), (key2728, 2), (key2618, 2), (key2673, 2), (key2782, -1), (key2805, -1), (key2628, -1), (key2702, -1), (key2612, -1), (key2667, -1), (key2860, 2), (key2640, 2), (key2794, 2), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, -1), (key2671, -1)]

def rawRow16346 : Integer.Sparse Key := [(key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2893, 2), (key2735, 2), (key2646, 2), (key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2831, 2), (key2795, 2), (key2728, 2), (key2641, 2), (key2673, 2), (key2618, 2), (key2805, -1), (key2782, -1), (key2702, -1), (key2628, -1), (key2667, -1), (key2612, -1), (key2860, 2), (key2794, 2), (key2640, 2), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, -1), (key2616, -1)]

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

def rawRow16383 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2932, -2), (key2773, 6), (key2847, -2), (key2847, -2), (key2969, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2594, -2), (key2881, -2), (key2881, -2), (key2890, 6), (key2601, -2), (key2911, -2), (key2911, -2)]

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

def rawRow16384 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2770, -2), (key2773, 6), (key2847, -2), (key2969, -2), (key2847, -2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2881, -2), (key2594, -2), (key2881, -2), (key2890, 6), (key2911, -2), (key2601, -2), (key2911, -2)]

def rawRow16385 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2770, -2), (key2773, 6), (key2969, -2), (key2847, -2), (key2847, -2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2881, -2), (key2881, -2), (key2594, -2), (key2890, 6), (key2911, -2), (key2911, -2), (key2601, -2)]

def rawRow16386 : Integer.Sparse Key := [(key2770, -2), (key2773, -2), (key2932, -2), (key2770, 6), (key2878, -2), (key2881, -2), (key2990, -2), (key2591, 2), (key2594, 2), (key2847, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2591, -2), (key2847, -2), (key2878, -2), (key2911, 6), (key2601, -2), (key2890, -2), (key2911, -2)]

def rawRow16387 : Integer.Sparse Key := [(key2773, -2), (key2770, -2), (key2932, -2), (key2770, 6), (key2881, -2), (key2878, -2), (key2990, -2), (key2594, 2), (key2591, 2), (key2881, 2), (key2847, 2), (key2990, 2), (key2969, 2), (key2591, -2), (key2878, -2), (key2847, -2), (key2911, 6), (key2601, -2), (key2911, -2), (key2890, -2)]

def rawRow16388 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2773, -2), (key2770, 6), (key2878, -2), (key2990, -2), (key2881, -2), (key2847, 2), (key2969, 2), (key2591, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2847, -2), (key2591, -2), (key2878, -2), (key2911, 6), (key2890, -2), (key2601, -2), (key2911, -2)]

def rawRow16389 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2773, -2), (key2770, 6), (key2990, -2), (key2878, -2), (key2881, -2), (key2969, 2), (key2847, 2), (key2990, 2), (key2591, 2), (key2881, 2), (key2594, 2), (key2847, -2), (key2878, -2), (key2591, -2), (key2911, 6), (key2890, -2), (key2911, -2), (key2601, -2)]

def rawRow16390 : Integer.Sparse Key := [(key2773, -2), (key2932, -2), (key2770, -2), (key2770, 6), (key2881, -2), (key2990, -2), (key2878, -2), (key2881, 2), (key2990, 2), (key2594, 2), (key2969, 2), (key2591, 2), (key2847, 2), (key2878, -2), (key2591, -2), (key2847, -2), (key2911, 6), (key2911, -2), (key2601, -2), (key2890, -2)]

def rawRow16391 : Integer.Sparse Key := [(key2932, -2), (key2773, -2), (key2770, -2), (key2770, 6), (key2990, -2), (key2881, -2), (key2878, -2), (key2990, 2), (key2881, 2), (key2969, 2), (key2594, 2), (key2847, 2), (key2591, 2), (key2878, -2), (key2847, -2), (key2591, -2), (key2911, 6), (key2911, -2), (key2890, -2), (key2601, -2)]

def rawRow16392 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2969, -2), (key2890, 6), (key2770, -2), (key2770, -2), (key2932, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2601, -2), (key2911, -2), (key2911, -2), (key2773, 6), (key2594, -2), (key2881, -2), (key2881, -2)]

def rawRow16393 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2847, -2), (key2890, 6), (key2770, -2), (key2932, -2), (key2770, -2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2911, -2), (key2601, -2), (key2911, -2), (key2773, 6), (key2881, -2), (key2594, -2), (key2881, -2)]

def rawRow16394 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2847, -2), (key2890, 6), (key2932, -2), (key2770, -2), (key2770, -2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2911, -2), (key2911, -2), (key2601, -2), (key2773, 6), (key2881, -2), (key2881, -2), (key2594, -2)]

def rawRow16395 : Integer.Sparse Key := [(key2847, -2), (key2890, -2), (key2969, -2), (key2847, 6), (key2878, -2), (key2911, -2), (key2990, -2), (key2591, 2), (key2601, 2), (key2770, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2591, -2), (key2770, -2), (key2878, -2), (key2881, 6), (key2594, -2), (key2773, -2), (key2881, -2)]

def rawRow16396 : Integer.Sparse Key := [(key2890, -2), (key2847, -2), (key2969, -2), (key2847, 6), (key2911, -2), (key2878, -2), (key2990, -2), (key2601, 2), (key2591, 2), (key2911, 2), (key2770, 2), (key2990, 2), (key2932, 2), (key2591, -2), (key2878, -2), (key2770, -2), (key2881, 6), (key2594, -2), (key2881, -2), (key2773, -2)]

def rawRow16397 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2890, -2), (key2847, 6), (key2878, -2), (key2990, -2), (key2911, -2), (key2770, 2), (key2932, 2), (key2591, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2770, -2), (key2591, -2), (key2878, -2), (key2881, 6), (key2773, -2), (key2594, -2), (key2881, -2)]

def rawRow16398 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2890, -2), (key2847, 6), (key2990, -2), (key2878, -2), (key2911, -2), (key2932, 2), (key2770, 2), (key2990, 2), (key2591, 2), (key2911, 2), (key2601, 2), (key2770, -2), (key2878, -2), (key2591, -2), (key2881, 6), (key2773, -2), (key2881, -2), (key2594, -2)]

def rawRow16399 : Integer.Sparse Key := [(key2890, -2), (key2969, -2), (key2847, -2), (key2847, 6), (key2911, -2), (key2990, -2), (key2878, -2), (key2911, 2), (key2990, 2), (key2601, 2), (key2932, 2), (key2591, 2), (key2770, 2), (key2878, -2), (key2591, -2), (key2770, -2), (key2881, 6), (key2881, -2), (key2594, -2), (key2773, -2)]

def rawRow16400 : Integer.Sparse Key := [(key2969, -2), (key2890, -2), (key2847, -2), (key2847, 6), (key2990, -2), (key2911, -2), (key2878, -2), (key2990, 2), (key2911, 2), (key2932, 2), (key2601, 2), (key2770, 2), (key2591, 2), (key2878, -2), (key2770, -2), (key2591, -2), (key2881, 6), (key2881, -2), (key2773, -2), (key2594, -2)]

def rawRow16401 : Integer.Sparse Key := [(key2878, -2), (key2881, -2), (key2990, -2), (key2911, 6), (key2770, -2), (key2773, -2), (key2932, -2), (key2591, 2), (key2594, 2), (key2847, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2601, -2), (key2890, -2), (key2911, -2), (key2770, 6), (key2591, -2), (key2847, -2), (key2878, -2)]

def rawRow16402 : Integer.Sparse Key := [(key2881, -2), (key2878, -2), (key2990, -2), (key2911, 6), (key2773, -2), (key2770, -2), (key2932, -2), (key2594, 2), (key2591, 2), (key2881, 2), (key2847, 2), (key2990, 2), (key2969, 2), (key2601, -2), (key2911, -2), (key2890, -2), (key2770, 6), (key2591, -2), (key2878, -2), (key2847, -2)]

def rawRow16403 : Integer.Sparse Key := [(key2878, -2), (key2990, -2), (key2881, -2), (key2911, 6), (key2770, -2), (key2932, -2), (key2773, -2), (key2847, 2), (key2969, 2), (key2591, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2890, -2), (key2601, -2), (key2911, -2), (key2770, 6), (key2847, -2), (key2591, -2), (key2878, -2)]

def rawRow16404 : Integer.Sparse Key := [(key2990, -2), (key2878, -2), (key2881, -2), (key2911, 6), (key2932, -2), (key2770, -2), (key2773, -2), (key2969, 2), (key2847, 2), (key2990, 2), (key2591, 2), (key2881, 2), (key2594, 2), (key2890, -2), (key2911, -2), (key2601, -2), (key2770, 6), (key2847, -2), (key2878, -2), (key2591, -2)]

def rawRow16405 : Integer.Sparse Key := [(key2881, -2), (key2990, -2), (key2878, -2), (key2911, 6), (key2773, -2), (key2932, -2), (key2770, -2), (key2881, 2), (key2990, 2), (key2594, 2), (key2969, 2), (key2591, 2), (key2847, 2), (key2911, -2), (key2601, -2), (key2890, -2), (key2770, 6), (key2878, -2), (key2591, -2), (key2847, -2)]

def rawRow16406 : Integer.Sparse Key := [(key2990, -2), (key2881, -2), (key2878, -2), (key2911, 6), (key2932, -2), (key2773, -2), (key2770, -2), (key2990, 2), (key2881, 2), (key2969, 2), (key2594, 2), (key2847, 2), (key2591, 2), (key2911, -2), (key2890, -2), (key2601, -2), (key2770, 6), (key2878, -2), (key2847, -2), (key2591, -2)]

def rawRow16407 : Integer.Sparse Key := [(key2878, -2), (key2911, -2), (key2990, -2), (key2881, 6), (key2847, -2), (key2890, -2), (key2969, -2), (key2591, 2), (key2601, 2), (key2770, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2594, -2), (key2773, -2), (key2881, -2), (key2847, 6), (key2591, -2), (key2770, -2), (key2878, -2)]

def rawRow16408 : Integer.Sparse Key := [(key2911, -2), (key2878, -2), (key2990, -2), (key2881, 6), (key2890, -2), (key2847, -2), (key2969, -2), (key2601, 2), (key2591, 2), (key2911, 2), (key2770, 2), (key2990, 2), (key2932, 2), (key2594, -2), (key2881, -2), (key2773, -2), (key2847, 6), (key2591, -2), (key2878, -2), (key2770, -2)]

def rawRow16409 : Integer.Sparse Key := [(key2878, -2), (key2990, -2), (key2911, -2), (key2881, 6), (key2847, -2), (key2969, -2), (key2890, -2), (key2770, 2), (key2932, 2), (key2591, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2773, -2), (key2594, -2), (key2881, -2), (key2847, 6), (key2770, -2), (key2591, -2), (key2878, -2)]

def rawRow16410 : Integer.Sparse Key := [(key2990, -2), (key2878, -2), (key2911, -2), (key2881, 6), (key2969, -2), (key2847, -2), (key2890, -2), (key2932, 2), (key2770, 2), (key2990, 2), (key2591, 2), (key2911, 2), (key2601, 2), (key2773, -2), (key2881, -2), (key2594, -2), (key2847, 6), (key2770, -2), (key2878, -2), (key2591, -2)]

def rawRow16411 : Integer.Sparse Key := [(key2911, -2), (key2990, -2), (key2878, -2), (key2881, 6), (key2890, -2), (key2969, -2), (key2847, -2), (key2911, 2), (key2990, 2), (key2601, 2), (key2932, 2), (key2591, 2), (key2770, 2), (key2881, -2), (key2594, -2), (key2773, -2), (key2847, 6), (key2878, -2), (key2591, -2), (key2770, -2)]

def rawRow16412 : Integer.Sparse Key := [(key2990, -2), (key2911, -2), (key2878, -2), (key2881, 6), (key2969, -2), (key2890, -2), (key2847, -2), (key2990, 2), (key2911, 2), (key2932, 2), (key2601, 2), (key2770, 2), (key2591, 2), (key2881, -2), (key2773, -2), (key2594, -2), (key2847, 6), (key2878, -2), (key2770, -2), (key2591, -2)]

def rawRow16413 : Integer.Sparse Key := [(key2881, -2), (key2911, -2), (key2990, -2), (key2878, 6), (key2881, -2), (key2911, -2), (key2990, -2), (key2594, 2), (key2601, 2), (key2773, 2), (key2890, 2), (key2932, 2), (key2969, 2), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6), (key2591, -2), (key2770, -2), (key2847, -2)]

def rawRow16414 : Integer.Sparse Key := [(key2911, -2), (key2881, -2), (key2990, -2), (key2878, 6), (key2911, -2), (key2881, -2), (key2990, -2), (key2601, 2), (key2594, 2), (key2890, 2), (key2773, 2), (key2969, 2), (key2932, 2), (key2591, -2), (key2847, -2), (key2770, -2), (key2878, 6), (key2591, -2), (key2847, -2), (key2770, -2)]

def rawRow16415 : Integer.Sparse Key := [(key2881, -2), (key2990, -2), (key2911, -2), (key2878, 6), (key2881, -2), (key2990, -2), (key2911, -2), (key2773, 2), (key2932, 2), (key2594, 2), (key2969, 2), (key2601, 2), (key2890, 2), (key2770, -2), (key2591, -2), (key2847, -2), (key2878, 6), (key2770, -2), (key2591, -2), (key2847, -2)]

def rawRow16416 : Integer.Sparse Key := [(key2990, -2), (key2881, -2), (key2911, -2), (key2878, 6), (key2990, -2), (key2881, -2), (key2911, -2), (key2932, 2), (key2773, 2), (key2969, 2), (key2594, 2), (key2890, 2), (key2601, 2), (key2770, -2), (key2847, -2), (key2591, -2), (key2878, 6), (key2770, -2), (key2847, -2), (key2591, -2)]

def rawRow16417 : Integer.Sparse Key := [(key2911, -2), (key2990, -2), (key2881, -2), (key2878, 6), (key2911, -2), (key2990, -2), (key2881, -2), (key2890, 2), (key2969, 2), (key2601, 2), (key2932, 2), (key2594, 2), (key2773, 2), (key2847, -2), (key2591, -2), (key2770, -2), (key2878, 6), (key2847, -2), (key2591, -2), (key2770, -2)]

def rawRow16418 : Integer.Sparse Key := [(key2990, -2), (key2911, -2), (key2881, -2), (key2878, 6), (key2990, -2), (key2911, -2), (key2881, -2), (key2969, 2), (key2890, 2), (key2932, 2), (key2601, 2), (key2773, 2), (key2594, 2), (key2847, -2), (key2770, -2), (key2591, -2), (key2878, 6), (key2847, -2), (key2770, -2), (key2591, -2)]

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

def rawRow16455 : Integer.Sparse Key := [(key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2619, 2), (key2832, 2), (key2832, 2), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key2992, 2), (key2992, 2), (key2642, -1), (key2642, -1), (key2729, -1), (key2729, -1), (key2883, -1), (key2883, -1), (key2649, 2), (key2905, 2), (key2905, 2), (key2654, -1), (key2654, -1), (key2748, -1), (key2748, -1), (key2913, -1), (key2913, -1)]

def rawRow16456 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2832, 2), (key2619, 2), (key2832, 2), (key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2726, 2), (key2992, 2), (key2640, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2729, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2905, 2), (key2649, 2), (key2905, 2), (key2748, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2748, -1)]

def rawRow16457 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2832, 2), (key2832, 2), (key2619, 2), (key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2992, 2), (key2726, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2883, -1), (key2729, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2642, -1), (key2905, 2), (key2905, 2), (key2649, 2), (key2913, -1), (key2748, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2654, -1)]

def rawRow16458 : Integer.Sparse Key := [(key2616, -1), (key2619, -1), (key2809, -1), (key2832, -1), (key2951, -1), (key2961, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2640, -1), (key2642, -1), (key2860, -1), (key2883, -1), (key2977, -1), (key2992, -1), (key2632, 2), (key2642, 2), (key2706, 2), (key2729, 2), (key2977, 2), (key2984, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1), (key2654, 2), (key2898, 2), (key2913, 2), (key2649, -1), (key2654, -1), (key2738, -1), (key2748, -1), (key2898, -1), (key2905, -1)]

def rawRow16459 : Integer.Sparse Key := [(key2619, -1), (key2616, -1), (key2832, -1), (key2809, -1), (key2961, -1), (key2951, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2642, -1), (key2640, -1), (key2883, -1), (key2860, -1), (key2992, -1), (key2977, -1), (key2642, 2), (key2632, 2), (key2729, 2), (key2706, 2), (key2984, 2), (key2977, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1), (key2654, 2), (key2913, 2), (key2898, 2), (key2654, -1), (key2649, -1), (key2748, -1), (key2738, -1), (key2905, -1), (key2898, -1)]

def rawRow16460 : Integer.Sparse Key := [(key2809, -1), (key2951, -1), (key2616, -1), (key2961, -1), (key2619, -1), (key2832, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2860, -1), (key2977, -1), (key2640, -1), (key2992, -1), (key2642, -1), (key2883, -1), (key2706, 2), (key2977, 2), (key2632, 2), (key2984, 2), (key2642, 2), (key2729, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2898, 2), (key2654, 2), (key2913, 2), (key2738, -1), (key2898, -1), (key2649, -1), (key2905, -1), (key2654, -1), (key2748, -1)]

def rawRow16461 : Integer.Sparse Key := [(key2951, -1), (key2809, -1), (key2961, -1), (key2616, -1), (key2832, -1), (key2619, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key2977, -1), (key2860, -1), (key2992, -1), (key2640, -1), (key2883, -1), (key2642, -1), (key2977, 2), (key2706, 2), (key2984, 2), (key2632, 2), (key2729, 2), (key2642, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1), (key2898, 2), (key2913, 2), (key2654, 2), (key2898, -1), (key2738, -1), (key2905, -1), (key2649, -1), (key2748, -1), (key2654, -1)]

def rawRow16462 : Integer.Sparse Key := [(key2832, -1), (key2961, -1), (key2619, -1), (key2951, -1), (key2616, -1), (key2809, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2883, -1), (key2992, -1), (key2642, -1), (key2977, -1), (key2640, -1), (key2860, -1), (key2729, 2), (key2984, 2), (key2642, 2), (key2977, 2), (key2632, 2), (key2706, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1), (key2913, 2), (key2654, 2), (key2898, 2), (key2748, -1), (key2905, -1), (key2654, -1), (key2898, -1), (key2649, -1), (key2738, -1)]

def rawRow16463 : Integer.Sparse Key := [(key2961, -1), (key2832, -1), (key2951, -1), (key2619, -1), (key2809, -1), (key2616, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key2992, -1), (key2883, -1), (key2977, -1), (key2642, -1), (key2860, -1), (key2640, -1), (key2984, 2), (key2729, 2), (key2977, 2), (key2642, 2), (key2706, 2), (key2632, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2913, 2), (key2898, 2), (key2654, 2), (key2905, -1), (key2748, -1), (key2898, -1), (key2654, -1), (key2738, -1), (key2649, -1)]

def rawRow16464 : Integer.Sparse Key := [(key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2649, 2), (key2905, 2), (key2905, 2), (key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key2992, 2), (key2992, 2), (key2654, -1), (key2654, -1), (key2748, -1), (key2748, -1), (key2913, -1), (key2913, -1), (key2619, 2), (key2832, 2), (key2832, 2), (key2642, -1), (key2642, -1), (key2729, -1), (key2729, -1), (key2883, -1), (key2883, -1)]

def rawRow16465 : Integer.Sparse Key := [(key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2905, 2), (key2649, 2), (key2905, 2), (key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2726, 2), (key2992, 2), (key2640, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2748, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2832, 2), (key2619, 2), (key2832, 2), (key2729, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2729, -1)]

def rawRow16466 : Integer.Sparse Key := [(key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2905, 2), (key2905, 2), (key2649, 2), (key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2992, 2), (key2726, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2913, -1), (key2748, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2654, -1), (key2832, 2), (key2832, 2), (key2619, 2), (key2883, -1), (key2729, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2642, -1)]

def rawRow16467 : Integer.Sparse Key := [(key2632, -1), (key2649, -1), (key2786, -1), (key2905, -1), (key2939, -1), (key2984, -1), (key2632, 2), (key2786, 2), (key2870, 2), (key2640, -1), (key2654, -1), (key2794, -1), (key2913, -1), (key2944, -1), (key2992, -1), (key2616, 2), (key2654, 2), (key2671, 2), (key2748, 2), (key2944, 2), (key2961, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1), (key2642, 2), (key2796, 2), (key2883, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2729, -1), (key2796, -1), (key2832, -1)]

def rawRow16468 : Integer.Sparse Key := [(key2649, -1), (key2632, -1), (key2905, -1), (key2786, -1), (key2984, -1), (key2939, -1), (key2632, 2), (key2870, 2), (key2786, 2), (key2654, -1), (key2640, -1), (key2913, -1), (key2794, -1), (key2992, -1), (key2944, -1), (key2654, 2), (key2616, 2), (key2748, 2), (key2671, 2), (key2961, 2), (key2944, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1), (key2642, 2), (key2883, 2), (key2796, 2), (key2642, -1), (key2619, -1), (key2729, -1), (key2674, -1), (key2832, -1), (key2796, -1)]

def rawRow16469 : Integer.Sparse Key := [(key2786, -1), (key2939, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2786, 2), (key2632, 2), (key2870, 2), (key2794, -1), (key2944, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2671, 2), (key2944, 2), (key2616, 2), (key2961, 2), (key2654, 2), (key2748, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2796, 2), (key2642, 2), (key2883, 2), (key2674, -1), (key2796, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2729, -1)]

def rawRow16470 : Integer.Sparse Key := [(key2939, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2905, -1), (key2649, -1), (key2786, 2), (key2870, 2), (key2632, 2), (key2944, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2913, -1), (key2654, -1), (key2944, 2), (key2671, 2), (key2961, 2), (key2616, 2), (key2748, 2), (key2654, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1), (key2796, 2), (key2883, 2), (key2642, 2), (key2796, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2729, -1), (key2642, -1)]

def rawRow16471 : Integer.Sparse Key := [(key2905, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2632, -1), (key2786, -1), (key2870, 2), (key2632, 2), (key2786, 2), (key2913, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2640, -1), (key2794, -1), (key2748, 2), (key2961, 2), (key2654, 2), (key2944, 2), (key2616, 2), (key2671, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1), (key2883, 2), (key2642, 2), (key2796, 2), (key2729, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2619, -1), (key2674, -1)]

def rawRow16472 : Integer.Sparse Key := [(key2984, -1), (key2905, -1), (key2939, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2870, 2), (key2786, 2), (key2632, 2), (key2992, -1), (key2913, -1), (key2944, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2961, 2), (key2748, 2), (key2944, 2), (key2654, 2), (key2671, 2), (key2616, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2883, 2), (key2796, 2), (key2642, 2), (key2832, -1), (key2729, -1), (key2796, -1), (key2642, -1), (key2674, -1), (key2619, -1)]

def rawRow16473 : Integer.Sparse Key := [(key2640, -1), (key2642, -1), (key2860, -1), (key2883, -1), (key2977, -1), (key2992, -1), (key2654, 2), (key2898, 2), (key2913, 2), (key2616, -1), (key2619, -1), (key2809, -1), (key2832, -1), (key2951, -1), (key2961, -1), (key2632, 2), (key2642, 2), (key2706, 2), (key2729, 2), (key2977, 2), (key2984, 2), (key2649, -1), (key2654, -1), (key2738, -1), (key2748, -1), (key2898, -1), (key2905, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1)]

def rawRow16474 : Integer.Sparse Key := [(key2642, -1), (key2640, -1), (key2883, -1), (key2860, -1), (key2992, -1), (key2977, -1), (key2654, 2), (key2913, 2), (key2898, 2), (key2619, -1), (key2616, -1), (key2832, -1), (key2809, -1), (key2961, -1), (key2951, -1), (key2642, 2), (key2632, 2), (key2729, 2), (key2706, 2), (key2984, 2), (key2977, 2), (key2654, -1), (key2649, -1), (key2748, -1), (key2738, -1), (key2905, -1), (key2898, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1)]

def rawRow16475 : Integer.Sparse Key := [(key2860, -1), (key2977, -1), (key2640, -1), (key2992, -1), (key2642, -1), (key2883, -1), (key2898, 2), (key2654, 2), (key2913, 2), (key2809, -1), (key2951, -1), (key2616, -1), (key2961, -1), (key2619, -1), (key2832, -1), (key2706, 2), (key2977, 2), (key2632, 2), (key2984, 2), (key2642, 2), (key2729, 2), (key2738, -1), (key2898, -1), (key2649, -1), (key2905, -1), (key2654, -1), (key2748, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1)]

def rawRow16476 : Integer.Sparse Key := [(key2977, -1), (key2860, -1), (key2992, -1), (key2640, -1), (key2883, -1), (key2642, -1), (key2898, 2), (key2913, 2), (key2654, 2), (key2951, -1), (key2809, -1), (key2961, -1), (key2616, -1), (key2832, -1), (key2619, -1), (key2977, 2), (key2706, 2), (key2984, 2), (key2632, 2), (key2729, 2), (key2642, 2), (key2898, -1), (key2738, -1), (key2905, -1), (key2649, -1), (key2748, -1), (key2654, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1)]

def rawRow16477 : Integer.Sparse Key := [(key2883, -1), (key2992, -1), (key2642, -1), (key2977, -1), (key2640, -1), (key2860, -1), (key2913, 2), (key2654, 2), (key2898, 2), (key2832, -1), (key2961, -1), (key2619, -1), (key2951, -1), (key2616, -1), (key2809, -1), (key2729, 2), (key2984, 2), (key2642, 2), (key2977, 2), (key2632, 2), (key2706, 2), (key2748, -1), (key2905, -1), (key2654, -1), (key2898, -1), (key2649, -1), (key2738, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1)]

def rawRow16478 : Integer.Sparse Key := [(key2992, -1), (key2883, -1), (key2977, -1), (key2642, -1), (key2860, -1), (key2640, -1), (key2913, 2), (key2898, 2), (key2654, 2), (key2961, -1), (key2832, -1), (key2951, -1), (key2619, -1), (key2809, -1), (key2616, -1), (key2984, 2), (key2729, 2), (key2977, 2), (key2642, 2), (key2706, 2), (key2632, 2), (key2905, -1), (key2748, -1), (key2898, -1), (key2654, -1), (key2738, -1), (key2649, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1)]

def rawRow16479 : Integer.Sparse Key := [(key2640, -1), (key2654, -1), (key2794, -1), (key2913, -1), (key2944, -1), (key2992, -1), (key2642, 2), (key2796, 2), (key2883, 2), (key2632, -1), (key2649, -1), (key2786, -1), (key2905, -1), (key2939, -1), (key2984, -1), (key2616, 2), (key2654, 2), (key2671, 2), (key2748, 2), (key2944, 2), (key2961, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2729, -1), (key2796, -1), (key2832, -1), (key2632, 2), (key2786, 2), (key2870, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1)]

def rawRow16480 : Integer.Sparse Key := [(key2654, -1), (key2640, -1), (key2913, -1), (key2794, -1), (key2992, -1), (key2944, -1), (key2642, 2), (key2883, 2), (key2796, 2), (key2649, -1), (key2632, -1), (key2905, -1), (key2786, -1), (key2984, -1), (key2939, -1), (key2654, 2), (key2616, 2), (key2748, 2), (key2671, 2), (key2961, 2), (key2944, 2), (key2642, -1), (key2619, -1), (key2729, -1), (key2674, -1), (key2832, -1), (key2796, -1), (key2632, 2), (key2870, 2), (key2786, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1)]

def rawRow16481 : Integer.Sparse Key := [(key2794, -1), (key2944, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2796, 2), (key2642, 2), (key2883, 2), (key2786, -1), (key2939, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2671, 2), (key2944, 2), (key2616, 2), (key2961, 2), (key2654, 2), (key2748, 2), (key2674, -1), (key2796, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2729, -1), (key2786, 2), (key2632, 2), (key2870, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1)]

def rawRow16482 : Integer.Sparse Key := [(key2944, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2913, -1), (key2654, -1), (key2796, 2), (key2883, 2), (key2642, 2), (key2939, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2905, -1), (key2649, -1), (key2944, 2), (key2671, 2), (key2961, 2), (key2616, 2), (key2748, 2), (key2654, 2), (key2796, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2729, -1), (key2642, -1), (key2786, 2), (key2870, 2), (key2632, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1)]

def rawRow16483 : Integer.Sparse Key := [(key2913, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2640, -1), (key2794, -1), (key2883, 2), (key2642, 2), (key2796, 2), (key2905, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2632, -1), (key2786, -1), (key2748, 2), (key2961, 2), (key2654, 2), (key2944, 2), (key2616, 2), (key2671, 2), (key2729, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2619, -1), (key2674, -1), (key2870, 2), (key2632, 2), (key2786, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1)]

def rawRow16484 : Integer.Sparse Key := [(key2992, -1), (key2913, -1), (key2944, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2883, 2), (key2796, 2), (key2642, 2), (key2984, -1), (key2905, -1), (key2939, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2961, 2), (key2748, 2), (key2944, 2), (key2654, 2), (key2671, 2), (key2616, 2), (key2832, -1), (key2729, -1), (key2796, -1), (key2642, -1), (key2674, -1), (key2619, -1), (key2870, 2), (key2786, 2), (key2632, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1)]

def rawRow16485 : Integer.Sparse Key := [(key2642, -1), (key2654, -1), (key2796, -1), (key2898, -1), (key2944, -1), (key2977, -1), (key2640, 2), (key2794, 2), (key2860, 2), (key2642, -1), (key2654, -1), (key2796, -1), (key2898, -1), (key2944, -1), (key2977, -1), (key2619, 2), (key2649, 2), (key2674, 2), (key2738, 2), (key2939, 2), (key2951, 2), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, -1), (key2809, -1), (key2640, 2), (key2794, 2), (key2860, 2), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, -1), (key2809, -1)]

def rawRow16486 : Integer.Sparse Key := [(key2654, -1), (key2642, -1), (key2898, -1), (key2796, -1), (key2977, -1), (key2944, -1), (key2640, 2), (key2860, 2), (key2794, 2), (key2654, -1), (key2642, -1), (key2898, -1), (key2796, -1), (key2977, -1), (key2944, -1), (key2649, 2), (key2619, 2), (key2738, 2), (key2674, 2), (key2951, 2), (key2939, 2), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, -1), (key2786, -1), (key2640, 2), (key2860, 2), (key2794, 2), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, -1), (key2786, -1)]

def rawRow16487 : Integer.Sparse Key := [(key2796, -1), (key2944, -1), (key2642, -1), (key2977, -1), (key2654, -1), (key2898, -1), (key2794, 2), (key2640, 2), (key2860, 2), (key2796, -1), (key2944, -1), (key2642, -1), (key2977, -1), (key2654, -1), (key2898, -1), (key2674, 2), (key2939, 2), (key2619, 2), (key2951, 2), (key2649, 2), (key2738, 2), (key2671, -1), (key2786, -1), (key2616, -1), (key2809, -1), (key2632, -1), (key2706, -1), (key2794, 2), (key2640, 2), (key2860, 2), (key2671, -1), (key2786, -1), (key2616, -1), (key2809, -1), (key2632, -1), (key2706, -1)]

def rawRow16488 : Integer.Sparse Key := [(key2944, -1), (key2796, -1), (key2977, -1), (key2642, -1), (key2898, -1), (key2654, -1), (key2794, 2), (key2860, 2), (key2640, 2), (key2944, -1), (key2796, -1), (key2977, -1), (key2642, -1), (key2898, -1), (key2654, -1), (key2939, 2), (key2674, 2), (key2951, 2), (key2619, 2), (key2738, 2), (key2649, 2), (key2786, -1), (key2671, -1), (key2809, -1), (key2616, -1), (key2706, -1), (key2632, -1), (key2794, 2), (key2860, 2), (key2640, 2), (key2786, -1), (key2671, -1), (key2809, -1), (key2616, -1), (key2706, -1), (key2632, -1)]

def rawRow16489 : Integer.Sparse Key := [(key2898, -1), (key2977, -1), (key2654, -1), (key2944, -1), (key2642, -1), (key2796, -1), (key2860, 2), (key2640, 2), (key2794, 2), (key2898, -1), (key2977, -1), (key2654, -1), (key2944, -1), (key2642, -1), (key2796, -1), (key2738, 2), (key2951, 2), (key2649, 2), (key2939, 2), (key2619, 2), (key2674, 2), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, -1), (key2671, -1), (key2860, 2), (key2640, 2), (key2794, 2), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, -1), (key2671, -1)]

def rawRow16490 : Integer.Sparse Key := [(key2977, -1), (key2898, -1), (key2944, -1), (key2654, -1), (key2796, -1), (key2642, -1), (key2860, 2), (key2794, 2), (key2640, 2), (key2977, -1), (key2898, -1), (key2944, -1), (key2654, -1), (key2796, -1), (key2642, -1), (key2951, 2), (key2738, 2), (key2939, 2), (key2649, 2), (key2674, 2), (key2619, 2), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, -1), (key2616, -1), (key2860, 2), (key2794, 2), (key2640, 2), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, -1), (key2616, -1)]

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

def rawRow16527 : Integer.Sparse Key := [(key2407, 2), (key2441, 2), (key2441, 2), (key2410, -2), (key2410, -2), (key2445, -2), (key2848, 2), (key2970, 2), (key2970, 2), (key2595, -1), (key2595, -1), (key2882, -1), (key2882, -1), (key2993, -1), (key2993, -1), (key2891, -2), (key2891, -2), (key2996, -2), (key2602, -1), (key2602, -1), (key2912, -1), (key2912, -1), (key3003, -1), (key3003, -1), (key2603, 4), (key2914, 4), (key2914, 4)]

def rawRow16528 : Integer.Sparse Key := [(key2441, 2), (key2407, 2), (key2441, 2), (key2410, -2), (key2445, -2), (key2410, -2), (key2970, 2), (key2848, 2), (key2970, 2), (key2882, -1), (key2993, -1), (key2595, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2891, -2), (key2996, -2), (key2891, -2), (key2912, -1), (key3003, -1), (key2602, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2914, 4), (key2603, 4), (key2914, 4)]

def rawRow16529 : Integer.Sparse Key := [(key2441, 2), (key2441, 2), (key2407, 2), (key2445, -2), (key2410, -2), (key2410, -2), (key2970, 2), (key2970, 2), (key2848, 2), (key2993, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2595, -1), (key2996, -2), (key2891, -2), (key2891, -2), (key3003, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2602, -1), (key2914, 4), (key2914, 4), (key2603, 4)]

def rawRow16530 : Integer.Sparse Key := [(key2410, 2), (key2441, 2), (key2445, 2), (key2407, -2), (key2410, -2), (key2441, -2), (key2882, 2), (key2991, 2), (key2993, 2), (key2592, -1), (key2595, -1), (key2848, -1), (key2882, -1), (key2970, -1), (key2991, -1), (key2912, -2), (key2914, -2), (key3003, -2), (key2602, -1), (key2603, -1), (key2891, -1), (key2914, -1), (key2996, -1), (key3003, -1), (key2602, 4), (key2891, 4), (key2912, 4)]

def rawRow16531 : Integer.Sparse Key := [(key2410, 2), (key2445, 2), (key2441, 2), (key2410, -2), (key2407, -2), (key2441, -2), (key2882, 2), (key2993, 2), (key2991, 2), (key2595, -1), (key2592, -1), (key2882, -1), (key2848, -1), (key2991, -1), (key2970, -1), (key2914, -2), (key2912, -2), (key3003, -2), (key2603, -1), (key2602, -1), (key2914, -1), (key2891, -1), (key3003, -1), (key2996, -1), (key2602, 4), (key2912, 4), (key2891, 4)]

def rawRow16532 : Integer.Sparse Key := [(key2441, 2), (key2410, 2), (key2445, 2), (key2407, -2), (key2441, -2), (key2410, -2), (key2991, 2), (key2882, 2), (key2993, 2), (key2848, -1), (key2970, -1), (key2592, -1), (key2991, -1), (key2595, -1), (key2882, -1), (key2912, -2), (key3003, -2), (key2914, -2), (key2891, -1), (key2996, -1), (key2602, -1), (key3003, -1), (key2603, -1), (key2914, -1), (key2891, 4), (key2602, 4), (key2912, 4)]

def rawRow16533 : Integer.Sparse Key := [(key2441, 2), (key2445, 2), (key2410, 2), (key2441, -2), (key2407, -2), (key2410, -2), (key2991, 2), (key2993, 2), (key2882, 2), (key2970, -1), (key2848, -1), (key2991, -1), (key2592, -1), (key2882, -1), (key2595, -1), (key3003, -2), (key2912, -2), (key2914, -2), (key2996, -1), (key2891, -1), (key3003, -1), (key2602, -1), (key2914, -1), (key2603, -1), (key2891, 4), (key2912, 4), (key2602, 4)]

def rawRow16534 : Integer.Sparse Key := [(key2445, 2), (key2410, 2), (key2441, 2), (key2410, -2), (key2441, -2), (key2407, -2), (key2993, 2), (key2882, 2), (key2991, 2), (key2882, -1), (key2991, -1), (key2595, -1), (key2970, -1), (key2592, -1), (key2848, -1), (key2914, -2), (key3003, -2), (key2912, -2), (key2914, -1), (key3003, -1), (key2603, -1), (key2996, -1), (key2602, -1), (key2891, -1), (key2912, 4), (key2602, 4), (key2891, 4)]

def rawRow16535 : Integer.Sparse Key := [(key2445, 2), (key2441, 2), (key2410, 2), (key2441, -2), (key2410, -2), (key2407, -2), (key2993, 2), (key2991, 2), (key2882, 2), (key2991, -1), (key2882, -1), (key2970, -1), (key2595, -1), (key2848, -1), (key2592, -1), (key3003, -2), (key2914, -2), (key2912, -2), (key3003, -1), (key2914, -1), (key2996, -1), (key2603, -1), (key2891, -1), (key2602, -1), (key2912, 4), (key2891, 4), (key2602, 4)]

def rawRow16536 : Integer.Sparse Key := [(key2473, 2), (key2507, 2), (key2507, 2), (key2483, -2), (key2483, -2), (key2526, -2), (key2407, 2), (key2441, 2), (key2441, 2), (key2602, -1), (key2602, -1), (key2912, -1), (key2912, -1), (key3003, -1), (key3003, -1), (key2774, -2), (key2774, -2), (key2934, -2), (key2595, -1), (key2595, -1), (key2882, -1), (key2882, -1), (key2993, -1), (key2993, -1), (key2603, 4), (key2914, 4), (key2914, 4)]

def rawRow16537 : Integer.Sparse Key := [(key2507, 2), (key2473, 2), (key2507, 2), (key2483, -2), (key2526, -2), (key2483, -2), (key2441, 2), (key2407, 2), (key2441, 2), (key2912, -1), (key3003, -1), (key2602, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2774, -2), (key2934, -2), (key2774, -2), (key2882, -1), (key2993, -1), (key2595, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2914, 4), (key2603, 4), (key2914, 4)]

def rawRow16538 : Integer.Sparse Key := [(key2507, 2), (key2507, 2), (key2473, 2), (key2526, -2), (key2483, -2), (key2483, -2), (key2441, 2), (key2441, 2), (key2407, 2), (key3003, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2602, -1), (key2934, -2), (key2774, -2), (key2774, -2), (key2993, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2595, -1), (key2914, 4), (key2914, 4), (key2603, 4)]

def rawRow16539 : Integer.Sparse Key := [(key2483, 2), (key2507, 2), (key2526, 2), (key2473, -2), (key2483, -2), (key2507, -2), (key2544, 2), (key2555, 2), (key2565, 2), (key2379, -1), (key2393, -1), (key2771, -1), (key2912, -1), (key2933, -1), (key2991, -1), (key2882, -2), (key2914, -2), (key2993, -2), (key2595, -1), (key2603, -1), (key2774, -1), (key2914, -1), (key2934, -1), (key2993, -1), (key2595, 4), (key2774, 4), (key2882, 4)]

def rawRow16540 : Integer.Sparse Key := [(key2483, 2), (key2526, 2), (key2507, 2), (key2483, -2), (key2473, -2), (key2507, -2), (key2544, 2), (key2565, 2), (key2555, 2), (key2393, -1), (key2379, -1), (key2912, -1), (key2771, -1), (key2991, -1), (key2933, -1), (key2914, -2), (key2882, -2), (key2993, -2), (key2603, -1), (key2595, -1), (key2914, -1), (key2774, -1), (key2993, -1), (key2934, -1), (key2595, 4), (key2882, 4), (key2774, 4)]

def rawRow16541 : Integer.Sparse Key := [(key2507, 2), (key2483, 2), (key2526, 2), (key2473, -2), (key2507, -2), (key2483, -2), (key2555, 2), (key2544, 2), (key2565, 2), (key2407, -1), (key2441, -1), (key2592, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2882, -2), (key2993, -2), (key2914, -2), (key2774, -1), (key2934, -1), (key2595, -1), (key2993, -1), (key2603, -1), (key2914, -1), (key2774, 4), (key2595, 4), (key2882, 4)]

def rawRow16542 : Integer.Sparse Key := [(key2507, 2), (key2526, 2), (key2483, 2), (key2507, -2), (key2473, -2), (key2483, -2), (key2555, 2), (key2565, 2), (key2544, 2), (key2441, -1), (key2407, -1), (key2991, -1), (key2592, -1), (key2912, -1), (key2602, -1), (key2993, -2), (key2882, -2), (key2914, -2), (key2934, -1), (key2774, -1), (key2993, -1), (key2595, -1), (key2914, -1), (key2603, -1), (key2774, 4), (key2882, 4), (key2595, 4)]

def rawRow16543 : Integer.Sparse Key := [(key2526, 2), (key2483, 2), (key2507, 2), (key2483, -2), (key2507, -2), (key2473, -2), (key2565, 2), (key2544, 2), (key2555, 2), (key2544, -1), (key2555, -1), (key2393, -1), (key2441, -1), (key2379, -1), (key2771, -1), (key2914, -2), (key2993, -2), (key2882, -2), (key2914, -1), (key2993, -1), (key2603, -1), (key2934, -1), (key2595, -1), (key2774, -1), (key2882, 4), (key2595, 4), (key2774, 4)]

def rawRow16544 : Integer.Sparse Key := [(key2526, 2), (key2507, 2), (key2483, 2), (key2507, -2), (key2483, -2), (key2473, -2), (key2565, 2), (key2555, 2), (key2544, 2), (key2555, -1), (key2544, -1), (key2441, -1), (key2393, -1), (key2407, -1), (key2592, -1), (key2993, -2), (key2914, -2), (key2882, -2), (key2993, -1), (key2914, -1), (key2934, -1), (key2603, -1), (key2774, -1), (key2595, -1), (key2882, 4), (key2774, 4), (key2595, 4)]

def rawRow16545 : Integer.Sparse Key := [(key2539, 2), (key2555, 2), (key2557, 2), (key2544, -2), (key2545, -2), (key2565, -2), (key2410, 2), (key2441, 2), (key2445, 2), (key2393, -1), (key2395, -1), (key2483, -1), (key2545, -1), (key2526, -1), (key2565, -1), (key2407, -2), (key2410, -2), (key2441, -2), (key2592, -1), (key2595, -1), (key2848, -1), (key2882, -1), (key2970, -1), (key2991, -1), (key2602, 4), (key2891, 4), (key2912, 4)]

def rawRow16546 : Integer.Sparse Key := [(key2539, 2), (key2557, 2), (key2555, 2), (key2545, -2), (key2544, -2), (key2565, -2), (key2410, 2), (key2445, 2), (key2441, 2), (key2395, -1), (key2393, -1), (key2545, -1), (key2483, -1), (key2565, -1), (key2526, -1), (key2410, -2), (key2407, -2), (key2441, -2), (key2595, -1), (key2592, -1), (key2882, -1), (key2848, -1), (key2991, -1), (key2970, -1), (key2602, 4), (key2912, 4), (key2891, 4)]

def rawRow16547 : Integer.Sparse Key := [(key2555, 2), (key2539, 2), (key2557, 2), (key2544, -2), (key2565, -2), (key2545, -2), (key2441, 2), (key2410, 2), (key2445, 2), (key2483, -1), (key2526, -1), (key2393, -1), (key2565, -1), (key2395, -1), (key2545, -1), (key2407, -2), (key2441, -2), (key2410, -2), (key2848, -1), (key2970, -1), (key2592, -1), (key2991, -1), (key2595, -1), (key2882, -1), (key2891, 4), (key2602, 4), (key2912, 4)]

def rawRow16548 : Integer.Sparse Key := [(key2555, 2), (key2557, 2), (key2539, 2), (key2565, -2), (key2544, -2), (key2545, -2), (key2441, 2), (key2445, 2), (key2410, 2), (key2526, -1), (key2483, -1), (key2565, -1), (key2393, -1), (key2545, -1), (key2395, -1), (key2441, -2), (key2407, -2), (key2410, -2), (key2970, -1), (key2848, -1), (key2991, -1), (key2592, -1), (key2882, -1), (key2595, -1), (key2891, 4), (key2912, 4), (key2602, 4)]

def rawRow16549 : Integer.Sparse Key := [(key2557, 2), (key2539, 2), (key2555, 2), (key2545, -2), (key2565, -2), (key2544, -2), (key2445, 2), (key2410, 2), (key2441, 2), (key2545, -1), (key2565, -1), (key2395, -1), (key2526, -1), (key2393, -1), (key2483, -1), (key2410, -2), (key2441, -2), (key2407, -2), (key2882, -1), (key2991, -1), (key2595, -1), (key2970, -1), (key2592, -1), (key2848, -1), (key2912, 4), (key2602, 4), (key2891, 4)]

def rawRow16550 : Integer.Sparse Key := [(key2557, 2), (key2555, 2), (key2539, 2), (key2565, -2), (key2545, -2), (key2544, -2), (key2445, 2), (key2441, 2), (key2410, 2), (key2565, -1), (key2545, -1), (key2526, -1), (key2395, -1), (key2483, -1), (key2393, -1), (key2441, -2), (key2410, -2), (key2407, -2), (key2991, -1), (key2882, -1), (key2970, -1), (key2595, -1), (key2848, -1), (key2592, -1), (key2912, 4), (key2891, 4), (key2602, 4)]

def rawRow16551 : Integer.Sparse Key := [(key2544, 2), (key2555, 2), (key2565, 2), (key2539, -2), (key2545, -2), (key2557, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2382, -1), (key2395, -1), (key2410, -1), (key2545, -1), (key2445, -1), (key2557, -1), (key2473, -2), (key2483, -2), (key2507, -2), (key2379, -1), (key2393, -1), (key2771, -1), (key2912, -1), (key2933, -1), (key2991, -1), (key2595, 4), (key2774, 4), (key2882, 4)]

def rawRow16552 : Integer.Sparse Key := [(key2544, 2), (key2565, 2), (key2555, 2), (key2545, -2), (key2539, -2), (key2557, -2), (key2483, 2), (key2526, 2), (key2507, 2), (key2395, -1), (key2382, -1), (key2545, -1), (key2410, -1), (key2557, -1), (key2445, -1), (key2483, -2), (key2473, -2), (key2507, -2), (key2393, -1), (key2379, -1), (key2912, -1), (key2771, -1), (key2991, -1), (key2933, -1), (key2595, 4), (key2882, 4), (key2774, 4)]

def rawRow16553 : Integer.Sparse Key := [(key2555, 2), (key2544, 2), (key2565, 2), (key2539, -2), (key2557, -2), (key2545, -2), (key2507, 2), (key2483, 2), (key2526, 2), (key2410, -1), (key2445, -1), (key2382, -1), (key2557, -1), (key2395, -1), (key2545, -1), (key2473, -2), (key2507, -2), (key2483, -2), (key2407, -1), (key2441, -1), (key2592, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2774, 4), (key2595, 4), (key2882, 4)]

def rawRow16554 : Integer.Sparse Key := [(key2555, 2), (key2565, 2), (key2544, 2), (key2557, -2), (key2539, -2), (key2545, -2), (key2507, 2), (key2526, 2), (key2483, 2), (key2445, -1), (key2410, -1), (key2557, -1), (key2382, -1), (key2545, -1), (key2395, -1), (key2507, -2), (key2473, -2), (key2483, -2), (key2441, -1), (key2407, -1), (key2991, -1), (key2592, -1), (key2912, -1), (key2602, -1), (key2774, 4), (key2882, 4), (key2595, 4)]

def rawRow16555 : Integer.Sparse Key := [(key2565, 2), (key2544, 2), (key2555, 2), (key2545, -2), (key2557, -2), (key2539, -2), (key2526, 2), (key2483, 2), (key2507, 2), (key2545, -1), (key2557, -1), (key2395, -1), (key2445, -1), (key2382, -1), (key2410, -1), (key2483, -2), (key2507, -2), (key2473, -2), (key2544, -1), (key2555, -1), (key2393, -1), (key2441, -1), (key2379, -1), (key2771, -1), (key2882, 4), (key2595, 4), (key2774, 4)]

def rawRow16556 : Integer.Sparse Key := [(key2565, 2), (key2555, 2), (key2544, 2), (key2557, -2), (key2545, -2), (key2539, -2), (key2526, 2), (key2507, 2), (key2483, 2), (key2557, -1), (key2545, -1), (key2445, -1), (key2395, -1), (key2410, -1), (key2382, -1), (key2507, -2), (key2483, -2), (key2473, -2), (key2555, -1), (key2544, -1), (key2441, -1), (key2393, -1), (key2407, -1), (key2592, -1), (key2882, 4), (key2774, 4), (key2595, 4)]

def rawRow16557 : Integer.Sparse Key := [(key2545, 2), (key2557, 2), (key2565, 2), (key2539, -2), (key2544, -2), (key2555, -2), (key2545, 2), (key2557, 2), (key2565, 2), (key2382, -1), (key2393, -1), (key2410, -1), (key2483, -1), (key2441, -1), (key2507, -1), (key2539, -2), (key2544, -2), (key2555, -2), (key2382, -1), (key2393, -1), (key2410, -1), (key2483, -1), (key2441, -1), (key2507, -1), (key2379, 4), (key2771, 4), (key2848, 4)]

def rawRow16558 : Integer.Sparse Key := [(key2545, 2), (key2565, 2), (key2557, 2), (key2544, -2), (key2539, -2), (key2555, -2), (key2545, 2), (key2565, 2), (key2557, 2), (key2393, -1), (key2382, -1), (key2483, -1), (key2410, -1), (key2507, -1), (key2441, -1), (key2544, -2), (key2539, -2), (key2555, -2), (key2393, -1), (key2382, -1), (key2483, -1), (key2410, -1), (key2507, -1), (key2441, -1), (key2379, 4), (key2848, 4), (key2771, 4)]

def rawRow16559 : Integer.Sparse Key := [(key2557, 2), (key2545, 2), (key2565, 2), (key2539, -2), (key2555, -2), (key2544, -2), (key2557, 2), (key2545, 2), (key2565, 2), (key2410, -1), (key2441, -1), (key2382, -1), (key2507, -1), (key2393, -1), (key2483, -1), (key2539, -2), (key2555, -2), (key2544, -2), (key2410, -1), (key2441, -1), (key2382, -1), (key2507, -1), (key2393, -1), (key2483, -1), (key2407, 4), (key2592, 4), (key2848, 4)]

def rawRow16560 : Integer.Sparse Key := [(key2557, 2), (key2565, 2), (key2545, 2), (key2555, -2), (key2539, -2), (key2544, -2), (key2557, 2), (key2565, 2), (key2545, 2), (key2441, -1), (key2410, -1), (key2507, -1), (key2382, -1), (key2483, -1), (key2393, -1), (key2555, -2), (key2539, -2), (key2544, -2), (key2441, -1), (key2410, -1), (key2507, -1), (key2382, -1), (key2483, -1), (key2393, -1), (key2407, 4), (key2848, 4), (key2592, 4)]

def rawRow16561 : Integer.Sparse Key := [(key2565, 2), (key2545, 2), (key2557, 2), (key2544, -2), (key2555, -2), (key2539, -2), (key2565, 2), (key2545, 2), (key2557, 2), (key2483, -1), (key2507, -1), (key2393, -1), (key2441, -1), (key2382, -1), (key2410, -1), (key2544, -2), (key2555, -2), (key2539, -2), (key2483, -1), (key2507, -1), (key2393, -1), (key2441, -1), (key2382, -1), (key2410, -1), (key2473, 4), (key2379, 4), (key2771, 4)]

def rawRow16562 : Integer.Sparse Key := [(key2565, 2), (key2557, 2), (key2545, 2), (key2555, -2), (key2544, -2), (key2539, -2), (key2565, 2), (key2557, 2), (key2545, 2), (key2507, -1), (key2483, -1), (key2441, -1), (key2393, -1), (key2410, -1), (key2382, -1), (key2555, -2), (key2544, -2), (key2539, -2), (key2507, -1), (key2483, -1), (key2441, -1), (key2393, -1), (key2410, -1), (key2382, -1), (key2473, 4), (key2407, 4), (key2592, 4)]

def rawRow16563 : Integer.Sparse Key := [(key2702, 2), (key2702, 2), (key2728, 2), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2805, 2), (key2805, 2), (key2831, 2), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key3023, -1), (key3023, -1), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key3026, -1), (key3026, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2)]

def rawRow16564 : Integer.Sparse Key := [(key2702, 2), (key2728, 2), (key2702, 2), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2805, 2), (key2831, 2), (key2805, 2), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2870, -1), (key3026, -1), (key2632, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2)]

def rawRow16565 : Integer.Sparse Key := [(key2728, 2), (key2702, 2), (key2702, 2), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2831, 2), (key2805, 2), (key2805, 2), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3023, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key3026, -1), (key2870, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2)]

def rawRow16566 : Integer.Sparse Key := [(key2735, 2), (key2737, 2), (key2747, 2), (key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2948, 2), (key2950, 2), (key2960, 2), (key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2726, -1), (key2732, -1), (key2870, -1), (key2885, -1), (key3026, -1), (key3030, -1), (key2640, -1), (key2644, -1), (key2860, -1), (key2885, -1), (key3023, -1), (key3030, -1), (key2632, 2), (key2644, 2), (key2706, 2), (key2732, 2), (key3023, 2), (key3026, 2)]

def rawRow16567 : Integer.Sparse Key := [(key2737, 2), (key2735, 2), (key2747, 2), (key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2950, 2), (key2948, 2), (key2960, 2), (key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2732, -1), (key2726, -1), (key2885, -1), (key2870, -1), (key3030, -1), (key3026, -1), (key2644, -1), (key2640, -1), (key2885, -1), (key2860, -1), (key3030, -1), (key3023, -1), (key2644, 2), (key2632, 2), (key2732, 2), (key2706, 2), (key3026, 2), (key3023, 2)]

def rawRow16568 : Integer.Sparse Key := [(key2735, 2), (key2747, 2), (key2737, 2), (key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2948, 2), (key2960, 2), (key2950, 2), (key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2870, -1), (key3026, -1), (key2726, -1), (key3030, -1), (key2732, -1), (key2885, -1), (key2860, -1), (key3023, -1), (key2640, -1), (key3030, -1), (key2644, -1), (key2885, -1), (key2706, 2), (key3023, 2), (key2632, 2), (key3026, 2), (key2644, 2), (key2732, 2)]

def rawRow16569 : Integer.Sparse Key := [(key2747, 2), (key2735, 2), (key2737, 2), (key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2960, 2), (key2948, 2), (key2950, 2), (key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key3026, -1), (key2870, -1), (key3030, -1), (key2726, -1), (key2885, -1), (key2732, -1), (key3023, -1), (key2860, -1), (key3030, -1), (key2640, -1), (key2885, -1), (key2644, -1), (key3023, 2), (key2706, 2), (key3026, 2), (key2632, 2), (key2732, 2), (key2644, 2)]

def rawRow16570 : Integer.Sparse Key := [(key2737, 2), (key2747, 2), (key2735, 2), (key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2950, 2), (key2960, 2), (key2948, 2), (key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2885, -1), (key3030, -1), (key2732, -1), (key3026, -1), (key2726, -1), (key2870, -1), (key2885, -1), (key3030, -1), (key2644, -1), (key3023, -1), (key2640, -1), (key2860, -1), (key2732, 2), (key3026, 2), (key2644, 2), (key3023, 2), (key2632, 2), (key2706, 2)]

def rawRow16571 : Integer.Sparse Key := [(key2747, 2), (key2737, 2), (key2735, 2), (key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2960, 2), (key2950, 2), (key2948, 2), (key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key3030, -1), (key2885, -1), (key3026, -1), (key2732, -1), (key2870, -1), (key2726, -1), (key3030, -1), (key2885, -1), (key3023, -1), (key2644, -1), (key2860, -1), (key2640, -1), (key3026, 2), (key2732, 2), (key3023, 2), (key2644, 2), (key2706, 2), (key2632, 2)]

def rawRow16572 : Integer.Sparse Key := [(key2805, 2), (key2805, 2), (key2831, 2), (key2782, -1), (key2782, -1), (key2893, -1), (key2893, -1), (key2904, -1), (key2904, -1), (key2702, 2), (key2702, 2), (key2728, 2), (key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2)]

def rawRow16573 : Integer.Sparse Key := [(key2805, 2), (key2831, 2), (key2805, 2), (key2893, -1), (key2904, -1), (key2782, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2702, 2), (key2728, 2), (key2702, 2), (key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2)]

def rawRow16574 : Integer.Sparse Key := [(key2831, 2), (key2805, 2), (key2805, 2), (key2904, -1), (key2893, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2782, -1), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2)]

def rawRow16575 : Integer.Sparse Key := [(key2893, 2), (key2897, 2), (key2904, 2), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2972, 2), (key2976, 2), (key2983, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2)]

def rawRow16576 : Integer.Sparse Key := [(key2897, 2), (key2893, 2), (key2904, 2), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2976, 2), (key2972, 2), (key2983, 2), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2)]

def rawRow16577 : Integer.Sparse Key := [(key2893, 2), (key2904, 2), (key2897, 2), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2972, 2), (key2983, 2), (key2976, 2), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2)]

def rawRow16578 : Integer.Sparse Key := [(key2904, 2), (key2893, 2), (key2897, 2), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2983, 2), (key2972, 2), (key2976, 2), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2)]

def rawRow16579 : Integer.Sparse Key := [(key2897, 2), (key2904, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, 2), (key2983, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2)]

def rawRow16580 : Integer.Sparse Key := [(key2904, 2), (key2897, 2), (key2893, 2), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, 2), (key2976, 2), (key2972, 2), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2)]

def rawRow16581 : Integer.Sparse Key := [(key2948, 2), (key2950, 2), (key2960, 2), (key2936, -1), (key2938, -1), (key2972, -1), (key2997, -1), (key2983, -1), (key3000, -1), (key2735, 2), (key2737, 2), (key2747, 2), (key2646, -1), (key2648, -1), (key2893, -1), (key2997, -1), (key2904, -1), (key3000, -1), (key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2628, 2), (key2648, 2), (key2782, 2), (key2938, 2), (key2904, 2), (key2983, 2)]

def rawRow16582 : Integer.Sparse Key := [(key2950, 2), (key2948, 2), (key2960, 2), (key2938, -1), (key2936, -1), (key2997, -1), (key2972, -1), (key3000, -1), (key2983, -1), (key2737, 2), (key2735, 2), (key2747, 2), (key2648, -1), (key2646, -1), (key2997, -1), (key2893, -1), (key3000, -1), (key2904, -1), (key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2648, 2), (key2628, 2), (key2938, 2), (key2782, 2), (key2983, 2), (key2904, 2)]

def rawRow16583 : Integer.Sparse Key := [(key2948, 2), (key2960, 2), (key2950, 2), (key2972, -1), (key2983, -1), (key2936, -1), (key3000, -1), (key2938, -1), (key2997, -1), (key2735, 2), (key2747, 2), (key2737, 2), (key2893, -1), (key2904, -1), (key2646, -1), (key3000, -1), (key2648, -1), (key2997, -1), (key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2782, 2), (key2904, 2), (key2628, 2), (key2983, 2), (key2648, 2), (key2938, 2)]

def rawRow16584 : Integer.Sparse Key := [(key2960, 2), (key2948, 2), (key2950, 2), (key2983, -1), (key2972, -1), (key3000, -1), (key2936, -1), (key2997, -1), (key2938, -1), (key2747, 2), (key2735, 2), (key2737, 2), (key2904, -1), (key2893, -1), (key3000, -1), (key2646, -1), (key2997, -1), (key2648, -1), (key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key2904, 2), (key2782, 2), (key2983, 2), (key2628, 2), (key2938, 2), (key2648, 2)]

def rawRow16585 : Integer.Sparse Key := [(key2950, 2), (key2960, 2), (key2948, 2), (key2997, -1), (key3000, -1), (key2938, -1), (key2983, -1), (key2936, -1), (key2972, -1), (key2737, 2), (key2747, 2), (key2735, 2), (key2997, -1), (key3000, -1), (key2648, -1), (key2904, -1), (key2646, -1), (key2893, -1), (key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2938, 2), (key2983, 2), (key2648, 2), (key2904, 2), (key2628, 2), (key2782, 2)]

def rawRow16586 : Integer.Sparse Key := [(key2960, 2), (key2950, 2), (key2948, 2), (key3000, -1), (key2997, -1), (key2983, -1), (key2938, -1), (key2972, -1), (key2936, -1), (key2747, 2), (key2737, 2), (key2735, 2), (key3000, -1), (key2997, -1), (key2904, -1), (key2648, -1), (key2893, -1), (key2646, -1), (key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2983, 2), (key2938, 2), (key2904, 2), (key2648, 2), (key2782, 2), (key2628, 2)]

def rawRow16587 : Integer.Sparse Key := [(key2972, 2), (key2976, 2), (key2983, 2), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2893, 2), (key2897, 2), (key2904, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2)]

def rawRow16588 : Integer.Sparse Key := [(key2976, 2), (key2972, 2), (key2983, 2), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2897, 2), (key2893, 2), (key2904, 2), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2)]

def rawRow16589 : Integer.Sparse Key := [(key2972, 2), (key2983, 2), (key2976, 2), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2893, 2), (key2904, 2), (key2897, 2), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2)]

def rawRow16590 : Integer.Sparse Key := [(key2983, 2), (key2972, 2), (key2976, 2), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2904, 2), (key2893, 2), (key2897, 2), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2)]

def rawRow16591 : Integer.Sparse Key := [(key2976, 2), (key2983, 2), (key2972, 2), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2897, 2), (key2904, 2), (key2893, 2), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2)]

def rawRow16592 : Integer.Sparse Key := [(key2983, 2), (key2976, 2), (key2972, 2), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key2904, 2), (key2897, 2), (key2893, 2), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2)]

def rawRow16593 : Integer.Sparse Key := [(key2997, 2), (key2998, 2), (key3000, 2), (key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2997, 2), (key2998, 2), (key3000, 2), (key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2618, 2), (key2641, 2), (key2673, 2), (key2795, 2), (key2728, 2), (key2831, 2)]

def rawRow16594 : Integer.Sparse Key := [(key2998, 2), (key2997, 2), (key3000, 2), (key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2998, 2), (key2997, 2), (key3000, 2), (key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2641, 2), (key2618, 2), (key2795, 2), (key2673, 2), (key2831, 2), (key2728, 2)]

def rawRow16595 : Integer.Sparse Key := [(key2997, 2), (key3000, 2), (key2998, 2), (key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2997, 2), (key3000, 2), (key2998, 2), (key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2673, 2), (key2728, 2), (key2618, 2), (key2831, 2), (key2641, 2), (key2795, 2)]

def rawRow16596 : Integer.Sparse Key := [(key3000, 2), (key2997, 2), (key2998, 2), (key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key3000, 2), (key2997, 2), (key2998, 2), (key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2728, 2), (key2673, 2), (key2831, 2), (key2618, 2), (key2795, 2), (key2641, 2)]

def rawRow16597 : Integer.Sparse Key := [(key2998, 2), (key3000, 2), (key2997, 2), (key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2998, 2), (key3000, 2), (key2997, 2), (key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2795, 2), (key2831, 2), (key2641, 2), (key2728, 2), (key2618, 2), (key2673, 2)]

def rawRow16598 : Integer.Sparse Key := [(key3000, 2), (key2998, 2), (key2997, 2), (key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key3000, 2), (key2998, 2), (key2997, 2), (key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2831, 2), (key2795, 2), (key2728, 2), (key2641, 2), (key2673, 2), (key2618, 2)]

def rawRow16599 : Integer.Sparse Key := [(key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2673, 2), (key2737, 2), (key2737, 2), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2621, -2), (key2835, -2), (key2835, -2), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key3023, -1), (key3023, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2753, 2), (key2920, 2), (key2920, 2), (key2658, -2), (key2923, -2), (key2923, -2)]

def rawRow16600 : Integer.Sparse Key := [(key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2737, 2), (key2673, 2), (key2737, 2), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2835, -2), (key2621, -2), (key2835, -2), (key2860, -1), (key3023, -1), (key2706, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2920, 2), (key2753, 2), (key2920, 2), (key2923, -2), (key2658, -2), (key2923, -2)]

def rawRow16601 : Integer.Sparse Key := [(key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2737, 2), (key2737, 2), (key2673, 2), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key2835, -2), (key2835, -2), (key2621, -2), (key3023, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2920, 2), (key2920, 2), (key2753, 2), (key2923, -2), (key2923, -2), (key2658, -2)]

def rawRow16602 : Integer.Sparse Key := [(key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2667, 2), (key2702, 2), (key2735, 2), (key2612, 1), (key2618, 1), (key2805, 1), (key2950, 1), (key2831, 1), (key2960, 1), (key2616, -2), (key2809, -2), (key2829, -2), (key2726, -1), (key2732, -1), (key2870, -1), (key2885, -1), (key3026, -1), (key3030, -1), (key2640, 1), (key2644, 1), (key2860, 1), (key2885, 1), (key3023, 1), (key3030, 1), (key2758, 2), (key2923, 2), (key2927, 2), (key2660, -2), (key2920, -2), (key2927, -2)]

def rawRow16603 : Integer.Sparse Key := [(key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2667, 2), (key2735, 2), (key2702, 2), (key2618, 1), (key2612, 1), (key2950, 1), (key2805, 1), (key2960, 1), (key2831, 1), (key2616, -2), (key2829, -2), (key2809, -2), (key2732, -1), (key2726, -1), (key2885, -1), (key2870, -1), (key3030, -1), (key3026, -1), (key2644, 1), (key2640, 1), (key2885, 1), (key2860, 1), (key3030, 1), (key3023, 1), (key2758, 2), (key2927, 2), (key2923, 2), (key2660, -2), (key2927, -2), (key2920, -2)]

def rawRow16604 : Integer.Sparse Key := [(key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2702, 2), (key2667, 2), (key2735, 2), (key2805, 1), (key2831, 1), (key2612, 1), (key2960, 1), (key2618, 1), (key2950, 1), (key2809, -2), (key2616, -2), (key2829, -2), (key2870, -1), (key3026, -1), (key2726, -1), (key3030, -1), (key2732, -1), (key2885, -1), (key2860, 1), (key3023, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2923, 2), (key2758, 2), (key2927, 2), (key2920, -2), (key2660, -2), (key2927, -2)]

def rawRow16605 : Integer.Sparse Key := [(key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2702, 2), (key2735, 2), (key2667, 2), (key2831, 1), (key2805, 1), (key2960, 1), (key2612, 1), (key2950, 1), (key2618, 1), (key2809, -2), (key2829, -2), (key2616, -2), (key3026, -1), (key2870, -1), (key3030, -1), (key2726, -1), (key2885, -1), (key2732, -1), (key3023, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key2885, 1), (key2644, 1), (key2923, 2), (key2927, 2), (key2758, 2), (key2920, -2), (key2927, -2), (key2660, -2)]

def rawRow16606 : Integer.Sparse Key := [(key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2735, 2), (key2667, 2), (key2702, 2), (key2950, 1), (key2960, 1), (key2618, 1), (key2831, 1), (key2612, 1), (key2805, 1), (key2829, -2), (key2616, -2), (key2809, -2), (key2885, -1), (key3030, -1), (key2732, -1), (key3026, -1), (key2726, -1), (key2870, -1), (key2885, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2640, 1), (key2860, 1), (key2927, 2), (key2758, 2), (key2923, 2), (key2927, -2), (key2660, -2), (key2920, -2)]

def rawRow16607 : Integer.Sparse Key := [(key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2735, 2), (key2702, 2), (key2667, 2), (key2960, 1), (key2950, 1), (key2831, 1), (key2618, 1), (key2805, 1), (key2612, 1), (key2829, -2), (key2809, -2), (key2616, -2), (key3030, -1), (key2885, -1), (key3026, -1), (key2732, -1), (key2870, -1), (key2726, -1), (key3030, 1), (key2885, 1), (key3023, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key2927, 2), (key2923, 2), (key2758, 2), (key2927, -2), (key2920, -2), (key2660, -2)]

def rawRow16608 : Integer.Sparse Key := [(key2782, -1), (key2782, -1), (key2893, -1), (key2893, -1), (key2904, -1), (key2904, -1), (key2795, 2), (key2897, 2), (key2897, 2), (key2628, 1), (key2628, 1), (key2972, 1), (key2972, 1), (key2983, 1), (key2983, 1), (key2641, -2), (key2976, -2), (key2976, -2), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2676, 2), (key2798, 2), (key2798, 2), (key2621, -2), (key2835, -2), (key2835, -2)]

def rawRow16609 : Integer.Sparse Key := [(key2893, -1), (key2904, -1), (key2782, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2897, 2), (key2795, 2), (key2897, 2), (key2972, 1), (key2983, 1), (key2628, 1), (key2983, 1), (key2628, 1), (key2972, 1), (key2976, -2), (key2641, -2), (key2976, -2), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2798, 2), (key2676, 2), (key2798, 2), (key2835, -2), (key2621, -2), (key2835, -2)]

def rawRow16610 : Integer.Sparse Key := [(key2904, -1), (key2893, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2782, -1), (key2897, 2), (key2897, 2), (key2795, 2), (key2983, 1), (key2972, 1), (key2983, 1), (key2628, 1), (key2972, 1), (key2628, 1), (key2976, -2), (key2976, -2), (key2641, -2), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key2798, 2), (key2798, 2), (key2676, 2), (key2835, -2), (key2835, -2), (key2621, -2)]

def rawRow16611 : Integer.Sparse Key := [(key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2782, 2), (key2805, 2), (key2893, 2), (key2628, 1), (key2641, 1), (key2702, 1), (key2976, 1), (key2728, 1), (key2983, 1), (key2628, -2), (key2702, -2), (key2972, -2), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2732, 2), (key2835, 2), (key2885, 2), (key2644, -2), (key2798, -2), (key2885, -2)]

def rawRow16612 : Integer.Sparse Key := [(key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2782, 2), (key2893, 2), (key2805, 2), (key2641, 1), (key2628, 1), (key2976, 1), (key2702, 1), (key2983, 1), (key2728, 1), (key2628, -2), (key2972, -2), (key2702, -2), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2732, 2), (key2885, 2), (key2835, 2), (key2644, -2), (key2885, -2), (key2798, -2)]

def rawRow16613 : Integer.Sparse Key := [(key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2805, 2), (key2782, 2), (key2893, 2), (key2702, 1), (key2728, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2702, -2), (key2628, -2), (key2972, -2), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2835, 2), (key2732, 2), (key2885, 2), (key2798, -2), (key2644, -2), (key2885, -2)]

def rawRow16614 : Integer.Sparse Key := [(key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2805, 2), (key2893, 2), (key2782, 2), (key2728, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2976, 1), (key2641, 1), (key2702, -2), (key2972, -2), (key2628, -2), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2835, 2), (key2885, 2), (key2732, 2), (key2798, -2), (key2885, -2), (key2644, -2)]

def rawRow16615 : Integer.Sparse Key := [(key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2893, 2), (key2782, 2), (key2805, 2), (key2976, 1), (key2983, 1), (key2641, 1), (key2728, 1), (key2628, 1), (key2702, 1), (key2972, -2), (key2628, -2), (key2702, -2), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2885, 2), (key2732, 2), (key2835, 2), (key2885, -2), (key2644, -2), (key2798, -2)]

def rawRow16616 : Integer.Sparse Key := [(key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2893, 2), (key2805, 2), (key2782, 2), (key2983, 1), (key2976, 1), (key2728, 1), (key2641, 1), (key2702, 1), (key2628, 1), (key2972, -2), (key2702, -2), (key2628, -2), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2885, 2), (key2835, 2), (key2732, 2), (key2885, -2), (key2798, -2), (key2644, -2)]

def rawRow16617 : Integer.Sparse Key := [(key2936, -1), (key2938, -1), (key2972, -1), (key2997, -1), (key2983, -1), (key3000, -1), (key2943, 2), (key2976, 2), (key2998, 2), (key2646, 1), (key2648, 1), (key2893, 1), (key2997, 1), (key2904, 1), (key3000, 1), (key2653, -2), (key2897, -2), (key2998, -2), (key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2612, 1), (key2618, 1), (key2805, 1), (key2950, 1), (key2831, 1), (key2960, 1), (key2671, 2), (key2786, 2), (key2794, 2), (key2616, -2), (key2809, -2), (key2829, -2)]

def rawRow16618 : Integer.Sparse Key := [(key2938, -1), (key2936, -1), (key2997, -1), (key2972, -1), (key3000, -1), (key2983, -1), (key2943, 2), (key2998, 2), (key2976, 2), (key2648, 1), (key2646, 1), (key2997, 1), (key2893, 1), (key3000, 1), (key2904, 1), (key2653, -2), (key2998, -2), (key2897, -2), (key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2618, 1), (key2612, 1), (key2950, 1), (key2805, 1), (key2960, 1), (key2831, 1), (key2671, 2), (key2794, 2), (key2786, 2), (key2616, -2), (key2829, -2), (key2809, -2)]

def rawRow16619 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2936, -1), (key3000, -1), (key2938, -1), (key2997, -1), (key2976, 2), (key2943, 2), (key2998, 2), (key2893, 1), (key2904, 1), (key2646, 1), (key3000, 1), (key2648, 1), (key2997, 1), (key2897, -2), (key2653, -2), (key2998, -2), (key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2805, 1), (key2831, 1), (key2612, 1), (key2960, 1), (key2618, 1), (key2950, 1), (key2786, 2), (key2671, 2), (key2794, 2), (key2809, -2), (key2616, -2), (key2829, -2)]

def rawRow16620 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key3000, -1), (key2936, -1), (key2997, -1), (key2938, -1), (key2976, 2), (key2998, 2), (key2943, 2), (key2904, 1), (key2893, 1), (key3000, 1), (key2646, 1), (key2997, 1), (key2648, 1), (key2897, -2), (key2998, -2), (key2653, -2), (key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2831, 1), (key2805, 1), (key2960, 1), (key2612, 1), (key2950, 1), (key2618, 1), (key2786, 2), (key2794, 2), (key2671, 2), (key2809, -2), (key2829, -2), (key2616, -2)]

def rawRow16621 : Integer.Sparse Key := [(key2997, -1), (key3000, -1), (key2938, -1), (key2983, -1), (key2936, -1), (key2972, -1), (key2998, 2), (key2943, 2), (key2976, 2), (key2997, 1), (key3000, 1), (key2648, 1), (key2904, 1), (key2646, 1), (key2893, 1), (key2998, -2), (key2653, -2), (key2897, -2), (key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2950, 1), (key2960, 1), (key2618, 1), (key2831, 1), (key2612, 1), (key2805, 1), (key2794, 2), (key2671, 2), (key2786, 2), (key2829, -2), (key2616, -2), (key2809, -2)]

def rawRow16622 : Integer.Sparse Key := [(key3000, -1), (key2997, -1), (key2983, -1), (key2938, -1), (key2972, -1), (key2936, -1), (key2998, 2), (key2976, 2), (key2943, 2), (key3000, 1), (key2997, 1), (key2904, 1), (key2648, 1), (key2893, 1), (key2646, 1), (key2998, -2), (key2897, -2), (key2653, -2), (key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2960, 1), (key2950, 1), (key2831, 1), (key2618, 1), (key2805, 1), (key2612, 1), (key2794, 2), (key2786, 2), (key2671, 2), (key2829, -2), (key2809, -2), (key2616, -2)]

def rawRow16623 : Integer.Sparse Key := [(key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2938, 2), (key2950, 2), (key2997, 2), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2648, -2), (key2737, -2), (key2997, -2), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2976, 1), (key2728, 1), (key2983, 1), (key2706, 2), (key2809, 2), (key2860, 2), (key2632, -2), (key2786, -2), (key2870, -2)]

def rawRow16624 : Integer.Sparse Key := [(key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2938, 2), (key2997, 2), (key2950, 2), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2648, -2), (key2997, -2), (key2737, -2), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2641, 1), (key2628, 1), (key2976, 1), (key2702, 1), (key2983, 1), (key2728, 1), (key2706, 2), (key2860, 2), (key2809, 2), (key2632, -2), (key2870, -2), (key2786, -2)]

def rawRow16625 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2950, 2), (key2938, 2), (key2997, 2), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2737, -2), (key2648, -2), (key2997, -2), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2702, 1), (key2728, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2809, 2), (key2706, 2), (key2860, 2), (key2786, -2), (key2632, -2), (key2870, -2)]

def rawRow16626 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2950, 2), (key2997, 2), (key2938, 2), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2737, -2), (key2997, -2), (key2648, -2), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2728, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2976, 1), (key2641, 1), (key2809, 2), (key2860, 2), (key2706, 2), (key2786, -2), (key2870, -2), (key2632, -2)]

def rawRow16627 : Integer.Sparse Key := [(key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2997, 2), (key2938, 2), (key2950, 2), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2997, -2), (key2648, -2), (key2737, -2), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, 1), (key2983, 1), (key2641, 1), (key2728, 1), (key2628, 1), (key2702, 1), (key2860, 2), (key2706, 2), (key2809, 2), (key2870, -2), (key2632, -2), (key2786, -2)]

def rawRow16628 : Integer.Sparse Key := [(key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key2997, 2), (key2950, 2), (key2938, 2), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2997, -2), (key2737, -2), (key2648, -2), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, 1), (key2976, 1), (key2728, 1), (key2641, 1), (key2702, 1), (key2628, 1), (key2860, 2), (key2809, 2), (key2706, 2), (key2870, -2), (key2786, -2), (key2632, -2)]

def rawRow16629 : Integer.Sparse Key := [(key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2936, 2), (key2948, 2), (key2972, 2), (key2648, 1), (key2653, 1), (key2737, 1), (key2897, 1), (key2747, 1), (key2904, 1), (key2646, -2), (key2735, -2), (key2893, -2), (key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2648, 1), (key2653, 1), (key2737, 1), (key2897, 1), (key2747, 1), (key2904, 1), (key2726, 2), (key2829, 2), (key2870, 2), (key2640, -2), (key2794, -2), (key2860, -2)]

def rawRow16630 : Integer.Sparse Key := [(key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2936, 2), (key2972, 2), (key2948, 2), (key2653, 1), (key2648, 1), (key2897, 1), (key2737, 1), (key2904, 1), (key2747, 1), (key2646, -2), (key2893, -2), (key2735, -2), (key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2653, 1), (key2648, 1), (key2897, 1), (key2737, 1), (key2904, 1), (key2747, 1), (key2726, 2), (key2870, 2), (key2829, 2), (key2640, -2), (key2860, -2), (key2794, -2)]

def rawRow16631 : Integer.Sparse Key := [(key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2948, 2), (key2936, 2), (key2972, 2), (key2737, 1), (key2747, 1), (key2648, 1), (key2904, 1), (key2653, 1), (key2897, 1), (key2735, -2), (key2646, -2), (key2893, -2), (key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2737, 1), (key2747, 1), (key2648, 1), (key2904, 1), (key2653, 1), (key2897, 1), (key2829, 2), (key2726, 2), (key2870, 2), (key2794, -2), (key2640, -2), (key2860, -2)]

def rawRow16632 : Integer.Sparse Key := [(key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key2948, 2), (key2972, 2), (key2936, 2), (key2747, 1), (key2737, 1), (key2904, 1), (key2648, 1), (key2897, 1), (key2653, 1), (key2735, -2), (key2893, -2), (key2646, -2), (key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key2747, 1), (key2737, 1), (key2904, 1), (key2648, 1), (key2897, 1), (key2653, 1), (key2829, 2), (key2870, 2), (key2726, 2), (key2794, -2), (key2860, -2), (key2640, -2)]

def rawRow16633 : Integer.Sparse Key := [(key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2972, 2), (key2936, 2), (key2948, 2), (key2897, 1), (key2904, 1), (key2653, 1), (key2747, 1), (key2648, 1), (key2737, 1), (key2893, -2), (key2646, -2), (key2735, -2), (key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2897, 1), (key2904, 1), (key2653, 1), (key2747, 1), (key2648, 1), (key2737, 1), (key2870, 2), (key2726, 2), (key2829, 2), (key2860, -2), (key2640, -2), (key2794, -2)]

def rawRow16634 : Integer.Sparse Key := [(key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key2972, 2), (key2948, 2), (key2936, 2), (key2904, 1), (key2897, 1), (key2747, 1), (key2653, 1), (key2737, 1), (key2648, 1), (key2893, -2), (key2735, -2), (key2646, -2), (key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key2904, 1), (key2897, 1), (key2747, 1), (key2653, 1), (key2737, 1), (key2648, 1), (key2870, 2), (key2829, 2), (key2726, 2), (key2860, -2), (key2794, -2), (key2640, -2)]

def rawRow16635 : Integer.Sparse Key := [(key2671, -1), (key2671, -1), (key2794, -1), (key2794, -1), (key2944, -1), (key2944, -1), (key2674, 2), (key2796, 2), (key2796, 2), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1), (key2619, -2), (key2832, -2), (key2832, -2), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key2977, -1), (key2977, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1), (key2738, 2), (key2898, 2), (key2898, 2), (key2649, -2), (key2905, -2), (key2905, -2)]

def rawRow16636 : Integer.Sparse Key := [(key2794, -1), (key2944, -1), (key2671, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2796, 2), (key2674, 2), (key2796, 2), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2832, -2), (key2619, -2), (key2832, -2), (key2860, -1), (key2977, -1), (key2706, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2898, 2), (key2738, 2), (key2898, 2), (key2905, -2), (key2649, -2), (key2905, -2)]

def rawRow16637 : Integer.Sparse Key := [(key2944, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2796, 2), (key2796, 2), (key2674, 2), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2832, -2), (key2832, -2), (key2619, -2), (key2977, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2898, 2), (key2898, 2), (key2738, 2), (key2905, -2), (key2905, -2), (key2649, -2)]

def rawRow16638 : Integer.Sparse Key := [(key2671, -1), (key2674, -1), (key2786, -1), (key2796, -1), (key2939, -1), (key2944, -1), (key2671, 2), (key2786, 2), (key2794, 2), (key2616, 1), (key2619, 1), (key2809, 1), (key2832, 1), (key2951, 1), (key2961, 1), (key2616, -2), (key2809, -2), (key2829, -2), (key2726, -1), (key2729, -1), (key2870, -1), (key2883, -1), (key2984, -1), (key2992, -1), (key2640, 1), (key2642, 1), (key2860, 1), (key2883, 1), (key2977, 1), (key2992, 1), (key2748, 2), (key2905, 2), (key2913, 2), (key2654, -2), (key2898, -2), (key2913, -2)]

def rawRow16639 : Integer.Sparse Key := [(key2674, -1), (key2671, -1), (key2796, -1), (key2786, -1), (key2944, -1), (key2939, -1), (key2671, 2), (key2794, 2), (key2786, 2), (key2619, 1), (key2616, 1), (key2832, 1), (key2809, 1), (key2961, 1), (key2951, 1), (key2616, -2), (key2829, -2), (key2809, -2), (key2729, -1), (key2726, -1), (key2883, -1), (key2870, -1), (key2992, -1), (key2984, -1), (key2642, 1), (key2640, 1), (key2883, 1), (key2860, 1), (key2992, 1), (key2977, 1), (key2748, 2), (key2913, 2), (key2905, 2), (key2654, -2), (key2913, -2), (key2898, -2)]

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

def rawRow16640 : Integer.Sparse Key := [(key2786, -1), (key2939, -1), (key2671, -1), (key2944, -1), (key2674, -1), (key2796, -1), (key2786, 2), (key2671, 2), (key2794, 2), (key2809, 1), (key2951, 1), (key2616, 1), (key2961, 1), (key2619, 1), (key2832, 1), (key2809, -2), (key2616, -2), (key2829, -2), (key2870, -1), (key2984, -1), (key2726, -1), (key2992, -1), (key2729, -1), (key2883, -1), (key2860, 1), (key2977, 1), (key2640, 1), (key2992, 1), (key2642, 1), (key2883, 1), (key2905, 2), (key2748, 2), (key2913, 2), (key2898, -2), (key2654, -2), (key2913, -2)]

def rawRow16641 : Integer.Sparse Key := [(key2939, -1), (key2786, -1), (key2944, -1), (key2671, -1), (key2796, -1), (key2674, -1), (key2786, 2), (key2794, 2), (key2671, 2), (key2951, 1), (key2809, 1), (key2961, 1), (key2616, 1), (key2832, 1), (key2619, 1), (key2809, -2), (key2829, -2), (key2616, -2), (key2984, -1), (key2870, -1), (key2992, -1), (key2726, -1), (key2883, -1), (key2729, -1), (key2977, 1), (key2860, 1), (key2992, 1), (key2640, 1), (key2883, 1), (key2642, 1), (key2905, 2), (key2913, 2), (key2748, 2), (key2898, -2), (key2913, -2), (key2654, -2)]

def rawRow16642 : Integer.Sparse Key := [(key2796, -1), (key2944, -1), (key2674, -1), (key2939, -1), (key2671, -1), (key2786, -1), (key2794, 2), (key2671, 2), (key2786, 2), (key2832, 1), (key2961, 1), (key2619, 1), (key2951, 1), (key2616, 1), (key2809, 1), (key2829, -2), (key2616, -2), (key2809, -2), (key2883, -1), (key2992, -1), (key2729, -1), (key2984, -1), (key2726, -1), (key2870, -1), (key2883, 1), (key2992, 1), (key2642, 1), (key2977, 1), (key2640, 1), (key2860, 1), (key2913, 2), (key2748, 2), (key2905, 2), (key2913, -2), (key2654, -2), (key2898, -2)]

def rawRow16643 : Integer.Sparse Key := [(key2944, -1), (key2796, -1), (key2939, -1), (key2674, -1), (key2786, -1), (key2671, -1), (key2794, 2), (key2786, 2), (key2671, 2), (key2961, 1), (key2832, 1), (key2951, 1), (key2619, 1), (key2809, 1), (key2616, 1), (key2829, -2), (key2809, -2), (key2616, -2), (key2992, -1), (key2883, -1), (key2984, -1), (key2729, -1), (key2870, -1), (key2726, -1), (key2992, 1), (key2883, 1), (key2977, 1), (key2642, 1), (key2860, 1), (key2640, 1), (key2913, 2), (key2905, 2), (key2748, 2), (key2913, -2), (key2898, -2), (key2654, -2)]

def rawRow16644 : Integer.Sparse Key := [(key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key2977, -1), (key2977, -1), (key2738, 2), (key2898, 2), (key2898, 2), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1), (key2649, -2), (key2905, -2), (key2905, -2), (key2671, -1), (key2671, -1), (key2794, -1), (key2794, -1), (key2944, -1), (key2944, -1), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1), (key2674, 2), (key2796, 2), (key2796, 2), (key2619, -2), (key2832, -2), (key2832, -2)]

def rawRow16645 : Integer.Sparse Key := [(key2860, -1), (key2977, -1), (key2706, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2898, 2), (key2738, 2), (key2898, 2), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2905, -2), (key2649, -2), (key2905, -2), (key2794, -1), (key2944, -1), (key2671, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2796, 2), (key2674, 2), (key2796, 2), (key2832, -2), (key2619, -2), (key2832, -2)]

def rawRow16646 : Integer.Sparse Key := [(key2977, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2898, 2), (key2898, 2), (key2738, 2), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2905, -2), (key2905, -2), (key2649, -2), (key2944, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2796, 2), (key2796, 2), (key2674, 2), (key2832, -2), (key2832, -2), (key2619, -2)]

def rawRow16647 : Integer.Sparse Key := [(key2706, -1), (key2738, -1), (key2809, -1), (key2898, -1), (key2951, -1), (key2977, -1), (key2706, 2), (key2809, 2), (key2860, 2), (key2632, 1), (key2649, 1), (key2786, 1), (key2905, 1), (key2939, 1), (key2984, 1), (key2632, -2), (key2786, -2), (key2870, -2), (key2726, -1), (key2748, -1), (key2829, -1), (key2913, -1), (key2961, -1), (key2992, -1), (key2640, 1), (key2654, 1), (key2794, 1), (key2913, 1), (key2944, 1), (key2992, 1), (key2729, 2), (key2832, 2), (key2883, 2), (key2642, -2), (key2796, -2), (key2883, -2)]

def rawRow16648 : Integer.Sparse Key := [(key2738, -1), (key2706, -1), (key2898, -1), (key2809, -1), (key2977, -1), (key2951, -1), (key2706, 2), (key2860, 2), (key2809, 2), (key2649, 1), (key2632, 1), (key2905, 1), (key2786, 1), (key2984, 1), (key2939, 1), (key2632, -2), (key2870, -2), (key2786, -2), (key2748, -1), (key2726, -1), (key2913, -1), (key2829, -1), (key2992, -1), (key2961, -1), (key2654, 1), (key2640, 1), (key2913, 1), (key2794, 1), (key2992, 1), (key2944, 1), (key2729, 2), (key2883, 2), (key2832, 2), (key2642, -2), (key2883, -2), (key2796, -2)]

def rawRow16649 : Integer.Sparse Key := [(key2809, -1), (key2951, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2809, 2), (key2706, 2), (key2860, 2), (key2786, 1), (key2939, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2786, -2), (key2632, -2), (key2870, -2), (key2829, -1), (key2961, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2794, 1), (key2944, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2832, 2), (key2729, 2), (key2883, 2), (key2796, -2), (key2642, -2), (key2883, -2)]

def rawRow16650 : Integer.Sparse Key := [(key2951, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2898, -1), (key2738, -1), (key2809, 2), (key2860, 2), (key2706, 2), (key2939, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2905, 1), (key2649, 1), (key2786, -2), (key2870, -2), (key2632, -2), (key2961, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2913, -1), (key2748, -1), (key2944, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2913, 1), (key2654, 1), (key2832, 2), (key2883, 2), (key2729, 2), (key2796, -2), (key2883, -2), (key2642, -2)]

def rawRow16651 : Integer.Sparse Key := [(key2898, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2706, -1), (key2809, -1), (key2860, 2), (key2706, 2), (key2809, 2), (key2905, 1), (key2984, 1), (key2649, 1), (key2939, 1), (key2632, 1), (key2786, 1), (key2870, -2), (key2632, -2), (key2786, -2), (key2913, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2726, -1), (key2829, -1), (key2913, 1), (key2992, 1), (key2654, 1), (key2944, 1), (key2640, 1), (key2794, 1), (key2883, 2), (key2729, 2), (key2832, 2), (key2883, -2), (key2642, -2), (key2796, -2)]

def rawRow16652 : Integer.Sparse Key := [(key2977, -1), (key2898, -1), (key2951, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2860, 2), (key2809, 2), (key2706, 2), (key2984, 1), (key2905, 1), (key2939, 1), (key2649, 1), (key2786, 1), (key2632, 1), (key2870, -2), (key2786, -2), (key2632, -2), (key2992, -1), (key2913, -1), (key2961, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2992, 1), (key2913, 1), (key2944, 1), (key2654, 1), (key2794, 1), (key2640, 1), (key2883, 2), (key2832, 2), (key2729, 2), (key2883, -2), (key2796, -2), (key2642, -2)]

def rawRow16653 : Integer.Sparse Key := [(key2726, -1), (key2729, -1), (key2870, -1), (key2883, -1), (key2984, -1), (key2992, -1), (key2748, 2), (key2905, 2), (key2913, 2), (key2640, 1), (key2642, 1), (key2860, 1), (key2883, 1), (key2977, 1), (key2992, 1), (key2654, -2), (key2898, -2), (key2913, -2), (key2671, -1), (key2674, -1), (key2786, -1), (key2796, -1), (key2939, -1), (key2944, -1), (key2616, 1), (key2619, 1), (key2809, 1), (key2832, 1), (key2951, 1), (key2961, 1), (key2671, 2), (key2786, 2), (key2794, 2), (key2616, -2), (key2809, -2), (key2829, -2)]

def rawRow16654 : Integer.Sparse Key := [(key2729, -1), (key2726, -1), (key2883, -1), (key2870, -1), (key2992, -1), (key2984, -1), (key2748, 2), (key2913, 2), (key2905, 2), (key2642, 1), (key2640, 1), (key2883, 1), (key2860, 1), (key2992, 1), (key2977, 1), (key2654, -2), (key2913, -2), (key2898, -2), (key2674, -1), (key2671, -1), (key2796, -1), (key2786, -1), (key2944, -1), (key2939, -1), (key2619, 1), (key2616, 1), (key2832, 1), (key2809, 1), (key2961, 1), (key2951, 1), (key2671, 2), (key2794, 2), (key2786, 2), (key2616, -2), (key2829, -2), (key2809, -2)]

def rawRow16655 : Integer.Sparse Key := [(key2870, -1), (key2984, -1), (key2726, -1), (key2992, -1), (key2729, -1), (key2883, -1), (key2905, 2), (key2748, 2), (key2913, 2), (key2860, 1), (key2977, 1), (key2640, 1), (key2992, 1), (key2642, 1), (key2883, 1), (key2898, -2), (key2654, -2), (key2913, -2), (key2786, -1), (key2939, -1), (key2671, -1), (key2944, -1), (key2674, -1), (key2796, -1), (key2809, 1), (key2951, 1), (key2616, 1), (key2961, 1), (key2619, 1), (key2832, 1), (key2786, 2), (key2671, 2), (key2794, 2), (key2809, -2), (key2616, -2), (key2829, -2)]

def rawRow16656 : Integer.Sparse Key := [(key2984, -1), (key2870, -1), (key2992, -1), (key2726, -1), (key2883, -1), (key2729, -1), (key2905, 2), (key2913, 2), (key2748, 2), (key2977, 1), (key2860, 1), (key2992, 1), (key2640, 1), (key2883, 1), (key2642, 1), (key2898, -2), (key2913, -2), (key2654, -2), (key2939, -1), (key2786, -1), (key2944, -1), (key2671, -1), (key2796, -1), (key2674, -1), (key2951, 1), (key2809, 1), (key2961, 1), (key2616, 1), (key2832, 1), (key2619, 1), (key2786, 2), (key2794, 2), (key2671, 2), (key2809, -2), (key2829, -2), (key2616, -2)]

def rawRow16657 : Integer.Sparse Key := [(key2883, -1), (key2992, -1), (key2729, -1), (key2984, -1), (key2726, -1), (key2870, -1), (key2913, 2), (key2748, 2), (key2905, 2), (key2883, 1), (key2992, 1), (key2642, 1), (key2977, 1), (key2640, 1), (key2860, 1), (key2913, -2), (key2654, -2), (key2898, -2), (key2796, -1), (key2944, -1), (key2674, -1), (key2939, -1), (key2671, -1), (key2786, -1), (key2832, 1), (key2961, 1), (key2619, 1), (key2951, 1), (key2616, 1), (key2809, 1), (key2794, 2), (key2671, 2), (key2786, 2), (key2829, -2), (key2616, -2), (key2809, -2)]

def rawRow16658 : Integer.Sparse Key := [(key2992, -1), (key2883, -1), (key2984, -1), (key2729, -1), (key2870, -1), (key2726, -1), (key2913, 2), (key2905, 2), (key2748, 2), (key2992, 1), (key2883, 1), (key2977, 1), (key2642, 1), (key2860, 1), (key2640, 1), (key2913, -2), (key2898, -2), (key2654, -2), (key2944, -1), (key2796, -1), (key2939, -1), (key2674, -1), (key2786, -1), (key2671, -1), (key2961, 1), (key2832, 1), (key2951, 1), (key2619, 1), (key2809, 1), (key2616, 1), (key2794, 2), (key2786, 2), (key2671, 2), (key2829, -2), (key2809, -2), (key2616, -2)]

def rawRow16659 : Integer.Sparse Key := [(key2726, -1), (key2748, -1), (key2829, -1), (key2913, -1), (key2961, -1), (key2992, -1), (key2729, 2), (key2832, 2), (key2883, 2), (key2640, 1), (key2654, 1), (key2794, 1), (key2913, 1), (key2944, 1), (key2992, 1), (key2642, -2), (key2796, -2), (key2883, -2), (key2706, -1), (key2738, -1), (key2809, -1), (key2898, -1), (key2951, -1), (key2977, -1), (key2632, 1), (key2649, 1), (key2786, 1), (key2905, 1), (key2939, 1), (key2984, 1), (key2706, 2), (key2809, 2), (key2860, 2), (key2632, -2), (key2786, -2), (key2870, -2)]

def rawRow16660 : Integer.Sparse Key := [(key2748, -1), (key2726, -1), (key2913, -1), (key2829, -1), (key2992, -1), (key2961, -1), (key2729, 2), (key2883, 2), (key2832, 2), (key2654, 1), (key2640, 1), (key2913, 1), (key2794, 1), (key2992, 1), (key2944, 1), (key2642, -2), (key2883, -2), (key2796, -2), (key2738, -1), (key2706, -1), (key2898, -1), (key2809, -1), (key2977, -1), (key2951, -1), (key2649, 1), (key2632, 1), (key2905, 1), (key2786, 1), (key2984, 1), (key2939, 1), (key2706, 2), (key2860, 2), (key2809, 2), (key2632, -2), (key2870, -2), (key2786, -2)]

def rawRow16661 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2832, 2), (key2729, 2), (key2883, 2), (key2794, 1), (key2944, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2796, -2), (key2642, -2), (key2883, -2), (key2809, -1), (key2951, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2786, 1), (key2939, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2809, 2), (key2706, 2), (key2860, 2), (key2786, -2), (key2632, -2), (key2870, -2)]

def rawRow16662 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2913, -1), (key2748, -1), (key2832, 2), (key2883, 2), (key2729, 2), (key2944, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2913, 1), (key2654, 1), (key2796, -2), (key2883, -2), (key2642, -2), (key2951, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2898, -1), (key2738, -1), (key2939, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2905, 1), (key2649, 1), (key2809, 2), (key2860, 2), (key2706, 2), (key2786, -2), (key2870, -2), (key2632, -2)]

def rawRow16663 : Integer.Sparse Key := [(key2913, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2726, -1), (key2829, -1), (key2883, 2), (key2729, 2), (key2832, 2), (key2913, 1), (key2992, 1), (key2654, 1), (key2944, 1), (key2640, 1), (key2794, 1), (key2883, -2), (key2642, -2), (key2796, -2), (key2898, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2706, -1), (key2809, -1), (key2905, 1), (key2984, 1), (key2649, 1), (key2939, 1), (key2632, 1), (key2786, 1), (key2860, 2), (key2706, 2), (key2809, 2), (key2870, -2), (key2632, -2), (key2786, -2)]

def rawRow16664 : Integer.Sparse Key := [(key2992, -1), (key2913, -1), (key2961, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2883, 2), (key2832, 2), (key2729, 2), (key2992, 1), (key2913, 1), (key2944, 1), (key2654, 1), (key2794, 1), (key2640, 1), (key2883, -2), (key2796, -2), (key2642, -2), (key2977, -1), (key2898, -1), (key2951, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2984, 1), (key2905, 1), (key2939, 1), (key2649, 1), (key2786, 1), (key2632, 1), (key2860, 2), (key2809, 2), (key2706, 2), (key2870, -2), (key2786, -2), (key2632, -2)]

def rawRow16665 : Integer.Sparse Key := [(key2729, -1), (key2748, -1), (key2832, -1), (key2905, -1), (key2961, -1), (key2984, -1), (key2726, 2), (key2829, 2), (key2870, 2), (key2642, 1), (key2654, 1), (key2796, 1), (key2898, 1), (key2944, 1), (key2977, 1), (key2640, -2), (key2794, -2), (key2860, -2), (key2729, -1), (key2748, -1), (key2832, -1), (key2905, -1), (key2961, -1), (key2984, -1), (key2642, 1), (key2654, 1), (key2796, 1), (key2898, 1), (key2944, 1), (key2977, 1), (key2726, 2), (key2829, 2), (key2870, 2), (key2640, -2), (key2794, -2), (key2860, -2)]

def rawRow16666 : Integer.Sparse Key := [(key2748, -1), (key2729, -1), (key2905, -1), (key2832, -1), (key2984, -1), (key2961, -1), (key2726, 2), (key2870, 2), (key2829, 2), (key2654, 1), (key2642, 1), (key2898, 1), (key2796, 1), (key2977, 1), (key2944, 1), (key2640, -2), (key2860, -2), (key2794, -2), (key2748, -1), (key2729, -1), (key2905, -1), (key2832, -1), (key2984, -1), (key2961, -1), (key2654, 1), (key2642, 1), (key2898, 1), (key2796, 1), (key2977, 1), (key2944, 1), (key2726, 2), (key2870, 2), (key2829, 2), (key2640, -2), (key2860, -2), (key2794, -2)]

def rawRow16667 : Integer.Sparse Key := [(key2832, -1), (key2961, -1), (key2729, -1), (key2984, -1), (key2748, -1), (key2905, -1), (key2829, 2), (key2726, 2), (key2870, 2), (key2796, 1), (key2944, 1), (key2642, 1), (key2977, 1), (key2654, 1), (key2898, 1), (key2794, -2), (key2640, -2), (key2860, -2), (key2832, -1), (key2961, -1), (key2729, -1), (key2984, -1), (key2748, -1), (key2905, -1), (key2796, 1), (key2944, 1), (key2642, 1), (key2977, 1), (key2654, 1), (key2898, 1), (key2829, 2), (key2726, 2), (key2870, 2), (key2794, -2), (key2640, -2), (key2860, -2)]

def rawRow16668 : Integer.Sparse Key := [(key2961, -1), (key2832, -1), (key2984, -1), (key2729, -1), (key2905, -1), (key2748, -1), (key2829, 2), (key2870, 2), (key2726, 2), (key2944, 1), (key2796, 1), (key2977, 1), (key2642, 1), (key2898, 1), (key2654, 1), (key2794, -2), (key2860, -2), (key2640, -2), (key2961, -1), (key2832, -1), (key2984, -1), (key2729, -1), (key2905, -1), (key2748, -1), (key2944, 1), (key2796, 1), (key2977, 1), (key2642, 1), (key2898, 1), (key2654, 1), (key2829, 2), (key2870, 2), (key2726, 2), (key2794, -2), (key2860, -2), (key2640, -2)]

def rawRow16669 : Integer.Sparse Key := [(key2905, -1), (key2984, -1), (key2748, -1), (key2961, -1), (key2729, -1), (key2832, -1), (key2870, 2), (key2726, 2), (key2829, 2), (key2898, 1), (key2977, 1), (key2654, 1), (key2944, 1), (key2642, 1), (key2796, 1), (key2860, -2), (key2640, -2), (key2794, -2), (key2905, -1), (key2984, -1), (key2748, -1), (key2961, -1), (key2729, -1), (key2832, -1), (key2898, 1), (key2977, 1), (key2654, 1), (key2944, 1), (key2642, 1), (key2796, 1), (key2870, 2), (key2726, 2), (key2829, 2), (key2860, -2), (key2640, -2), (key2794, -2)]

def rawRow16670 : Integer.Sparse Key := [(key2984, -1), (key2905, -1), (key2961, -1), (key2748, -1), (key2832, -1), (key2729, -1), (key2870, 2), (key2829, 2), (key2726, 2), (key2977, 1), (key2898, 1), (key2944, 1), (key2654, 1), (key2796, 1), (key2642, 1), (key2860, -2), (key2794, -2), (key2640, -2), (key2984, -1), (key2905, -1), (key2961, -1), (key2748, -1), (key2832, -1), (key2729, -1), (key2977, 1), (key2898, 1), (key2944, 1), (key2654, 1), (key2796, 1), (key2642, 1), (key2870, 2), (key2829, 2), (key2726, 2), (key2860, -2), (key2794, -2), (key2640, -2)]

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

def rawRow16881 : Integer.Sparse Key := [(key798, 4), (key804, 4), (key771, 4), (key873, -4), (key798, -4), (key804, -4), (key804, -4), (key771, -4), (key779, -4), (key804, 12)]

def rawRow16882 : Integer.Sparse Key := [(key804, 4), (key771, 4), (key798, 4), (key804, -4), (key873, -4), (key798, -4), (key779, -4), (key804, -4), (key771, -4), (key804, 12)]

def rawRow16883 : Integer.Sparse Key := [(key804, 4), (key798, 4), (key771, 4), (key873, -4), (key804, -4), (key798, -4), (key804, -4), (key779, -4), (key771, -4), (key804, 12)]

def rawRow16884 : Integer.Sparse Key := [(key798, 4), (key798, 4), (key873, 4), (key771, -4), (key804, -4), (key804, -4), (key771, -4), (key804, -4), (key804, -4), (key779, 12)]

def rawRow16885 : Integer.Sparse Key := [(key798, 4), (key873, 4), (key798, 4), (key804, -4), (key771, -4), (key804, -4), (key804, -4), (key771, -4), (key804, -4), (key779, 12)]

def rawRow16886 : Integer.Sparse Key := [(key873, 4), (key798, 4), (key798, 4), (key804, -4), (key804, -4), (key771, -4), (key804, -4), (key804, -4), (key771, -4), (key779, 12)]

def rawRow16887 : Integer.Sparse Key := [(key2147, -1), (key2152, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2176, 2), (key2176, 2), (key2187, 2), (key2147, -1), (key2152, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2240, 2), (key2246, 2), (key2240, 2), (key2253, 2), (key2246, 2), (key2253, 2), (key2276, -1), (key2279, -1), (key2276, -1), (key2287, -1), (key2279, -1), (key2287, -1), (key2176, 2), (key2176, 2), (key2187, 2), (key2276, -1), (key2279, -1), (key2276, -1), (key2287, -1), (key2279, -1), (key2287, -1)]

def rawRow16888 : Integer.Sparse Key := [(key2152, -1), (key2147, -1), (key2166, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2176, 2), (key2187, 2), (key2176, 2), (key2152, -1), (key2147, -1), (key2166, -1), (key2147, -1), (key2166, -1), (key2152, -1), (key2246, 2), (key2240, 2), (key2253, 2), (key2240, 2), (key2253, 2), (key2246, 2), (key2279, -1), (key2276, -1), (key2287, -1), (key2276, -1), (key2287, -1), (key2279, -1), (key2176, 2), (key2187, 2), (key2176, 2), (key2279, -1), (key2276, -1), (key2287, -1), (key2276, -1), (key2287, -1), (key2279, -1)]

def rawRow16889 : Integer.Sparse Key := [(key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2147, -1), (key2147, -1), (key2187, 2), (key2176, 2), (key2176, 2), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2147, -1), (key2147, -1), (key2253, 2), (key2253, 2), (key2246, 2), (key2246, 2), (key2240, 2), (key2240, 2), (key2287, -1), (key2287, -1), (key2279, -1), (key2279, -1), (key2276, -1), (key2276, -1), (key2187, 2), (key2176, 2), (key2176, 2), (key2287, -1), (key2287, -1), (key2279, -1), (key2279, -1), (key2276, -1), (key2276, -1)]

def rawRow16890 : Integer.Sparse Key := [(key2028, -1), (key2033, -1), (key2147, -1), (key2166, -1), (key2176, -1), (key2187, -1), (key2033, 2), (key2152, 2), (key2166, 2), (key2058, -1), (key2063, -1), (key2240, -1), (key2253, -1), (key2276, -1), (key2287, -1), (key2058, 2), (key2069, 2), (key2147, 2), (key2166, 2), (key2279, 2), (key2287, 2), (key2063, -1), (key2069, -1), (key2152, -1), (key2166, -1), (key2246, -1), (key2253, -1), (key2079, 2), (key2276, 2), (key2287, 2), (key2079, -1), (key2085, -1), (key2176, -1), (key2187, -1), (key2279, -1), (key2287, -1)]

def rawRow16891 : Integer.Sparse Key := [(key2033, -1), (key2028, -1), (key2166, -1), (key2147, -1), (key2187, -1), (key2176, -1), (key2033, 2), (key2166, 2), (key2152, 2), (key2063, -1), (key2058, -1), (key2253, -1), (key2240, -1), (key2287, -1), (key2276, -1), (key2069, 2), (key2058, 2), (key2166, 2), (key2147, 2), (key2287, 2), (key2279, 2), (key2069, -1), (key2063, -1), (key2166, -1), (key2152, -1), (key2253, -1), (key2246, -1), (key2079, 2), (key2287, 2), (key2276, 2), (key2085, -1), (key2079, -1), (key2187, -1), (key2176, -1), (key2287, -1), (key2279, -1)]

def rawRow16892 : Integer.Sparse Key := [(key2147, -1), (key2176, -1), (key2028, -1), (key2187, -1), (key2033, -1), (key2166, -1), (key2152, 2), (key2033, 2), (key2166, 2), (key2240, -1), (key2276, -1), (key2058, -1), (key2287, -1), (key2063, -1), (key2253, -1), (key2147, 2), (key2279, 2), (key2058, 2), (key2287, 2), (key2069, 2), (key2166, 2), (key2152, -1), (key2246, -1), (key2063, -1), (key2253, -1), (key2069, -1), (key2166, -1), (key2276, 2), (key2079, 2), (key2287, 2), (key2176, -1), (key2279, -1), (key2079, -1), (key2287, -1), (key2085, -1), (key2187, -1)]

def rawRow16893 : Integer.Sparse Key := [(key2176, -1), (key2147, -1), (key2187, -1), (key2028, -1), (key2166, -1), (key2033, -1), (key2152, 2), (key2166, 2), (key2033, 2), (key2276, -1), (key2240, -1), (key2287, -1), (key2058, -1), (key2253, -1), (key2063, -1), (key2279, 2), (key2147, 2), (key2287, 2), (key2058, 2), (key2166, 2), (key2069, 2), (key2246, -1), (key2152, -1), (key2253, -1), (key2063, -1), (key2166, -1), (key2069, -1), (key2276, 2), (key2287, 2), (key2079, 2), (key2279, -1), (key2176, -1), (key2287, -1), (key2079, -1), (key2187, -1), (key2085, -1)]

def rawRow16894 : Integer.Sparse Key := [(key2166, -1), (key2187, -1), (key2033, -1), (key2176, -1), (key2028, -1), (key2147, -1), (key2166, 2), (key2033, 2), (key2152, 2), (key2253, -1), (key2287, -1), (key2063, -1), (key2276, -1), (key2058, -1), (key2240, -1), (key2166, 2), (key2287, 2), (key2069, 2), (key2279, 2), (key2058, 2), (key2147, 2), (key2166, -1), (key2253, -1), (key2069, -1), (key2246, -1), (key2063, -1), (key2152, -1), (key2287, 2), (key2079, 2), (key2276, 2), (key2187, -1), (key2287, -1), (key2085, -1), (key2279, -1), (key2079, -1), (key2176, -1)]

def rawRow16895 : Integer.Sparse Key := [(key2187, -1), (key2166, -1), (key2176, -1), (key2033, -1), (key2147, -1), (key2028, -1), (key2166, 2), (key2152, 2), (key2033, 2), (key2287, -1), (key2253, -1), (key2276, -1), (key2063, -1), (key2240, -1), (key2058, -1), (key2287, 2), (key2166, 2), (key2279, 2), (key2069, 2), (key2147, 2), (key2058, 2), (key2253, -1), (key2166, -1), (key2246, -1), (key2069, -1), (key2152, -1), (key2063, -1), (key2287, 2), (key2276, 2), (key2079, 2), (key2287, -1), (key2187, -1), (key2279, -1), (key2085, -1), (key2176, -1), (key2079, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16896 : Integer.Sparse Key := [(key2058, -1), (key2063, -1), (key2240, -1), (key2253, -1), (key2276, -1), (key2287, -1), (key2079, 2), (key2276, 2), (key2287, 2), (key2028, -1), (key2033, -1), (key2147, -1), (key2166, -1), (key2176, -1), (key2187, -1), (key2058, 2), (key2069, 2), (key2147, 2), (key2166, 2), (key2279, 2), (key2287, 2), (key2079, -1), (key2085, -1), (key2176, -1), (key2187, -1), (key2279, -1), (key2287, -1), (key2033, 2), (key2152, 2), (key2166, 2), (key2063, -1), (key2069, -1), (key2152, -1), (key2166, -1), (key2246, -1), (key2253, -1)]

def rawRow16897 : Integer.Sparse Key := [(key2063, -1), (key2058, -1), (key2253, -1), (key2240, -1), (key2287, -1), (key2276, -1), (key2079, 2), (key2287, 2), (key2276, 2), (key2033, -1), (key2028, -1), (key2166, -1), (key2147, -1), (key2187, -1), (key2176, -1), (key2069, 2), (key2058, 2), (key2166, 2), (key2147, 2), (key2287, 2), (key2279, 2), (key2085, -1), (key2079, -1), (key2187, -1), (key2176, -1), (key2287, -1), (key2279, -1), (key2033, 2), (key2166, 2), (key2152, 2), (key2069, -1), (key2063, -1), (key2166, -1), (key2152, -1), (key2253, -1), (key2246, -1)]

def rawRow16898 : Integer.Sparse Key := [(key2240, -1), (key2276, -1), (key2058, -1), (key2287, -1), (key2063, -1), (key2253, -1), (key2276, 2), (key2079, 2), (key2287, 2), (key2147, -1), (key2176, -1), (key2028, -1), (key2187, -1), (key2033, -1), (key2166, -1), (key2147, 2), (key2279, 2), (key2058, 2), (key2287, 2), (key2069, 2), (key2166, 2), (key2176, -1), (key2279, -1), (key2079, -1), (key2287, -1), (key2085, -1), (key2187, -1), (key2152, 2), (key2033, 2), (key2166, 2), (key2152, -1), (key2246, -1), (key2063, -1), (key2253, -1), (key2069, -1), (key2166, -1)]

def rawRow16899 : Integer.Sparse Key := [(key2276, -1), (key2240, -1), (key2287, -1), (key2058, -1), (key2253, -1), (key2063, -1), (key2276, 2), (key2287, 2), (key2079, 2), (key2176, -1), (key2147, -1), (key2187, -1), (key2028, -1), (key2166, -1), (key2033, -1), (key2279, 2), (key2147, 2), (key2287, 2), (key2058, 2), (key2166, 2), (key2069, 2), (key2279, -1), (key2176, -1), (key2287, -1), (key2079, -1), (key2187, -1), (key2085, -1), (key2152, 2), (key2166, 2), (key2033, 2), (key2246, -1), (key2152, -1), (key2253, -1), (key2063, -1), (key2166, -1), (key2069, -1)]

def rawRow16900 : Integer.Sparse Key := [(key2253, -1), (key2287, -1), (key2063, -1), (key2276, -1), (key2058, -1), (key2240, -1), (key2287, 2), (key2079, 2), (key2276, 2), (key2166, -1), (key2187, -1), (key2033, -1), (key2176, -1), (key2028, -1), (key2147, -1), (key2166, 2), (key2287, 2), (key2069, 2), (key2279, 2), (key2058, 2), (key2147, 2), (key2187, -1), (key2287, -1), (key2085, -1), (key2279, -1), (key2079, -1), (key2176, -1), (key2166, 2), (key2033, 2), (key2152, 2), (key2166, -1), (key2253, -1), (key2069, -1), (key2246, -1), (key2063, -1), (key2152, -1)]

def rawRow16901 : Integer.Sparse Key := [(key2287, -1), (key2253, -1), (key2276, -1), (key2063, -1), (key2240, -1), (key2058, -1), (key2287, 2), (key2276, 2), (key2079, 2), (key2187, -1), (key2166, -1), (key2176, -1), (key2033, -1), (key2147, -1), (key2028, -1), (key2287, 2), (key2166, 2), (key2279, 2), (key2069, 2), (key2147, 2), (key2058, 2), (key2287, -1), (key2187, -1), (key2279, -1), (key2085, -1), (key2176, -1), (key2079, -1), (key2166, 2), (key2152, 2), (key2033, 2), (key2253, -1), (key2166, -1), (key2246, -1), (key2069, -1), (key2152, -1), (key2063, -1)]

def rawRow16902 : Integer.Sparse Key := [(key2058, -1), (key2079, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2287, -1), (key2063, 2), (key2063, 2), (key2253, 2), (key2058, -1), (key2079, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2287, -1), (key2028, 2), (key2085, 2), (key2028, 2), (key2187, 2), (key2085, 2), (key2187, 2), (key2033, -1), (key2069, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2166, -1), (key2063, 2), (key2063, 2), (key2253, 2), (key2033, -1), (key2069, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2166, -1)]

def rawRow16903 : Integer.Sparse Key := [(key2079, -1), (key2058, -1), (key2287, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2063, 2), (key2253, 2), (key2063, 2), (key2079, -1), (key2058, -1), (key2287, -1), (key2058, -1), (key2287, -1), (key2079, -1), (key2085, 2), (key2028, 2), (key2187, 2), (key2028, 2), (key2187, 2), (key2085, 2), (key2069, -1), (key2033, -1), (key2166, -1), (key2033, -1), (key2166, -1), (key2069, -1), (key2063, 2), (key2253, 2), (key2063, 2), (key2069, -1), (key2033, -1), (key2166, -1), (key2033, -1), (key2166, -1), (key2069, -1)]

def rawRow16904 : Integer.Sparse Key := [(key2287, -1), (key2287, -1), (key2079, -1), (key2079, -1), (key2058, -1), (key2058, -1), (key2253, 2), (key2063, 2), (key2063, 2), (key2287, -1), (key2287, -1), (key2079, -1), (key2079, -1), (key2058, -1), (key2058, -1), (key2187, 2), (key2187, 2), (key2085, 2), (key2085, 2), (key2028, 2), (key2028, 2), (key2166, -1), (key2166, -1), (key2069, -1), (key2069, -1), (key2033, -1), (key2033, -1), (key2253, 2), (key2063, 2), (key2063, 2), (key2166, -1), (key2166, -1), (key2069, -1), (key2069, -1), (key2033, -1), (key2033, -1)]

def rawRow16905 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key362, -2), (key366, 6), (key731, -2), (key733, -2), (key733, -2), (key865, 2), (key867, 2), (key865, 2), (key881, 2), (key867, 2), (key881, 2), (key927, -2), (key927, -2), (key938, -2), (key750, 6), (key927, -2), (key927, -2), (key938, -2)]

def rawRow16906 : Integer.Sparse Key := [(key362, -2), (key360, -2), (key362, -2), (key366, 6), (key733, -2), (key731, -2), (key733, -2), (key867, 2), (key865, 2), (key881, 2), (key865, 2), (key881, 2), (key867, 2), (key927, -2), (key938, -2), (key927, -2), (key750, 6), (key927, -2), (key938, -2), (key927, -2)]

def rawRow16907 : Integer.Sparse Key := [(key362, -2), (key362, -2), (key360, -2), (key366, 6), (key733, -2), (key733, -2), (key731, -2), (key881, 2), (key881, 2), (key867, 2), (key867, 2), (key865, 2), (key865, 2), (key938, -2), (key927, -2), (key927, -2), (key750, 6), (key938, -2), (key927, -2), (key927, -2)]

def rawRow16908 : Integer.Sparse Key := [(key360, -2), (key362, -2), (key366, -2), (key362, 6), (key865, -2), (key867, -2), (key927, -2), (key731, 2), (key733, 2), (key865, 2), (key881, 2), (key927, 2), (key938, 2), (key733, -2), (key867, -2), (key881, -2), (key927, 6), (key750, -2), (key927, -2), (key938, -2)]

def rawRow16909 : Integer.Sparse Key := [(key362, -2), (key360, -2), (key366, -2), (key362, 6), (key867, -2), (key865, -2), (key927, -2), (key733, 2), (key731, 2), (key881, 2), (key865, 2), (key938, 2), (key927, 2), (key733, -2), (key881, -2), (key867, -2), (key927, 6), (key750, -2), (key938, -2), (key927, -2)]

def rawRow16910 : Integer.Sparse Key := [(key360, -2), (key366, -2), (key362, -2), (key362, 6), (key865, -2), (key927, -2), (key867, -2), (key865, 2), (key927, 2), (key731, 2), (key938, 2), (key733, 2), (key881, 2), (key867, -2), (key733, -2), (key881, -2), (key927, 6), (key927, -2), (key750, -2), (key938, -2)]

def rawRow16911 : Integer.Sparse Key := [(key366, -2), (key360, -2), (key362, -2), (key362, 6), (key927, -2), (key865, -2), (key867, -2), (key927, 2), (key865, 2), (key938, 2), (key731, 2), (key881, 2), (key733, 2), (key867, -2), (key881, -2), (key733, -2), (key927, 6), (key927, -2), (key938, -2), (key750, -2)]

def rawRow16912 : Integer.Sparse Key := [(key362, -2), (key366, -2), (key360, -2), (key362, 6), (key867, -2), (key927, -2), (key865, -2), (key881, 2), (key938, 2), (key733, 2), (key927, 2), (key731, 2), (key865, 2), (key881, -2), (key733, -2), (key867, -2), (key927, 6), (key938, -2), (key750, -2), (key927, -2)]

def rawRow16913 : Integer.Sparse Key := [(key366, -2), (key362, -2), (key360, -2), (key362, 6), (key927, -2), (key867, -2), (key865, -2), (key938, 2), (key881, 2), (key927, 2), (key733, 2), (key865, 2), (key731, 2), (key881, -2), (key867, -2), (key733, -2), (key927, 6), (key938, -2), (key927, -2), (key750, -2)]

def rawRow16914 : Integer.Sparse Key := [(key529, -2), (key531, -2), (key537, -2), (key537, 6), (key360, -2), (key362, -2), (key366, -2), (key731, 2), (key733, 2), (key865, 2), (key881, 2), (key927, 2), (key938, 2), (key750, -2), (key927, -2), (key938, -2), (key733, 6), (key733, -2), (key867, -2), (key881, -2)]

def rawRow16915 : Integer.Sparse Key := [(key531, -2), (key529, -2), (key537, -2), (key537, 6), (key362, -2), (key360, -2), (key366, -2), (key733, 2), (key731, 2), (key881, 2), (key865, 2), (key938, 2), (key927, 2), (key750, -2), (key938, -2), (key927, -2), (key733, 6), (key733, -2), (key881, -2), (key867, -2)]

def rawRow16916 : Integer.Sparse Key := [(key529, -2), (key537, -2), (key531, -2), (key537, 6), (key360, -2), (key366, -2), (key362, -2), (key865, 2), (key927, 2), (key731, 2), (key938, 2), (key733, 2), (key881, 2), (key927, -2), (key750, -2), (key938, -2), (key733, 6), (key867, -2), (key733, -2), (key881, -2)]

def rawRow16917 : Integer.Sparse Key := [(key537, -2), (key529, -2), (key531, -2), (key537, 6), (key366, -2), (key360, -2), (key362, -2), (key927, 2), (key865, 2), (key938, 2), (key731, 2), (key881, 2), (key733, 2), (key927, -2), (key938, -2), (key750, -2), (key733, 6), (key867, -2), (key881, -2), (key733, -2)]

def rawRow16918 : Integer.Sparse Key := [(key531, -2), (key537, -2), (key529, -2), (key537, 6), (key362, -2), (key366, -2), (key360, -2), (key881, 2), (key938, 2), (key733, 2), (key927, 2), (key731, 2), (key865, 2), (key938, -2), (key750, -2), (key927, -2), (key733, 6), (key881, -2), (key733, -2), (key867, -2)]

def rawRow16919 : Integer.Sparse Key := [(key537, -2), (key531, -2), (key529, -2), (key537, 6), (key366, -2), (key362, -2), (key360, -2), (key938, 2), (key881, 2), (key927, 2), (key733, 2), (key865, 2), (key731, 2), (key938, -2), (key927, -2), (key750, -2), (key733, 6), (key881, -2), (key867, -2), (key733, -2)]

def rawRow16920 : Integer.Sparse Key := [(key529, -2), (key537, -2), (key537, -2), (key531, 6), (key529, -2), (key537, -2), (key537, -2), (key360, 2), (key366, 2), (key731, 2), (key938, 2), (key750, 2), (key938, 2), (key733, -2), (key733, -2), (key881, -2), (key867, 6), (key733, -2), (key733, -2), (key881, -2)]

def rawRow16921 : Integer.Sparse Key := [(key537, -2), (key529, -2), (key537, -2), (key531, 6), (key537, -2), (key529, -2), (key537, -2), (key366, 2), (key360, 2), (key938, 2), (key731, 2), (key938, 2), (key750, 2), (key733, -2), (key881, -2), (key733, -2), (key867, 6), (key733, -2), (key881, -2), (key733, -2)]

def rawRow16922 : Integer.Sparse Key := [(key537, -2), (key537, -2), (key529, -2), (key531, 6), (key537, -2), (key537, -2), (key529, -2), (key676, 2), (key676, 2), (key366, 2), (key366, 2), (key360, 2), (key731, 2), (key881, -2), (key733, -2), (key733, -2), (key867, 6), (key881, -2), (key733, -2), (key733, -2)]

def rawRow16923 : Integer.Sparse Key := [(key1989, 2), (key1989, 2), (key1994, 2), (key1999, -2), (key2003, -2), (key2003, -2), (key1989, 2), (key1989, 2), (key1994, 2), (key2268, -1), (key2272, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2294, -1), (key1999, -2), (key2003, -2), (key2003, -2), (key2268, -1), (key2272, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2294, -1), (key2324, 4), (key2324, 4), (key2336, 4)]

def rawRow16924 : Integer.Sparse Key := [(key1989, 2), (key1994, 2), (key1989, 2), (key2003, -2), (key1999, -2), (key2003, -2), (key1989, 2), (key1994, 2), (key1989, 2), (key2272, -1), (key2268, -1), (key2294, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2003, -2), (key1999, -2), (key2003, -2), (key2272, -1), (key2268, -1), (key2294, -1), (key2268, -1), (key2294, -1), (key2272, -1), (key2324, 4), (key2336, 4), (key2324, 4)]

def rawRow16925 : Integer.Sparse Key := [(key1994, 2), (key1989, 2), (key1989, 2), (key2003, -2), (key2003, -2), (key1999, -2), (key1994, 2), (key1989, 2), (key1989, 2), (key2294, -1), (key2294, -1), (key2272, -1), (key2272, -1), (key2268, -1), (key2268, -1), (key2003, -2), (key2003, -2), (key1999, -2), (key2294, -1), (key2294, -1), (key2272, -1), (key2272, -1), (key2268, -1), (key2268, -1), (key2336, 4), (key2324, 4), (key2324, 4)]

def rawRow16926 : Integer.Sparse Key := [(key1989, 2), (key1999, 2), (key2003, 2), (key1989, -2), (key1994, -2), (key2003, -2), (key2234, 2), (key2268, 2), (key2272, 2), (key1989, -1), (key1994, -1), (key2234, -1), (key2259, -1), (key2272, -1), (key2294, -1), (key2268, -2), (key2272, -2), (key2324, -2), (key1999, -1), (key2003, -1), (key2268, -1), (key2294, -1), (key2324, -1), (key2336, -1), (key2003, 4), (key2272, 4), (key2294, 4)]

def rawRow16927 : Integer.Sparse Key := [(key1989, 2), (key2003, 2), (key1999, 2), (key1994, -2), (key1989, -2), (key2003, -2), (key2234, 2), (key2272, 2), (key2268, 2), (key1994, -1), (key1989, -1), (key2259, -1), (key2234, -1), (key2294, -1), (key2272, -1), (key2272, -2), (key2268, -2), (key2324, -2), (key2003, -1), (key1999, -1), (key2294, -1), (key2268, -1), (key2336, -1), (key2324, -1), (key2003, 4), (key2294, 4), (key2272, 4)]

def rawRow16928 : Integer.Sparse Key := [(key1999, 2), (key1989, 2), (key2003, 2), (key1989, -2), (key2003, -2), (key1994, -2), (key2268, 2), (key2234, 2), (key2272, 2), (key2234, -1), (key2272, -1), (key1989, -1), (key2294, -1), (key1994, -1), (key2259, -1), (key2268, -2), (key2324, -2), (key2272, -2), (key2268, -1), (key2324, -1), (key1999, -1), (key2336, -1), (key2003, -1), (key2294, -1), (key2272, 4), (key2003, 4), (key2294, 4)]

def rawRow16929 : Integer.Sparse Key := [(key1999, 2), (key2003, 2), (key1989, 2), (key2003, -2), (key1989, -2), (key1994, -2), (key2268, 2), (key2272, 2), (key2234, 2), (key2272, -1), (key2234, -1), (key2294, -1), (key1989, -1), (key2259, -1), (key1994, -1), (key2324, -2), (key2268, -2), (key2272, -2), (key2324, -1), (key2268, -1), (key2336, -1), (key1999, -1), (key2294, -1), (key2003, -1), (key2272, 4), (key2294, 4), (key2003, 4)]

def rawRow16930 : Integer.Sparse Key := [(key2003, 2), (key1989, 2), (key1999, 2), (key1994, -2), (key2003, -2), (key1989, -2), (key2272, 2), (key2234, 2), (key2268, 2), (key2259, -1), (key2294, -1), (key1994, -1), (key2272, -1), (key1989, -1), (key2234, -1), (key2272, -2), (key2324, -2), (key2268, -2), (key2294, -1), (key2336, -1), (key2003, -1), (key2324, -1), (key1999, -1), (key2268, -1), (key2294, 4), (key2003, 4), (key2272, 4)]

def rawRow16931 : Integer.Sparse Key := [(key2003, 2), (key1999, 2), (key1989, 2), (key2003, -2), (key1994, -2), (key1989, -2), (key2272, 2), (key2268, 2), (key2234, 2), (key2294, -1), (key2259, -1), (key2272, -1), (key1994, -1), (key2234, -1), (key1989, -1), (key2324, -2), (key2272, -2), (key2268, -2), (key2336, -1), (key2294, -1), (key2324, -1), (key2003, -1), (key2268, -1), (key1999, -1), (key2294, 4), (key2272, 4), (key2003, 4)]

def rawRow16932 : Integer.Sparse Key := [(key2234, 2), (key2268, 2), (key2272, 2), (key2268, -2), (key2272, -2), (key2324, -2), (key1989, 2), (key1999, 2), (key2003, 2), (key1999, -1), (key2003, -1), (key2268, -1), (key2294, -1), (key2324, -1), (key2336, -1), (key1989, -2), (key1994, -2), (key2003, -2), (key1989, -1), (key1994, -1), (key2234, -1), (key2259, -1), (key2272, -1), (key2294, -1), (key2003, 4), (key2272, 4), (key2294, 4)]

def rawRow16933 : Integer.Sparse Key := [(key2234, 2), (key2272, 2), (key2268, 2), (key2272, -2), (key2268, -2), (key2324, -2), (key1989, 2), (key2003, 2), (key1999, 2), (key2003, -1), (key1999, -1), (key2294, -1), (key2268, -1), (key2336, -1), (key2324, -1), (key1994, -2), (key1989, -2), (key2003, -2), (key1994, -1), (key1989, -1), (key2259, -1), (key2234, -1), (key2294, -1), (key2272, -1), (key2003, 4), (key2294, 4), (key2272, 4)]

def rawRow16934 : Integer.Sparse Key := [(key2268, 2), (key2234, 2), (key2272, 2), (key2268, -2), (key2324, -2), (key2272, -2), (key1999, 2), (key1989, 2), (key2003, 2), (key2268, -1), (key2324, -1), (key1999, -1), (key2336, -1), (key2003, -1), (key2294, -1), (key1989, -2), (key2003, -2), (key1994, -2), (key2234, -1), (key2272, -1), (key1989, -1), (key2294, -1), (key1994, -1), (key2259, -1), (key2272, 4), (key2003, 4), (key2294, 4)]

def rawRow16935 : Integer.Sparse Key := [(key2268, 2), (key2272, 2), (key2234, 2), (key2324, -2), (key2268, -2), (key2272, -2), (key1999, 2), (key2003, 2), (key1989, 2), (key2324, -1), (key2268, -1), (key2336, -1), (key1999, -1), (key2294, -1), (key2003, -1), (key2003, -2), (key1989, -2), (key1994, -2), (key2272, -1), (key2234, -1), (key2294, -1), (key1989, -1), (key2259, -1), (key1994, -1), (key2272, 4), (key2294, 4), (key2003, 4)]

def rawRow16936 : Integer.Sparse Key := [(key2272, 2), (key2234, 2), (key2268, 2), (key2272, -2), (key2324, -2), (key2268, -2), (key2003, 2), (key1989, 2), (key1999, 2), (key2294, -1), (key2336, -1), (key2003, -1), (key2324, -1), (key1999, -1), (key2268, -1), (key1994, -2), (key2003, -2), (key1989, -2), (key2259, -1), (key2294, -1), (key1994, -1), (key2272, -1), (key1989, -1), (key2234, -1), (key2294, 4), (key2003, 4), (key2272, 4)]

def rawRow16937 : Integer.Sparse Key := [(key2272, 2), (key2268, 2), (key2234, 2), (key2324, -2), (key2272, -2), (key2268, -2), (key2003, 2), (key1999, 2), (key1989, 2), (key2336, -1), (key2294, -1), (key2324, -1), (key2003, -1), (key2268, -1), (key1999, -1), (key2003, -2), (key1994, -2), (key1989, -2), (key2294, -1), (key2259, -1), (key2272, -1), (key1994, -1), (key2234, -1), (key1989, -1), (key2294, 4), (key2272, 4), (key2003, 4)]

def rawRow16938 : Integer.Sparse Key := [(key2268, 2), (key2268, 2), (key2324, 2), (key2234, -2), (key2272, -2), (key2272, -2), (key2268, 2), (key2268, 2), (key2324, 2), (key1989, -1), (key2003, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key2294, -1), (key2234, -2), (key2272, -2), (key2272, -2), (key1989, -1), (key2003, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key2294, -1), (key1994, 4), (key1994, 4), (key2259, 4)]

def rawRow16939 : Integer.Sparse Key := [(key2268, 2), (key2324, 2), (key2268, 2), (key2272, -2), (key2234, -2), (key2272, -2), (key2268, 2), (key2324, 2), (key2268, 2), (key2003, -1), (key1989, -1), (key2294, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key2272, -2), (key2234, -2), (key2272, -2), (key2003, -1), (key1989, -1), (key2294, -1), (key1989, -1), (key2294, -1), (key2003, -1), (key1994, 4), (key2259, 4), (key1994, 4)]

def rawRow16940 : Integer.Sparse Key := [(key2324, 2), (key2268, 2), (key2268, 2), (key2272, -2), (key2272, -2), (key2234, -2), (key2324, 2), (key2268, 2), (key2268, 2), (key2294, -1), (key2294, -1), (key2003, -1), (key2003, -1), (key1989, -1), (key1989, -1), (key2272, -2), (key2272, -2), (key2234, -2), (key2294, -1), (key2294, -1), (key2003, -1), (key2003, -1), (key1989, -1), (key1989, -1), (key2259, 4), (key1994, 4), (key1994, 4)]

def rawRow16941 : Integer.Sparse Key := [(key2027, 2), (key2033, 2), (key2033, 2), (key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2027, 2), (key2033, 2), (key2033, 2), (key2146, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2146, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2166, -1), (key2239, 2), (key2246, 2), (key2239, 2), (key2253, 2), (key2246, 2), (key2253, 2)]

def rawRow16942 : Integer.Sparse Key := [(key2033, 2), (key2027, 2), (key2033, 2), (key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2033, 2), (key2027, 2), (key2033, 2), (key2152, -1), (key2146, -1), (key2166, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2152, -1), (key2146, -1), (key2166, -1), (key2146, -1), (key2166, -1), (key2152, -1), (key2246, 2), (key2239, 2), (key2253, 2), (key2239, 2), (key2253, 2), (key2246, 2)]

def rawRow16943 : Integer.Sparse Key := [(key2033, 2), (key2033, 2), (key2027, 2), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2033, 2), (key2033, 2), (key2027, 2), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2146, -1), (key2146, -1), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2166, -1), (key2166, -1), (key2152, -1), (key2152, -1), (key2146, -1), (key2146, -1), (key2253, 2), (key2253, 2), (key2246, 2), (key2246, 2), (key2239, 2), (key2239, 2)]

def rawRow16944 : Integer.Sparse Key := [(key2057, 2), (key2063, 2), (key2092, 2), (key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2146, 2), (key2152, 2), (key2194, 2), (key2027, -1), (key2033, -1), (key2146, -1), (key2166, -1), (key2194, -1), (key2200, -1), (key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2057, -1), (key2063, -1), (key2239, -1), (key2253, -1), (key2303, -1), (key2310, -1), (key2057, 2), (key2069, 2), (key2146, 2), (key2166, 2), (key2305, 2), (key2310, 2)]

def rawRow16945 : Integer.Sparse Key := [(key2063, 2), (key2057, 2), (key2092, 2), (key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2152, 2), (key2146, 2), (key2194, 2), (key2033, -1), (key2027, -1), (key2166, -1), (key2146, -1), (key2200, -1), (key2194, -1), (key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2063, -1), (key2057, -1), (key2253, -1), (key2239, -1), (key2310, -1), (key2303, -1), (key2069, 2), (key2057, 2), (key2166, 2), (key2146, 2), (key2310, 2), (key2305, 2)]

def rawRow16946 : Integer.Sparse Key := [(key2057, 2), (key2092, 2), (key2063, 2), (key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2146, 2), (key2194, 2), (key2152, 2), (key2146, -1), (key2194, -1), (key2027, -1), (key2200, -1), (key2033, -1), (key2166, -1), (key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2239, -1), (key2303, -1), (key2057, -1), (key2310, -1), (key2063, -1), (key2253, -1), (key2146, 2), (key2305, 2), (key2057, 2), (key2310, 2), (key2069, 2), (key2166, 2)]

def rawRow16947 : Integer.Sparse Key := [(key2092, 2), (key2057, 2), (key2063, 2), (key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2194, 2), (key2146, 2), (key2152, 2), (key2194, -1), (key2146, -1), (key2200, -1), (key2027, -1), (key2166, -1), (key2033, -1), (key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2303, -1), (key2239, -1), (key2310, -1), (key2057, -1), (key2253, -1), (key2063, -1), (key2305, 2), (key2146, 2), (key2310, 2), (key2057, 2), (key2166, 2), (key2069, 2)]

def rawRow16948 : Integer.Sparse Key := [(key2063, 2), (key2092, 2), (key2057, 2), (key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2152, 2), (key2194, 2), (key2146, 2), (key2166, -1), (key2200, -1), (key2033, -1), (key2194, -1), (key2027, -1), (key2146, -1), (key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2253, -1), (key2310, -1), (key2063, -1), (key2303, -1), (key2057, -1), (key2239, -1), (key2166, 2), (key2310, 2), (key2069, 2), (key2305, 2), (key2057, 2), (key2146, 2)]

def rawRow16949 : Integer.Sparse Key := [(key2092, 2), (key2063, 2), (key2057, 2), (key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2194, 2), (key2152, 2), (key2146, 2), (key2200, -1), (key2166, -1), (key2194, -1), (key2033, -1), (key2146, -1), (key2027, -1), (key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2310, -1), (key2253, -1), (key2303, -1), (key2063, -1), (key2239, -1), (key2057, -1), (key2310, 2), (key2166, 2), (key2305, 2), (key2069, 2), (key2146, 2), (key2057, 2)]

def rawRow16950 : Integer.Sparse Key := [(key2146, 2), (key2152, 2), (key2194, 2), (key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2057, 2), (key2063, 2), (key2092, 2), (key2057, -1), (key2063, -1), (key2239, -1), (key2253, -1), (key2303, -1), (key2310, -1), (key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2027, -1), (key2033, -1), (key2146, -1), (key2166, -1), (key2194, -1), (key2200, -1), (key2057, 2), (key2069, 2), (key2146, 2), (key2166, 2), (key2305, 2), (key2310, 2)]

def rawRow16951 : Integer.Sparse Key := [(key2152, 2), (key2146, 2), (key2194, 2), (key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2063, 2), (key2057, 2), (key2092, 2), (key2063, -1), (key2057, -1), (key2253, -1), (key2239, -1), (key2310, -1), (key2303, -1), (key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2033, -1), (key2027, -1), (key2166, -1), (key2146, -1), (key2200, -1), (key2194, -1), (key2069, 2), (key2057, 2), (key2166, 2), (key2146, 2), (key2310, 2), (key2305, 2)]

def rawRow16952 : Integer.Sparse Key := [(key2146, 2), (key2194, 2), (key2152, 2), (key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2057, 2), (key2092, 2), (key2063, 2), (key2239, -1), (key2303, -1), (key2057, -1), (key2310, -1), (key2063, -1), (key2253, -1), (key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2146, -1), (key2194, -1), (key2027, -1), (key2200, -1), (key2033, -1), (key2166, -1), (key2146, 2), (key2305, 2), (key2057, 2), (key2310, 2), (key2069, 2), (key2166, 2)]

def rawRow16953 : Integer.Sparse Key := [(key2194, 2), (key2146, 2), (key2152, 2), (key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2092, 2), (key2057, 2), (key2063, 2), (key2303, -1), (key2239, -1), (key2310, -1), (key2057, -1), (key2253, -1), (key2063, -1), (key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2194, -1), (key2146, -1), (key2200, -1), (key2027, -1), (key2166, -1), (key2033, -1), (key2305, 2), (key2146, 2), (key2310, 2), (key2057, 2), (key2166, 2), (key2069, 2)]

def rawRow16954 : Integer.Sparse Key := [(key2152, 2), (key2194, 2), (key2146, 2), (key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2063, 2), (key2092, 2), (key2057, 2), (key2253, -1), (key2310, -1), (key2063, -1), (key2303, -1), (key2057, -1), (key2239, -1), (key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2166, -1), (key2200, -1), (key2033, -1), (key2194, -1), (key2027, -1), (key2146, -1), (key2166, 2), (key2310, 2), (key2069, 2), (key2305, 2), (key2057, 2), (key2146, 2)]

def rawRow16955 : Integer.Sparse Key := [(key2194, 2), (key2152, 2), (key2146, 2), (key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2092, 2), (key2063, 2), (key2057, 2), (key2310, -1), (key2253, -1), (key2303, -1), (key2063, -1), (key2239, -1), (key2057, -1), (key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2200, -1), (key2166, -1), (key2194, -1), (key2033, -1), (key2146, -1), (key2027, -1), (key2310, 2), (key2166, 2), (key2305, 2), (key2069, 2), (key2146, 2), (key2057, 2)]

def rawRow16956 : Integer.Sparse Key := [(key2239, 2), (key2303, 2), (key2303, 2), (key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2239, 2), (key2303, 2), (key2303, 2), (key2057, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2310, -1), (key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2057, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2310, -1), (key2027, 2), (key2095, 2), (key2027, 2), (key2200, 2), (key2095, 2), (key2200, 2)]

def rawRow16957 : Integer.Sparse Key := [(key2303, 2), (key2239, 2), (key2303, 2), (key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2303, 2), (key2239, 2), (key2303, 2), (key2092, -1), (key2057, -1), (key2310, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2092, -1), (key2057, -1), (key2310, -1), (key2057, -1), (key2310, -1), (key2092, -1), (key2095, 2), (key2027, 2), (key2200, 2), (key2027, 2), (key2200, 2), (key2095, 2)]

def rawRow16958 : Integer.Sparse Key := [(key2303, 2), (key2303, 2), (key2239, 2), (key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2303, 2), (key2303, 2), (key2239, 2), (key2310, -1), (key2310, -1), (key2092, -1), (key2092, -1), (key2057, -1), (key2057, -1), (key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2310, -1), (key2310, -1), (key2092, -1), (key2092, -1), (key2057, -1), (key2057, -1), (key2200, 2), (key2200, 2), (key2095, 2), (key2095, 2), (key2027, 2), (key2027, 2)]

def rawRow16959 : Integer.Sparse Key := [(key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2092, 2), (key2092, 2), (key2095, 2), (key2146, 1), (key2152, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2194, -2), (key2194, -2), (key2200, -2), (key2057, -1), (key2063, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2146, 1), (key2152, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2092, 2), (key2092, 2), (key2095, 2), (key2194, -2), (key2194, -2), (key2200, -2)]

def rawRow16960 : Integer.Sparse Key := [(key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2092, 2), (key2095, 2), (key2092, 2), (key2152, 1), (key2146, 1), (key2166, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2194, -2), (key2200, -2), (key2194, -2), (key2063, -1), (key2057, -1), (key2069, -1), (key2057, -1), (key2069, -1), (key2063, -1), (key2152, 1), (key2146, 1), (key2166, 1), (key2146, 1), (key2166, 1), (key2152, 1), (key2092, 2), (key2095, 2), (key2092, 2), (key2194, -2), (key2200, -2), (key2194, -2)]

def rawRow16961 : Integer.Sparse Key := [(key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2095, 2), (key2092, 2), (key2092, 2), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2146, 1), (key2146, 1), (key2200, -2), (key2194, -2), (key2194, -2), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2057, -1), (key2057, -1), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2146, 1), (key2146, 1), (key2095, 2), (key2092, 2), (key2092, 2), (key2200, -2), (key2194, -2), (key2194, -2)]

def rawRow16962 : Integer.Sparse Key := [(key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2033, 2), (key2063, 2), (key2069, 2), (key2027, 1), (key2033, 1), (key2146, 1), (key2166, 1), (key2194, 1), (key2200, 1), (key2033, -2), (key2152, -2), (key2166, -2), (key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2057, 1), (key2063, 1), (key2239, 1), (key2253, 1), (key2303, 1), (key2310, 1), (key2194, 2), (key2303, 2), (key2305, 2), (key2092, -2), (key2303, -2), (key2310, -2)]

def rawRow16963 : Integer.Sparse Key := [(key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, 1), (key2027, 1), (key2166, 1), (key2146, 1), (key2200, 1), (key2194, 1), (key2033, -2), (key2166, -2), (key2152, -2), (key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2063, 1), (key2057, 1), (key2253, 1), (key2239, 1), (key2310, 1), (key2303, 1), (key2194, 2), (key2305, 2), (key2303, 2), (key2092, -2), (key2310, -2), (key2303, -2)]

def rawRow16964 : Integer.Sparse Key := [(key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2063, 2), (key2033, 2), (key2069, 2), (key2146, 1), (key2194, 1), (key2027, 1), (key2200, 1), (key2033, 1), (key2166, 1), (key2152, -2), (key2033, -2), (key2166, -2), (key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2239, 1), (key2303, 1), (key2057, 1), (key2310, 1), (key2063, 1), (key2253, 1), (key2303, 2), (key2194, 2), (key2305, 2), (key2303, -2), (key2092, -2), (key2310, -2)]

def rawRow16965 : Integer.Sparse Key := [(key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2063, 2), (key2069, 2), (key2033, 2), (key2194, 1), (key2146, 1), (key2200, 1), (key2027, 1), (key2166, 1), (key2033, 1), (key2152, -2), (key2166, -2), (key2033, -2), (key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2303, 1), (key2239, 1), (key2310, 1), (key2057, 1), (key2253, 1), (key2063, 1), (key2303, 2), (key2305, 2), (key2194, 2), (key2303, -2), (key2310, -2), (key2092, -2)]

def rawRow16966 : Integer.Sparse Key := [(key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, 1), (key2200, 1), (key2033, 1), (key2194, 1), (key2027, 1), (key2146, 1), (key2166, -2), (key2033, -2), (key2152, -2), (key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2253, 1), (key2310, 1), (key2063, 1), (key2303, 1), (key2057, 1), (key2239, 1), (key2305, 2), (key2194, 2), (key2303, 2), (key2310, -2), (key2092, -2), (key2303, -2)]

def rawRow16967 : Integer.Sparse Key := [(key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2069, 2), (key2063, 2), (key2033, 2), (key2200, 1), (key2166, 1), (key2194, 1), (key2033, 1), (key2146, 1), (key2027, 1), (key2166, -2), (key2152, -2), (key2033, -2), (key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2310, 1), (key2253, 1), (key2303, 1), (key2063, 1), (key2239, 1), (key2057, 1), (key2305, 2), (key2303, 2), (key2194, 2), (key2310, -2), (key2303, -2), (key2092, -2)]

def rawRow16968 : Integer.Sparse Key := [(key2146, -1), (key2152, -1), (key2239, -1), (key2246, -1), (key2303, -1), (key2305, -1), (key2194, 2), (key2303, 2), (key2305, 2), (key2057, 1), (key2063, 1), (key2239, 1), (key2253, 1), (key2303, 1), (key2310, 1), (key2092, -2), (key2303, -2), (key2310, -2), (key2027, -1), (key2033, -1), (key2057, -1), (key2069, -1), (key2092, -1), (key2095, -1), (key2027, 1), (key2033, 1), (key2146, 1), (key2166, 1), (key2194, 1), (key2200, 1), (key2033, 2), (key2063, 2), (key2069, 2), (key2033, -2), (key2152, -2), (key2166, -2)]

def rawRow16969 : Integer.Sparse Key := [(key2152, -1), (key2146, -1), (key2246, -1), (key2239, -1), (key2305, -1), (key2303, -1), (key2194, 2), (key2305, 2), (key2303, 2), (key2063, 1), (key2057, 1), (key2253, 1), (key2239, 1), (key2310, 1), (key2303, 1), (key2092, -2), (key2310, -2), (key2303, -2), (key2033, -1), (key2027, -1), (key2069, -1), (key2057, -1), (key2095, -1), (key2092, -1), (key2033, 1), (key2027, 1), (key2166, 1), (key2146, 1), (key2200, 1), (key2194, 1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, -2), (key2166, -2), (key2152, -2)]

def rawRow16970 : Integer.Sparse Key := [(key2239, -1), (key2303, -1), (key2146, -1), (key2305, -1), (key2152, -1), (key2246, -1), (key2303, 2), (key2194, 2), (key2305, 2), (key2239, 1), (key2303, 1), (key2057, 1), (key2310, 1), (key2063, 1), (key2253, 1), (key2303, -2), (key2092, -2), (key2310, -2), (key2057, -1), (key2092, -1), (key2027, -1), (key2095, -1), (key2033, -1), (key2069, -1), (key2146, 1), (key2194, 1), (key2027, 1), (key2200, 1), (key2033, 1), (key2166, 1), (key2063, 2), (key2033, 2), (key2069, 2), (key2152, -2), (key2033, -2), (key2166, -2)]

def rawRow16971 : Integer.Sparse Key := [(key2303, -1), (key2239, -1), (key2305, -1), (key2146, -1), (key2246, -1), (key2152, -1), (key2303, 2), (key2305, 2), (key2194, 2), (key2303, 1), (key2239, 1), (key2310, 1), (key2057, 1), (key2253, 1), (key2063, 1), (key2303, -2), (key2310, -2), (key2092, -2), (key2092, -1), (key2057, -1), (key2095, -1), (key2027, -1), (key2069, -1), (key2033, -1), (key2194, 1), (key2146, 1), (key2200, 1), (key2027, 1), (key2166, 1), (key2033, 1), (key2063, 2), (key2069, 2), (key2033, 2), (key2152, -2), (key2166, -2), (key2033, -2)]

def rawRow16972 : Integer.Sparse Key := [(key2246, -1), (key2305, -1), (key2152, -1), (key2303, -1), (key2146, -1), (key2239, -1), (key2305, 2), (key2194, 2), (key2303, 2), (key2253, 1), (key2310, 1), (key2063, 1), (key2303, 1), (key2057, 1), (key2239, 1), (key2310, -2), (key2092, -2), (key2303, -2), (key2069, -1), (key2095, -1), (key2033, -1), (key2092, -1), (key2027, -1), (key2057, -1), (key2166, 1), (key2200, 1), (key2033, 1), (key2194, 1), (key2027, 1), (key2146, 1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, -2), (key2033, -2), (key2152, -2)]

def rawRow16973 : Integer.Sparse Key := [(key2305, -1), (key2246, -1), (key2303, -1), (key2152, -1), (key2239, -1), (key2146, -1), (key2305, 2), (key2303, 2), (key2194, 2), (key2310, 1), (key2253, 1), (key2303, 1), (key2063, 1), (key2239, 1), (key2057, 1), (key2310, -2), (key2303, -2), (key2092, -2), (key2095, -1), (key2069, -1), (key2092, -1), (key2033, -1), (key2057, -1), (key2027, -1), (key2200, 1), (key2166, 1), (key2194, 1), (key2033, 1), (key2146, 1), (key2027, 1), (key2069, 2), (key2063, 2), (key2033, 2), (key2166, -2), (key2152, -2), (key2033, -2)]

def rawRow16974 : Integer.Sparse Key := [(key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2152, 2), (key2152, 2), (key2246, 2), (key2057, 1), (key2092, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2310, 1), (key2063, -2), (key2063, -2), (key2253, -2), (key2146, -1), (key2194, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2305, -1), (key2057, 1), (key2092, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2310, 1), (key2152, 2), (key2152, 2), (key2246, 2), (key2063, -2), (key2063, -2), (key2253, -2)]

def rawRow16975 : Integer.Sparse Key := [(key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2152, 2), (key2246, 2), (key2152, 2), (key2092, 1), (key2057, 1), (key2310, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2063, -2), (key2253, -2), (key2063, -2), (key2194, -1), (key2146, -1), (key2305, -1), (key2146, -1), (key2305, -1), (key2194, -1), (key2092, 1), (key2057, 1), (key2310, 1), (key2057, 1), (key2310, 1), (key2092, 1), (key2152, 2), (key2246, 2), (key2152, 2), (key2063, -2), (key2253, -2), (key2063, -2)]

def rawRow16976 : Integer.Sparse Key := [(key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2246, 2), (key2152, 2), (key2152, 2), (key2310, 1), (key2310, 1), (key2092, 1), (key2092, 1), (key2057, 1), (key2057, 1), (key2253, -2), (key2063, -2), (key2063, -2), (key2305, -1), (key2305, -1), (key2194, -1), (key2194, -1), (key2146, -1), (key2146, -1), (key2310, 1), (key2310, 1), (key2092, 1), (key2092, 1), (key2057, 1), (key2057, 1), (key2246, 2), (key2152, 2), (key2152, 2), (key2253, -2), (key2063, -2), (key2063, -2)]

def rawRow16977 : Integer.Sparse Key := [(key2058, -1), (key2063, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2079, 2), (key2079, 2), (key2085, 2), (key2147, 1), (key2152, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2176, -2), (key2176, -2), (key2187, -2), (key2058, -1), (key2063, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2069, -1), (key2147, 1), (key2152, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2166, 1), (key2079, 2), (key2079, 2), (key2085, 2), (key2176, -2), (key2176, -2), (key2187, -2)]

def rawRow16978 : Integer.Sparse Key := [(key2063, -1), (key2058, -1), (key2069, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2079, 2), (key2085, 2), (key2079, 2), (key2152, 1), (key2147, 1), (key2166, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2176, -2), (key2187, -2), (key2176, -2), (key2063, -1), (key2058, -1), (key2069, -1), (key2058, -1), (key2069, -1), (key2063, -1), (key2152, 1), (key2147, 1), (key2166, 1), (key2147, 1), (key2166, 1), (key2152, 1), (key2079, 2), (key2085, 2), (key2079, 2), (key2176, -2), (key2187, -2), (key2176, -2)]

def rawRow16979 : Integer.Sparse Key := [(key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2058, -1), (key2058, -1), (key2085, 2), (key2079, 2), (key2079, 2), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2147, 1), (key2147, 1), (key2187, -2), (key2176, -2), (key2176, -2), (key2069, -1), (key2069, -1), (key2063, -1), (key2063, -1), (key2058, -1), (key2058, -1), (key2166, 1), (key2166, 1), (key2152, 1), (key2152, 1), (key2147, 1), (key2147, 1), (key2085, 2), (key2079, 2), (key2079, 2), (key2187, -2), (key2176, -2), (key2176, -2)]

def rawRow16980 : Integer.Sparse Key := [(key2028, -1), (key2033, -1), (key2058, -1), (key2069, -1), (key2079, -1), (key2085, -1), (key2033, 2), (key2063, 2), (key2069, 2), (key2028, 1), (key2033, 1), (key2147, 1), (key2166, 1), (key2176, 1), (key2187, 1), (key2033, -2), (key2152, -2), (key2166, -2), (key2147, -1), (key2152, -1), (key2240, -1), (key2246, -1), (key2276, -1), (key2279, -1), (key2058, 1), (key2063, 1), (key2240, 1), (key2253, 1), (key2276, 1), (key2287, 1), (key2176, 2), (key2276, 2), (key2279, 2), (key2079, -2), (key2276, -2), (key2287, -2)]

def rawRow16981 : Integer.Sparse Key := [(key2033, -1), (key2028, -1), (key2069, -1), (key2058, -1), (key2085, -1), (key2079, -1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, 1), (key2028, 1), (key2166, 1), (key2147, 1), (key2187, 1), (key2176, 1), (key2033, -2), (key2166, -2), (key2152, -2), (key2152, -1), (key2147, -1), (key2246, -1), (key2240, -1), (key2279, -1), (key2276, -1), (key2063, 1), (key2058, 1), (key2253, 1), (key2240, 1), (key2287, 1), (key2276, 1), (key2176, 2), (key2279, 2), (key2276, 2), (key2079, -2), (key2287, -2), (key2276, -2)]

def rawRow16982 : Integer.Sparse Key := [(key2058, -1), (key2079, -1), (key2028, -1), (key2085, -1), (key2033, -1), (key2069, -1), (key2063, 2), (key2033, 2), (key2069, 2), (key2147, 1), (key2176, 1), (key2028, 1), (key2187, 1), (key2033, 1), (key2166, 1), (key2152, -2), (key2033, -2), (key2166, -2), (key2240, -1), (key2276, -1), (key2147, -1), (key2279, -1), (key2152, -1), (key2246, -1), (key2240, 1), (key2276, 1), (key2058, 1), (key2287, 1), (key2063, 1), (key2253, 1), (key2276, 2), (key2176, 2), (key2279, 2), (key2276, -2), (key2079, -2), (key2287, -2)]

def rawRow16983 : Integer.Sparse Key := [(key2079, -1), (key2058, -1), (key2085, -1), (key2028, -1), (key2069, -1), (key2033, -1), (key2063, 2), (key2069, 2), (key2033, 2), (key2176, 1), (key2147, 1), (key2187, 1), (key2028, 1), (key2166, 1), (key2033, 1), (key2152, -2), (key2166, -2), (key2033, -2), (key2276, -1), (key2240, -1), (key2279, -1), (key2147, -1), (key2246, -1), (key2152, -1), (key2276, 1), (key2240, 1), (key2287, 1), (key2058, 1), (key2253, 1), (key2063, 1), (key2276, 2), (key2279, 2), (key2176, 2), (key2276, -2), (key2287, -2), (key2079, -2)]

def rawRow16984 : Integer.Sparse Key := [(key2069, -1), (key2085, -1), (key2033, -1), (key2079, -1), (key2028, -1), (key2058, -1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, 1), (key2187, 1), (key2033, 1), (key2176, 1), (key2028, 1), (key2147, 1), (key2166, -2), (key2033, -2), (key2152, -2), (key2246, -1), (key2279, -1), (key2152, -1), (key2276, -1), (key2147, -1), (key2240, -1), (key2253, 1), (key2287, 1), (key2063, 1), (key2276, 1), (key2058, 1), (key2240, 1), (key2279, 2), (key2176, 2), (key2276, 2), (key2287, -2), (key2079, -2), (key2276, -2)]

def rawRow16985 : Integer.Sparse Key := [(key2085, -1), (key2069, -1), (key2079, -1), (key2033, -1), (key2058, -1), (key2028, -1), (key2069, 2), (key2063, 2), (key2033, 2), (key2187, 1), (key2166, 1), (key2176, 1), (key2033, 1), (key2147, 1), (key2028, 1), (key2166, -2), (key2152, -2), (key2033, -2), (key2279, -1), (key2246, -1), (key2276, -1), (key2152, -1), (key2240, -1), (key2147, -1), (key2287, 1), (key2253, 1), (key2276, 1), (key2063, 1), (key2240, 1), (key2058, 1), (key2279, 2), (key2276, 2), (key2176, 2), (key2287, -2), (key2276, -2), (key2079, -2)]

def rawRow16986 : Integer.Sparse Key := [(key2147, -1), (key2152, -1), (key2240, -1), (key2246, -1), (key2276, -1), (key2279, -1), (key2176, 2), (key2276, 2), (key2279, 2), (key2058, 1), (key2063, 1), (key2240, 1), (key2253, 1), (key2276, 1), (key2287, 1), (key2079, -2), (key2276, -2), (key2287, -2), (key2028, -1), (key2033, -1), (key2058, -1), (key2069, -1), (key2079, -1), (key2085, -1), (key2028, 1), (key2033, 1), (key2147, 1), (key2166, 1), (key2176, 1), (key2187, 1), (key2033, 2), (key2063, 2), (key2069, 2), (key2033, -2), (key2152, -2), (key2166, -2)]

def rawRow16987 : Integer.Sparse Key := [(key2152, -1), (key2147, -1), (key2246, -1), (key2240, -1), (key2279, -1), (key2276, -1), (key2176, 2), (key2279, 2), (key2276, 2), (key2063, 1), (key2058, 1), (key2253, 1), (key2240, 1), (key2287, 1), (key2276, 1), (key2079, -2), (key2287, -2), (key2276, -2), (key2033, -1), (key2028, -1), (key2069, -1), (key2058, -1), (key2085, -1), (key2079, -1), (key2033, 1), (key2028, 1), (key2166, 1), (key2147, 1), (key2187, 1), (key2176, 1), (key2033, 2), (key2069, 2), (key2063, 2), (key2033, -2), (key2166, -2), (key2152, -2)]

def rawRow16988 : Integer.Sparse Key := [(key2240, -1), (key2276, -1), (key2147, -1), (key2279, -1), (key2152, -1), (key2246, -1), (key2276, 2), (key2176, 2), (key2279, 2), (key2240, 1), (key2276, 1), (key2058, 1), (key2287, 1), (key2063, 1), (key2253, 1), (key2276, -2), (key2079, -2), (key2287, -2), (key2058, -1), (key2079, -1), (key2028, -1), (key2085, -1), (key2033, -1), (key2069, -1), (key2147, 1), (key2176, 1), (key2028, 1), (key2187, 1), (key2033, 1), (key2166, 1), (key2063, 2), (key2033, 2), (key2069, 2), (key2152, -2), (key2033, -2), (key2166, -2)]

def rawRow16989 : Integer.Sparse Key := [(key2276, -1), (key2240, -1), (key2279, -1), (key2147, -1), (key2246, -1), (key2152, -1), (key2276, 2), (key2279, 2), (key2176, 2), (key2276, 1), (key2240, 1), (key2287, 1), (key2058, 1), (key2253, 1), (key2063, 1), (key2276, -2), (key2287, -2), (key2079, -2), (key2079, -1), (key2058, -1), (key2085, -1), (key2028, -1), (key2069, -1), (key2033, -1), (key2176, 1), (key2147, 1), (key2187, 1), (key2028, 1), (key2166, 1), (key2033, 1), (key2063, 2), (key2069, 2), (key2033, 2), (key2152, -2), (key2166, -2), (key2033, -2)]

def rawRow16990 : Integer.Sparse Key := [(key2246, -1), (key2279, -1), (key2152, -1), (key2276, -1), (key2147, -1), (key2240, -1), (key2279, 2), (key2176, 2), (key2276, 2), (key2253, 1), (key2287, 1), (key2063, 1), (key2276, 1), (key2058, 1), (key2240, 1), (key2287, -2), (key2079, -2), (key2276, -2), (key2069, -1), (key2085, -1), (key2033, -1), (key2079, -1), (key2028, -1), (key2058, -1), (key2166, 1), (key2187, 1), (key2033, 1), (key2176, 1), (key2028, 1), (key2147, 1), (key2069, 2), (key2033, 2), (key2063, 2), (key2166, -2), (key2033, -2), (key2152, -2)]

def rawRow16991 : Integer.Sparse Key := [(key2279, -1), (key2246, -1), (key2276, -1), (key2152, -1), (key2240, -1), (key2147, -1), (key2279, 2), (key2276, 2), (key2176, 2), (key2287, 1), (key2253, 1), (key2276, 1), (key2063, 1), (key2240, 1), (key2058, 1), (key2287, -2), (key2276, -2), (key2079, -2), (key2085, -1), (key2069, -1), (key2079, -1), (key2033, -1), (key2058, -1), (key2028, -1), (key2187, 1), (key2166, 1), (key2176, 1), (key2033, 1), (key2147, 1), (key2028, 1), (key2069, 2), (key2063, 2), (key2033, 2), (key2166, -2), (key2152, -2), (key2033, -2)]

def rawRow16992 : Integer.Sparse Key := [(key2147, -1), (key2176, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2279, -1), (key2152, 2), (key2152, 2), (key2246, 2), (key2058, 1), (key2079, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2287, 1), (key2063, -2), (key2063, -2), (key2253, -2), (key2147, -1), (key2176, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2279, -1), (key2058, 1), (key2079, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2287, 1), (key2152, 2), (key2152, 2), (key2246, 2), (key2063, -2), (key2063, -2), (key2253, -2)]

def rawRow16993 : Integer.Sparse Key := [(key2176, -1), (key2147, -1), (key2279, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2152, 2), (key2246, 2), (key2152, 2), (key2079, 1), (key2058, 1), (key2287, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2063, -2), (key2253, -2), (key2063, -2), (key2176, -1), (key2147, -1), (key2279, -1), (key2147, -1), (key2279, -1), (key2176, -1), (key2079, 1), (key2058, 1), (key2287, 1), (key2058, 1), (key2287, 1), (key2079, 1), (key2152, 2), (key2246, 2), (key2152, 2), (key2063, -2), (key2253, -2), (key2063, -2)]

def rawRow16994 : Integer.Sparse Key := [(key2279, -1), (key2279, -1), (key2176, -1), (key2176, -1), (key2147, -1), (key2147, -1), (key2246, 2), (key2152, 2), (key2152, 2), (key2287, 1), (key2287, 1), (key2079, 1), (key2079, 1), (key2058, 1), (key2058, 1), (key2253, -2), (key2063, -2), (key2063, -2), (key2279, -1), (key2279, -1), (key2176, -1), (key2176, -1), (key2147, -1), (key2147, -1), (key2287, 1), (key2287, 1), (key2079, 1), (key2079, 1), (key2058, 1), (key2058, 1), (key2246, 2), (key2152, 2), (key2152, 2), (key2253, -2), (key2063, -2), (key2063, -2)]

def rawRow16995 : Integer.Sparse Key := [(key2151, 2), (key2151, 2), (key2169, 2), (key2175, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2189, -1), (key2151, 2), (key2151, 2), (key2169, 2), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2175, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2189, -1), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2328, 2), (key2330, 2), (key2328, 2), (key2333, 2), (key2330, 2), (key2333, 2)]

def rawRow16996 : Integer.Sparse Key := [(key2151, 2), (key2169, 2), (key2151, 2), (key2179, -1), (key2175, -1), (key2189, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2151, 2), (key2169, 2), (key2151, 2), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2330, 2), (key2328, 2), (key2333, 2), (key2328, 2), (key2333, 2), (key2330, 2)]

def rawRow16997 : Integer.Sparse Key := [(key2169, 2), (key2151, 2), (key2151, 2), (key2189, -1), (key2189, -1), (key2179, -1), (key2179, -1), (key2175, -1), (key2175, -1), (key2169, 2), (key2151, 2), (key2151, 2), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2189, -1), (key2189, -1), (key2179, -1), (key2179, -1), (key2175, -1), (key2175, -1), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2333, 2), (key2333, 2), (key2330, 2), (key2330, 2), (key2328, 2), (key2328, 2)]

def rawRow16998 : Integer.Sparse Key := [(key2032, 2), (key2175, 2), (key2189, 2), (key2032, -1), (key2037, -1), (key2151, -1), (key2169, -1), (key2179, -1), (key2189, -1), (key2062, 2), (key2275, 2), (key2289, 2), (key2062, -1), (key2072, -1), (key2151, -1), (key2169, -1), (key2281, -1), (key2289, -1), (key2078, -1), (key2082, -1), (key2275, -1), (key2289, -1), (key2328, -1), (key2333, -1), (key2078, -1), (key2087, -1), (key2175, -1), (key2189, -1), (key2330, -1), (key2333, -1), (key2082, 2), (key2087, 2), (key2179, 2), (key2189, 2), (key2281, 2), (key2289, 2)]

def rawRow16999 : Integer.Sparse Key := [(key2032, 2), (key2189, 2), (key2175, 2), (key2037, -1), (key2032, -1), (key2169, -1), (key2151, -1), (key2189, -1), (key2179, -1), (key2062, 2), (key2289, 2), (key2275, 2), (key2072, -1), (key2062, -1), (key2169, -1), (key2151, -1), (key2289, -1), (key2281, -1), (key2082, -1), (key2078, -1), (key2289, -1), (key2275, -1), (key2333, -1), (key2328, -1), (key2087, -1), (key2078, -1), (key2189, -1), (key2175, -1), (key2333, -1), (key2330, -1), (key2087, 2), (key2082, 2), (key2189, 2), (key2179, 2), (key2289, 2), (key2281, 2)]

def rawRow17000 : Integer.Sparse Key := [(key2175, 2), (key2032, 2), (key2189, 2), (key2151, -1), (key2179, -1), (key2032, -1), (key2189, -1), (key2037, -1), (key2169, -1), (key2275, 2), (key2062, 2), (key2289, 2), (key2151, -1), (key2281, -1), (key2062, -1), (key2289, -1), (key2072, -1), (key2169, -1), (key2275, -1), (key2328, -1), (key2078, -1), (key2333, -1), (key2082, -1), (key2289, -1), (key2175, -1), (key2330, -1), (key2078, -1), (key2333, -1), (key2087, -1), (key2189, -1), (key2179, 2), (key2281, 2), (key2082, 2), (key2289, 2), (key2087, 2), (key2189, 2)]

def rawRow17001 : Integer.Sparse Key := [(key2175, 2), (key2189, 2), (key2032, 2), (key2179, -1), (key2151, -1), (key2189, -1), (key2032, -1), (key2169, -1), (key2037, -1), (key2275, 2), (key2289, 2), (key2062, 2), (key2281, -1), (key2151, -1), (key2289, -1), (key2062, -1), (key2169, -1), (key2072, -1), (key2328, -1), (key2275, -1), (key2333, -1), (key2078, -1), (key2289, -1), (key2082, -1), (key2330, -1), (key2175, -1), (key2333, -1), (key2078, -1), (key2189, -1), (key2087, -1), (key2281, 2), (key2179, 2), (key2289, 2), (key2082, 2), (key2189, 2), (key2087, 2)]

def rawRow17002 : Integer.Sparse Key := [(key2189, 2), (key2032, 2), (key2175, 2), (key2169, -1), (key2189, -1), (key2037, -1), (key2179, -1), (key2032, -1), (key2151, -1), (key2289, 2), (key2062, 2), (key2275, 2), (key2169, -1), (key2289, -1), (key2072, -1), (key2281, -1), (key2062, -1), (key2151, -1), (key2289, -1), (key2333, -1), (key2082, -1), (key2328, -1), (key2078, -1), (key2275, -1), (key2189, -1), (key2333, -1), (key2087, -1), (key2330, -1), (key2078, -1), (key2175, -1), (key2189, 2), (key2289, 2), (key2087, 2), (key2281, 2), (key2082, 2), (key2179, 2)]

def rawRow17003 : Integer.Sparse Key := [(key2189, 2), (key2175, 2), (key2032, 2), (key2189, -1), (key2169, -1), (key2179, -1), (key2037, -1), (key2151, -1), (key2032, -1), (key2289, 2), (key2275, 2), (key2062, 2), (key2289, -1), (key2169, -1), (key2281, -1), (key2072, -1), (key2151, -1), (key2062, -1), (key2333, -1), (key2289, -1), (key2328, -1), (key2082, -1), (key2275, -1), (key2078, -1), (key2333, -1), (key2189, -1), (key2330, -1), (key2087, -1), (key2175, -1), (key2078, -1), (key2289, 2), (key2189, 2), (key2281, 2), (key2087, 2), (key2179, 2), (key2082, 2)]

def rawRow17004 : Integer.Sparse Key := [(key2062, 2), (key2275, 2), (key2289, 2), (key2078, -1), (key2082, -1), (key2275, -1), (key2289, -1), (key2328, -1), (key2333, -1), (key2032, 2), (key2175, 2), (key2189, 2), (key2078, -1), (key2087, -1), (key2175, -1), (key2189, -1), (key2330, -1), (key2333, -1), (key2032, -1), (key2037, -1), (key2151, -1), (key2169, -1), (key2179, -1), (key2189, -1), (key2062, -1), (key2072, -1), (key2151, -1), (key2169, -1), (key2281, -1), (key2289, -1), (key2082, 2), (key2087, 2), (key2179, 2), (key2189, 2), (key2281, 2), (key2289, 2)]

def rawRow17005 : Integer.Sparse Key := [(key2062, 2), (key2289, 2), (key2275, 2), (key2082, -1), (key2078, -1), (key2289, -1), (key2275, -1), (key2333, -1), (key2328, -1), (key2032, 2), (key2189, 2), (key2175, 2), (key2087, -1), (key2078, -1), (key2189, -1), (key2175, -1), (key2333, -1), (key2330, -1), (key2037, -1), (key2032, -1), (key2169, -1), (key2151, -1), (key2189, -1), (key2179, -1), (key2072, -1), (key2062, -1), (key2169, -1), (key2151, -1), (key2289, -1), (key2281, -1), (key2087, 2), (key2082, 2), (key2189, 2), (key2179, 2), (key2289, 2), (key2281, 2)]

def rawRow17006 : Integer.Sparse Key := [(key2275, 2), (key2062, 2), (key2289, 2), (key2275, -1), (key2328, -1), (key2078, -1), (key2333, -1), (key2082, -1), (key2289, -1), (key2175, 2), (key2032, 2), (key2189, 2), (key2175, -1), (key2330, -1), (key2078, -1), (key2333, -1), (key2087, -1), (key2189, -1), (key2151, -1), (key2179, -1), (key2032, -1), (key2189, -1), (key2037, -1), (key2169, -1), (key2151, -1), (key2281, -1), (key2062, -1), (key2289, -1), (key2072, -1), (key2169, -1), (key2179, 2), (key2281, 2), (key2082, 2), (key2289, 2), (key2087, 2), (key2189, 2)]

def rawRow17007 : Integer.Sparse Key := [(key2275, 2), (key2289, 2), (key2062, 2), (key2328, -1), (key2275, -1), (key2333, -1), (key2078, -1), (key2289, -1), (key2082, -1), (key2175, 2), (key2189, 2), (key2032, 2), (key2330, -1), (key2175, -1), (key2333, -1), (key2078, -1), (key2189, -1), (key2087, -1), (key2179, -1), (key2151, -1), (key2189, -1), (key2032, -1), (key2169, -1), (key2037, -1), (key2281, -1), (key2151, -1), (key2289, -1), (key2062, -1), (key2169, -1), (key2072, -1), (key2281, 2), (key2179, 2), (key2289, 2), (key2082, 2), (key2189, 2), (key2087, 2)]

def rawRow17008 : Integer.Sparse Key := [(key2289, 2), (key2062, 2), (key2275, 2), (key2289, -1), (key2333, -1), (key2082, -1), (key2328, -1), (key2078, -1), (key2275, -1), (key2189, 2), (key2032, 2), (key2175, 2), (key2189, -1), (key2333, -1), (key2087, -1), (key2330, -1), (key2078, -1), (key2175, -1), (key2169, -1), (key2189, -1), (key2037, -1), (key2179, -1), (key2032, -1), (key2151, -1), (key2169, -1), (key2289, -1), (key2072, -1), (key2281, -1), (key2062, -1), (key2151, -1), (key2189, 2), (key2289, 2), (key2087, 2), (key2281, 2), (key2082, 2), (key2179, 2)]

def rawRow17009 : Integer.Sparse Key := [(key2289, 2), (key2275, 2), (key2062, 2), (key2333, -1), (key2289, -1), (key2328, -1), (key2082, -1), (key2275, -1), (key2078, -1), (key2189, 2), (key2175, 2), (key2032, 2), (key2333, -1), (key2189, -1), (key2330, -1), (key2087, -1), (key2175, -1), (key2078, -1), (key2189, -1), (key2169, -1), (key2179, -1), (key2037, -1), (key2151, -1), (key2032, -1), (key2289, -1), (key2169, -1), (key2281, -1), (key2072, -1), (key2151, -1), (key2062, -1), (key2289, 2), (key2189, 2), (key2281, 2), (key2087, 2), (key2179, 2), (key2082, 2)]

def rawRow17010 : Integer.Sparse Key := [(key2078, 2), (key2078, 2), (key2333, 2), (key2062, -1), (key2082, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2289, -1), (key2078, 2), (key2078, 2), (key2333, 2), (key2032, -1), (key2087, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2189, -1), (key2062, -1), (key2082, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2289, -1), (key2032, -1), (key2087, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2189, -1), (key2037, 2), (key2072, 2), (key2037, 2), (key2169, 2), (key2072, 2), (key2169, 2)]

def rawRow17011 : Integer.Sparse Key := [(key2078, 2), (key2333, 2), (key2078, 2), (key2082, -1), (key2062, -1), (key2289, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2078, 2), (key2333, 2), (key2078, 2), (key2087, -1), (key2032, -1), (key2189, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2082, -1), (key2062, -1), (key2289, -1), (key2062, -1), (key2289, -1), (key2082, -1), (key2087, -1), (key2032, -1), (key2189, -1), (key2032, -1), (key2189, -1), (key2087, -1), (key2072, 2), (key2037, 2), (key2169, 2), (key2037, 2), (key2169, 2), (key2072, 2)]

def rawRow17012 : Integer.Sparse Key := [(key2333, 2), (key2078, 2), (key2078, 2), (key2289, -1), (key2289, -1), (key2082, -1), (key2082, -1), (key2062, -1), (key2062, -1), (key2333, 2), (key2078, 2), (key2078, 2), (key2189, -1), (key2189, -1), (key2087, -1), (key2087, -1), (key2032, -1), (key2032, -1), (key2289, -1), (key2289, -1), (key2082, -1), (key2082, -1), (key2062, -1), (key2062, -1), (key2189, -1), (key2189, -1), (key2087, -1), (key2087, -1), (key2032, -1), (key2032, -1), (key2169, 2), (key2169, 2), (key2072, 2), (key2072, 2), (key2037, 2), (key2037, 2)]

def rawRow17013 : Integer.Sparse Key := [(key776, 4), (key778, 4), (key778, 4), (key801, -2), (key803, -2), (key801, -2), (key811, -2), (key803, -2), (key811, -2), (key801, -2), (key803, -2), (key801, -2), (key811, -2), (key803, -2), (key811, -2), (key871, 4), (key876, 4), (key876, 4)]

def rawRow17014 : Integer.Sparse Key := [(key778, 4), (key776, 4), (key778, 4), (key803, -2), (key801, -2), (key811, -2), (key801, -2), (key811, -2), (key803, -2), (key803, -2), (key801, -2), (key811, -2), (key801, -2), (key811, -2), (key803, -2), (key876, 4), (key871, 4), (key876, 4)]

def rawRow17015 : Integer.Sparse Key := [(key778, 4), (key778, 4), (key776, 4), (key811, -2), (key811, -2), (key803, -2), (key803, -2), (key801, -2), (key801, -2), (key811, -2), (key811, -2), (key803, -2), (key803, -2), (key801, -2), (key801, -2), (key876, 4), (key876, 4), (key871, 4)]

def rawRow17016 : Integer.Sparse Key := [(key801, 4), (key803, 4), (key811, 4), (key776, -2), (key778, -2), (key801, -2), (key811, -2), (key836, -2), (key839, -2), (key801, -2), (key803, -2), (key871, -2), (key876, -2), (key931, -2), (key934, -2), (key801, 4), (key811, 4), (key934, 4)]

def rawRow17017 : Integer.Sparse Key := [(key803, 4), (key801, 4), (key811, 4), (key778, -2), (key776, -2), (key811, -2), (key801, -2), (key839, -2), (key836, -2), (key803, -2), (key801, -2), (key876, -2), (key871, -2), (key934, -2), (key931, -2), (key811, 4), (key801, 4), (key934, 4)]

def rawRow17018 : Integer.Sparse Key := [(key801, 4), (key811, 4), (key803, 4), (key801, -2), (key811, -2), (key776, -2), (key839, -2), (key778, -2), (key811, -2), (key871, -2), (key931, -2), (key801, -2), (key934, -2), (key803, -2), (key876, -2), (key801, 4), (key934, 4), (key811, 4)]

def rawRow17019 : Integer.Sparse Key := [(key811, 4), (key801, 4), (key803, 4), (key811, -2), (key801, -2), (key839, -2), (key776, -2), (key811, -2), (key778, -2), (key931, -2), (key871, -2), (key934, -2), (key801, -2), (key876, -2), (key803, -2), (key934, 4), (key801, 4), (key811, 4)]

def rawRow17020 : Integer.Sparse Key := [(key803, 4), (key811, 4), (key801, 4), (key836, -2), (key839, -2), (key778, -2), (key811, -2), (key776, -2), (key801, -2), (key876, -2), (key934, -2), (key803, -2), (key931, -2), (key801, -2), (key871, -2), (key811, 4), (key934, 4), (key801, 4)]

def rawRow17021 : Integer.Sparse Key := [(key811, 4), (key803, 4), (key801, 4), (key839, -2), (key836, -2), (key811, -2), (key778, -2), (key801, -2), (key776, -2), (key934, -2), (key876, -2), (key931, -2), (key803, -2), (key871, -2), (key801, -2), (key934, 4), (key811, 4), (key801, 4)]

def rawRow17022 : Integer.Sparse Key := [(key801, 4), (key803, 4), (key811, 4), (key801, -2), (key803, -2), (key871, -2), (key931, -2), (key876, -2), (key934, -2), (key776, -2), (key778, -2), (key801, -2), (key811, -2), (key836, -2), (key839, -2), (key801, 4), (key811, 4), (key934, 4)]

def rawRow17023 : Integer.Sparse Key := [(key803, 4), (key801, 4), (key811, 4), (key803, -2), (key801, -2), (key931, -2), (key871, -2), (key934, -2), (key876, -2), (key778, -2), (key776, -2), (key811, -2), (key801, -2), (key839, -2), (key836, -2), (key811, 4), (key801, 4), (key934, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17024 : Integer.Sparse Key := [(key801, 4), (key811, 4), (key803, 4), (key871, -2), (key876, -2), (key801, -2), (key934, -2), (key803, -2), (key931, -2), (key801, -2), (key811, -2), (key776, -2), (key839, -2), (key778, -2), (key811, -2), (key801, 4), (key934, 4), (key811, 4)]

def rawRow17025 : Integer.Sparse Key := [(key811, 4), (key801, 4), (key803, 4), (key876, -2), (key871, -2), (key934, -2), (key801, -2), (key931, -2), (key803, -2), (key811, -2), (key801, -2), (key839, -2), (key776, -2), (key811, -2), (key778, -2), (key934, 4), (key801, 4), (key811, 4)]

def rawRow17026 : Integer.Sparse Key := [(key803, 4), (key811, 4), (key801, 4), (key931, -2), (key934, -2), (key803, -2), (key876, -2), (key801, -2), (key871, -2), (key836, -2), (key839, -2), (key778, -2), (key811, -2), (key776, -2), (key801, -2), (key811, 4), (key934, 4), (key801, 4)]

def rawRow17027 : Integer.Sparse Key := [(key811, 4), (key803, 4), (key801, 4), (key934, -2), (key931, -2), (key876, -2), (key803, -2), (key871, -2), (key801, -2), (key839, -2), (key836, -2), (key811, -2), (key778, -2), (key801, -2), (key776, -2), (key934, 4), (key811, 4), (key801, 4)]

def rawRow17028 : Integer.Sparse Key := [(key871, 4), (key876, 4), (key876, 4), (key801, -2), (key811, -2), (key801, -2), (key934, -2), (key811, -2), (key934, -2), (key801, -2), (key811, -2), (key801, -2), (key934, -2), (key811, -2), (key934, -2), (key776, 4), (key839, 4), (key839, 4)]

def rawRow17029 : Integer.Sparse Key := [(key876, 4), (key871, 4), (key876, 4), (key811, -2), (key801, -2), (key934, -2), (key801, -2), (key934, -2), (key811, -2), (key811, -2), (key801, -2), (key934, -2), (key801, -2), (key934, -2), (key811, -2), (key839, 4), (key776, 4), (key839, 4)]

def rawRow17030 : Integer.Sparse Key := [(key876, 4), (key876, 4), (key871, 4), (key934, -2), (key934, -2), (key811, -2), (key811, -2), (key801, -2), (key801, -2), (key934, -2), (key934, -2), (key811, -2), (key811, -2), (key801, -2), (key801, -2), (key839, 4), (key839, 4), (key776, 4)]

def rawRow17031 : Integer.Sparse Key := [(key1976, 4), (key2218, 4), (key2224, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, -2), (key2266, -2), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, -2), (key2266, -2), (key1997, 4), (key2262, 4), (key2266, 4)]

def rawRow17032 : Integer.Sparse Key := [(key1976, 4), (key2224, 4), (key2218, 4), (key1983, -2), (key1981, -2), (key2224, -2), (key2218, -2), (key2266, -2), (key2262, -2), (key1983, -2), (key1981, -2), (key2224, -2), (key2218, -2), (key2266, -2), (key2262, -2), (key1997, 4), (key2266, 4), (key2262, 4)]

def rawRow17033 : Integer.Sparse Key := [(key2218, 4), (key1976, 4), (key2224, 4), (key2218, -2), (key2262, -2), (key1981, -2), (key2266, -2), (key1983, -2), (key2224, -2), (key2218, -2), (key2262, -2), (key1981, -2), (key2266, -2), (key1983, -2), (key2224, -2), (key2262, 4), (key1997, 4), (key2266, 4)]

def rawRow17034 : Integer.Sparse Key := [(key2218, 4), (key2224, 4), (key1976, 4), (key2262, -2), (key2218, -2), (key2266, -2), (key1981, -2), (key2224, -2), (key1983, -2), (key2262, -2), (key2218, -2), (key2266, -2), (key1981, -2), (key2224, -2), (key1983, -2), (key2262, 4), (key2266, 4), (key1997, 4)]

def rawRow17035 : Integer.Sparse Key := [(key2224, 4), (key1976, 4), (key2218, 4), (key2224, -2), (key2266, -2), (key1983, -2), (key2262, -2), (key1981, -2), (key2218, -2), (key2224, -2), (key2266, -2), (key1983, -2), (key2262, -2), (key1981, -2), (key2218, -2), (key2266, 4), (key1997, 4), (key2262, 4)]

def rawRow17036 : Integer.Sparse Key := [(key2224, 4), (key2218, 4), (key1976, 4), (key2266, -2), (key2224, -2), (key2262, -2), (key1983, -2), (key2218, -2), (key1981, -2), (key2266, -2), (key2224, -2), (key2262, -2), (key1983, -2), (key2218, -2), (key1981, -2), (key2266, 4), (key2262, 4), (key1997, 4)]

def rawRow17037 : Integer.Sparse Key := [(key1981, 4), (key1981, 4), (key2266, 4), (key1976, -2), (key1983, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key2224, -2), (key1981, -2), (key1997, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key2266, -2), (key1983, 4), (key1983, 4), (key2224, 4)]

def rawRow17038 : Integer.Sparse Key := [(key1981, 4), (key2266, 4), (key1981, 4), (key1983, -2), (key1976, -2), (key2224, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key1997, -2), (key1981, -2), (key2266, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key1983, 4), (key2224, 4), (key1983, 4)]

def rawRow17039 : Integer.Sparse Key := [(key2266, 4), (key1981, 4), (key1981, 4), (key2224, -2), (key2224, -2), (key1983, -2), (key1983, -2), (key1976, -2), (key1976, -2), (key2266, -2), (key2266, -2), (key1997, -2), (key1997, -2), (key1981, -2), (key1981, -2), (key2224, 4), (key1983, 4), (key1983, 4)]

def rawRow17040 : Integer.Sparse Key := [(key1983, 4), (key1983, 4), (key2262, 4), (key1976, -2), (key1981, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key2218, -2), (key1983, -2), (key1997, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key2262, -2), (key1981, 4), (key1981, 4), (key2218, 4)]

def rawRow17041 : Integer.Sparse Key := [(key1983, 4), (key2262, 4), (key1983, 4), (key1981, -2), (key1976, -2), (key2218, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key1997, -2), (key1983, -2), (key2262, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key1981, 4), (key2218, 4), (key1981, 4)]

def rawRow17042 : Integer.Sparse Key := [(key2262, 4), (key1983, 4), (key1983, 4), (key2218, -2), (key2218, -2), (key1981, -2), (key1981, -2), (key1976, -2), (key1976, -2), (key2262, -2), (key2262, -2), (key1997, -2), (key1997, -2), (key1983, -2), (key1983, -2), (key2218, 4), (key1981, 4), (key1981, 4)]

def rawRow17043 : Integer.Sparse Key := [(key1981, 4), (key1981, 4), (key2266, 4), (key1981, -2), (key1997, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key2266, -2), (key1976, -2), (key1983, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key2224, -2), (key1983, 4), (key1983, 4), (key2224, 4)]

def rawRow17044 : Integer.Sparse Key := [(key1981, 4), (key2266, 4), (key1981, 4), (key1997, -2), (key1981, -2), (key2266, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key1983, -2), (key1976, -2), (key2224, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key1983, 4), (key2224, 4), (key1983, 4)]

def rawRow17045 : Integer.Sparse Key := [(key2266, 4), (key1981, 4), (key1981, 4), (key2266, -2), (key2266, -2), (key1997, -2), (key1997, -2), (key1981, -2), (key1981, -2), (key2224, -2), (key2224, -2), (key1983, -2), (key1983, -2), (key1976, -2), (key1976, -2), (key2224, 4), (key1983, 4), (key1983, 4)]

def rawRow17046 : Integer.Sparse Key := [(key1997, 4), (key1997, 4), (key1997, 4), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1976, 4), (key1976, 4), (key1976, 4)]

def rawRow17047 : Integer.Sparse Key := [(key1983, 4), (key1983, 4), (key2262, 4), (key1983, -2), (key1997, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key2262, -2), (key1976, -2), (key1981, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key2218, -2), (key1981, 4), (key1981, 4), (key2218, 4)]

def rawRow17048 : Integer.Sparse Key := [(key1983, 4), (key2262, 4), (key1983, 4), (key1997, -2), (key1983, -2), (key2262, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key1981, -2), (key1976, -2), (key2218, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key1981, 4), (key2218, 4), (key1981, 4)]

def rawRow17049 : Integer.Sparse Key := [(key2262, 4), (key1983, 4), (key1983, 4), (key2262, -2), (key2262, -2), (key1997, -2), (key1997, -2), (key1983, -2), (key1983, -2), (key2218, -2), (key2218, -2), (key1981, -2), (key1981, -2), (key1976, -2), (key1976, -2), (key2218, 4), (key1981, 4), (key1981, 4)]

def rawRow17050 : Integer.Sparse Key := [(key1997, 4), (key1997, 4), (key1997, 4), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1976, 4), (key1976, 4), (key1976, 4)]

def rawRow17051 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, -2), (key63, 6), (key693, -2), (key697, -2), (key701, -2), (key693, 2), (key697, 2), (key845, 2), (key848, 2), (key854, 2), (key855, 2), (key701, -2), (key854, -2), (key855, -2), (key701, 6), (key701, -2), (key854, -2), (key855, -2)]

def rawRow17052 : Integer.Sparse Key := [(key56, -2), (key54, -2), (key63, -2), (key63, 6), (key697, -2), (key693, -2), (key701, -2), (key697, 2), (key693, 2), (key848, 2), (key845, 2), (key855, 2), (key854, 2), (key701, -2), (key855, -2), (key854, -2), (key701, 6), (key701, -2), (key855, -2), (key854, -2)]

def rawRow17053 : Integer.Sparse Key := [(key54, -2), (key63, -2), (key56, -2), (key63, 6), (key693, -2), (key701, -2), (key697, -2), (key845, 2), (key854, 2), (key693, 2), (key855, 2), (key697, 2), (key848, 2), (key854, -2), (key701, -2), (key855, -2), (key701, 6), (key854, -2), (key701, -2), (key855, -2)]

def rawRow17054 : Integer.Sparse Key := [(key63, -2), (key54, -2), (key56, -2), (key63, 6), (key701, -2), (key693, -2), (key697, -2), (key854, 2), (key845, 2), (key855, 2), (key693, 2), (key848, 2), (key697, 2), (key854, -2), (key855, -2), (key701, -2), (key701, 6), (key854, -2), (key855, -2), (key701, -2)]

def rawRow17055 : Integer.Sparse Key := [(key56, -2), (key63, -2), (key54, -2), (key63, 6), (key697, -2), (key701, -2), (key693, -2), (key848, 2), (key855, 2), (key697, 2), (key854, 2), (key693, 2), (key845, 2), (key855, -2), (key701, -2), (key854, -2), (key701, 6), (key855, -2), (key701, -2), (key854, -2)]

def rawRow17056 : Integer.Sparse Key := [(key63, -2), (key56, -2), (key54, -2), (key63, 6), (key701, -2), (key697, -2), (key693, -2), (key855, 2), (key848, 2), (key854, 2), (key697, 2), (key845, 2), (key693, 2), (key855, -2), (key854, -2), (key701, -2), (key701, 6), (key855, -2), (key854, -2), (key701, -2)]

def rawRow17057 : Integer.Sparse Key := [(key54, -2), (key63, -2), (key63, -2), (key56, 6), (key845, -2), (key854, -2), (key854, -2), (key693, 2), (key701, 2), (key693, 2), (key855, 2), (key701, 2), (key855, 2), (key697, -2), (key697, -2), (key848, -2), (key854, 6), (key701, -2), (key701, -2), (key855, -2)]

def rawRow17058 : Integer.Sparse Key := [(key63, -2), (key54, -2), (key63, -2), (key56, 6), (key854, -2), (key845, -2), (key854, -2), (key701, 2), (key693, 2), (key855, 2), (key693, 2), (key855, 2), (key701, 2), (key697, -2), (key848, -2), (key697, -2), (key854, 6), (key701, -2), (key855, -2), (key701, -2)]

def rawRow17059 : Integer.Sparse Key := [(key63, -2), (key63, -2), (key54, -2), (key56, 6), (key854, -2), (key854, -2), (key845, -2), (key855, 2), (key855, 2), (key701, 2), (key701, 2), (key693, 2), (key693, 2), (key848, -2), (key697, -2), (key697, -2), (key854, 6), (key855, -2), (key701, -2), (key701, -2)]

def rawRow17060 : Integer.Sparse Key := [(key56, -2), (key63, -2), (key63, -2), (key54, 6), (key848, -2), (key855, -2), (key855, -2), (key697, 2), (key701, 2), (key697, 2), (key854, 2), (key701, 2), (key854, 2), (key693, -2), (key693, -2), (key845, -2), (key855, 6), (key701, -2), (key701, -2), (key854, -2)]

def rawRow17061 : Integer.Sparse Key := [(key63, -2), (key56, -2), (key63, -2), (key54, 6), (key855, -2), (key848, -2), (key855, -2), (key701, 2), (key697, 2), (key854, 2), (key697, 2), (key854, 2), (key701, 2), (key693, -2), (key845, -2), (key693, -2), (key855, 6), (key701, -2), (key854, -2), (key701, -2)]

def rawRow17062 : Integer.Sparse Key := [(key63, -2), (key63, -2), (key56, -2), (key54, 6), (key855, -2), (key855, -2), (key848, -2), (key854, 2), (key854, 2), (key701, 2), (key701, 2), (key697, 2), (key697, 2), (key845, -2), (key693, -2), (key693, -2), (key855, 6), (key854, -2), (key701, -2), (key701, -2)]

def rawRow17063 : Integer.Sparse Key := [(key122, -2), (key128, -2), (key128, -2), (key128, 6), (key54, -2), (key63, -2), (key63, -2), (key693, 2), (key701, 2), (key693, 2), (key855, 2), (key701, 2), (key855, 2), (key701, -2), (key701, -2), (key855, -2), (key697, 6), (key697, -2), (key697, -2), (key848, -2)]

def rawRow17064 : Integer.Sparse Key := [(key128, -2), (key122, -2), (key128, -2), (key128, 6), (key63, -2), (key54, -2), (key63, -2), (key701, 2), (key693, 2), (key855, 2), (key693, 2), (key855, 2), (key701, 2), (key701, -2), (key855, -2), (key701, -2), (key697, 6), (key697, -2), (key848, -2), (key697, -2)]

def rawRow17065 : Integer.Sparse Key := [(key128, -2), (key128, -2), (key122, -2), (key128, 6), (key63, -2), (key63, -2), (key54, -2), (key855, 2), (key855, 2), (key701, 2), (key701, 2), (key693, 2), (key693, 2), (key855, -2), (key701, -2), (key701, -2), (key697, 6), (key848, -2), (key697, -2), (key697, -2)]

def rawRow17066 : Integer.Sparse Key := [(key128, -2), (key128, -2), (key128, -2), (key122, 6), (key199, -2), (key199, -2), (key199, -2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key54, -2), (key693, -2), (key693, -2), (key848, 6), (key697, -2), (key697, -2), (key697, -2)]

def rawRow17067 : Integer.Sparse Key := [(key198, -2), (key199, -2), (key199, -2), (key199, 6), (key56, -2), (key63, -2), (key63, -2), (key56, 2), (key63, 2), (key56, 2), (key128, 2), (key63, 2), (key128, 2), (key63, -2), (key63, -2), (key128, -2), (key54, 6), (key693, -2), (key693, -2), (key845, -2)]

def rawRow17068 : Integer.Sparse Key := [(key199, -2), (key198, -2), (key199, -2), (key199, 6), (key63, -2), (key56, -2), (key63, -2), (key63, 2), (key56, 2), (key128, 2), (key56, 2), (key128, 2), (key63, 2), (key63, -2), (key128, -2), (key63, -2), (key54, 6), (key693, -2), (key845, -2), (key693, -2)]

def rawRow17069 : Integer.Sparse Key := [(key199, -2), (key199, -2), (key198, -2), (key199, 6), (key63, -2), (key63, -2), (key56, -2), (key128, 2), (key128, 2), (key63, 2), (key63, 2), (key56, 2), (key56, 2), (key128, -2), (key63, -2), (key63, -2), (key54, 6), (key845, -2), (key693, -2), (key693, -2)]

def rawRow17070 : Integer.Sparse Key := [(key199, -2), (key199, -2), (key199, -2), (key198, 6), (key128, -2), (key128, -2), (key128, -2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key56, -2), (key56, -2), (key56, -2), (key122, 6), (key54, -2), (key693, -2), (key693, -2)]

def rawRow17071 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, -2), (key1985, 6), (key1973, -2), (key1978, -2), (key1985, -2), (key1973, 2), (key1978, 2), (key2209, 2), (key2215, 2), (key2226, 2), (key2230, 2), (key1985, -2), (key2226, -2), (key2230, -2), (key1985, 6), (key1985, -2), (key2226, -2), (key2230, -2)]

def rawRow17072 : Integer.Sparse Key := [(key1978, -2), (key1973, -2), (key1985, -2), (key1985, 6), (key1978, -2), (key1973, -2), (key1985, -2), (key1978, 2), (key1973, 2), (key2215, 2), (key2209, 2), (key2230, 2), (key2226, 2), (key1985, -2), (key2230, -2), (key2226, -2), (key1985, 6), (key1985, -2), (key2230, -2), (key2226, -2)]

def rawRow17073 : Integer.Sparse Key := [(key1973, -2), (key1985, -2), (key1978, -2), (key1985, 6), (key1973, -2), (key1985, -2), (key1978, -2), (key2209, 2), (key2226, 2), (key1973, 2), (key2230, 2), (key1978, 2), (key2215, 2), (key2226, -2), (key1985, -2), (key2230, -2), (key1985, 6), (key2226, -2), (key1985, -2), (key2230, -2)]

def rawRow17074 : Integer.Sparse Key := [(key1985, -2), (key1973, -2), (key1978, -2), (key1985, 6), (key1985, -2), (key1973, -2), (key1978, -2), (key2226, 2), (key2209, 2), (key2230, 2), (key1973, 2), (key2215, 2), (key1978, 2), (key2226, -2), (key2230, -2), (key1985, -2), (key1985, 6), (key2226, -2), (key2230, -2), (key1985, -2)]

def rawRow17075 : Integer.Sparse Key := [(key1978, -2), (key1985, -2), (key1973, -2), (key1985, 6), (key1978, -2), (key1985, -2), (key1973, -2), (key2215, 2), (key2230, 2), (key1978, 2), (key2226, 2), (key1973, 2), (key2209, 2), (key2230, -2), (key1985, -2), (key2226, -2), (key1985, 6), (key2230, -2), (key1985, -2), (key2226, -2)]

def rawRow17076 : Integer.Sparse Key := [(key1985, -2), (key1978, -2), (key1973, -2), (key1985, 6), (key1985, -2), (key1978, -2), (key1973, -2), (key2230, 2), (key2215, 2), (key2226, 2), (key1978, 2), (key2209, 2), (key1973, 2), (key2230, -2), (key2226, -2), (key1985, -2), (key1985, 6), (key2230, -2), (key2226, -2), (key1985, -2)]

def rawRow17077 : Integer.Sparse Key := [(key1973, -2), (key1985, -2), (key1985, -2), (key1978, 6), (key2209, -2), (key2226, -2), (key2226, -2), (key1973, 2), (key1985, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key2230, 2), (key1978, -2), (key1978, -2), (key2215, -2), (key2226, 6), (key1985, -2), (key1985, -2), (key2230, -2)]

def rawRow17078 : Integer.Sparse Key := [(key1985, -2), (key1973, -2), (key1985, -2), (key1978, 6), (key2226, -2), (key2209, -2), (key2226, -2), (key1985, 2), (key1973, 2), (key2230, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key1978, -2), (key2215, -2), (key1978, -2), (key2226, 6), (key1985, -2), (key2230, -2), (key1985, -2)]

def rawRow17079 : Integer.Sparse Key := [(key1985, -2), (key1985, -2), (key1973, -2), (key1978, 6), (key2226, -2), (key2226, -2), (key2209, -2), (key2230, 2), (key2230, 2), (key1985, 2), (key1985, 2), (key1973, 2), (key1973, 2), (key2215, -2), (key1978, -2), (key1978, -2), (key2226, 6), (key2230, -2), (key1985, -2), (key1985, -2)]

def rawRow17080 : Integer.Sparse Key := [(key1978, -2), (key1985, -2), (key1985, -2), (key1973, 6), (key2215, -2), (key2230, -2), (key2230, -2), (key1978, 2), (key1985, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key2226, 2), (key1973, -2), (key1973, -2), (key2209, -2), (key2230, 6), (key1985, -2), (key1985, -2), (key2226, -2)]

def rawRow17081 : Integer.Sparse Key := [(key1985, -2), (key1978, -2), (key1985, -2), (key1973, 6), (key2230, -2), (key2215, -2), (key2230, -2), (key1985, 2), (key1978, 2), (key2226, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key1973, -2), (key2209, -2), (key1973, -2), (key2230, 6), (key1985, -2), (key2226, -2), (key1985, -2)]

def rawRow17082 : Integer.Sparse Key := [(key1985, -2), (key1985, -2), (key1978, -2), (key1973, 6), (key2230, -2), (key2230, -2), (key2215, -2), (key2226, 2), (key2226, 2), (key1985, 2), (key1985, 2), (key1978, 2), (key1978, 2), (key2209, -2), (key1973, -2), (key1973, -2), (key2230, 6), (key2226, -2), (key1985, -2), (key1985, -2)]

def rawRow17083 : Integer.Sparse Key := [(key2209, -2), (key2226, -2), (key2226, -2), (key2226, 6), (key1973, -2), (key1985, -2), (key1985, -2), (key1973, 2), (key1985, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key2230, 2), (key1985, -2), (key1985, -2), (key2230, -2), (key1978, 6), (key1978, -2), (key1978, -2), (key2215, -2)]

def rawRow17084 : Integer.Sparse Key := [(key2226, -2), (key2209, -2), (key2226, -2), (key2226, 6), (key1985, -2), (key1973, -2), (key1985, -2), (key1985, 2), (key1973, 2), (key2230, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key1985, -2), (key2230, -2), (key1985, -2), (key1978, 6), (key1978, -2), (key2215, -2), (key1978, -2)]

def rawRow17085 : Integer.Sparse Key := [(key2226, -2), (key2226, -2), (key2209, -2), (key2226, 6), (key1985, -2), (key1985, -2), (key1973, -2), (key2230, 2), (key2230, 2), (key1985, 2), (key1985, 2), (key1973, 2), (key1973, 2), (key2230, -2), (key1985, -2), (key1985, -2), (key1978, 6), (key2215, -2), (key1978, -2), (key1978, -2)]

def rawRow17086 : Integer.Sparse Key := [(key2226, -2), (key2226, -2), (key2226, -2), (key2209, 6), (key2230, -2), (key2230, -2), (key2230, -2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1973, -2), (key1973, -2), (key1973, -2), (key2215, 6), (key1978, -2), (key1978, -2), (key1978, -2)]

def rawRow17087 : Integer.Sparse Key := [(key2215, -2), (key2230, -2), (key2230, -2), (key2230, 6), (key1978, -2), (key1985, -2), (key1985, -2), (key1978, 2), (key1985, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key2226, 2), (key1985, -2), (key1985, -2), (key2226, -2), (key1973, 6), (key1973, -2), (key1973, -2), (key2209, -2)]

def rawRow17088 : Integer.Sparse Key := [(key2230, -2), (key2215, -2), (key2230, -2), (key2230, 6), (key1985, -2), (key1978, -2), (key1985, -2), (key1985, 2), (key1978, 2), (key2226, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key1985, -2), (key2226, -2), (key1985, -2), (key1973, 6), (key1973, -2), (key2209, -2), (key1973, -2)]

def rawRow17089 : Integer.Sparse Key := [(key2230, -2), (key2230, -2), (key2215, -2), (key2230, 6), (key1985, -2), (key1985, -2), (key1978, -2), (key2226, 2), (key2226, 2), (key1985, 2), (key1985, 2), (key1978, 2), (key1978, 2), (key2226, -2), (key1985, -2), (key1985, -2), (key1973, 6), (key2209, -2), (key1973, -2), (key1973, -2)]

def rawRow17090 : Integer.Sparse Key := [(key2230, -2), (key2230, -2), (key2230, -2), (key2215, 6), (key2226, -2), (key2226, -2), (key2226, -2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1978, -2), (key1978, -2), (key1978, -2), (key2209, 6), (key1973, -2), (key1973, -2), (key1973, -2)]

def rawRow17091 : Integer.Sparse Key := [(key2015, 6), (key2015, -2), (key2044, -2), (key2045, -2), (key2015, 6), (key2015, -2), (key2129, -2), (key2132, -2), (key2015, -2), (key2044, -2), (key2045, -2), (key2015, -2), (key2129, -2), (key2132, -2), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, 2), (key2213, 2)]

def rawRow17092 : Integer.Sparse Key := [(key2015, 6), (key2015, -2), (key2045, -2), (key2044, -2), (key2015, 6), (key2015, -2), (key2132, -2), (key2129, -2), (key2015, -2), (key2045, -2), (key2044, -2), (key2015, -2), (key2132, -2), (key2129, -2), (key2045, 2), (key2044, 2), (key2132, 2), (key2129, 2), (key2213, 2), (key2212, 2)]

def rawRow17093 : Integer.Sparse Key := [(key2015, 6), (key2044, -2), (key2015, -2), (key2045, -2), (key2015, 6), (key2129, -2), (key2015, -2), (key2132, -2), (key2044, -2), (key2015, -2), (key2045, -2), (key2129, -2), (key2015, -2), (key2132, -2), (key2129, 2), (key2212, 2), (key2044, 2), (key2213, 2), (key2045, 2), (key2132, 2)]

def rawRow17094 : Integer.Sparse Key := [(key2015, 6), (key2044, -2), (key2045, -2), (key2015, -2), (key2015, 6), (key2129, -2), (key2132, -2), (key2015, -2), (key2044, -2), (key2045, -2), (key2015, -2), (key2129, -2), (key2132, -2), (key2015, -2), (key2212, 2), (key2129, 2), (key2213, 2), (key2044, 2), (key2132, 2), (key2045, 2)]

def rawRow17095 : Integer.Sparse Key := [(key2015, 6), (key2045, -2), (key2015, -2), (key2044, -2), (key2015, 6), (key2132, -2), (key2015, -2), (key2129, -2), (key2045, -2), (key2015, -2), (key2044, -2), (key2132, -2), (key2015, -2), (key2129, -2), (key2132, 2), (key2213, 2), (key2045, 2), (key2212, 2), (key2044, 2), (key2129, 2)]

def rawRow17096 : Integer.Sparse Key := [(key2015, 6), (key2045, -2), (key2044, -2), (key2015, -2), (key2015, 6), (key2132, -2), (key2129, -2), (key2015, -2), (key2045, -2), (key2044, -2), (key2015, -2), (key2132, -2), (key2129, -2), (key2015, -2), (key2213, 2), (key2132, 2), (key2212, 2), (key2045, 2), (key2129, 2), (key2044, 2)]

def rawRow17097 : Integer.Sparse Key := [(key2044, 6), (key2015, -2), (key2015, -2), (key2045, -2), (key2129, 6), (key2015, -2), (key2015, -2), (key2132, -2), (key2129, -2), (key2129, -2), (key2212, -2), (key2044, -2), (key2044, -2), (key2213, -2), (key2015, 2), (key2045, 2), (key2015, 2), (key2132, 2), (key2045, 2), (key2132, 2)]

def rawRow17098 : Integer.Sparse Key := [(key2044, 6), (key2015, -2), (key2045, -2), (key2015, -2), (key2129, 6), (key2015, -2), (key2132, -2), (key2015, -2), (key2129, -2), (key2212, -2), (key2129, -2), (key2044, -2), (key2213, -2), (key2044, -2), (key2045, 2), (key2015, 2), (key2132, 2), (key2015, 2), (key2132, 2), (key2045, 2)]

def rawRow17099 : Integer.Sparse Key := [(key2044, 6), (key2045, -2), (key2015, -2), (key2015, -2), (key2129, 6), (key2132, -2), (key2015, -2), (key2015, -2), (key2212, -2), (key2129, -2), (key2129, -2), (key2213, -2), (key2044, -2), (key2044, -2), (key2132, 2), (key2132, 2), (key2045, 2), (key2045, 2), (key2015, 2), (key2015, 2)]

def rawRow17100 : Integer.Sparse Key := [(key2045, 6), (key2015, -2), (key2015, -2), (key2044, -2), (key2132, 6), (key2015, -2), (key2015, -2), (key2129, -2), (key2132, -2), (key2132, -2), (key2213, -2), (key2045, -2), (key2045, -2), (key2212, -2), (key2015, 2), (key2044, 2), (key2015, 2), (key2129, 2), (key2044, 2), (key2129, 2)]

def rawRow17101 : Integer.Sparse Key := [(key2045, 6), (key2015, -2), (key2044, -2), (key2015, -2), (key2132, 6), (key2015, -2), (key2129, -2), (key2015, -2), (key2132, -2), (key2213, -2), (key2132, -2), (key2045, -2), (key2212, -2), (key2045, -2), (key2044, 2), (key2015, 2), (key2129, 2), (key2015, 2), (key2129, 2), (key2044, 2)]

def rawRow17102 : Integer.Sparse Key := [(key2045, 6), (key2044, -2), (key2015, -2), (key2015, -2), (key2132, 6), (key2129, -2), (key2015, -2), (key2015, -2), (key2213, -2), (key2132, -2), (key2132, -2), (key2212, -2), (key2045, -2), (key2045, -2), (key2129, 2), (key2129, 2), (key2044, 2), (key2044, 2), (key2015, 2), (key2015, 2)]

def rawRow17103 : Integer.Sparse Key := [(key2129, 6), (key2129, -2), (key2129, -2), (key2212, -2), (key2044, 6), (key2044, -2), (key2044, -2), (key2213, -2), (key2015, -2), (key2015, -2), (key2045, -2), (key2015, -2), (key2015, -2), (key2132, -2), (key2015, 2), (key2045, 2), (key2015, 2), (key2132, 2), (key2045, 2), (key2132, 2)]

def rawRow17104 : Integer.Sparse Key := [(key2129, 6), (key2129, -2), (key2212, -2), (key2129, -2), (key2044, 6), (key2044, -2), (key2213, -2), (key2044, -2), (key2015, -2), (key2045, -2), (key2015, -2), (key2015, -2), (key2132, -2), (key2015, -2), (key2045, 2), (key2015, 2), (key2132, 2), (key2015, 2), (key2132, 2), (key2045, 2)]

def rawRow17105 : Integer.Sparse Key := [(key2129, 6), (key2212, -2), (key2129, -2), (key2129, -2), (key2044, 6), (key2213, -2), (key2044, -2), (key2044, -2), (key2045, -2), (key2015, -2), (key2015, -2), (key2132, -2), (key2015, -2), (key2015, -2), (key2132, 2), (key2132, 2), (key2045, 2), (key2045, 2), (key2015, 2), (key2015, 2)]

def rawRow17106 : Integer.Sparse Key := [(key2212, 6), (key2129, -2), (key2129, -2), (key2129, -2), (key2213, 6), (key2044, -2), (key2044, -2), (key2044, -2), (key2132, -2), (key2132, -2), (key2132, -2), (key2045, -2), (key2045, -2), (key2045, -2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2)]

def rawRow17107 : Integer.Sparse Key := [(key2132, 6), (key2132, -2), (key2132, -2), (key2213, -2), (key2045, 6), (key2045, -2), (key2045, -2), (key2212, -2), (key2015, -2), (key2015, -2), (key2044, -2), (key2015, -2), (key2015, -2), (key2129, -2), (key2015, 2), (key2044, 2), (key2015, 2), (key2129, 2), (key2044, 2), (key2129, 2)]

def rawRow17108 : Integer.Sparse Key := [(key2132, 6), (key2132, -2), (key2213, -2), (key2132, -2), (key2045, 6), (key2045, -2), (key2212, -2), (key2045, -2), (key2015, -2), (key2044, -2), (key2015, -2), (key2015, -2), (key2129, -2), (key2015, -2), (key2044, 2), (key2015, 2), (key2129, 2), (key2015, 2), (key2129, 2), (key2044, 2)]

def rawRow17109 : Integer.Sparse Key := [(key2132, 6), (key2213, -2), (key2132, -2), (key2132, -2), (key2045, 6), (key2212, -2), (key2045, -2), (key2045, -2), (key2044, -2), (key2015, -2), (key2015, -2), (key2129, -2), (key2015, -2), (key2015, -2), (key2129, 2), (key2129, 2), (key2044, 2), (key2044, 2), (key2015, 2), (key2015, 2)]

def rawRow17110 : Integer.Sparse Key := [(key2213, 6), (key2132, -2), (key2132, -2), (key2132, -2), (key2212, 6), (key2045, -2), (key2045, -2), (key2045, -2), (key2129, -2), (key2129, -2), (key2129, -2), (key2044, -2), (key2044, -2), (key2044, -2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2)]

def rawRow17111 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, -2), (key699, 6), (key694, -2), (key696, -2), (key699, -2), (key694, 2), (key696, 2), (key846, 2), (key847, 2), (key850, 2), (key852, 2), (key699, -2), (key850, -2), (key852, -2), (key699, 6), (key699, -2), (key850, -2), (key852, -2)]

def rawRow17112 : Integer.Sparse Key := [(key696, -2), (key694, -2), (key699, -2), (key699, 6), (key696, -2), (key694, -2), (key699, -2), (key696, 2), (key694, 2), (key847, 2), (key846, 2), (key852, 2), (key850, 2), (key699, -2), (key852, -2), (key850, -2), (key699, 6), (key699, -2), (key852, -2), (key850, -2)]

def rawRow17113 : Integer.Sparse Key := [(key694, -2), (key699, -2), (key696, -2), (key699, 6), (key694, -2), (key699, -2), (key696, -2), (key846, 2), (key850, 2), (key694, 2), (key852, 2), (key696, 2), (key847, 2), (key850, -2), (key699, -2), (key852, -2), (key699, 6), (key850, -2), (key699, -2), (key852, -2)]

def rawRow17114 : Integer.Sparse Key := [(key699, -2), (key694, -2), (key696, -2), (key699, 6), (key699, -2), (key694, -2), (key696, -2), (key850, 2), (key846, 2), (key852, 2), (key694, 2), (key847, 2), (key696, 2), (key850, -2), (key852, -2), (key699, -2), (key699, 6), (key850, -2), (key852, -2), (key699, -2)]

def rawRow17115 : Integer.Sparse Key := [(key696, -2), (key699, -2), (key694, -2), (key699, 6), (key696, -2), (key699, -2), (key694, -2), (key847, 2), (key852, 2), (key696, 2), (key850, 2), (key694, 2), (key846, 2), (key852, -2), (key699, -2), (key850, -2), (key699, 6), (key852, -2), (key699, -2), (key850, -2)]

def rawRow17116 : Integer.Sparse Key := [(key699, -2), (key696, -2), (key694, -2), (key699, 6), (key699, -2), (key696, -2), (key694, -2), (key852, 2), (key847, 2), (key850, 2), (key696, 2), (key846, 2), (key694, 2), (key852, -2), (key850, -2), (key699, -2), (key699, 6), (key852, -2), (key850, -2), (key699, -2)]

def rawRow17117 : Integer.Sparse Key := [(key694, -2), (key699, -2), (key699, -2), (key696, 6), (key846, -2), (key850, -2), (key850, -2), (key694, 2), (key699, 2), (key694, 2), (key852, 2), (key699, 2), (key852, 2), (key696, -2), (key696, -2), (key847, -2), (key850, 6), (key699, -2), (key699, -2), (key852, -2)]

def rawRow17118 : Integer.Sparse Key := [(key699, -2), (key694, -2), (key699, -2), (key696, 6), (key850, -2), (key846, -2), (key850, -2), (key699, 2), (key694, 2), (key852, 2), (key694, 2), (key852, 2), (key699, 2), (key696, -2), (key847, -2), (key696, -2), (key850, 6), (key699, -2), (key852, -2), (key699, -2)]

def rawRow17119 : Integer.Sparse Key := [(key699, -2), (key699, -2), (key694, -2), (key696, 6), (key850, -2), (key850, -2), (key846, -2), (key852, 2), (key852, 2), (key699, 2), (key699, 2), (key694, 2), (key694, 2), (key847, -2), (key696, -2), (key696, -2), (key850, 6), (key852, -2), (key699, -2), (key699, -2)]

def rawRow17120 : Integer.Sparse Key := [(key696, -2), (key699, -2), (key699, -2), (key694, 6), (key847, -2), (key852, -2), (key852, -2), (key696, 2), (key699, 2), (key696, 2), (key850, 2), (key699, 2), (key850, 2), (key694, -2), (key694, -2), (key846, -2), (key852, 6), (key699, -2), (key699, -2), (key850, -2)]

def rawRow17121 : Integer.Sparse Key := [(key699, -2), (key696, -2), (key699, -2), (key694, 6), (key852, -2), (key847, -2), (key852, -2), (key699, 2), (key696, 2), (key850, 2), (key696, 2), (key850, 2), (key699, 2), (key694, -2), (key846, -2), (key694, -2), (key852, 6), (key699, -2), (key850, -2), (key699, -2)]

def rawRow17122 : Integer.Sparse Key := [(key699, -2), (key699, -2), (key696, -2), (key694, 6), (key852, -2), (key852, -2), (key847, -2), (key850, 2), (key850, 2), (key699, 2), (key699, 2), (key696, 2), (key696, 2), (key846, -2), (key694, -2), (key694, -2), (key852, 6), (key850, -2), (key699, -2), (key699, -2)]

def rawRow17123 : Integer.Sparse Key := [(key846, -2), (key850, -2), (key850, -2), (key850, 6), (key694, -2), (key699, -2), (key699, -2), (key694, 2), (key699, 2), (key694, 2), (key852, 2), (key699, 2), (key852, 2), (key699, -2), (key699, -2), (key852, -2), (key696, 6), (key696, -2), (key696, -2), (key847, -2)]

def rawRow17124 : Integer.Sparse Key := [(key850, -2), (key846, -2), (key850, -2), (key850, 6), (key699, -2), (key694, -2), (key699, -2), (key699, 2), (key694, 2), (key852, 2), (key694, 2), (key852, 2), (key699, 2), (key699, -2), (key852, -2), (key699, -2), (key696, 6), (key696, -2), (key847, -2), (key696, -2)]

def rawRow17125 : Integer.Sparse Key := [(key850, -2), (key850, -2), (key846, -2), (key850, 6), (key699, -2), (key699, -2), (key694, -2), (key852, 2), (key852, 2), (key699, 2), (key699, 2), (key694, 2), (key694, 2), (key852, -2), (key699, -2), (key699, -2), (key696, 6), (key847, -2), (key696, -2), (key696, -2)]

def rawRow17126 : Integer.Sparse Key := [(key850, -2), (key850, -2), (key850, -2), (key846, 6), (key852, -2), (key852, -2), (key852, -2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key694, -2), (key694, -2), (key694, -2), (key847, 6), (key696, -2), (key696, -2), (key696, -2)]

def rawRow17127 : Integer.Sparse Key := [(key847, -2), (key852, -2), (key852, -2), (key852, 6), (key696, -2), (key699, -2), (key699, -2), (key696, 2), (key699, 2), (key696, 2), (key850, 2), (key699, 2), (key850, 2), (key699, -2), (key699, -2), (key850, -2), (key694, 6), (key694, -2), (key694, -2), (key846, -2)]

def rawRow17128 : Integer.Sparse Key := [(key852, -2), (key847, -2), (key852, -2), (key852, 6), (key699, -2), (key696, -2), (key699, -2), (key699, 2), (key696, 2), (key850, 2), (key696, 2), (key850, 2), (key699, 2), (key699, -2), (key850, -2), (key699, -2), (key694, 6), (key694, -2), (key846, -2), (key694, -2)]

def rawRow17129 : Integer.Sparse Key := [(key852, -2), (key852, -2), (key847, -2), (key852, 6), (key699, -2), (key699, -2), (key696, -2), (key850, 2), (key850, 2), (key699, 2), (key699, 2), (key696, 2), (key696, 2), (key850, -2), (key699, -2), (key699, -2), (key694, 6), (key846, -2), (key694, -2), (key694, -2)]

def rawRow17130 : Integer.Sparse Key := [(key852, -2), (key852, -2), (key852, -2), (key847, 6), (key850, -2), (key850, -2), (key850, -2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key696, -2), (key696, -2), (key696, -2), (key846, 6), (key694, -2), (key694, -2), (key694, -2)]

def rawRow17131 : Integer.Sparse Key := [(key695, 4), (key849, 4), (key853, 4), (key698, -2), (key700, -2), (key849, -2), (key853, -2), (key888, -2), (key889, -2), (key698, -2), (key700, -2), (key849, -2), (key853, -2), (key888, -2), (key889, -2), (key712, 4), (key888, 4), (key889, 4)]

def rawRow17132 : Integer.Sparse Key := [(key695, 4), (key853, 4), (key849, 4), (key700, -2), (key698, -2), (key853, -2), (key849, -2), (key889, -2), (key888, -2), (key700, -2), (key698, -2), (key853, -2), (key849, -2), (key889, -2), (key888, -2), (key712, 4), (key889, 4), (key888, 4)]

def rawRow17133 : Integer.Sparse Key := [(key849, 4), (key695, 4), (key853, 4), (key849, -2), (key888, -2), (key698, -2), (key889, -2), (key700, -2), (key853, -2), (key849, -2), (key888, -2), (key698, -2), (key889, -2), (key700, -2), (key853, -2), (key888, 4), (key712, 4), (key889, 4)]

def rawRow17134 : Integer.Sparse Key := [(key849, 4), (key853, 4), (key695, 4), (key888, -2), (key849, -2), (key889, -2), (key698, -2), (key853, -2), (key700, -2), (key888, -2), (key849, -2), (key889, -2), (key698, -2), (key853, -2), (key700, -2), (key888, 4), (key889, 4), (key712, 4)]

def rawRow17135 : Integer.Sparse Key := [(key853, 4), (key695, 4), (key849, 4), (key853, -2), (key889, -2), (key700, -2), (key888, -2), (key698, -2), (key849, -2), (key853, -2), (key889, -2), (key700, -2), (key888, -2), (key698, -2), (key849, -2), (key889, 4), (key712, 4), (key888, 4)]

def rawRow17136 : Integer.Sparse Key := [(key853, 4), (key849, 4), (key695, 4), (key889, -2), (key853, -2), (key888, -2), (key700, -2), (key849, -2), (key698, -2), (key889, -2), (key853, -2), (key888, -2), (key700, -2), (key849, -2), (key698, -2), (key889, 4), (key888, 4), (key712, 4)]

def rawRow17137 : Integer.Sparse Key := [(key698, 4), (key698, 4), (key889, 4), (key695, -2), (key700, -2), (key695, -2), (key853, -2), (key700, -2), (key853, -2), (key698, -2), (key712, -2), (key698, -2), (key889, -2), (key712, -2), (key889, -2), (key700, 4), (key700, 4), (key853, 4)]

def rawRow17138 : Integer.Sparse Key := [(key698, 4), (key889, 4), (key698, 4), (key700, -2), (key695, -2), (key853, -2), (key695, -2), (key853, -2), (key700, -2), (key712, -2), (key698, -2), (key889, -2), (key698, -2), (key889, -2), (key712, -2), (key700, 4), (key853, 4), (key700, 4)]

def rawRow17139 : Integer.Sparse Key := [(key889, 4), (key698, 4), (key698, 4), (key853, -2), (key853, -2), (key700, -2), (key700, -2), (key695, -2), (key695, -2), (key889, -2), (key889, -2), (key712, -2), (key712, -2), (key698, -2), (key698, -2), (key853, 4), (key700, 4), (key700, 4)]

def rawRow17140 : Integer.Sparse Key := [(key700, 4), (key700, 4), (key888, 4), (key695, -2), (key698, -2), (key695, -2), (key849, -2), (key698, -2), (key849, -2), (key700, -2), (key712, -2), (key700, -2), (key888, -2), (key712, -2), (key888, -2), (key698, 4), (key698, 4), (key849, 4)]

def rawRow17141 : Integer.Sparse Key := [(key700, 4), (key888, 4), (key700, 4), (key698, -2), (key695, -2), (key849, -2), (key695, -2), (key849, -2), (key698, -2), (key712, -2), (key700, -2), (key888, -2), (key700, -2), (key888, -2), (key712, -2), (key698, 4), (key849, 4), (key698, 4)]

def rawRow17142 : Integer.Sparse Key := [(key888, 4), (key700, 4), (key700, 4), (key849, -2), (key849, -2), (key698, -2), (key698, -2), (key695, -2), (key695, -2), (key888, -2), (key888, -2), (key712, -2), (key712, -2), (key700, -2), (key700, -2), (key849, 4), (key698, 4), (key698, 4)]

def rawRow17143 : Integer.Sparse Key := [(key698, 4), (key698, 4), (key889, 4), (key698, -2), (key712, -2), (key698, -2), (key889, -2), (key712, -2), (key889, -2), (key695, -2), (key700, -2), (key695, -2), (key853, -2), (key700, -2), (key853, -2), (key700, 4), (key700, 4), (key853, 4)]

def rawRow17144 : Integer.Sparse Key := [(key698, 4), (key889, 4), (key698, 4), (key712, -2), (key698, -2), (key889, -2), (key698, -2), (key889, -2), (key712, -2), (key700, -2), (key695, -2), (key853, -2), (key695, -2), (key853, -2), (key700, -2), (key700, 4), (key853, 4), (key700, 4)]

def rawRow17145 : Integer.Sparse Key := [(key889, 4), (key698, 4), (key698, 4), (key889, -2), (key889, -2), (key712, -2), (key712, -2), (key698, -2), (key698, -2), (key853, -2), (key853, -2), (key700, -2), (key700, -2), (key695, -2), (key695, -2), (key853, 4), (key700, 4), (key700, 4)]

def rawRow17146 : Integer.Sparse Key := [(key82, 4), (key82, 4), (key82, 4), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key700, -2), (key700, -2), (key700, -2), (key700, -2), (key700, -2), (key700, -2), (key695, 4), (key695, 4), (key695, 4)]

def rawRow17147 : Integer.Sparse Key := [(key68, 4), (key68, 4), (key145, 4), (key68, -2), (key82, -2), (key68, -2), (key145, -2), (key82, -2), (key145, -2), (key58, -2), (key65, -2), (key58, -2), (key130, -2), (key65, -2), (key130, -2), (key65, 4), (key65, 4), (key130, 4)]

def rawRow17148 : Integer.Sparse Key := [(key68, 4), (key145, 4), (key68, 4), (key82, -2), (key68, -2), (key145, -2), (key68, -2), (key145, -2), (key82, -2), (key65, -2), (key58, -2), (key130, -2), (key58, -2), (key130, -2), (key65, -2), (key65, 4), (key130, 4), (key65, 4)]

def rawRow17149 : Integer.Sparse Key := [(key145, 4), (key68, 4), (key68, 4), (key145, -2), (key145, -2), (key82, -2), (key82, -2), (key68, -2), (key68, -2), (key130, -2), (key130, -2), (key65, -2), (key65, -2), (key58, -2), (key58, -2), (key130, 4), (key65, 4), (key65, 4)]

def rawRow17150 : Integer.Sparse Key := [(key82, 4), (key82, 4), (key82, 4), (key68, -2), (key68, -2), (key68, -2), (key68, -2), (key68, -2), (key68, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key58, 4), (key58, 4), (key58, 4)]

def rawRow17151 : Integer.Sparse Key := [(key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2026, 2), (key2144, 2), (key2145, 2), (key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2042, 2), (key2047, 2), (key2127, 2), (key2134, 2), (key2228, 2), (key2229, 2), (key2055, -1), (key2056, -1), (key2144, -1), (key2145, -1), (key2228, -1), (key2229, -1), (key2026, 2), (key2144, 2), (key2145, 2), (key2055, -1), (key2056, -1), (key2144, -1), (key2145, -1), (key2228, -1), (key2229, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17152 : Integer.Sparse Key := [(key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2026, 2), (key2145, 2), (key2144, 2), (key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2047, 2), (key2042, 2), (key2134, 2), (key2127, 2), (key2229, 2), (key2228, 2), (key2056, -1), (key2055, -1), (key2145, -1), (key2144, -1), (key2229, -1), (key2228, -1), (key2026, 2), (key2145, 2), (key2144, 2), (key2056, -1), (key2055, -1), (key2145, -1), (key2144, -1), (key2229, -1), (key2228, -1)]

def rawRow17153 : Integer.Sparse Key := [(key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2144, 2), (key2026, 2), (key2145, 2), (key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2127, 2), (key2228, 2), (key2042, 2), (key2229, 2), (key2047, 2), (key2134, 2), (key2144, -1), (key2228, -1), (key2055, -1), (key2229, -1), (key2056, -1), (key2145, -1), (key2144, 2), (key2026, 2), (key2145, 2), (key2144, -1), (key2228, -1), (key2055, -1), (key2229, -1), (key2056, -1), (key2145, -1)]

def rawRow17154 : Integer.Sparse Key := [(key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2144, 2), (key2145, 2), (key2026, 2), (key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2228, 2), (key2127, 2), (key2229, 2), (key2042, 2), (key2134, 2), (key2047, 2), (key2228, -1), (key2144, -1), (key2229, -1), (key2055, -1), (key2145, -1), (key2056, -1), (key2144, 2), (key2145, 2), (key2026, 2), (key2228, -1), (key2144, -1), (key2229, -1), (key2055, -1), (key2145, -1), (key2056, -1)]

def rawRow17155 : Integer.Sparse Key := [(key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2145, 2), (key2026, 2), (key2144, 2), (key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2134, 2), (key2229, 2), (key2047, 2), (key2228, 2), (key2042, 2), (key2127, 2), (key2145, -1), (key2229, -1), (key2056, -1), (key2228, -1), (key2055, -1), (key2144, -1), (key2145, 2), (key2026, 2), (key2144, 2), (key2145, -1), (key2229, -1), (key2056, -1), (key2228, -1), (key2055, -1), (key2144, -1)]

def rawRow17156 : Integer.Sparse Key := [(key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2145, 2), (key2144, 2), (key2026, 2), (key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2229, 2), (key2134, 2), (key2228, 2), (key2047, 2), (key2127, 2), (key2042, 2), (key2229, -1), (key2145, -1), (key2228, -1), (key2056, -1), (key2144, -1), (key2055, -1), (key2145, 2), (key2144, 2), (key2026, 2), (key2229, -1), (key2145, -1), (key2228, -1), (key2056, -1), (key2144, -1), (key2055, -1)]

def rawRow17157 : Integer.Sparse Key := [(key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2019, 2), (key2019, 2), (key2134, 2), (key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2), (key2019, -1), (key2047, -1), (key2019, -1), (key2134, -1), (key2047, -1), (key2134, -1), (key2055, 2), (key2055, 2), (key2229, 2), (key2026, -1), (key2056, -1), (key2026, -1), (key2145, -1), (key2056, -1), (key2145, -1)]

def rawRow17158 : Integer.Sparse Key := [(key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2019, 2), (key2134, 2), (key2019, 2), (key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2047, -1), (key2019, -1), (key2134, -1), (key2019, -1), (key2134, -1), (key2047, -1), (key2055, 2), (key2229, 2), (key2055, 2), (key2056, -1), (key2026, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2056, -1)]

def rawRow17159 : Integer.Sparse Key := [(key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2134, 2), (key2019, 2), (key2019, 2), (key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2), (key2134, -1), (key2134, -1), (key2047, -1), (key2047, -1), (key2019, -1), (key2019, -1), (key2229, 2), (key2055, 2), (key2055, 2), (key2145, -1), (key2145, -1), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1)]

def rawRow17160 : Integer.Sparse Key := [(key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2013, 2), (key2013, 2), (key2127, 2), (key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2), (key2013, -1), (key2042, -1), (key2013, -1), (key2127, -1), (key2042, -1), (key2127, -1), (key2056, 2), (key2056, 2), (key2228, 2), (key2026, -1), (key2055, -1), (key2026, -1), (key2144, -1), (key2055, -1), (key2144, -1)]

def rawRow17161 : Integer.Sparse Key := [(key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2013, 2), (key2127, 2), (key2013, 2), (key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2042, -1), (key2013, -1), (key2127, -1), (key2013, -1), (key2127, -1), (key2042, -1), (key2056, 2), (key2228, 2), (key2056, 2), (key2055, -1), (key2026, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2055, -1)]

def rawRow17162 : Integer.Sparse Key := [(key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2127, 2), (key2013, 2), (key2013, 2), (key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2), (key2127, -1), (key2127, -1), (key2042, -1), (key2042, -1), (key2013, -1), (key2013, -1), (key2228, 2), (key2056, 2), (key2056, 2), (key2144, -1), (key2144, -1), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1)]

def rawRow17163 : Integer.Sparse Key := [(key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2055, 2), (key2055, 2), (key2229, 2), (key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2), (key2026, -1), (key2056, -1), (key2026, -1), (key2145, -1), (key2056, -1), (key2145, -1), (key2019, 2), (key2019, 2), (key2134, 2), (key2019, -1), (key2047, -1), (key2019, -1), (key2134, -1), (key2047, -1), (key2134, -1)]

def rawRow17164 : Integer.Sparse Key := [(key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2055, 2), (key2229, 2), (key2055, 2), (key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2056, -1), (key2026, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2056, -1), (key2019, 2), (key2134, 2), (key2019, 2), (key2047, -1), (key2019, -1), (key2134, -1), (key2019, -1), (key2134, -1), (key2047, -1)]

def rawRow17165 : Integer.Sparse Key := [(key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2229, 2), (key2055, 2), (key2055, 2), (key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2), (key2145, -1), (key2145, -1), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2134, 2), (key2019, 2), (key2019, 2), (key2134, -1), (key2134, -1), (key2047, -1), (key2047, -1), (key2019, -1), (key2019, -1)]

def rawRow17166 : Integer.Sparse Key := [(key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2042, 2), (key2042, 2), (key2042, 2), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2047, 2), (key2047, 2), (key2047, 2), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1)]

def rawRow17167 : Integer.Sparse Key := [(key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2056, 2), (key2056, 2), (key2228, 2), (key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2), (key2026, -1), (key2055, -1), (key2026, -1), (key2144, -1), (key2055, -1), (key2144, -1), (key2013, 2), (key2013, 2), (key2127, 2), (key2013, -1), (key2042, -1), (key2013, -1), (key2127, -1), (key2042, -1), (key2127, -1)]

def rawRow17168 : Integer.Sparse Key := [(key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2056, 2), (key2228, 2), (key2056, 2), (key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2055, -1), (key2026, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2055, -1), (key2013, 2), (key2127, 2), (key2013, 2), (key2042, -1), (key2013, -1), (key2127, -1), (key2013, -1), (key2127, -1), (key2042, -1)]

def rawRow17169 : Integer.Sparse Key := [(key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2228, 2), (key2056, 2), (key2056, 2), (key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2), (key2144, -1), (key2144, -1), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2127, 2), (key2013, 2), (key2013, 2), (key2127, -1), (key2127, -1), (key2042, -1), (key2042, -1), (key2013, -1), (key2013, -1)]

def rawRow17170 : Integer.Sparse Key := [(key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2047, 2), (key2047, 2), (key2047, 2), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2042, 2), (key2042, 2), (key2042, 2), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1)]

def rawRow17171 : Integer.Sparse Key := [(key2103, 4), (key2108, 4), (key2109, 4), (key2108, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2131, 12)]

def rawRow17172 : Integer.Sparse Key := [(key2103, 4), (key2109, 4), (key2108, 4), (key2109, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2131, 12)]

def rawRow17173 : Integer.Sparse Key := [(key2108, 4), (key2103, 4), (key2109, 4), (key2108, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2131, 12)]

def rawRow17174 : Integer.Sparse Key := [(key2108, 4), (key2109, 4), (key2103, 4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, 12)]

def rawRow17175 : Integer.Sparse Key := [(key2109, 4), (key2103, 4), (key2108, 4), (key2109, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2131, 12)]

def rawRow17176 : Integer.Sparse Key := [(key2109, 4), (key2108, 4), (key2103, 4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, 12)]

def rawRow17177 : Integer.Sparse Key := [(key2108, 4), (key2108, 4), (key2131, 4), (key2103, -4), (key2109, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2131, -4), (key2109, 12)]

def rawRow17178 : Integer.Sparse Key := [(key2108, 4), (key2131, 4), (key2108, 4), (key2109, -4), (key2103, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2131, -4), (key2109, 12)]

def rawRow17179 : Integer.Sparse Key := [(key2131, 4), (key2108, 4), (key2108, 4), (key2109, -4), (key2109, -4), (key2103, -4), (key2131, -4), (key2131, -4), (key2108, -4), (key2109, 12)]

def rawRow17180 : Integer.Sparse Key := [(key2109, 4), (key2109, 4), (key2131, 4), (key2103, -4), (key2108, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2131, -4), (key2108, 12)]

def rawRow17181 : Integer.Sparse Key := [(key2109, 4), (key2131, 4), (key2109, 4), (key2108, -4), (key2103, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2131, -4), (key2108, 12)]

def rawRow17182 : Integer.Sparse Key := [(key2131, 4), (key2109, 4), (key2109, 4), (key2108, -4), (key2108, -4), (key2103, -4), (key2131, -4), (key2131, -4), (key2109, -4), (key2108, 12)]

def rawRow17183 : Integer.Sparse Key := [(key2108, 4), (key2108, 4), (key2131, 4), (key2108, -4), (key2131, -4), (key2131, -4), (key2103, -4), (key2109, -4), (key2109, -4), (key2109, 12)]

def rawRow17184 : Integer.Sparse Key := [(key2108, 4), (key2131, 4), (key2108, 4), (key2131, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2103, -4), (key2109, -4), (key2109, 12)]

def rawRow17185 : Integer.Sparse Key := [(key2131, 4), (key2108, 4), (key2108, 4), (key2131, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2109, -4), (key2103, -4), (key2109, 12)]

def rawRow17186 : Integer.Sparse Key := [(key2131, 4), (key2131, 4), (key2131, 4), (key2108, -4), (key2108, -4), (key2108, -4), (key2109, -4), (key2109, -4), (key2109, -4), (key2103, 12)]

def rawRow17187 : Integer.Sparse Key := [(key2109, 4), (key2109, 4), (key2131, 4), (key2109, -4), (key2131, -4), (key2131, -4), (key2103, -4), (key2108, -4), (key2108, -4), (key2108, 12)]

def rawRow17188 : Integer.Sparse Key := [(key2109, 4), (key2131, 4), (key2109, 4), (key2131, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2103, -4), (key2108, -4), (key2108, 12)]

def rawRow17189 : Integer.Sparse Key := [(key2131, 4), (key2109, 4), (key2109, 4), (key2131, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2108, -4), (key2103, -4), (key2108, 12)]

def rawRow17190 : Integer.Sparse Key := [(key2131, 4), (key2131, 4), (key2131, 4), (key2109, -4), (key2109, -4), (key2109, -4), (key2108, -4), (key2108, -4), (key2108, -4), (key2103, 12)]

def rawRow17191 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, -2), (key1982, 6), (key1974, -2), (key1977, -2), (key1982, -2), (key1974, 2), (key1977, 2), (key2210, 2), (key2214, 2), (key2219, 2), (key2223, 2), (key1982, -2), (key2219, -2), (key2223, -2), (key1982, 6), (key1982, -2), (key2219, -2), (key2223, -2)]

def rawRow17192 : Integer.Sparse Key := [(key1977, -2), (key1974, -2), (key1982, -2), (key1982, 6), (key1977, -2), (key1974, -2), (key1982, -2), (key1977, 2), (key1974, 2), (key2214, 2), (key2210, 2), (key2223, 2), (key2219, 2), (key1982, -2), (key2223, -2), (key2219, -2), (key1982, 6), (key1982, -2), (key2223, -2), (key2219, -2)]

def rawRow17193 : Integer.Sparse Key := [(key1974, -2), (key1982, -2), (key1977, -2), (key1982, 6), (key1974, -2), (key1982, -2), (key1977, -2), (key2210, 2), (key2219, 2), (key1974, 2), (key2223, 2), (key1977, 2), (key2214, 2), (key2219, -2), (key1982, -2), (key2223, -2), (key1982, 6), (key2219, -2), (key1982, -2), (key2223, -2)]

def rawRow17194 : Integer.Sparse Key := [(key1982, -2), (key1974, -2), (key1977, -2), (key1982, 6), (key1982, -2), (key1974, -2), (key1977, -2), (key2219, 2), (key2210, 2), (key2223, 2), (key1974, 2), (key2214, 2), (key1977, 2), (key2219, -2), (key2223, -2), (key1982, -2), (key1982, 6), (key2219, -2), (key2223, -2), (key1982, -2)]

def rawRow17195 : Integer.Sparse Key := [(key1977, -2), (key1982, -2), (key1974, -2), (key1982, 6), (key1977, -2), (key1982, -2), (key1974, -2), (key2214, 2), (key2223, 2), (key1977, 2), (key2219, 2), (key1974, 2), (key2210, 2), (key2223, -2), (key1982, -2), (key2219, -2), (key1982, 6), (key2223, -2), (key1982, -2), (key2219, -2)]

def rawRow17196 : Integer.Sparse Key := [(key1982, -2), (key1977, -2), (key1974, -2), (key1982, 6), (key1982, -2), (key1977, -2), (key1974, -2), (key2223, 2), (key2214, 2), (key2219, 2), (key1977, 2), (key2210, 2), (key1974, 2), (key2223, -2), (key2219, -2), (key1982, -2), (key1982, 6), (key2223, -2), (key2219, -2), (key1982, -2)]

def rawRow17197 : Integer.Sparse Key := [(key1974, -2), (key1982, -2), (key1982, -2), (key1977, 6), (key2210, -2), (key2219, -2), (key2219, -2), (key1974, 2), (key1982, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key2223, 2), (key1977, -2), (key1977, -2), (key2214, -2), (key2219, 6), (key1982, -2), (key1982, -2), (key2223, -2)]

def rawRow17198 : Integer.Sparse Key := [(key1982, -2), (key1974, -2), (key1982, -2), (key1977, 6), (key2219, -2), (key2210, -2), (key2219, -2), (key1982, 2), (key1974, 2), (key2223, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key1977, -2), (key2214, -2), (key1977, -2), (key2219, 6), (key1982, -2), (key2223, -2), (key1982, -2)]

def rawRow17199 : Integer.Sparse Key := [(key1982, -2), (key1982, -2), (key1974, -2), (key1977, 6), (key2219, -2), (key2219, -2), (key2210, -2), (key2223, 2), (key2223, 2), (key1982, 2), (key1982, 2), (key1974, 2), (key1974, 2), (key2214, -2), (key1977, -2), (key1977, -2), (key2219, 6), (key2223, -2), (key1982, -2), (key1982, -2)]

def rawRow17200 : Integer.Sparse Key := [(key1977, -2), (key1982, -2), (key1982, -2), (key1974, 6), (key2214, -2), (key2223, -2), (key2223, -2), (key1977, 2), (key1982, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key2219, 2), (key1974, -2), (key1974, -2), (key2210, -2), (key2223, 6), (key1982, -2), (key1982, -2), (key2219, -2)]

def rawRow17201 : Integer.Sparse Key := [(key1982, -2), (key1977, -2), (key1982, -2), (key1974, 6), (key2223, -2), (key2214, -2), (key2223, -2), (key1982, 2), (key1977, 2), (key2219, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key1974, -2), (key2210, -2), (key1974, -2), (key2223, 6), (key1982, -2), (key2219, -2), (key1982, -2)]

def rawRow17202 : Integer.Sparse Key := [(key1982, -2), (key1982, -2), (key1977, -2), (key1974, 6), (key2223, -2), (key2223, -2), (key2214, -2), (key2219, 2), (key2219, 2), (key1982, 2), (key1982, 2), (key1977, 2), (key1977, 2), (key2210, -2), (key1974, -2), (key1974, -2), (key2223, 6), (key2219, -2), (key1982, -2), (key1982, -2)]

def rawRow17203 : Integer.Sparse Key := [(key2210, -2), (key2219, -2), (key2219, -2), (key2219, 6), (key1974, -2), (key1982, -2), (key1982, -2), (key1974, 2), (key1982, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key2223, 2), (key1982, -2), (key1982, -2), (key2223, -2), (key1977, 6), (key1977, -2), (key1977, -2), (key2214, -2)]

def rawRow17204 : Integer.Sparse Key := [(key2219, -2), (key2210, -2), (key2219, -2), (key2219, 6), (key1982, -2), (key1974, -2), (key1982, -2), (key1982, 2), (key1974, 2), (key2223, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key1982, -2), (key2223, -2), (key1982, -2), (key1977, 6), (key1977, -2), (key2214, -2), (key1977, -2)]

def rawRow17205 : Integer.Sparse Key := [(key2219, -2), (key2219, -2), (key2210, -2), (key2219, 6), (key1982, -2), (key1982, -2), (key1974, -2), (key2223, 2), (key2223, 2), (key1982, 2), (key1982, 2), (key1974, 2), (key1974, 2), (key2223, -2), (key1982, -2), (key1982, -2), (key1977, 6), (key2214, -2), (key1977, -2), (key1977, -2)]

def rawRow17206 : Integer.Sparse Key := [(key2219, -2), (key2219, -2), (key2219, -2), (key2210, 6), (key2223, -2), (key2223, -2), (key2223, -2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1974, -2), (key1974, -2), (key1974, -2), (key2214, 6), (key1977, -2), (key1977, -2), (key1977, -2)]

def rawRow17207 : Integer.Sparse Key := [(key2214, -2), (key2223, -2), (key2223, -2), (key2223, 6), (key1977, -2), (key1982, -2), (key1982, -2), (key1977, 2), (key1982, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key2219, 2), (key1982, -2), (key1982, -2), (key2219, -2), (key1974, 6), (key1974, -2), (key1974, -2), (key2210, -2)]

def rawRow17208 : Integer.Sparse Key := [(key2223, -2), (key2214, -2), (key2223, -2), (key2223, 6), (key1982, -2), (key1977, -2), (key1982, -2), (key1982, 2), (key1977, 2), (key2219, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key1982, -2), (key2219, -2), (key1982, -2), (key1974, 6), (key1974, -2), (key2210, -2), (key1974, -2)]

def rawRow17209 : Integer.Sparse Key := [(key2223, -2), (key2223, -2), (key2214, -2), (key2223, 6), (key1982, -2), (key1982, -2), (key1977, -2), (key2219, 2), (key2219, 2), (key1982, 2), (key1982, 2), (key1977, 2), (key1977, 2), (key2219, -2), (key1982, -2), (key1982, -2), (key1974, 6), (key2210, -2), (key1974, -2), (key1974, -2)]

def rawRow17210 : Integer.Sparse Key := [(key2223, -2), (key2223, -2), (key2223, -2), (key2214, 6), (key2219, -2), (key2219, -2), (key2219, -2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1977, -2), (key1977, -2), (key1977, -2), (key2210, 6), (key1974, -2), (key1974, -2), (key1974, -2)]

def rawRow17211 : Integer.Sparse Key := [(key758, 4), (key762, 4), (key764, 4), (key762, -4), (key764, -4), (key789, -4), (key762, -4), (key764, -4), (key789, -4), (key789, 12)]

def rawRow17212 : Integer.Sparse Key := [(key758, 4), (key764, 4), (key762, 4), (key764, -4), (key762, -4), (key789, -4), (key764, -4), (key762, -4), (key789, -4), (key789, 12)]

def rawRow17213 : Integer.Sparse Key := [(key762, 4), (key758, 4), (key764, 4), (key762, -4), (key789, -4), (key764, -4), (key762, -4), (key789, -4), (key764, -4), (key789, 12)]

def rawRow17214 : Integer.Sparse Key := [(key762, 4), (key764, 4), (key758, 4), (key789, -4), (key762, -4), (key764, -4), (key789, -4), (key762, -4), (key764, -4), (key789, 12)]

def rawRow17215 : Integer.Sparse Key := [(key764, 4), (key758, 4), (key762, 4), (key764, -4), (key789, -4), (key762, -4), (key764, -4), (key789, -4), (key762, -4), (key789, 12)]

def rawRow17216 : Integer.Sparse Key := [(key764, 4), (key762, 4), (key758, 4), (key789, -4), (key764, -4), (key762, -4), (key789, -4), (key764, -4), (key762, -4), (key789, 12)]

def rawRow17217 : Integer.Sparse Key := [(key762, 4), (key762, 4), (key789, 4), (key758, -4), (key764, -4), (key764, -4), (key762, -4), (key789, -4), (key789, -4), (key764, 12)]

def rawRow17218 : Integer.Sparse Key := [(key762, 4), (key789, 4), (key762, 4), (key764, -4), (key758, -4), (key764, -4), (key789, -4), (key762, -4), (key789, -4), (key764, 12)]

def rawRow17219 : Integer.Sparse Key := [(key789, 4), (key762, 4), (key762, 4), (key764, -4), (key764, -4), (key758, -4), (key789, -4), (key789, -4), (key762, -4), (key764, 12)]

def rawRow17220 : Integer.Sparse Key := [(key764, 4), (key764, 4), (key789, 4), (key758, -4), (key762, -4), (key762, -4), (key764, -4), (key789, -4), (key789, -4), (key762, 12)]

def rawRow17221 : Integer.Sparse Key := [(key764, 4), (key789, 4), (key764, 4), (key762, -4), (key758, -4), (key762, -4), (key789, -4), (key764, -4), (key789, -4), (key762, 12)]

def rawRow17222 : Integer.Sparse Key := [(key789, 4), (key764, 4), (key764, 4), (key762, -4), (key762, -4), (key758, -4), (key789, -4), (key789, -4), (key764, -4), (key762, 12)]

def rawRow17223 : Integer.Sparse Key := [(key762, 4), (key762, 4), (key789, 4), (key762, -4), (key789, -4), (key789, -4), (key758, -4), (key764, -4), (key764, -4), (key764, 12)]

def rawRow17224 : Integer.Sparse Key := [(key762, 4), (key789, 4), (key762, 4), (key789, -4), (key762, -4), (key789, -4), (key764, -4), (key758, -4), (key764, -4), (key764, 12)]

def rawRow17225 : Integer.Sparse Key := [(key789, 4), (key762, 4), (key762, 4), (key789, -4), (key789, -4), (key762, -4), (key764, -4), (key764, -4), (key758, -4), (key764, 12)]

def rawRow17226 : Integer.Sparse Key := [(key789, 4), (key789, 4), (key789, 4), (key762, -4), (key762, -4), (key762, -4), (key764, -4), (key764, -4), (key764, -4), (key758, 12)]

def rawRow17227 : Integer.Sparse Key := [(key764, 4), (key764, 4), (key789, 4), (key764, -4), (key789, -4), (key789, -4), (key758, -4), (key762, -4), (key762, -4), (key762, 12)]

def rawRow17228 : Integer.Sparse Key := [(key764, 4), (key789, 4), (key764, 4), (key789, -4), (key764, -4), (key789, -4), (key762, -4), (key758, -4), (key762, -4), (key762, 12)]

def rawRow17229 : Integer.Sparse Key := [(key789, 4), (key764, 4), (key764, 4), (key789, -4), (key789, -4), (key764, -4), (key762, -4), (key762, -4), (key758, -4), (key762, 12)]

def rawRow17230 : Integer.Sparse Key := [(key789, 4), (key789, 4), (key789, 4), (key764, -4), (key764, -4), (key764, -4), (key762, -4), (key762, -4), (key762, -4), (key758, 12)]

def rawRow17231 : Integer.Sparse Key := [(key2014, -1), (key2018, -1), (key2128, -1), (key2133, -1), (key2138, -1), (key2141, -1), (key2023, 2), (key2138, 2), (key2141, 2), (key2014, -1), (key2018, -1), (key2128, -1), (key2133, -1), (key2138, -1), (key2141, -1), (key2043, 2), (key2046, 2), (key2128, 2), (key2133, 2), (key2221, 2), (key2222, 2), (key2051, -1), (key2052, -1), (key2138, -1), (key2141, -1), (key2221, -1), (key2222, -1), (key2023, 2), (key2138, 2), (key2141, 2), (key2051, -1), (key2052, -1), (key2138, -1), (key2141, -1), (key2221, -1), (key2222, -1)]

def rawRow17232 : Integer.Sparse Key := [(key2018, -1), (key2014, -1), (key2133, -1), (key2128, -1), (key2141, -1), (key2138, -1), (key2023, 2), (key2141, 2), (key2138, 2), (key2018, -1), (key2014, -1), (key2133, -1), (key2128, -1), (key2141, -1), (key2138, -1), (key2046, 2), (key2043, 2), (key2133, 2), (key2128, 2), (key2222, 2), (key2221, 2), (key2052, -1), (key2051, -1), (key2141, -1), (key2138, -1), (key2222, -1), (key2221, -1), (key2023, 2), (key2141, 2), (key2138, 2), (key2052, -1), (key2051, -1), (key2141, -1), (key2138, -1), (key2222, -1), (key2221, -1)]

def rawRow17233 : Integer.Sparse Key := [(key2128, -1), (key2138, -1), (key2014, -1), (key2141, -1), (key2018, -1), (key2133, -1), (key2138, 2), (key2023, 2), (key2141, 2), (key2128, -1), (key2138, -1), (key2014, -1), (key2141, -1), (key2018, -1), (key2133, -1), (key2128, 2), (key2221, 2), (key2043, 2), (key2222, 2), (key2046, 2), (key2133, 2), (key2138, -1), (key2221, -1), (key2051, -1), (key2222, -1), (key2052, -1), (key2141, -1), (key2138, 2), (key2023, 2), (key2141, 2), (key2138, -1), (key2221, -1), (key2051, -1), (key2222, -1), (key2052, -1), (key2141, -1)]

def rawRow17234 : Integer.Sparse Key := [(key2138, -1), (key2128, -1), (key2141, -1), (key2014, -1), (key2133, -1), (key2018, -1), (key2138, 2), (key2141, 2), (key2023, 2), (key2138, -1), (key2128, -1), (key2141, -1), (key2014, -1), (key2133, -1), (key2018, -1), (key2221, 2), (key2128, 2), (key2222, 2), (key2043, 2), (key2133, 2), (key2046, 2), (key2221, -1), (key2138, -1), (key2222, -1), (key2051, -1), (key2141, -1), (key2052, -1), (key2138, 2), (key2141, 2), (key2023, 2), (key2221, -1), (key2138, -1), (key2222, -1), (key2051, -1), (key2141, -1), (key2052, -1)]

def rawRow17235 : Integer.Sparse Key := [(key2133, -1), (key2141, -1), (key2018, -1), (key2138, -1), (key2014, -1), (key2128, -1), (key2141, 2), (key2023, 2), (key2138, 2), (key2133, -1), (key2141, -1), (key2018, -1), (key2138, -1), (key2014, -1), (key2128, -1), (key2133, 2), (key2222, 2), (key2046, 2), (key2221, 2), (key2043, 2), (key2128, 2), (key2141, -1), (key2222, -1), (key2052, -1), (key2221, -1), (key2051, -1), (key2138, -1), (key2141, 2), (key2023, 2), (key2138, 2), (key2141, -1), (key2222, -1), (key2052, -1), (key2221, -1), (key2051, -1), (key2138, -1)]

def rawRow17236 : Integer.Sparse Key := [(key2141, -1), (key2133, -1), (key2138, -1), (key2018, -1), (key2128, -1), (key2014, -1), (key2141, 2), (key2138, 2), (key2023, 2), (key2141, -1), (key2133, -1), (key2138, -1), (key2018, -1), (key2128, -1), (key2014, -1), (key2222, 2), (key2133, 2), (key2221, 2), (key2046, 2), (key2128, 2), (key2043, 2), (key2222, -1), (key2141, -1), (key2221, -1), (key2052, -1), (key2138, -1), (key2051, -1), (key2141, 2), (key2138, 2), (key2023, 2), (key2222, -1), (key2141, -1), (key2221, -1), (key2052, -1), (key2138, -1), (key2051, -1)]

def rawRow17237 : Integer.Sparse Key := [(key2014, -1), (key2023, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2018, 2), (key2018, 2), (key2133, 2), (key2043, -1), (key2051, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2222, -1), (key2014, 2), (key2052, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2141, 2), (key2018, -1), (key2046, -1), (key2018, -1), (key2133, -1), (key2046, -1), (key2133, -1), (key2051, 2), (key2051, 2), (key2222, 2), (key2023, -1), (key2052, -1), (key2023, -1), (key2141, -1), (key2052, -1), (key2141, -1)]

def rawRow17238 : Integer.Sparse Key := [(key2023, -1), (key2014, -1), (key2141, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2018, 2), (key2133, 2), (key2018, 2), (key2051, -1), (key2043, -1), (key2222, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2052, 2), (key2014, 2), (key2141, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2046, -1), (key2018, -1), (key2133, -1), (key2018, -1), (key2133, -1), (key2046, -1), (key2051, 2), (key2222, 2), (key2051, 2), (key2052, -1), (key2023, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2052, -1)]

def rawRow17239 : Integer.Sparse Key := [(key2141, -1), (key2141, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2133, 2), (key2018, 2), (key2018, 2), (key2222, -1), (key2222, -1), (key2051, -1), (key2051, -1), (key2043, -1), (key2043, -1), (key2141, 2), (key2141, 2), (key2052, 2), (key2052, 2), (key2014, 2), (key2014, 2), (key2133, -1), (key2133, -1), (key2046, -1), (key2046, -1), (key2018, -1), (key2018, -1), (key2222, 2), (key2051, 2), (key2051, 2), (key2141, -1), (key2141, -1), (key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1)]

def rawRow17240 : Integer.Sparse Key := [(key2018, -1), (key2023, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2014, 2), (key2014, 2), (key2128, 2), (key2046, -1), (key2052, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2221, -1), (key2018, 2), (key2051, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2138, 2), (key2014, -1), (key2043, -1), (key2014, -1), (key2128, -1), (key2043, -1), (key2128, -1), (key2052, 2), (key2052, 2), (key2221, 2), (key2023, -1), (key2051, -1), (key2023, -1), (key2138, -1), (key2051, -1), (key2138, -1)]

def rawRow17241 : Integer.Sparse Key := [(key2023, -1), (key2018, -1), (key2138, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2014, 2), (key2128, 2), (key2014, 2), (key2052, -1), (key2046, -1), (key2221, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2051, 2), (key2018, 2), (key2138, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2043, -1), (key2014, -1), (key2128, -1), (key2014, -1), (key2128, -1), (key2043, -1), (key2052, 2), (key2221, 2), (key2052, 2), (key2051, -1), (key2023, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2051, -1)]

def rawRow17242 : Integer.Sparse Key := [(key2138, -1), (key2138, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2128, 2), (key2014, 2), (key2014, 2), (key2221, -1), (key2221, -1), (key2052, -1), (key2052, -1), (key2046, -1), (key2046, -1), (key2138, 2), (key2138, 2), (key2051, 2), (key2051, 2), (key2018, 2), (key2018, 2), (key2128, -1), (key2128, -1), (key2043, -1), (key2043, -1), (key2014, -1), (key2014, -1), (key2221, 2), (key2052, 2), (key2052, 2), (key2138, -1), (key2138, -1), (key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1)]

def rawRow17243 : Integer.Sparse Key := [(key2043, -1), (key2051, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2222, -1), (key2051, 2), (key2051, 2), (key2222, 2), (key2014, -1), (key2023, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2014, 2), (key2052, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2141, 2), (key2023, -1), (key2052, -1), (key2023, -1), (key2141, -1), (key2052, -1), (key2141, -1), (key2018, 2), (key2018, 2), (key2133, 2), (key2018, -1), (key2046, -1), (key2018, -1), (key2133, -1), (key2046, -1), (key2133, -1)]

def rawRow17244 : Integer.Sparse Key := [(key2051, -1), (key2043, -1), (key2222, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2051, 2), (key2222, 2), (key2051, 2), (key2023, -1), (key2014, -1), (key2141, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2052, 2), (key2014, 2), (key2141, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2052, -1), (key2023, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2052, -1), (key2018, 2), (key2133, 2), (key2018, 2), (key2046, -1), (key2018, -1), (key2133, -1), (key2018, -1), (key2133, -1), (key2046, -1)]

def rawRow17245 : Integer.Sparse Key := [(key2222, -1), (key2222, -1), (key2051, -1), (key2051, -1), (key2043, -1), (key2043, -1), (key2222, 2), (key2051, 2), (key2051, 2), (key2141, -1), (key2141, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2141, 2), (key2141, 2), (key2052, 2), (key2052, 2), (key2014, 2), (key2014, 2), (key2141, -1), (key2141, -1), (key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1), (key2133, 2), (key2018, 2), (key2018, 2), (key2133, -1), (key2133, -1), (key2046, -1), (key2046, -1), (key2018, -1), (key2018, -1)]

def rawRow17246 : Integer.Sparse Key := [(key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2043, 2), (key2043, 2), (key2043, 2), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2046, 2), (key2046, 2), (key2046, 2), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1)]

def rawRow17247 : Integer.Sparse Key := [(key2046, -1), (key2052, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2221, -1), (key2052, 2), (key2052, 2), (key2221, 2), (key2018, -1), (key2023, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2018, 2), (key2051, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2138, 2), (key2023, -1), (key2051, -1), (key2023, -1), (key2138, -1), (key2051, -1), (key2138, -1), (key2014, 2), (key2014, 2), (key2128, 2), (key2014, -1), (key2043, -1), (key2014, -1), (key2128, -1), (key2043, -1), (key2128, -1)]

def rawRow17248 : Integer.Sparse Key := [(key2052, -1), (key2046, -1), (key2221, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2052, 2), (key2221, 2), (key2052, 2), (key2023, -1), (key2018, -1), (key2138, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2051, 2), (key2018, 2), (key2138, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2051, -1), (key2023, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2051, -1), (key2014, 2), (key2128, 2), (key2014, 2), (key2043, -1), (key2014, -1), (key2128, -1), (key2014, -1), (key2128, -1), (key2043, -1)]

def rawRow17249 : Integer.Sparse Key := [(key2221, -1), (key2221, -1), (key2052, -1), (key2052, -1), (key2046, -1), (key2046, -1), (key2221, 2), (key2052, 2), (key2052, 2), (key2138, -1), (key2138, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2138, 2), (key2138, 2), (key2051, 2), (key2051, 2), (key2018, 2), (key2018, 2), (key2138, -1), (key2138, -1), (key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1), (key2128, 2), (key2014, 2), (key2014, 2), (key2128, -1), (key2128, -1), (key2043, -1), (key2043, -1), (key2014, -1), (key2014, -1)]

def rawRow17250 : Integer.Sparse Key := [(key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2046, 2), (key2046, 2), (key2046, 2), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2043, 2), (key2043, 2), (key2043, 2), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1)]

def rawRow17251 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, -2), (key365, 6), (key357, -2), (key359, -2), (key365, -2), (key357, 2), (key359, 2), (key527, 2), (key674, 2), (key535, 2), (key675, 2), (key365, -2), (key535, -2), (key675, -2), (key365, 6), (key365, -2), (key535, -2), (key675, -2)]

def rawRow17252 : Integer.Sparse Key := [(key359, -2), (key357, -2), (key365, -2), (key365, 6), (key359, -2), (key357, -2), (key365, -2), (key359, 2), (key357, 2), (key674, 2), (key527, 2), (key675, 2), (key535, 2), (key365, -2), (key675, -2), (key535, -2), (key365, 6), (key365, -2), (key675, -2), (key535, -2)]

def rawRow17253 : Integer.Sparse Key := [(key357, -2), (key365, -2), (key359, -2), (key365, 6), (key357, -2), (key365, -2), (key359, -2), (key527, 2), (key535, 2), (key357, 2), (key675, 2), (key359, 2), (key674, 2), (key535, -2), (key365, -2), (key675, -2), (key365, 6), (key535, -2), (key365, -2), (key675, -2)]

def rawRow17254 : Integer.Sparse Key := [(key365, -2), (key357, -2), (key359, -2), (key365, 6), (key365, -2), (key357, -2), (key359, -2), (key535, 2), (key527, 2), (key675, 2), (key357, 2), (key674, 2), (key359, 2), (key535, -2), (key675, -2), (key365, -2), (key365, 6), (key535, -2), (key675, -2), (key365, -2)]

def rawRow17255 : Integer.Sparse Key := [(key359, -2), (key365, -2), (key357, -2), (key365, 6), (key359, -2), (key365, -2), (key357, -2), (key674, 2), (key675, 2), (key359, 2), (key535, 2), (key357, 2), (key527, 2), (key675, -2), (key365, -2), (key535, -2), (key365, 6), (key675, -2), (key365, -2), (key535, -2)]

def rawRow17256 : Integer.Sparse Key := [(key365, -2), (key359, -2), (key357, -2), (key365, 6), (key365, -2), (key359, -2), (key357, -2), (key675, 2), (key674, 2), (key535, 2), (key359, 2), (key527, 2), (key357, 2), (key675, -2), (key535, -2), (key365, -2), (key365, 6), (key675, -2), (key535, -2), (key365, -2)]

def rawRow17257 : Integer.Sparse Key := [(key357, -2), (key365, -2), (key365, -2), (key359, 6), (key527, -2), (key535, -2), (key535, -2), (key357, 2), (key365, 2), (key357, 2), (key675, 2), (key365, 2), (key675, 2), (key359, -2), (key359, -2), (key674, -2), (key535, 6), (key365, -2), (key365, -2), (key675, -2)]

def rawRow17258 : Integer.Sparse Key := [(key365, -2), (key357, -2), (key365, -2), (key359, 6), (key535, -2), (key527, -2), (key535, -2), (key365, 2), (key357, 2), (key675, 2), (key357, 2), (key675, 2), (key365, 2), (key359, -2), (key674, -2), (key359, -2), (key535, 6), (key365, -2), (key675, -2), (key365, -2)]

def rawRow17259 : Integer.Sparse Key := [(key365, -2), (key365, -2), (key357, -2), (key359, 6), (key535, -2), (key535, -2), (key527, -2), (key675, 2), (key675, 2), (key365, 2), (key365, 2), (key357, 2), (key357, 2), (key674, -2), (key359, -2), (key359, -2), (key535, 6), (key675, -2), (key365, -2), (key365, -2)]

def rawRow17260 : Integer.Sparse Key := [(key359, -2), (key365, -2), (key365, -2), (key357, 6), (key674, -2), (key675, -2), (key675, -2), (key359, 2), (key365, 2), (key359, 2), (key535, 2), (key365, 2), (key535, 2), (key357, -2), (key357, -2), (key527, -2), (key675, 6), (key365, -2), (key365, -2), (key535, -2)]

def rawRow17261 : Integer.Sparse Key := [(key365, -2), (key359, -2), (key365, -2), (key357, 6), (key675, -2), (key674, -2), (key675, -2), (key365, 2), (key359, 2), (key535, 2), (key359, 2), (key535, 2), (key365, 2), (key357, -2), (key527, -2), (key357, -2), (key675, 6), (key365, -2), (key535, -2), (key365, -2)]

def rawRow17262 : Integer.Sparse Key := [(key365, -2), (key365, -2), (key359, -2), (key357, 6), (key675, -2), (key675, -2), (key674, -2), (key535, 2), (key535, 2), (key365, 2), (key365, 2), (key359, 2), (key359, 2), (key527, -2), (key357, -2), (key357, -2), (key675, 6), (key535, -2), (key365, -2), (key365, -2)]

def rawRow17263 : Integer.Sparse Key := [(key527, -2), (key535, -2), (key535, -2), (key535, 6), (key357, -2), (key365, -2), (key365, -2), (key357, 2), (key365, 2), (key357, 2), (key675, 2), (key365, 2), (key675, 2), (key365, -2), (key365, -2), (key675, -2), (key359, 6), (key359, -2), (key359, -2), (key674, -2)]

def rawRow17264 : Integer.Sparse Key := [(key535, -2), (key527, -2), (key535, -2), (key535, 6), (key365, -2), (key357, -2), (key365, -2), (key365, 2), (key357, 2), (key675, 2), (key357, 2), (key675, 2), (key365, 2), (key365, -2), (key675, -2), (key365, -2), (key359, 6), (key359, -2), (key674, -2), (key359, -2)]

def rawRow17265 : Integer.Sparse Key := [(key535, -2), (key535, -2), (key527, -2), (key535, 6), (key365, -2), (key365, -2), (key357, -2), (key675, 2), (key675, 2), (key365, 2), (key365, 2), (key357, 2), (key357, 2), (key675, -2), (key365, -2), (key365, -2), (key359, 6), (key674, -2), (key359, -2), (key359, -2)]

def rawRow17266 : Integer.Sparse Key := [(key535, -2), (key535, -2), (key535, -2), (key527, 6), (key675, -2), (key675, -2), (key675, -2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key357, -2), (key357, -2), (key357, -2), (key674, 6), (key359, -2), (key359, -2), (key359, -2)]

def rawRow17267 : Integer.Sparse Key := [(key674, -2), (key675, -2), (key675, -2), (key675, 6), (key359, -2), (key365, -2), (key365, -2), (key359, 2), (key365, 2), (key359, 2), (key535, 2), (key365, 2), (key535, 2), (key365, -2), (key365, -2), (key535, -2), (key357, 6), (key357, -2), (key357, -2), (key527, -2)]

def rawRow17268 : Integer.Sparse Key := [(key675, -2), (key674, -2), (key675, -2), (key675, 6), (key365, -2), (key359, -2), (key365, -2), (key365, 2), (key359, 2), (key535, 2), (key359, 2), (key535, 2), (key365, 2), (key365, -2), (key535, -2), (key365, -2), (key357, 6), (key357, -2), (key527, -2), (key357, -2)]

def rawRow17269 : Integer.Sparse Key := [(key675, -2), (key675, -2), (key674, -2), (key675, 6), (key365, -2), (key365, -2), (key359, -2), (key535, 2), (key535, 2), (key365, 2), (key365, 2), (key359, 2), (key359, 2), (key535, -2), (key365, -2), (key365, -2), (key357, 6), (key527, -2), (key357, -2), (key357, -2)]

def rawRow17270 : Integer.Sparse Key := [(key675, -2), (key675, -2), (key675, -2), (key674, 6), (key535, -2), (key535, -2), (key535, -2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key359, -2), (key359, -2), (key359, -2), (key527, 6), (key357, -2), (key357, -2), (key357, -2)]

def rawRow17271 : Integer.Sparse Key := [(key1976, 2), (key1981, 2), (key1983, 2), (key1981, -2), (key1983, -2), (key1997, -2), (key1976, 2), (key1981, 2), (key1983, 2), (key1981, -1), (key1983, -1), (key2218, -1), (key2224, -1), (key2262, -1), (key2266, -1), (key1981, -2), (key1983, -2), (key1997, -2), (key1981, -1), (key1983, -1), (key2218, -1), (key2224, -1), (key2262, -1), (key2266, -1), (key1997, 4), (key2262, 4), (key2266, 4)]

def rawRow17272 : Integer.Sparse Key := [(key1976, 2), (key1983, 2), (key1981, 2), (key1983, -2), (key1981, -2), (key1997, -2), (key1976, 2), (key1983, 2), (key1981, 2), (key1983, -1), (key1981, -1), (key2224, -1), (key2218, -1), (key2266, -1), (key2262, -1), (key1983, -2), (key1981, -2), (key1997, -2), (key1983, -1), (key1981, -1), (key2224, -1), (key2218, -1), (key2266, -1), (key2262, -1), (key1997, 4), (key2266, 4), (key2262, 4)]

def rawRow17273 : Integer.Sparse Key := [(key1981, 2), (key1976, 2), (key1983, 2), (key1981, -2), (key1997, -2), (key1983, -2), (key1981, 2), (key1976, 2), (key1983, 2), (key2218, -1), (key2262, -1), (key1981, -1), (key2266, -1), (key1983, -1), (key2224, -1), (key1981, -2), (key1997, -2), (key1983, -2), (key2218, -1), (key2262, -1), (key1981, -1), (key2266, -1), (key1983, -1), (key2224, -1), (key2262, 4), (key1997, 4), (key2266, 4)]

def rawRow17274 : Integer.Sparse Key := [(key1981, 2), (key1983, 2), (key1976, 2), (key1997, -2), (key1981, -2), (key1983, -2), (key1981, 2), (key1983, 2), (key1976, 2), (key2262, -1), (key2218, -1), (key2266, -1), (key1981, -1), (key2224, -1), (key1983, -1), (key1997, -2), (key1981, -2), (key1983, -2), (key2262, -1), (key2218, -1), (key2266, -1), (key1981, -1), (key2224, -1), (key1983, -1), (key2262, 4), (key2266, 4), (key1997, 4)]

def rawRow17275 : Integer.Sparse Key := [(key1983, 2), (key1976, 2), (key1981, 2), (key1983, -2), (key1997, -2), (key1981, -2), (key1983, 2), (key1976, 2), (key1981, 2), (key2224, -1), (key2266, -1), (key1983, -1), (key2262, -1), (key1981, -1), (key2218, -1), (key1983, -2), (key1997, -2), (key1981, -2), (key2224, -1), (key2266, -1), (key1983, -1), (key2262, -1), (key1981, -1), (key2218, -1), (key2266, 4), (key1997, 4), (key2262, 4)]

def rawRow17276 : Integer.Sparse Key := [(key1983, 2), (key1981, 2), (key1976, 2), (key1997, -2), (key1983, -2), (key1981, -2), (key1983, 2), (key1981, 2), (key1976, 2), (key2266, -1), (key2224, -1), (key2262, -1), (key1983, -1), (key2218, -1), (key1981, -1), (key1997, -2), (key1983, -2), (key1981, -2), (key2266, -1), (key2224, -1), (key2262, -1), (key1983, -1), (key2218, -1), (key1981, -1), (key2266, 4), (key2262, 4), (key1997, 4)]

def rawRow17277 : Integer.Sparse Key := [(key1981, 2), (key1981, 2), (key1997, 2), (key1976, -2), (key1983, -2), (key1983, -2), (key2218, 2), (key2218, 2), (key2262, 2), (key1976, -1), (key1983, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key2224, -1), (key2218, -2), (key2262, -2), (key2262, -2), (key1981, -1), (key1997, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key2266, -1), (key1983, 4), (key1983, 4), (key2224, 4)]

def rawRow17278 : Integer.Sparse Key := [(key1981, 2), (key1997, 2), (key1981, 2), (key1983, -2), (key1976, -2), (key1983, -2), (key2218, 2), (key2262, 2), (key2218, 2), (key1983, -1), (key1976, -1), (key2224, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key2262, -2), (key2218, -2), (key2262, -2), (key1997, -1), (key1981, -1), (key2266, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key1983, 4), (key2224, 4), (key1983, 4)]

def rawRow17279 : Integer.Sparse Key := [(key1997, 2), (key1981, 2), (key1981, 2), (key1983, -2), (key1983, -2), (key1976, -2), (key2262, 2), (key2218, 2), (key2218, 2), (key2224, -1), (key2224, -1), (key1983, -1), (key1983, -1), (key1976, -1), (key1976, -1), (key2262, -2), (key2262, -2), (key2218, -2), (key2266, -1), (key2266, -1), (key1997, -1), (key1997, -1), (key1981, -1), (key1981, -1), (key2224, 4), (key1983, 4), (key1983, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17280 : Integer.Sparse Key := [(key1983, 2), (key1983, 2), (key1997, 2), (key1976, -2), (key1981, -2), (key1981, -2), (key2224, 2), (key2224, 2), (key2266, 2), (key1976, -1), (key1981, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key2218, -1), (key2224, -2), (key2266, -2), (key2266, -2), (key1983, -1), (key1997, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key2262, -1), (key1981, 4), (key1981, 4), (key2218, 4)]

def rawRow17281 : Integer.Sparse Key := [(key1983, 2), (key1997, 2), (key1983, 2), (key1981, -2), (key1976, -2), (key1981, -2), (key2224, 2), (key2266, 2), (key2224, 2), (key1981, -1), (key1976, -1), (key2218, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key2266, -2), (key2224, -2), (key2266, -2), (key1997, -1), (key1983, -1), (key2262, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key1981, 4), (key2218, 4), (key1981, 4)]

def rawRow17282 : Integer.Sparse Key := [(key1997, 2), (key1983, 2), (key1983, 2), (key1981, -2), (key1981, -2), (key1976, -2), (key2266, 2), (key2224, 2), (key2224, 2), (key2218, -1), (key2218, -1), (key1981, -1), (key1981, -1), (key1976, -1), (key1976, -1), (key2266, -2), (key2266, -2), (key2224, -2), (key2262, -1), (key2262, -1), (key1997, -1), (key1997, -1), (key1983, -1), (key1983, -1), (key2218, 4), (key1981, 4), (key1981, 4)]

def rawRow17283 : Integer.Sparse Key := [(key2218, 2), (key2218, 2), (key2262, 2), (key2218, -2), (key2262, -2), (key2262, -2), (key1981, 2), (key1981, 2), (key1997, 2), (key1981, -1), (key1997, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key2266, -1), (key1976, -2), (key1983, -2), (key1983, -2), (key1976, -1), (key1983, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key2224, -1), (key1983, 4), (key1983, 4), (key2224, 4)]

def rawRow17284 : Integer.Sparse Key := [(key2218, 2), (key2262, 2), (key2218, 2), (key2262, -2), (key2218, -2), (key2262, -2), (key1981, 2), (key1997, 2), (key1981, 2), (key1997, -1), (key1981, -1), (key2266, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key1983, -2), (key1976, -2), (key1983, -2), (key1983, -1), (key1976, -1), (key2224, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key1983, 4), (key2224, 4), (key1983, 4)]

def rawRow17285 : Integer.Sparse Key := [(key2262, 2), (key2218, 2), (key2218, 2), (key2262, -2), (key2262, -2), (key2218, -2), (key1997, 2), (key1981, 2), (key1981, 2), (key2266, -1), (key2266, -1), (key1997, -1), (key1997, -1), (key1981, -1), (key1981, -1), (key1983, -2), (key1983, -2), (key1976, -2), (key2224, -1), (key2224, -1), (key1983, -1), (key1983, -1), (key1976, -1), (key1976, -1), (key2224, 4), (key1983, 4), (key1983, 4)]

def rawRow17286 : Integer.Sparse Key := [(key2262, 2), (key2262, 2), (key2262, 2), (key2218, -2), (key2218, -2), (key2218, -2), (key2266, 2), (key2266, 2), (key2266, 2), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key2224, -2), (key2224, -2), (key2224, -2), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1976, 4), (key1976, 4), (key1976, 4)]

def rawRow17287 : Integer.Sparse Key := [(key2224, 2), (key2224, 2), (key2266, 2), (key2224, -2), (key2266, -2), (key2266, -2), (key1983, 2), (key1983, 2), (key1997, 2), (key1983, -1), (key1997, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key2262, -1), (key1976, -2), (key1981, -2), (key1981, -2), (key1976, -1), (key1981, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key2218, -1), (key1981, 4), (key1981, 4), (key2218, 4)]

def rawRow17288 : Integer.Sparse Key := [(key2224, 2), (key2266, 2), (key2224, 2), (key2266, -2), (key2224, -2), (key2266, -2), (key1983, 2), (key1997, 2), (key1983, 2), (key1997, -1), (key1983, -1), (key2262, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key1981, -2), (key1976, -2), (key1981, -2), (key1981, -1), (key1976, -1), (key2218, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key1981, 4), (key2218, 4), (key1981, 4)]

def rawRow17289 : Integer.Sparse Key := [(key2266, 2), (key2224, 2), (key2224, 2), (key2266, -2), (key2266, -2), (key2224, -2), (key1997, 2), (key1983, 2), (key1983, 2), (key2262, -1), (key2262, -1), (key1997, -1), (key1997, -1), (key1983, -1), (key1983, -1), (key1981, -2), (key1981, -2), (key1976, -2), (key2218, -1), (key2218, -1), (key1981, -1), (key1981, -1), (key1976, -1), (key1976, -1), (key2218, 4), (key1981, 4), (key1981, 4)]

def rawRow17290 : Integer.Sparse Key := [(key2266, 2), (key2266, 2), (key2266, 2), (key2224, -2), (key2224, -2), (key2224, -2), (key2262, 2), (key2262, 2), (key2262, 2), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key2218, -2), (key2218, -2), (key2218, -2), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1976, 4), (key1976, 4), (key1976, 4)]

def rawRow17291 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, 2), (key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2013, 2), (key2019, 2), (key2026, 2), (key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2042, 2), (key2047, 2), (key2127, 2), (key2134, 2), (key2228, 2), (key2229, 2)]

def rawRow17292 : Integer.Sparse Key := [(key2019, 2), (key2013, 2), (key2026, 2), (key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2019, 2), (key2013, 2), (key2026, 2), (key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2047, 2), (key2042, 2), (key2134, 2), (key2127, 2), (key2229, 2), (key2228, 2)]

def rawRow17293 : Integer.Sparse Key := [(key2013, 2), (key2026, 2), (key2019, 2), (key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2013, 2), (key2026, 2), (key2019, 2), (key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2127, 2), (key2228, 2), (key2042, 2), (key2229, 2), (key2047, 2), (key2134, 2)]

def rawRow17294 : Integer.Sparse Key := [(key2026, 2), (key2013, 2), (key2019, 2), (key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2026, 2), (key2013, 2), (key2019, 2), (key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2228, 2), (key2127, 2), (key2229, 2), (key2042, 2), (key2134, 2), (key2047, 2)]

def rawRow17295 : Integer.Sparse Key := [(key2019, 2), (key2026, 2), (key2013, 2), (key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2019, 2), (key2026, 2), (key2013, 2), (key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2134, 2), (key2229, 2), (key2047, 2), (key2228, 2), (key2042, 2), (key2127, 2)]

def rawRow17296 : Integer.Sparse Key := [(key2026, 2), (key2019, 2), (key2013, 2), (key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2026, 2), (key2019, 2), (key2013, 2), (key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2229, 2), (key2134, 2), (key2228, 2), (key2047, 2), (key2127, 2), (key2042, 2)]

def rawRow17297 : Integer.Sparse Key := [(key2042, 2), (key2055, 2), (key2055, 2), (key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2127, 2), (key2144, 2), (key2144, 2), (key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2)]

def rawRow17298 : Integer.Sparse Key := [(key2055, 2), (key2042, 2), (key2055, 2), (key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2144, 2), (key2127, 2), (key2144, 2), (key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2)]

def rawRow17299 : Integer.Sparse Key := [(key2055, 2), (key2055, 2), (key2042, 2), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2144, 2), (key2144, 2), (key2127, 2), (key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2)]

def rawRow17300 : Integer.Sparse Key := [(key2047, 2), (key2056, 2), (key2056, 2), (key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2134, 2), (key2145, 2), (key2145, 2), (key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2)]

def rawRow17301 : Integer.Sparse Key := [(key2056, 2), (key2047, 2), (key2056, 2), (key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2145, 2), (key2134, 2), (key2145, 2), (key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2)]

def rawRow17302 : Integer.Sparse Key := [(key2056, 2), (key2056, 2), (key2047, 2), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2145, 2), (key2145, 2), (key2134, 2), (key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2)]

def rawRow17303 : Integer.Sparse Key := [(key2127, 2), (key2144, 2), (key2144, 2), (key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2042, 2), (key2055, 2), (key2055, 2), (key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2)]

def rawRow17304 : Integer.Sparse Key := [(key2144, 2), (key2127, 2), (key2144, 2), (key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2055, 2), (key2042, 2), (key2055, 2), (key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2)]

def rawRow17305 : Integer.Sparse Key := [(key2144, 2), (key2144, 2), (key2127, 2), (key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2055, 2), (key2055, 2), (key2042, 2), (key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2)]

def rawRow17306 : Integer.Sparse Key := [(key2228, 2), (key2228, 2), (key2228, 2), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2229, 2), (key2229, 2), (key2229, 2), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2)]

def rawRow17307 : Integer.Sparse Key := [(key2134, 2), (key2145, 2), (key2145, 2), (key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2047, 2), (key2056, 2), (key2056, 2), (key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2)]

def rawRow17308 : Integer.Sparse Key := [(key2145, 2), (key2134, 2), (key2145, 2), (key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2056, 2), (key2047, 2), (key2056, 2), (key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2)]

def rawRow17309 : Integer.Sparse Key := [(key2145, 2), (key2145, 2), (key2134, 2), (key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2056, 2), (key2056, 2), (key2047, 2), (key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2)]

def rawRow17310 : Integer.Sparse Key := [(key2229, 2), (key2229, 2), (key2229, 2), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2228, 2), (key2228, 2), (key2228, 2), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2)]

def rawRow17311 : Integer.Sparse Key := [(key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2026, 2), (key2055, 2), (key2056, 2), (key2013, 1), (key2019, 1), (key2127, 1), (key2134, 1), (key2144, 1), (key2145, 1), (key2026, -2), (key2144, -2), (key2145, -2), (key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2013, 1), (key2019, 1), (key2127, 1), (key2134, 1), (key2144, 1), (key2145, 1), (key2026, 2), (key2055, 2), (key2056, 2), (key2026, -2), (key2144, -2), (key2145, -2)]

def rawRow17312 : Integer.Sparse Key := [(key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2026, 2), (key2056, 2), (key2055, 2), (key2019, 1), (key2013, 1), (key2134, 1), (key2127, 1), (key2145, 1), (key2144, 1), (key2026, -2), (key2145, -2), (key2144, -2), (key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2019, 1), (key2013, 1), (key2134, 1), (key2127, 1), (key2145, 1), (key2144, 1), (key2026, 2), (key2056, 2), (key2055, 2), (key2026, -2), (key2145, -2), (key2144, -2)]

def rawRow17313 : Integer.Sparse Key := [(key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2055, 2), (key2026, 2), (key2056, 2), (key2127, 1), (key2144, 1), (key2013, 1), (key2145, 1), (key2019, 1), (key2134, 1), (key2144, -2), (key2026, -2), (key2145, -2), (key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2127, 1), (key2144, 1), (key2013, 1), (key2145, 1), (key2019, 1), (key2134, 1), (key2055, 2), (key2026, 2), (key2056, 2), (key2144, -2), (key2026, -2), (key2145, -2)]

def rawRow17314 : Integer.Sparse Key := [(key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2055, 2), (key2056, 2), (key2026, 2), (key2144, 1), (key2127, 1), (key2145, 1), (key2013, 1), (key2134, 1), (key2019, 1), (key2144, -2), (key2145, -2), (key2026, -2), (key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2144, 1), (key2127, 1), (key2145, 1), (key2013, 1), (key2134, 1), (key2019, 1), (key2055, 2), (key2056, 2), (key2026, 2), (key2144, -2), (key2145, -2), (key2026, -2)]

def rawRow17315 : Integer.Sparse Key := [(key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2056, 2), (key2026, 2), (key2055, 2), (key2134, 1), (key2145, 1), (key2019, 1), (key2144, 1), (key2013, 1), (key2127, 1), (key2145, -2), (key2026, -2), (key2144, -2), (key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2134, 1), (key2145, 1), (key2019, 1), (key2144, 1), (key2013, 1), (key2127, 1), (key2056, 2), (key2026, 2), (key2055, 2), (key2145, -2), (key2026, -2), (key2144, -2)]

def rawRow17316 : Integer.Sparse Key := [(key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2056, 2), (key2055, 2), (key2026, 2), (key2145, 1), (key2134, 1), (key2144, 1), (key2019, 1), (key2127, 1), (key2013, 1), (key2145, -2), (key2144, -2), (key2026, -2), (key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2145, 1), (key2134, 1), (key2144, 1), (key2019, 1), (key2127, 1), (key2013, 1), (key2056, 2), (key2055, 2), (key2026, 2), (key2145, -2), (key2144, -2), (key2026, -2)]

def rawRow17317 : Integer.Sparse Key := [(key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2019, 2), (key2019, 2), (key2047, 2), (key2013, 1), (key2026, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2145, 1), (key2019, -2), (key2019, -2), (key2134, -2), (key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2042, 1), (key2055, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2229, 1), (key2144, 2), (key2144, 2), (key2228, 2), (key2055, -2), (key2055, -2), (key2229, -2)]

def rawRow17318 : Integer.Sparse Key := [(key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2019, 2), (key2047, 2), (key2019, 2), (key2026, 1), (key2013, 1), (key2145, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2019, -2), (key2134, -2), (key2019, -2), (key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2055, 1), (key2042, 1), (key2229, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2144, 2), (key2228, 2), (key2144, 2), (key2055, -2), (key2229, -2), (key2055, -2)]

def rawRow17319 : Integer.Sparse Key := [(key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2047, 2), (key2019, 2), (key2019, 2), (key2145, 1), (key2145, 1), (key2026, 1), (key2026, 1), (key2013, 1), (key2013, 1), (key2134, -2), (key2019, -2), (key2019, -2), (key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2229, 1), (key2229, 1), (key2055, 1), (key2055, 1), (key2042, 1), (key2042, 1), (key2228, 2), (key2144, 2), (key2144, 2), (key2229, -2), (key2055, -2), (key2055, -2)]

def rawRow17320 : Integer.Sparse Key := [(key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2013, 2), (key2013, 2), (key2042, 2), (key2019, 1), (key2026, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2144, 1), (key2013, -2), (key2013, -2), (key2127, -2), (key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2047, 1), (key2056, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2228, 1), (key2145, 2), (key2145, 2), (key2229, 2), (key2056, -2), (key2056, -2), (key2228, -2)]

def rawRow17321 : Integer.Sparse Key := [(key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2013, 2), (key2042, 2), (key2013, 2), (key2026, 1), (key2019, 1), (key2144, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2013, -2), (key2127, -2), (key2013, -2), (key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2056, 1), (key2047, 1), (key2228, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2145, 2), (key2229, 2), (key2145, 2), (key2056, -2), (key2228, -2), (key2056, -2)]

def rawRow17322 : Integer.Sparse Key := [(key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2042, 2), (key2013, 2), (key2013, 2), (key2144, 1), (key2144, 1), (key2026, 1), (key2026, 1), (key2019, 1), (key2019, 1), (key2127, -2), (key2013, -2), (key2013, -2), (key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2228, 1), (key2228, 1), (key2056, 1), (key2056, 1), (key2047, 1), (key2047, 1), (key2229, 2), (key2145, 2), (key2145, 2), (key2228, -2), (key2056, -2), (key2056, -2)]

def rawRow17323 : Integer.Sparse Key := [(key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2144, 2), (key2144, 2), (key2228, 2), (key2042, 1), (key2055, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2229, 1), (key2055, -2), (key2055, -2), (key2229, -2), (key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2013, 1), (key2026, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2145, 1), (key2019, 2), (key2019, 2), (key2047, 2), (key2019, -2), (key2019, -2), (key2134, -2)]

def rawRow17324 : Integer.Sparse Key := [(key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2144, 2), (key2228, 2), (key2144, 2), (key2055, 1), (key2042, 1), (key2229, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2055, -2), (key2229, -2), (key2055, -2), (key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2026, 1), (key2013, 1), (key2145, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2019, 2), (key2047, 2), (key2019, 2), (key2019, -2), (key2134, -2), (key2019, -2)]

def rawRow17325 : Integer.Sparse Key := [(key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2228, 2), (key2144, 2), (key2144, 2), (key2229, 1), (key2229, 1), (key2055, 1), (key2055, 1), (key2042, 1), (key2042, 1), (key2229, -2), (key2055, -2), (key2055, -2), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, 1), (key2145, 1), (key2026, 1), (key2026, 1), (key2013, 1), (key2013, 1), (key2047, 2), (key2019, 2), (key2019, 2), (key2134, -2), (key2019, -2), (key2019, -2)]

def rawRow17326 : Integer.Sparse Key := [(key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2127, 2), (key2127, 2), (key2127, 2), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2042, -2), (key2042, -2), (key2042, -2), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2134, 2), (key2134, 2), (key2134, 2), (key2047, -2), (key2047, -2), (key2047, -2)]

def rawRow17327 : Integer.Sparse Key := [(key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2145, 2), (key2145, 2), (key2229, 2), (key2047, 1), (key2056, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2228, 1), (key2056, -2), (key2056, -2), (key2228, -2), (key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2019, 1), (key2026, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2144, 1), (key2013, 2), (key2013, 2), (key2042, 2), (key2013, -2), (key2013, -2), (key2127, -2)]

def rawRow17328 : Integer.Sparse Key := [(key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2145, 2), (key2229, 2), (key2145, 2), (key2056, 1), (key2047, 1), (key2228, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2056, -2), (key2228, -2), (key2056, -2), (key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2026, 1), (key2019, 1), (key2144, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2013, 2), (key2042, 2), (key2013, 2), (key2013, -2), (key2127, -2), (key2013, -2)]

def rawRow17329 : Integer.Sparse Key := [(key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2229, 2), (key2145, 2), (key2145, 2), (key2228, 1), (key2228, 1), (key2056, 1), (key2056, 1), (key2047, 1), (key2047, 1), (key2228, -2), (key2056, -2), (key2056, -2), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, 1), (key2144, 1), (key2026, 1), (key2026, 1), (key2019, 1), (key2019, 1), (key2042, 2), (key2013, 2), (key2013, 2), (key2127, -2), (key2013, -2), (key2013, -2)]

def rawRow17330 : Integer.Sparse Key := [(key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2134, 2), (key2134, 2), (key2134, 2), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2047, -2), (key2047, -2), (key2047, -2), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2127, 2), (key2127, 2), (key2127, 2), (key2042, -2), (key2042, -2), (key2042, -2)]

def rawRow17331 : Integer.Sparse Key := [(key2014, -1), (key2018, -1), (key2043, -1), (key2046, -1), (key2051, -1), (key2052, -1), (key2023, 2), (key2051, 2), (key2052, 2), (key2014, 1), (key2018, 1), (key2128, 1), (key2133, 1), (key2138, 1), (key2141, 1), (key2023, -2), (key2138, -2), (key2141, -2), (key2014, -1), (key2018, -1), (key2043, -1), (key2046, -1), (key2051, -1), (key2052, -1), (key2014, 1), (key2018, 1), (key2128, 1), (key2133, 1), (key2138, 1), (key2141, 1), (key2023, 2), (key2051, 2), (key2052, 2), (key2023, -2), (key2138, -2), (key2141, -2)]

def rawRow17332 : Integer.Sparse Key := [(key2018, -1), (key2014, -1), (key2046, -1), (key2043, -1), (key2052, -1), (key2051, -1), (key2023, 2), (key2052, 2), (key2051, 2), (key2018, 1), (key2014, 1), (key2133, 1), (key2128, 1), (key2141, 1), (key2138, 1), (key2023, -2), (key2141, -2), (key2138, -2), (key2018, -1), (key2014, -1), (key2046, -1), (key2043, -1), (key2052, -1), (key2051, -1), (key2018, 1), (key2014, 1), (key2133, 1), (key2128, 1), (key2141, 1), (key2138, 1), (key2023, 2), (key2052, 2), (key2051, 2), (key2023, -2), (key2141, -2), (key2138, -2)]

def rawRow17333 : Integer.Sparse Key := [(key2043, -1), (key2051, -1), (key2014, -1), (key2052, -1), (key2018, -1), (key2046, -1), (key2051, 2), (key2023, 2), (key2052, 2), (key2128, 1), (key2138, 1), (key2014, 1), (key2141, 1), (key2018, 1), (key2133, 1), (key2138, -2), (key2023, -2), (key2141, -2), (key2043, -1), (key2051, -1), (key2014, -1), (key2052, -1), (key2018, -1), (key2046, -1), (key2128, 1), (key2138, 1), (key2014, 1), (key2141, 1), (key2018, 1), (key2133, 1), (key2051, 2), (key2023, 2), (key2052, 2), (key2138, -2), (key2023, -2), (key2141, -2)]

def rawRow17334 : Integer.Sparse Key := [(key2051, -1), (key2043, -1), (key2052, -1), (key2014, -1), (key2046, -1), (key2018, -1), (key2051, 2), (key2052, 2), (key2023, 2), (key2138, 1), (key2128, 1), (key2141, 1), (key2014, 1), (key2133, 1), (key2018, 1), (key2138, -2), (key2141, -2), (key2023, -2), (key2051, -1), (key2043, -1), (key2052, -1), (key2014, -1), (key2046, -1), (key2018, -1), (key2138, 1), (key2128, 1), (key2141, 1), (key2014, 1), (key2133, 1), (key2018, 1), (key2051, 2), (key2052, 2), (key2023, 2), (key2138, -2), (key2141, -2), (key2023, -2)]

def rawRow17335 : Integer.Sparse Key := [(key2046, -1), (key2052, -1), (key2018, -1), (key2051, -1), (key2014, -1), (key2043, -1), (key2052, 2), (key2023, 2), (key2051, 2), (key2133, 1), (key2141, 1), (key2018, 1), (key2138, 1), (key2014, 1), (key2128, 1), (key2141, -2), (key2023, -2), (key2138, -2), (key2046, -1), (key2052, -1), (key2018, -1), (key2051, -1), (key2014, -1), (key2043, -1), (key2133, 1), (key2141, 1), (key2018, 1), (key2138, 1), (key2014, 1), (key2128, 1), (key2052, 2), (key2023, 2), (key2051, 2), (key2141, -2), (key2023, -2), (key2138, -2)]

def rawRow17336 : Integer.Sparse Key := [(key2052, -1), (key2046, -1), (key2051, -1), (key2018, -1), (key2043, -1), (key2014, -1), (key2052, 2), (key2051, 2), (key2023, 2), (key2141, 1), (key2133, 1), (key2138, 1), (key2018, 1), (key2128, 1), (key2014, 1), (key2141, -2), (key2138, -2), (key2023, -2), (key2052, -1), (key2046, -1), (key2051, -1), (key2018, -1), (key2043, -1), (key2014, -1), (key2141, 1), (key2133, 1), (key2138, 1), (key2018, 1), (key2128, 1), (key2014, 1), (key2052, 2), (key2051, 2), (key2023, 2), (key2141, -2), (key2138, -2), (key2023, -2)]

def rawRow17337 : Integer.Sparse Key := [(key2014, -1), (key2023, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2052, -1), (key2018, 2), (key2018, 2), (key2046, 2), (key2014, 1), (key2023, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2141, 1), (key2018, -2), (key2018, -2), (key2133, -2), (key2128, -1), (key2138, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2221, -1), (key2043, 1), (key2051, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2222, 1), (key2138, 2), (key2138, 2), (key2221, 2), (key2051, -2), (key2051, -2), (key2222, -2)]

def rawRow17338 : Integer.Sparse Key := [(key2023, -1), (key2014, -1), (key2052, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2018, 2), (key2046, 2), (key2018, 2), (key2023, 1), (key2014, 1), (key2141, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2018, -2), (key2133, -2), (key2018, -2), (key2138, -1), (key2128, -1), (key2221, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2051, 1), (key2043, 1), (key2222, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2138, 2), (key2221, 2), (key2138, 2), (key2051, -2), (key2222, -2), (key2051, -2)]

def rawRow17339 : Integer.Sparse Key := [(key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2046, 2), (key2018, 2), (key2018, 2), (key2141, 1), (key2141, 1), (key2023, 1), (key2023, 1), (key2014, 1), (key2014, 1), (key2133, -2), (key2018, -2), (key2018, -2), (key2221, -1), (key2221, -1), (key2138, -1), (key2138, -1), (key2128, -1), (key2128, -1), (key2222, 1), (key2222, 1), (key2051, 1), (key2051, 1), (key2043, 1), (key2043, 1), (key2221, 2), (key2138, 2), (key2138, 2), (key2222, -2), (key2051, -2), (key2051, -2)]

def rawRow17340 : Integer.Sparse Key := [(key2018, -1), (key2023, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2051, -1), (key2014, 2), (key2014, 2), (key2043, 2), (key2018, 1), (key2023, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2138, 1), (key2014, -2), (key2014, -2), (key2128, -2), (key2133, -1), (key2141, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2222, -1), (key2046, 1), (key2052, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2221, 1), (key2141, 2), (key2141, 2), (key2222, 2), (key2052, -2), (key2052, -2), (key2221, -2)]

def rawRow17341 : Integer.Sparse Key := [(key2023, -1), (key2018, -1), (key2051, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2014, 2), (key2043, 2), (key2014, 2), (key2023, 1), (key2018, 1), (key2138, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2014, -2), (key2128, -2), (key2014, -2), (key2141, -1), (key2133, -1), (key2222, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2052, 1), (key2046, 1), (key2221, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2141, 2), (key2222, 2), (key2141, 2), (key2052, -2), (key2221, -2), (key2052, -2)]

def rawRow17342 : Integer.Sparse Key := [(key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2043, 2), (key2014, 2), (key2014, 2), (key2138, 1), (key2138, 1), (key2023, 1), (key2023, 1), (key2018, 1), (key2018, 1), (key2128, -2), (key2014, -2), (key2014, -2), (key2222, -1), (key2222, -1), (key2141, -1), (key2141, -1), (key2133, -1), (key2133, -1), (key2221, 1), (key2221, 1), (key2052, 1), (key2052, 1), (key2046, 1), (key2046, 1), (key2222, 2), (key2141, 2), (key2141, 2), (key2221, -2), (key2052, -2), (key2052, -2)]

def rawRow17343 : Integer.Sparse Key := [(key2128, -1), (key2138, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2221, -1), (key2138, 2), (key2138, 2), (key2221, 2), (key2043, 1), (key2051, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2222, 1), (key2051, -2), (key2051, -2), (key2222, -2), (key2014, -1), (key2023, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2052, -1), (key2014, 1), (key2023, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2141, 1), (key2018, 2), (key2018, 2), (key2046, 2), (key2018, -2), (key2018, -2), (key2133, -2)]

def rawRow17344 : Integer.Sparse Key := [(key2138, -1), (key2128, -1), (key2221, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2138, 2), (key2221, 2), (key2138, 2), (key2051, 1), (key2043, 1), (key2222, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2051, -2), (key2222, -2), (key2051, -2), (key2023, -1), (key2014, -1), (key2052, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2023, 1), (key2014, 1), (key2141, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2018, 2), (key2046, 2), (key2018, 2), (key2018, -2), (key2133, -2), (key2018, -2)]

def rawRow17345 : Integer.Sparse Key := [(key2221, -1), (key2221, -1), (key2138, -1), (key2138, -1), (key2128, -1), (key2128, -1), (key2221, 2), (key2138, 2), (key2138, 2), (key2222, 1), (key2222, 1), (key2051, 1), (key2051, 1), (key2043, 1), (key2043, 1), (key2222, -2), (key2051, -2), (key2051, -2), (key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2141, 1), (key2141, 1), (key2023, 1), (key2023, 1), (key2014, 1), (key2014, 1), (key2046, 2), (key2018, 2), (key2018, 2), (key2133, -2), (key2018, -2), (key2018, -2)]

def rawRow17346 : Integer.Sparse Key := [(key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2128, 2), (key2128, 2), (key2128, 2), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2043, -2), (key2043, -2), (key2043, -2), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2133, 2), (key2133, 2), (key2133, 2), (key2046, -2), (key2046, -2), (key2046, -2)]

def rawRow17347 : Integer.Sparse Key := [(key2133, -1), (key2141, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2222, -1), (key2141, 2), (key2141, 2), (key2222, 2), (key2046, 1), (key2052, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2221, 1), (key2052, -2), (key2052, -2), (key2221, -2), (key2018, -1), (key2023, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2051, -1), (key2018, 1), (key2023, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2138, 1), (key2014, 2), (key2014, 2), (key2043, 2), (key2014, -2), (key2014, -2), (key2128, -2)]

def rawRow17348 : Integer.Sparse Key := [(key2141, -1), (key2133, -1), (key2222, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2141, 2), (key2222, 2), (key2141, 2), (key2052, 1), (key2046, 1), (key2221, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2052, -2), (key2221, -2), (key2052, -2), (key2023, -1), (key2018, -1), (key2051, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2023, 1), (key2018, 1), (key2138, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2014, 2), (key2043, 2), (key2014, 2), (key2014, -2), (key2128, -2), (key2014, -2)]

def rawRow17349 : Integer.Sparse Key := [(key2222, -1), (key2222, -1), (key2141, -1), (key2141, -1), (key2133, -1), (key2133, -1), (key2222, 2), (key2141, 2), (key2141, 2), (key2221, 1), (key2221, 1), (key2052, 1), (key2052, 1), (key2046, 1), (key2046, 1), (key2221, -2), (key2052, -2), (key2052, -2), (key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2138, 1), (key2138, 1), (key2023, 1), (key2023, 1), (key2018, 1), (key2018, 1), (key2043, 2), (key2014, 2), (key2014, 2), (key2128, -2), (key2014, -2), (key2014, -2)]

def rawRow17350 : Integer.Sparse Key := [(key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2133, 2), (key2133, 2), (key2133, 2), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2046, -2), (key2046, -2), (key2046, -2), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2128, 2), (key2128, 2), (key2128, 2), (key2043, -2), (key2043, -2), (key2043, -2)]

def rawRow17351 : Integer.Sparse Key := [(key2017, 2), (key2137, 2), (key2142, 2), (key2022, -1), (key2024, -1), (key2137, -1), (key2142, -1), (key2172, -1), (key2173, -1), (key2017, 2), (key2137, 2), (key2142, 2), (key2050, -1), (key2053, -1), (key2137, -1), (key2142, -1), (key2264, -1), (key2265, -1), (key2022, -1), (key2024, -1), (key2137, -1), (key2142, -1), (key2172, -1), (key2173, -1), (key2050, -1), (key2053, -1), (key2137, -1), (key2142, -1), (key2264, -1), (key2265, -1), (key2075, 2), (key2076, 2), (key2172, 2), (key2173, 2), (key2264, 2), (key2265, 2)]

def rawRow17352 : Integer.Sparse Key := [(key2017, 2), (key2142, 2), (key2137, 2), (key2024, -1), (key2022, -1), (key2142, -1), (key2137, -1), (key2173, -1), (key2172, -1), (key2017, 2), (key2142, 2), (key2137, 2), (key2053, -1), (key2050, -1), (key2142, -1), (key2137, -1), (key2265, -1), (key2264, -1), (key2024, -1), (key2022, -1), (key2142, -1), (key2137, -1), (key2173, -1), (key2172, -1), (key2053, -1), (key2050, -1), (key2142, -1), (key2137, -1), (key2265, -1), (key2264, -1), (key2076, 2), (key2075, 2), (key2173, 2), (key2172, 2), (key2265, 2), (key2264, 2)]

def rawRow17353 : Integer.Sparse Key := [(key2137, 2), (key2017, 2), (key2142, 2), (key2137, -1), (key2172, -1), (key2022, -1), (key2173, -1), (key2024, -1), (key2142, -1), (key2137, 2), (key2017, 2), (key2142, 2), (key2137, -1), (key2264, -1), (key2050, -1), (key2265, -1), (key2053, -1), (key2142, -1), (key2137, -1), (key2172, -1), (key2022, -1), (key2173, -1), (key2024, -1), (key2142, -1), (key2137, -1), (key2264, -1), (key2050, -1), (key2265, -1), (key2053, -1), (key2142, -1), (key2172, 2), (key2264, 2), (key2075, 2), (key2265, 2), (key2076, 2), (key2173, 2)]

def rawRow17354 : Integer.Sparse Key := [(key2137, 2), (key2142, 2), (key2017, 2), (key2172, -1), (key2137, -1), (key2173, -1), (key2022, -1), (key2142, -1), (key2024, -1), (key2137, 2), (key2142, 2), (key2017, 2), (key2264, -1), (key2137, -1), (key2265, -1), (key2050, -1), (key2142, -1), (key2053, -1), (key2172, -1), (key2137, -1), (key2173, -1), (key2022, -1), (key2142, -1), (key2024, -1), (key2264, -1), (key2137, -1), (key2265, -1), (key2050, -1), (key2142, -1), (key2053, -1), (key2264, 2), (key2172, 2), (key2265, 2), (key2075, 2), (key2173, 2), (key2076, 2)]

def rawRow17355 : Integer.Sparse Key := [(key2142, 2), (key2017, 2), (key2137, 2), (key2142, -1), (key2173, -1), (key2024, -1), (key2172, -1), (key2022, -1), (key2137, -1), (key2142, 2), (key2017, 2), (key2137, 2), (key2142, -1), (key2265, -1), (key2053, -1), (key2264, -1), (key2050, -1), (key2137, -1), (key2142, -1), (key2173, -1), (key2024, -1), (key2172, -1), (key2022, -1), (key2137, -1), (key2142, -1), (key2265, -1), (key2053, -1), (key2264, -1), (key2050, -1), (key2137, -1), (key2173, 2), (key2265, 2), (key2076, 2), (key2264, 2), (key2075, 2), (key2172, 2)]

def rawRow17356 : Integer.Sparse Key := [(key2142, 2), (key2137, 2), (key2017, 2), (key2173, -1), (key2142, -1), (key2172, -1), (key2024, -1), (key2137, -1), (key2022, -1), (key2142, 2), (key2137, 2), (key2017, 2), (key2265, -1), (key2142, -1), (key2264, -1), (key2053, -1), (key2137, -1), (key2050, -1), (key2173, -1), (key2142, -1), (key2172, -1), (key2024, -1), (key2137, -1), (key2022, -1), (key2265, -1), (key2142, -1), (key2264, -1), (key2053, -1), (key2137, -1), (key2050, -1), (key2265, 2), (key2173, 2), (key2264, 2), (key2076, 2), (key2172, 2), (key2075, 2)]

def rawRow17357 : Integer.Sparse Key := [(key2022, 2), (key2022, 2), (key2173, 2), (key2017, -1), (key2024, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2142, -1), (key2050, 2), (key2050, 2), (key2265, 2), (key2017, -1), (key2053, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2142, -1), (key2050, -1), (key2075, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2265, -1), (key2022, -1), (key2076, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2173, -1), (key2024, 2), (key2053, 2), (key2024, 2), (key2142, 2), (key2053, 2), (key2142, 2)]

def rawRow17358 : Integer.Sparse Key := [(key2022, 2), (key2173, 2), (key2022, 2), (key2024, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2050, 2), (key2265, 2), (key2050, 2), (key2053, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2075, -1), (key2050, -1), (key2265, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2076, -1), (key2022, -1), (key2173, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2053, 2), (key2024, 2), (key2142, 2), (key2024, 2), (key2142, 2), (key2053, 2)]

def rawRow17359 : Integer.Sparse Key := [(key2173, 2), (key2022, 2), (key2022, 2), (key2142, -1), (key2142, -1), (key2024, -1), (key2024, -1), (key2017, -1), (key2017, -1), (key2265, 2), (key2050, 2), (key2050, 2), (key2142, -1), (key2142, -1), (key2053, -1), (key2053, -1), (key2017, -1), (key2017, -1), (key2265, -1), (key2265, -1), (key2075, -1), (key2075, -1), (key2050, -1), (key2050, -1), (key2173, -1), (key2173, -1), (key2076, -1), (key2076, -1), (key2022, -1), (key2022, -1), (key2142, 2), (key2142, 2), (key2053, 2), (key2053, 2), (key2024, 2), (key2024, 2)]

def rawRow17360 : Integer.Sparse Key := [(key2024, 2), (key2024, 2), (key2172, 2), (key2017, -1), (key2022, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2137, -1), (key2053, 2), (key2053, 2), (key2264, 2), (key2017, -1), (key2050, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2137, -1), (key2053, -1), (key2076, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2264, -1), (key2024, -1), (key2075, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2172, -1), (key2022, 2), (key2050, 2), (key2022, 2), (key2137, 2), (key2050, 2), (key2137, 2)]

def rawRow17361 : Integer.Sparse Key := [(key2024, 2), (key2172, 2), (key2024, 2), (key2022, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2053, 2), (key2264, 2), (key2053, 2), (key2050, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2076, -1), (key2053, -1), (key2264, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2075, -1), (key2024, -1), (key2172, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2050, 2), (key2022, 2), (key2137, 2), (key2022, 2), (key2137, 2), (key2050, 2)]

def rawRow17362 : Integer.Sparse Key := [(key2172, 2), (key2024, 2), (key2024, 2), (key2137, -1), (key2137, -1), (key2022, -1), (key2022, -1), (key2017, -1), (key2017, -1), (key2264, 2), (key2053, 2), (key2053, 2), (key2137, -1), (key2137, -1), (key2050, -1), (key2050, -1), (key2017, -1), (key2017, -1), (key2264, -1), (key2264, -1), (key2076, -1), (key2076, -1), (key2053, -1), (key2053, -1), (key2172, -1), (key2172, -1), (key2075, -1), (key2075, -1), (key2024, -1), (key2024, -1), (key2137, 2), (key2137, 2), (key2050, 2), (key2050, 2), (key2022, 2), (key2022, 2)]

def rawRow17363 : Integer.Sparse Key := [(key2050, 2), (key2050, 2), (key2265, 2), (key2050, -1), (key2075, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2265, -1), (key2022, 2), (key2022, 2), (key2173, 2), (key2022, -1), (key2076, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2173, -1), (key2017, -1), (key2024, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2142, -1), (key2017, -1), (key2053, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2142, -1), (key2024, 2), (key2053, 2), (key2024, 2), (key2142, 2), (key2053, 2), (key2142, 2)]

def rawRow17364 : Integer.Sparse Key := [(key2050, 2), (key2265, 2), (key2050, 2), (key2075, -1), (key2050, -1), (key2265, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2022, 2), (key2173, 2), (key2022, 2), (key2076, -1), (key2022, -1), (key2173, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2024, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2053, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2053, 2), (key2024, 2), (key2142, 2), (key2024, 2), (key2142, 2), (key2053, 2)]

def rawRow17365 : Integer.Sparse Key := [(key2265, 2), (key2050, 2), (key2050, 2), (key2265, -1), (key2265, -1), (key2075, -1), (key2075, -1), (key2050, -1), (key2050, -1), (key2173, 2), (key2022, 2), (key2022, 2), (key2173, -1), (key2173, -1), (key2076, -1), (key2076, -1), (key2022, -1), (key2022, -1), (key2142, -1), (key2142, -1), (key2024, -1), (key2024, -1), (key2017, -1), (key2017, -1), (key2142, -1), (key2142, -1), (key2053, -1), (key2053, -1), (key2017, -1), (key2017, -1), (key2142, 2), (key2142, 2), (key2053, 2), (key2053, 2), (key2024, 2), (key2024, 2)]

def rawRow17366 : Integer.Sparse Key := [(key2075, 2), (key2075, 2), (key2075, 2), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2076, 2), (key2076, 2), (key2076, 2), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2)]

def rawRow17367 : Integer.Sparse Key := [(key2053, 2), (key2053, 2), (key2264, 2), (key2053, -1), (key2076, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2264, -1), (key2024, 2), (key2024, 2), (key2172, 2), (key2024, -1), (key2075, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2172, -1), (key2017, -1), (key2022, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2137, -1), (key2017, -1), (key2050, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2137, -1), (key2022, 2), (key2050, 2), (key2022, 2), (key2137, 2), (key2050, 2), (key2137, 2)]

def rawRow17368 : Integer.Sparse Key := [(key2053, 2), (key2264, 2), (key2053, 2), (key2076, -1), (key2053, -1), (key2264, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2024, 2), (key2172, 2), (key2024, 2), (key2075, -1), (key2024, -1), (key2172, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2022, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2050, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2050, 2), (key2022, 2), (key2137, 2), (key2022, 2), (key2137, 2), (key2050, 2)]

def rawRow17369 : Integer.Sparse Key := [(key2264, 2), (key2053, 2), (key2053, 2), (key2264, -1), (key2264, -1), (key2076, -1), (key2076, -1), (key2053, -1), (key2053, -1), (key2172, 2), (key2024, 2), (key2024, 2), (key2172, -1), (key2172, -1), (key2075, -1), (key2075, -1), (key2024, -1), (key2024, -1), (key2137, -1), (key2137, -1), (key2022, -1), (key2022, -1), (key2017, -1), (key2017, -1), (key2137, -1), (key2137, -1), (key2050, -1), (key2050, -1), (key2017, -1), (key2017, -1), (key2137, 2), (key2137, 2), (key2050, 2), (key2050, 2), (key2022, 2), (key2022, 2)]

def rawRow17370 : Integer.Sparse Key := [(key2076, 2), (key2076, 2), (key2076, 2), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2075, 2), (key2075, 2), (key2075, 2), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2)]

def rawRow17371 : Integer.Sparse Key := [(key770, 4), (key774, 4), (key783, 4), (key770, -2), (key774, -2), (key797, -2), (key834, -2), (key808, -2), (key837, -2), (key770, -2), (key774, -2), (key797, -2), (key834, -2), (key808, -2), (key837, -2), (key797, 4), (key834, 4), (key932, 4)]

def rawRow17372 : Integer.Sparse Key := [(key774, 4), (key770, 4), (key783, 4), (key774, -2), (key770, -2), (key834, -2), (key797, -2), (key837, -2), (key808, -2), (key774, -2), (key770, -2), (key834, -2), (key797, -2), (key837, -2), (key808, -2), (key834, 4), (key797, 4), (key932, 4)]

def rawRow17373 : Integer.Sparse Key := [(key770, 4), (key783, 4), (key774, 4), (key797, -2), (key808, -2), (key770, -2), (key837, -2), (key774, -2), (key834, -2), (key797, -2), (key808, -2), (key770, -2), (key837, -2), (key774, -2), (key834, -2), (key797, 4), (key932, 4), (key834, 4)]

def rawRow17374 : Integer.Sparse Key := [(key783, 4), (key770, 4), (key774, 4), (key808, -2), (key797, -2), (key837, -2), (key770, -2), (key834, -2), (key774, -2), (key808, -2), (key797, -2), (key837, -2), (key770, -2), (key834, -2), (key774, -2), (key932, 4), (key797, 4), (key834, 4)]

def rawRow17375 : Integer.Sparse Key := [(key774, 4), (key783, 4), (key770, 4), (key834, -2), (key837, -2), (key774, -2), (key808, -2), (key770, -2), (key797, -2), (key834, -2), (key837, -2), (key774, -2), (key808, -2), (key770, -2), (key797, -2), (key834, 4), (key932, 4), (key797, 4)]

def rawRow17376 : Integer.Sparse Key := [(key783, 4), (key774, 4), (key770, 4), (key837, -2), (key834, -2), (key808, -2), (key774, -2), (key797, -2), (key770, -2), (key837, -2), (key834, -2), (key808, -2), (key774, -2), (key797, -2), (key770, -2), (key932, 4), (key834, 4), (key797, 4)]

def rawRow17377 : Integer.Sparse Key := [(key797, 4), (key808, 4), (key808, 4), (key770, -2), (key783, -2), (key770, -2), (key837, -2), (key783, -2), (key837, -2), (key797, -2), (key808, -2), (key797, -2), (key932, -2), (key808, -2), (key932, -2), (key770, 4), (key837, 4), (key837, 4)]

def rawRow17378 : Integer.Sparse Key := [(key808, 4), (key797, 4), (key808, 4), (key783, -2), (key770, -2), (key837, -2), (key770, -2), (key837, -2), (key783, -2), (key808, -2), (key797, -2), (key932, -2), (key797, -2), (key932, -2), (key808, -2), (key837, 4), (key770, 4), (key837, 4)]

def rawRow17379 : Integer.Sparse Key := [(key808, 4), (key808, 4), (key797, 4), (key837, -2), (key837, -2), (key783, -2), (key783, -2), (key770, -2), (key770, -2), (key932, -2), (key932, -2), (key808, -2), (key808, -2), (key797, -2), (key797, -2), (key837, 4), (key837, 4), (key770, 4)]

def rawRow17380 : Integer.Sparse Key := [(key834, 4), (key837, 4), (key837, 4), (key774, -2), (key783, -2), (key774, -2), (key808, -2), (key783, -2), (key808, -2), (key834, -2), (key837, -2), (key834, -2), (key932, -2), (key837, -2), (key932, -2), (key774, 4), (key808, 4), (key808, 4)]

def rawRow17381 : Integer.Sparse Key := [(key837, 4), (key834, 4), (key837, 4), (key783, -2), (key774, -2), (key808, -2), (key774, -2), (key808, -2), (key783, -2), (key837, -2), (key834, -2), (key932, -2), (key834, -2), (key932, -2), (key837, -2), (key808, 4), (key774, 4), (key808, 4)]

def rawRow17382 : Integer.Sparse Key := [(key837, 4), (key837, 4), (key834, 4), (key808, -2), (key808, -2), (key783, -2), (key783, -2), (key774, -2), (key774, -2), (key932, -2), (key932, -2), (key837, -2), (key837, -2), (key834, -2), (key834, -2), (key808, 4), (key808, 4), (key774, 4)]

def rawRow17383 : Integer.Sparse Key := [(key797, 4), (key808, 4), (key808, 4), (key797, -2), (key808, -2), (key797, -2), (key932, -2), (key808, -2), (key932, -2), (key770, -2), (key783, -2), (key770, -2), (key837, -2), (key783, -2), (key837, -2), (key770, 4), (key837, 4), (key837, 4)]

def rawRow17384 : Integer.Sparse Key := [(key808, 4), (key797, 4), (key808, 4), (key808, -2), (key797, -2), (key932, -2), (key797, -2), (key932, -2), (key808, -2), (key783, -2), (key770, -2), (key837, -2), (key770, -2), (key837, -2), (key783, -2), (key837, 4), (key770, 4), (key837, 4)]

def rawRow17385 : Integer.Sparse Key := [(key808, 4), (key808, 4), (key797, 4), (key932, -2), (key932, -2), (key808, -2), (key808, -2), (key797, -2), (key797, -2), (key837, -2), (key837, -2), (key783, -2), (key783, -2), (key770, -2), (key770, -2), (key837, 4), (key837, 4), (key770, 4)]

def rawRow17386 : Integer.Sparse Key := [(key932, 4), (key932, 4), (key932, 4), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key783, 4), (key783, 4), (key783, 4)]

def rawRow17387 : Integer.Sparse Key := [(key834, 4), (key837, 4), (key837, 4), (key834, -2), (key837, -2), (key834, -2), (key932, -2), (key837, -2), (key932, -2), (key774, -2), (key783, -2), (key774, -2), (key808, -2), (key783, -2), (key808, -2), (key774, 4), (key808, 4), (key808, 4)]

def rawRow17388 : Integer.Sparse Key := [(key837, 4), (key834, 4), (key837, 4), (key837, -2), (key834, -2), (key932, -2), (key834, -2), (key932, -2), (key837, -2), (key783, -2), (key774, -2), (key808, -2), (key774, -2), (key808, -2), (key783, -2), (key808, 4), (key774, 4), (key808, 4)]

def rawRow17389 : Integer.Sparse Key := [(key837, 4), (key837, 4), (key834, 4), (key932, -2), (key932, -2), (key837, -2), (key837, -2), (key834, -2), (key834, -2), (key808, -2), (key808, -2), (key783, -2), (key783, -2), (key774, -2), (key774, -2), (key808, 4), (key808, 4), (key774, 4)]

def rawRow17390 : Integer.Sparse Key := [(key932, 4), (key932, 4), (key932, 4), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key783, 4), (key783, 4), (key783, 4)]

def rawRow17391 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key761, 2), (key766, 2), (key793, 2), (key768, 2), (key769, 2), (key793, 2), (key761, 2), (key766, 2), (key793, 2), (key793, -6), (key768, 2), (key769, 2), (key793, 2), (key793, -6)]

def rawRow17392 : Integer.Sparse Key := [(key759, -2), (key757, -2), (key766, -2), (key761, -2), (key769, -2), (key768, -2), (key766, 2), (key761, 2), (key793, 2), (key769, 2), (key768, 2), (key793, 2), (key766, 2), (key761, 2), (key793, 2), (key793, -6), (key769, 2), (key768, 2), (key793, 2), (key793, -6)]

def rawRow17393 : Integer.Sparse Key := [(key761, -2), (key766, -2), (key757, -2), (key769, -2), (key759, -2), (key766, -2), (key761, 2), (key793, 2), (key766, 2), (key768, 2), (key793, 2), (key769, 2), (key761, 2), (key793, 2), (key766, 2), (key793, -6), (key768, 2), (key793, 2), (key769, 2), (key793, -6)]

def rawRow17394 : Integer.Sparse Key := [(key766, -2), (key761, -2), (key769, -2), (key757, -2), (key766, -2), (key759, -2), (key793, 2), (key761, 2), (key766, 2), (key793, 2), (key768, 2), (key769, 2), (key793, 2), (key761, 2), (key766, 2), (key793, -6), (key793, 2), (key768, 2), (key769, 2), (key793, -6)]

def rawRow17395 : Integer.Sparse Key := [(key768, -2), (key769, -2), (key759, -2), (key766, -2), (key757, -2), (key761, -2), (key766, 2), (key793, 2), (key761, 2), (key769, 2), (key793, 2), (key768, 2), (key766, 2), (key793, 2), (key761, 2), (key793, -6), (key769, 2), (key793, 2), (key768, 2), (key793, -6)]

def rawRow17396 : Integer.Sparse Key := [(key769, -2), (key768, -2), (key766, -2), (key759, -2), (key761, -2), (key757, -2), (key793, 2), (key766, 2), (key761, 2), (key793, 2), (key769, 2), (key768, 2), (key793, 2), (key766, 2), (key761, 2), (key793, -6), (key793, 2), (key769, 2), (key768, 2), (key793, -6)]

def rawRow17397 : Integer.Sparse Key := [(key761, -2), (key766, -2), (key761, -2), (key793, -2), (key766, -2), (key793, -2), (key757, 2), (key769, 2), (key769, 2), (key759, 2), (key766, 2), (key766, 2), (key761, 2), (key793, 2), (key793, 2), (key766, -6), (key768, 2), (key793, 2), (key793, 2), (key769, -6)]

def rawRow17398 : Integer.Sparse Key := [(key766, -2), (key761, -2), (key793, -2), (key761, -2), (key793, -2), (key766, -2), (key769, 2), (key757, 2), (key769, 2), (key766, 2), (key759, 2), (key766, 2), (key793, 2), (key761, 2), (key793, 2), (key766, -6), (key793, 2), (key768, 2), (key793, 2), (key769, -6)]

def rawRow17399 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key766, -2), (key766, -2), (key761, -2), (key761, -2), (key769, 2), (key769, 2), (key757, 2), (key766, 2), (key766, 2), (key759, 2), (key793, 2), (key793, 2), (key761, 2), (key766, -6), (key793, 2), (key793, 2), (key768, 2), (key769, -6)]

def rawRow17400 : Integer.Sparse Key := [(key768, -2), (key769, -2), (key768, -2), (key793, -2), (key769, -2), (key793, -2), (key759, 2), (key766, 2), (key766, 2), (key757, 2), (key761, 2), (key761, 2), (key766, 2), (key793, 2), (key793, 2), (key761, -6), (key769, 2), (key793, 2), (key793, 2), (key768, -6)]

def rawRow17401 : Integer.Sparse Key := [(key769, -2), (key768, -2), (key793, -2), (key768, -2), (key793, -2), (key769, -2), (key766, 2), (key759, 2), (key766, 2), (key761, 2), (key757, 2), (key761, 2), (key793, 2), (key766, 2), (key793, 2), (key761, -6), (key793, 2), (key769, 2), (key793, 2), (key768, -6)]

def rawRow17402 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key769, -2), (key769, -2), (key768, -2), (key768, -2), (key766, 2), (key766, 2), (key759, 2), (key761, 2), (key761, 2), (key757, 2), (key793, 2), (key793, 2), (key766, 2), (key761, -6), (key793, 2), (key793, 2), (key769, 2), (key768, -6)]

def rawRow17403 : Integer.Sparse Key := [(key761, -2), (key766, -2), (key761, -2), (key793, -2), (key766, -2), (key793, -2), (key761, 2), (key793, 2), (key793, 2), (key766, 2), (key793, 2), (key793, 2), (key757, 2), (key769, 2), (key769, 2), (key769, -6), (key759, 2), (key766, 2), (key766, 2), (key766, -6)]

def rawRow17404 : Integer.Sparse Key := [(key766, -2), (key761, -2), (key793, -2), (key761, -2), (key793, -2), (key766, -2), (key793, 2), (key761, 2), (key793, 2), (key793, 2), (key766, 2), (key793, 2), (key769, 2), (key757, 2), (key769, 2), (key769, -6), (key766, 2), (key759, 2), (key766, 2), (key766, -6)]

def rawRow17405 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key766, -2), (key766, -2), (key761, -2), (key761, -2), (key793, 2), (key793, 2), (key761, 2), (key793, 2), (key793, 2), (key766, 2), (key769, 2), (key769, 2), (key757, 2), (key769, -6), (key766, 2), (key766, 2), (key759, 2), (key766, -6)]

def rawRow17406 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key766, 2), (key766, 2), (key766, 2), (key761, 2), (key761, 2), (key761, 2), (key769, 2), (key769, 2), (key769, 2), (key757, -6), (key766, 2), (key766, 2), (key766, 2), (key759, -6)]

def rawRow17407 : Integer.Sparse Key := [(key768, -2), (key769, -2), (key768, -2), (key793, -2), (key769, -2), (key793, -2), (key768, 2), (key793, 2), (key793, 2), (key769, 2), (key793, 2), (key793, 2), (key759, 2), (key766, 2), (key766, 2), (key766, -6), (key757, 2), (key761, 2), (key761, 2), (key761, -6)]

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

def rawRow17408 : Integer.Sparse Key := [(key769, -2), (key768, -2), (key793, -2), (key768, -2), (key793, -2), (key769, -2), (key793, 2), (key768, 2), (key793, 2), (key793, 2), (key769, 2), (key793, 2), (key766, 2), (key759, 2), (key766, 2), (key766, -6), (key761, 2), (key757, 2), (key761, 2), (key761, -6)]

def rawRow17409 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key769, -2), (key769, -2), (key768, -2), (key768, -2), (key793, 2), (key793, 2), (key768, 2), (key793, 2), (key793, 2), (key769, 2), (key766, 2), (key766, 2), (key759, 2), (key766, -6), (key761, 2), (key761, 2), (key757, 2), (key761, -6)]

def rawRow17410 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key769, 2), (key769, 2), (key769, 2), (key768, 2), (key768, 2), (key768, 2), (key766, 2), (key766, 2), (key766, 2), (key759, -6), (key761, 2), (key761, 2), (key761, 2), (key757, -6)]

def rawRow17411 : Integer.Sparse Key := [(key1854, 4), (key1887, 4), (key1887, 4), (key1856, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1890, -2), (key1890, -2), (key1856, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1890, -2), (key1890, -2), (key1858, 4), (key1890, 4), (key1890, 4)]

def rawRow17412 : Integer.Sparse Key := [(key1887, 4), (key1854, 4), (key1887, 4), (key1887, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1890, 4), (key1858, 4), (key1890, 4)]

def rawRow17413 : Integer.Sparse Key := [(key1887, 4), (key1887, 4), (key1854, 4), (key1890, -2), (key1887, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1856, -2), (key1890, -2), (key1887, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1856, -2), (key1890, 4), (key1890, 4), (key1858, 4)]

def rawRow17414 : Integer.Sparse Key := [(key1856, 4), (key1856, 4), (key1890, 4), (key1854, -2), (key1856, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1887, -2), (key1856, -2), (key1858, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1890, -2), (key1856, 4), (key1856, 4), (key1887, 4)]

def rawRow17415 : Integer.Sparse Key := [(key1856, 4), (key1890, 4), (key1856, 4), (key1856, -2), (key1854, -2), (key1887, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1858, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1856, 4), (key1887, 4), (key1856, 4)]

def rawRow17416 : Integer.Sparse Key := [(key1890, 4), (key1856, 4), (key1856, 4), (key1887, -2), (key1887, -2), (key1856, -2), (key1856, -2), (key1854, -2), (key1854, -2), (key1890, -2), (key1890, -2), (key1858, -2), (key1858, -2), (key1856, -2), (key1856, -2), (key1887, 4), (key1856, 4), (key1856, 4)]

def rawRow17417 : Integer.Sparse Key := [(key1856, 4), (key1856, 4), (key1890, 4), (key1856, -2), (key1858, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1890, -2), (key1854, -2), (key1856, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1887, -2), (key1856, 4), (key1856, 4), (key1887, 4)]

def rawRow17418 : Integer.Sparse Key := [(key1856, 4), (key1890, 4), (key1856, 4), (key1858, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1856, -2), (key1854, -2), (key1887, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1856, 4), (key1887, 4), (key1856, 4)]

def rawRow17419 : Integer.Sparse Key := [(key1890, 4), (key1856, 4), (key1856, 4), (key1890, -2), (key1890, -2), (key1858, -2), (key1858, -2), (key1856, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1856, -2), (key1856, -2), (key1854, -2), (key1854, -2), (key1887, 4), (key1856, 4), (key1856, 4)]

def rawRow17420 : Integer.Sparse Key := [(key1858, 4), (key1858, 4), (key1858, 4), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1854, 4), (key1854, 4), (key1854, 4)]

def rawRow17421 : Integer.Sparse Key := [(key620, -2), (key620, -2), (key624, -2), (key624, 6), (key620, -2), (key620, -2), (key624, -2), (key620, 2), (key620, 2), (key646, 2), (key646, 2), (key652, 2), (key652, 2), (key624, -2), (key652, -2), (key652, -2), (key624, 6), (key624, -2), (key652, -2), (key652, -2)]

def rawRow17422 : Integer.Sparse Key := [(key620, -2), (key624, -2), (key620, -2), (key624, 6), (key620, -2), (key624, -2), (key620, -2), (key646, 2), (key652, 2), (key620, 2), (key652, 2), (key620, 2), (key646, 2), (key652, -2), (key624, -2), (key652, -2), (key624, 6), (key652, -2), (key624, -2), (key652, -2)]

def rawRow17423 : Integer.Sparse Key := [(key624, -2), (key620, -2), (key620, -2), (key624, 6), (key624, -2), (key620, -2), (key620, -2), (key652, 2), (key646, 2), (key652, 2), (key620, 2), (key646, 2), (key620, 2), (key652, -2), (key652, -2), (key624, -2), (key624, 6), (key652, -2), (key652, -2), (key624, -2)]

def rawRow17424 : Integer.Sparse Key := [(key620, -2), (key624, -2), (key624, -2), (key620, 6), (key646, -2), (key652, -2), (key652, -2), (key620, 2), (key624, 2), (key620, 2), (key652, 2), (key624, 2), (key652, 2), (key620, -2), (key620, -2), (key646, -2), (key652, 6), (key624, -2), (key624, -2), (key652, -2)]

def rawRow17425 : Integer.Sparse Key := [(key624, -2), (key620, -2), (key624, -2), (key620, 6), (key652, -2), (key646, -2), (key652, -2), (key624, 2), (key620, 2), (key652, 2), (key620, 2), (key652, 2), (key624, 2), (key620, -2), (key646, -2), (key620, -2), (key652, 6), (key624, -2), (key652, -2), (key624, -2)]

def rawRow17426 : Integer.Sparse Key := [(key624, -2), (key624, -2), (key620, -2), (key620, 6), (key652, -2), (key652, -2), (key646, -2), (key652, 2), (key652, 2), (key624, 2), (key624, 2), (key620, 2), (key620, 2), (key646, -2), (key620, -2), (key620, -2), (key652, 6), (key652, -2), (key624, -2), (key624, -2)]

def rawRow17427 : Integer.Sparse Key := [(key646, -2), (key652, -2), (key652, -2), (key652, 6), (key620, -2), (key624, -2), (key624, -2), (key620, 2), (key624, 2), (key620, 2), (key652, 2), (key624, 2), (key652, 2), (key624, -2), (key624, -2), (key652, -2), (key620, 6), (key620, -2), (key620, -2), (key646, -2)]

def rawRow17428 : Integer.Sparse Key := [(key652, -2), (key646, -2), (key652, -2), (key652, 6), (key624, -2), (key620, -2), (key624, -2), (key624, 2), (key620, 2), (key652, 2), (key620, 2), (key652, 2), (key624, 2), (key624, -2), (key652, -2), (key624, -2), (key620, 6), (key620, -2), (key646, -2), (key620, -2)]

def rawRow17429 : Integer.Sparse Key := [(key652, -2), (key652, -2), (key646, -2), (key652, 6), (key624, -2), (key624, -2), (key620, -2), (key652, 2), (key652, 2), (key624, 2), (key624, 2), (key620, 2), (key620, 2), (key652, -2), (key624, -2), (key624, -2), (key620, 6), (key646, -2), (key620, -2), (key620, -2)]

def rawRow17430 : Integer.Sparse Key := [(key652, -2), (key652, -2), (key652, -2), (key646, 6), (key652, -2), (key652, -2), (key652, -2), (key624, 2), (key624, 2), (key624, 2), (key624, 2), (key624, 2), (key624, 2), (key620, -2), (key620, -2), (key620, -2), (key646, 6), (key620, -2), (key620, -2), (key620, -2)]

def rawRow17431 : Integer.Sparse Key := [(key1853, -2), (key1853, -2), (key1857, -2), (key1857, 6), (key1853, -2), (key1853, -2), (key1857, -2), (key1853, 2), (key1853, 2), (key1885, 2), (key1885, 2), (key1888, 2), (key1888, 2), (key1857, -2), (key1888, -2), (key1888, -2), (key1857, 6), (key1857, -2), (key1888, -2), (key1888, -2)]

def rawRow17432 : Integer.Sparse Key := [(key1853, -2), (key1857, -2), (key1853, -2), (key1857, 6), (key1853, -2), (key1857, -2), (key1853, -2), (key1885, 2), (key1888, 2), (key1853, 2), (key1888, 2), (key1853, 2), (key1885, 2), (key1888, -2), (key1857, -2), (key1888, -2), (key1857, 6), (key1888, -2), (key1857, -2), (key1888, -2)]

def rawRow17433 : Integer.Sparse Key := [(key1857, -2), (key1853, -2), (key1853, -2), (key1857, 6), (key1857, -2), (key1853, -2), (key1853, -2), (key1888, 2), (key1885, 2), (key1888, 2), (key1853, 2), (key1885, 2), (key1853, 2), (key1888, -2), (key1888, -2), (key1857, -2), (key1857, 6), (key1888, -2), (key1888, -2), (key1857, -2)]

def rawRow17434 : Integer.Sparse Key := [(key1853, -2), (key1857, -2), (key1857, -2), (key1853, 6), (key1885, -2), (key1888, -2), (key1888, -2), (key1853, 2), (key1857, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1888, 2), (key1853, -2), (key1853, -2), (key1885, -2), (key1888, 6), (key1857, -2), (key1857, -2), (key1888, -2)]

def rawRow17435 : Integer.Sparse Key := [(key1857, -2), (key1853, -2), (key1857, -2), (key1853, 6), (key1888, -2), (key1885, -2), (key1888, -2), (key1857, 2), (key1853, 2), (key1888, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1853, -2), (key1885, -2), (key1853, -2), (key1888, 6), (key1857, -2), (key1888, -2), (key1857, -2)]

def rawRow17436 : Integer.Sparse Key := [(key1857, -2), (key1857, -2), (key1853, -2), (key1853, 6), (key1888, -2), (key1888, -2), (key1885, -2), (key1888, 2), (key1888, 2), (key1857, 2), (key1857, 2), (key1853, 2), (key1853, 2), (key1885, -2), (key1853, -2), (key1853, -2), (key1888, 6), (key1888, -2), (key1857, -2), (key1857, -2)]

def rawRow17437 : Integer.Sparse Key := [(key1885, -2), (key1888, -2), (key1888, -2), (key1888, 6), (key1853, -2), (key1857, -2), (key1857, -2), (key1853, 2), (key1857, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1888, 2), (key1857, -2), (key1857, -2), (key1888, -2), (key1853, 6), (key1853, -2), (key1853, -2), (key1885, -2)]

def rawRow17438 : Integer.Sparse Key := [(key1888, -2), (key1885, -2), (key1888, -2), (key1888, 6), (key1857, -2), (key1853, -2), (key1857, -2), (key1857, 2), (key1853, 2), (key1888, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1857, -2), (key1888, -2), (key1857, -2), (key1853, 6), (key1853, -2), (key1885, -2), (key1853, -2)]

def rawRow17439 : Integer.Sparse Key := [(key1888, -2), (key1888, -2), (key1885, -2), (key1888, 6), (key1857, -2), (key1857, -2), (key1853, -2), (key1888, 2), (key1888, 2), (key1857, 2), (key1857, 2), (key1853, 2), (key1853, 2), (key1888, -2), (key1857, -2), (key1857, -2), (key1853, 6), (key1885, -2), (key1853, -2), (key1853, -2)]

def rawRow17440 : Integer.Sparse Key := [(key1888, -2), (key1888, -2), (key1888, -2), (key1885, 6), (key1888, -2), (key1888, -2), (key1888, -2), (key1857, 2), (key1857, 2), (key1857, 2), (key1857, 2), (key1857, 2), (key1857, 2), (key1853, -2), (key1853, -2), (key1853, -2), (key1885, 6), (key1853, -2), (key1853, -2), (key1853, -2)]

def rawRow17441 : Integer.Sparse Key := [(key1959, 6), (key1959, -2), (key1961, -2), (key1961, -2), (key1959, 6), (key1959, -2), (key1967, -2), (key1967, -2), (key1959, -2), (key1961, -2), (key1961, -2), (key1959, -2), (key1967, -2), (key1967, -2), (key1961, 2), (key1961, 2), (key1967, 2), (key1967, 2), (key1970, 2), (key1970, 2)]

def rawRow17442 : Integer.Sparse Key := [(key1959, 6), (key1961, -2), (key1959, -2), (key1961, -2), (key1959, 6), (key1967, -2), (key1959, -2), (key1967, -2), (key1961, -2), (key1959, -2), (key1961, -2), (key1967, -2), (key1959, -2), (key1967, -2), (key1967, 2), (key1970, 2), (key1961, 2), (key1970, 2), (key1961, 2), (key1967, 2)]

def rawRow17443 : Integer.Sparse Key := [(key1959, 6), (key1961, -2), (key1961, -2), (key1959, -2), (key1959, 6), (key1967, -2), (key1967, -2), (key1959, -2), (key1961, -2), (key1961, -2), (key1959, -2), (key1967, -2), (key1967, -2), (key1959, -2), (key1970, 2), (key1967, 2), (key1970, 2), (key1961, 2), (key1967, 2), (key1961, 2)]

def rawRow17444 : Integer.Sparse Key := [(key1961, 6), (key1959, -2), (key1959, -2), (key1961, -2), (key1967, 6), (key1959, -2), (key1959, -2), (key1967, -2), (key1967, -2), (key1967, -2), (key1970, -2), (key1961, -2), (key1961, -2), (key1970, -2), (key1959, 2), (key1961, 2), (key1959, 2), (key1967, 2), (key1961, 2), (key1967, 2)]

def rawRow17445 : Integer.Sparse Key := [(key1961, 6), (key1959, -2), (key1961, -2), (key1959, -2), (key1967, 6), (key1959, -2), (key1967, -2), (key1959, -2), (key1967, -2), (key1970, -2), (key1967, -2), (key1961, -2), (key1970, -2), (key1961, -2), (key1961, 2), (key1959, 2), (key1967, 2), (key1959, 2), (key1967, 2), (key1961, 2)]

def rawRow17446 : Integer.Sparse Key := [(key1961, 6), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, 6), (key1967, -2), (key1959, -2), (key1959, -2), (key1970, -2), (key1967, -2), (key1967, -2), (key1970, -2), (key1961, -2), (key1961, -2), (key1967, 2), (key1967, 2), (key1961, 2), (key1961, 2), (key1959, 2), (key1959, 2)]

def rawRow17447 : Integer.Sparse Key := [(key1967, 6), (key1967, -2), (key1967, -2), (key1970, -2), (key1961, 6), (key1961, -2), (key1961, -2), (key1970, -2), (key1959, -2), (key1959, -2), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, -2), (key1959, 2), (key1961, 2), (key1959, 2), (key1967, 2), (key1961, 2), (key1967, 2)]

def rawRow17448 : Integer.Sparse Key := [(key1967, 6), (key1967, -2), (key1970, -2), (key1967, -2), (key1961, 6), (key1961, -2), (key1970, -2), (key1961, -2), (key1959, -2), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, -2), (key1959, -2), (key1961, 2), (key1959, 2), (key1967, 2), (key1959, 2), (key1967, 2), (key1961, 2)]

def rawRow17449 : Integer.Sparse Key := [(key1967, 6), (key1970, -2), (key1967, -2), (key1967, -2), (key1961, 6), (key1970, -2), (key1961, -2), (key1961, -2), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, -2), (key1959, -2), (key1959, -2), (key1967, 2), (key1967, 2), (key1961, 2), (key1961, 2), (key1959, 2), (key1959, 2)]

def rawRow17450 : Integer.Sparse Key := [(key1970, 6), (key1967, -2), (key1967, -2), (key1967, -2), (key1970, 6), (key1961, -2), (key1961, -2), (key1961, -2), (key1967, -2), (key1967, -2), (key1967, -2), (key1961, -2), (key1961, -2), (key1961, -2), (key1959, 2), (key1959, 2), (key1959, 2), (key1959, 2), (key1959, 2), (key1959, 2)]

def rawRow17451 : Integer.Sparse Key := [(key665, -2), (key665, -2), (key666, -2), (key666, 6), (key665, -2), (key665, -2), (key666, -2), (key665, 2), (key665, 2), (key682, 2), (key682, 2), (key683, 2), (key683, 2), (key666, -2), (key683, -2), (key683, -2), (key666, 6), (key666, -2), (key683, -2), (key683, -2)]

def rawRow17452 : Integer.Sparse Key := [(key665, -2), (key666, -2), (key665, -2), (key666, 6), (key665, -2), (key666, -2), (key665, -2), (key682, 2), (key683, 2), (key665, 2), (key683, 2), (key665, 2), (key682, 2), (key683, -2), (key666, -2), (key683, -2), (key666, 6), (key683, -2), (key666, -2), (key683, -2)]

def rawRow17453 : Integer.Sparse Key := [(key666, -2), (key665, -2), (key665, -2), (key666, 6), (key666, -2), (key665, -2), (key665, -2), (key683, 2), (key682, 2), (key683, 2), (key665, 2), (key682, 2), (key665, 2), (key683, -2), (key683, -2), (key666, -2), (key666, 6), (key683, -2), (key683, -2), (key666, -2)]

def rawRow17454 : Integer.Sparse Key := [(key665, -2), (key666, -2), (key666, -2), (key665, 6), (key682, -2), (key683, -2), (key683, -2), (key665, 2), (key666, 2), (key665, 2), (key683, 2), (key666, 2), (key683, 2), (key665, -2), (key665, -2), (key682, -2), (key683, 6), (key666, -2), (key666, -2), (key683, -2)]

def rawRow17455 : Integer.Sparse Key := [(key666, -2), (key665, -2), (key666, -2), (key665, 6), (key683, -2), (key682, -2), (key683, -2), (key666, 2), (key665, 2), (key683, 2), (key665, 2), (key683, 2), (key666, 2), (key665, -2), (key682, -2), (key665, -2), (key683, 6), (key666, -2), (key683, -2), (key666, -2)]

def rawRow17456 : Integer.Sparse Key := [(key666, -2), (key666, -2), (key665, -2), (key665, 6), (key683, -2), (key683, -2), (key682, -2), (key683, 2), (key683, 2), (key666, 2), (key666, 2), (key665, 2), (key665, 2), (key682, -2), (key665, -2), (key665, -2), (key683, 6), (key683, -2), (key666, -2), (key666, -2)]

def rawRow17457 : Integer.Sparse Key := [(key682, -2), (key683, -2), (key683, -2), (key683, 6), (key665, -2), (key666, -2), (key666, -2), (key665, 2), (key666, 2), (key665, 2), (key683, 2), (key666, 2), (key683, 2), (key666, -2), (key666, -2), (key683, -2), (key665, 6), (key665, -2), (key665, -2), (key682, -2)]

def rawRow17458 : Integer.Sparse Key := [(key683, -2), (key682, -2), (key683, -2), (key683, 6), (key666, -2), (key665, -2), (key666, -2), (key666, 2), (key665, 2), (key683, 2), (key665, 2), (key683, 2), (key666, 2), (key666, -2), (key683, -2), (key666, -2), (key665, 6), (key665, -2), (key682, -2), (key665, -2)]

def rawRow17459 : Integer.Sparse Key := [(key683, -2), (key683, -2), (key682, -2), (key683, 6), (key666, -2), (key666, -2), (key665, -2), (key683, 2), (key683, 2), (key666, 2), (key666, 2), (key665, 2), (key665, 2), (key683, -2), (key666, -2), (key666, -2), (key665, 6), (key682, -2), (key665, -2), (key665, -2)]

def rawRow17460 : Integer.Sparse Key := [(key683, -2), (key683, -2), (key683, -2), (key682, 6), (key683, -2), (key683, -2), (key683, -2), (key666, 2), (key666, 2), (key666, 2), (key666, 2), (key666, 2), (key666, 2), (key665, -2), (key665, -2), (key665, -2), (key682, 6), (key665, -2), (key665, -2), (key665, -2)]

def rawRow17461 : Integer.Sparse Key := [(key621, 4), (key649, 4), (key649, 4), (key623, -2), (key623, -2), (key649, -2), (key649, -2), (key653, -2), (key653, -2), (key623, -2), (key623, -2), (key649, -2), (key649, -2), (key653, -2), (key653, -2), (key625, 4), (key653, 4), (key653, 4)]

def rawRow17462 : Integer.Sparse Key := [(key649, 4), (key621, 4), (key649, 4), (key649, -2), (key653, -2), (key623, -2), (key653, -2), (key623, -2), (key649, -2), (key649, -2), (key653, -2), (key623, -2), (key653, -2), (key623, -2), (key649, -2), (key653, 4), (key625, 4), (key653, 4)]

def rawRow17463 : Integer.Sparse Key := [(key649, 4), (key649, 4), (key621, 4), (key653, -2), (key649, -2), (key653, -2), (key623, -2), (key649, -2), (key623, -2), (key653, -2), (key649, -2), (key653, -2), (key623, -2), (key649, -2), (key623, -2), (key653, 4), (key653, 4), (key625, 4)]

def rawRow17464 : Integer.Sparse Key := [(key623, 4), (key623, 4), (key653, 4), (key621, -2), (key623, -2), (key621, -2), (key649, -2), (key623, -2), (key649, -2), (key623, -2), (key625, -2), (key623, -2), (key653, -2), (key625, -2), (key653, -2), (key623, 4), (key623, 4), (key649, 4)]

def rawRow17465 : Integer.Sparse Key := [(key623, 4), (key653, 4), (key623, 4), (key623, -2), (key621, -2), (key649, -2), (key621, -2), (key649, -2), (key623, -2), (key625, -2), (key623, -2), (key653, -2), (key623, -2), (key653, -2), (key625, -2), (key623, 4), (key649, 4), (key623, 4)]

def rawRow17466 : Integer.Sparse Key := [(key653, 4), (key623, 4), (key623, 4), (key649, -2), (key649, -2), (key623, -2), (key623, -2), (key621, -2), (key621, -2), (key653, -2), (key653, -2), (key625, -2), (key625, -2), (key623, -2), (key623, -2), (key649, 4), (key623, 4), (key623, 4)]

def rawRow17467 : Integer.Sparse Key := [(key623, 4), (key623, 4), (key653, 4), (key623, -2), (key625, -2), (key623, -2), (key653, -2), (key625, -2), (key653, -2), (key621, -2), (key623, -2), (key621, -2), (key649, -2), (key623, -2), (key649, -2), (key623, 4), (key623, 4), (key649, 4)]

def rawRow17468 : Integer.Sparse Key := [(key623, 4), (key653, 4), (key623, 4), (key625, -2), (key623, -2), (key653, -2), (key623, -2), (key653, -2), (key625, -2), (key623, -2), (key621, -2), (key649, -2), (key621, -2), (key649, -2), (key623, -2), (key623, 4), (key649, 4), (key623, 4)]

def rawRow17469 : Integer.Sparse Key := [(key653, 4), (key623, 4), (key623, 4), (key653, -2), (key653, -2), (key625, -2), (key625, -2), (key623, -2), (key623, -2), (key649, -2), (key649, -2), (key623, -2), (key623, -2), (key621, -2), (key621, -2), (key649, 4), (key623, 4), (key623, 4)]

def rawRow17470 : Integer.Sparse Key := [(key625, 4), (key625, 4), (key625, 4), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key621, 4), (key621, 4), (key621, 4)]

def rawRow17471 : Integer.Sparse Key := [(key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1866, 2), (key1881, 2), (key1881, 2), (key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1868, 2), (key1868, 2), (key1878, 2), (key1878, 2), (key1889, 2), (key1889, 2), (key1871, -1), (key1871, -1), (key1881, -1), (key1881, -1), (key1889, -1), (key1889, -1), (key1866, 2), (key1881, 2), (key1881, 2), (key1871, -1), (key1871, -1), (key1881, -1), (key1881, -1), (key1889, -1), (key1889, -1)]

def rawRow17472 : Integer.Sparse Key := [(key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1881, 2), (key1866, 2), (key1881, 2), (key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1878, 2), (key1889, 2), (key1868, 2), (key1889, 2), (key1868, 2), (key1878, 2), (key1881, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1871, -1), (key1881, -1), (key1881, 2), (key1866, 2), (key1881, 2), (key1881, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1871, -1), (key1881, -1)]

def rawRow17473 : Integer.Sparse Key := [(key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1866, 2), (key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1889, 2), (key1878, 2), (key1889, 2), (key1868, 2), (key1878, 2), (key1868, 2), (key1889, -1), (key1881, -1), (key1889, -1), (key1871, -1), (key1881, -1), (key1871, -1), (key1881, 2), (key1881, 2), (key1866, 2), (key1889, -1), (key1881, -1), (key1889, -1), (key1871, -1), (key1881, -1), (key1871, -1)]

def rawRow17474 : Integer.Sparse Key := [(key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1862, 2), (key1862, 2), (key1878, 2), (key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2), (key1862, -1), (key1868, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1878, -1), (key1871, 2), (key1871, 2), (key1889, 2), (key1866, -1), (key1871, -1), (key1866, -1), (key1881, -1), (key1871, -1), (key1881, -1)]

def rawRow17475 : Integer.Sparse Key := [(key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1862, 2), (key1878, 2), (key1862, 2), (key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1868, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1871, 2), (key1889, 2), (key1871, 2), (key1871, -1), (key1866, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1871, -1)]

def rawRow17476 : Integer.Sparse Key := [(key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1878, 2), (key1862, 2), (key1862, 2), (key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2), (key1878, -1), (key1878, -1), (key1868, -1), (key1868, -1), (key1862, -1), (key1862, -1), (key1889, 2), (key1871, 2), (key1871, 2), (key1881, -1), (key1881, -1), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1)]

def rawRow17477 : Integer.Sparse Key := [(key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1871, 2), (key1871, 2), (key1889, 2), (key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2), (key1866, -1), (key1871, -1), (key1866, -1), (key1881, -1), (key1871, -1), (key1881, -1), (key1862, 2), (key1862, 2), (key1878, 2), (key1862, -1), (key1868, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1878, -1)]

def rawRow17478 : Integer.Sparse Key := [(key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1871, 2), (key1889, 2), (key1871, 2), (key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1871, -1), (key1866, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1871, -1), (key1862, 2), (key1878, 2), (key1862, 2), (key1868, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1878, -1), (key1868, -1)]

def rawRow17479 : Integer.Sparse Key := [(key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1889, 2), (key1871, 2), (key1871, 2), (key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2), (key1881, -1), (key1881, -1), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1878, 2), (key1862, 2), (key1862, 2), (key1878, -1), (key1878, -1), (key1868, -1), (key1868, -1), (key1862, -1), (key1862, -1)]

def rawRow17480 : Integer.Sparse Key := [(key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1868, 2), (key1868, 2), (key1868, 2), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1868, 2), (key1868, 2), (key1868, 2), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1)]

def rawRow17481 : Integer.Sparse Key := [(key1963, 4), (key1965, 4), (key1965, 4), (key1965, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1968, 12)]

def rawRow17482 : Integer.Sparse Key := [(key1965, 4), (key1963, 4), (key1965, 4), (key1965, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1968, 12)]

def rawRow17483 : Integer.Sparse Key := [(key1965, 4), (key1965, 4), (key1963, 4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, 12)]

def rawRow17484 : Integer.Sparse Key := [(key1965, 4), (key1965, 4), (key1968, 4), (key1963, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1968, -4), (key1965, 12)]

def rawRow17485 : Integer.Sparse Key := [(key1965, 4), (key1968, 4), (key1965, 4), (key1965, -4), (key1963, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1968, -4), (key1965, 12)]

def rawRow17486 : Integer.Sparse Key := [(key1968, 4), (key1965, 4), (key1965, 4), (key1965, -4), (key1965, -4), (key1963, -4), (key1968, -4), (key1968, -4), (key1965, -4), (key1965, 12)]

def rawRow17487 : Integer.Sparse Key := [(key1965, 4), (key1965, 4), (key1968, 4), (key1965, -4), (key1968, -4), (key1968, -4), (key1963, -4), (key1965, -4), (key1965, -4), (key1965, 12)]

def rawRow17488 : Integer.Sparse Key := [(key1965, 4), (key1968, 4), (key1965, 4), (key1968, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1963, -4), (key1965, -4), (key1965, 12)]

def rawRow17489 : Integer.Sparse Key := [(key1968, 4), (key1965, 4), (key1965, 4), (key1968, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1963, -4), (key1965, 12)]

def rawRow17490 : Integer.Sparse Key := [(key1968, 4), (key1968, 4), (key1968, 4), (key1965, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1963, 12)]

def rawRow17491 : Integer.Sparse Key := [(key1934, -2), (key1934, -2), (key1935, -2), (key1935, 6), (key1934, -2), (key1934, -2), (key1935, -2), (key1934, 2), (key1934, 2), (key1954, 2), (key1954, 2), (key1955, 2), (key1955, 2), (key1935, -2), (key1955, -2), (key1955, -2), (key1935, 6), (key1935, -2), (key1955, -2), (key1955, -2)]

def rawRow17492 : Integer.Sparse Key := [(key1934, -2), (key1935, -2), (key1934, -2), (key1935, 6), (key1934, -2), (key1935, -2), (key1934, -2), (key1954, 2), (key1955, 2), (key1934, 2), (key1955, 2), (key1934, 2), (key1954, 2), (key1955, -2), (key1935, -2), (key1955, -2), (key1935, 6), (key1955, -2), (key1935, -2), (key1955, -2)]

def rawRow17493 : Integer.Sparse Key := [(key1935, -2), (key1934, -2), (key1934, -2), (key1935, 6), (key1935, -2), (key1934, -2), (key1934, -2), (key1955, 2), (key1954, 2), (key1955, 2), (key1934, 2), (key1954, 2), (key1934, 2), (key1955, -2), (key1955, -2), (key1935, -2), (key1935, 6), (key1955, -2), (key1955, -2), (key1935, -2)]

def rawRow17494 : Integer.Sparse Key := [(key1934, -2), (key1935, -2), (key1935, -2), (key1934, 6), (key1954, -2), (key1955, -2), (key1955, -2), (key1934, 2), (key1935, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1955, 2), (key1934, -2), (key1934, -2), (key1954, -2), (key1955, 6), (key1935, -2), (key1935, -2), (key1955, -2)]

def rawRow17495 : Integer.Sparse Key := [(key1935, -2), (key1934, -2), (key1935, -2), (key1934, 6), (key1955, -2), (key1954, -2), (key1955, -2), (key1935, 2), (key1934, 2), (key1955, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1934, -2), (key1954, -2), (key1934, -2), (key1955, 6), (key1935, -2), (key1955, -2), (key1935, -2)]

def rawRow17496 : Integer.Sparse Key := [(key1935, -2), (key1935, -2), (key1934, -2), (key1934, 6), (key1955, -2), (key1955, -2), (key1954, -2), (key1955, 2), (key1955, 2), (key1935, 2), (key1935, 2), (key1934, 2), (key1934, 2), (key1954, -2), (key1934, -2), (key1934, -2), (key1955, 6), (key1955, -2), (key1935, -2), (key1935, -2)]

def rawRow17497 : Integer.Sparse Key := [(key1954, -2), (key1955, -2), (key1955, -2), (key1955, 6), (key1934, -2), (key1935, -2), (key1935, -2), (key1934, 2), (key1935, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1955, 2), (key1935, -2), (key1935, -2), (key1955, -2), (key1934, 6), (key1934, -2), (key1934, -2), (key1954, -2)]

def rawRow17498 : Integer.Sparse Key := [(key1955, -2), (key1954, -2), (key1955, -2), (key1955, 6), (key1935, -2), (key1934, -2), (key1935, -2), (key1935, 2), (key1934, 2), (key1955, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1935, -2), (key1955, -2), (key1935, -2), (key1934, 6), (key1934, -2), (key1954, -2), (key1934, -2)]

def rawRow17499 : Integer.Sparse Key := [(key1955, -2), (key1955, -2), (key1954, -2), (key1955, 6), (key1935, -2), (key1935, -2), (key1934, -2), (key1955, 2), (key1955, 2), (key1935, 2), (key1935, 2), (key1934, 2), (key1934, 2), (key1955, -2), (key1935, -2), (key1935, -2), (key1934, 6), (key1954, -2), (key1934, -2), (key1934, -2)]

def rawRow17500 : Integer.Sparse Key := [(key1955, -2), (key1955, -2), (key1955, -2), (key1954, 6), (key1955, -2), (key1955, -2), (key1955, -2), (key1935, 2), (key1935, 2), (key1935, 2), (key1935, 2), (key1935, 2), (key1935, 2), (key1934, -2), (key1934, -2), (key1934, -2), (key1954, 6), (key1934, -2), (key1934, -2), (key1934, -2)]

def rawRow17501 : Integer.Sparse Key := [(key688, 4), (key689, 4), (key689, 4), (key689, -4), (key689, -4), (key691, -4), (key689, -4), (key689, -4), (key691, -4), (key691, 12)]

def rawRow17502 : Integer.Sparse Key := [(key689, 4), (key688, 4), (key689, 4), (key689, -4), (key691, -4), (key689, -4), (key689, -4), (key691, -4), (key689, -4), (key691, 12)]

def rawRow17503 : Integer.Sparse Key := [(key689, 4), (key689, 4), (key688, 4), (key691, -4), (key689, -4), (key689, -4), (key691, -4), (key689, -4), (key689, -4), (key691, 12)]

def rawRow17504 : Integer.Sparse Key := [(key689, 4), (key689, 4), (key691, 4), (key688, -4), (key689, -4), (key689, -4), (key689, -4), (key691, -4), (key691, -4), (key689, 12)]

def rawRow17505 : Integer.Sparse Key := [(key689, 4), (key691, 4), (key689, 4), (key689, -4), (key688, -4), (key689, -4), (key691, -4), (key689, -4), (key691, -4), (key689, 12)]

def rawRow17506 : Integer.Sparse Key := [(key691, 4), (key689, 4), (key689, 4), (key689, -4), (key689, -4), (key688, -4), (key691, -4), (key691, -4), (key689, -4), (key689, 12)]

def rawRow17507 : Integer.Sparse Key := [(key689, 4), (key689, 4), (key691, 4), (key689, -4), (key691, -4), (key691, -4), (key688, -4), (key689, -4), (key689, -4), (key689, 12)]

def rawRow17508 : Integer.Sparse Key := [(key689, 4), (key691, 4), (key689, 4), (key691, -4), (key689, -4), (key691, -4), (key689, -4), (key688, -4), (key689, -4), (key689, 12)]

def rawRow17509 : Integer.Sparse Key := [(key691, 4), (key689, 4), (key689, 4), (key691, -4), (key691, -4), (key689, -4), (key689, -4), (key689, -4), (key688, -4), (key689, 12)]

def rawRow17510 : Integer.Sparse Key := [(key691, 4), (key691, 4), (key691, 4), (key689, -4), (key689, -4), (key689, -4), (key689, -4), (key689, -4), (key689, -4), (key688, 12)]

def rawRow17511 : Integer.Sparse Key := [(key1938, -1), (key1938, -1), (key1950, -1), (key1950, -1), (key1951, -1), (key1951, -1), (key1939, 2), (key1951, 2), (key1951, 2), (key1938, -1), (key1938, -1), (key1950, -1), (key1950, -1), (key1951, -1), (key1951, -1), (key1941, 2), (key1941, 2), (key1950, 2), (key1950, 2), (key1956, 2), (key1956, 2), (key1942, -1), (key1942, -1), (key1951, -1), (key1951, -1), (key1956, -1), (key1956, -1), (key1939, 2), (key1951, 2), (key1951, 2), (key1942, -1), (key1942, -1), (key1951, -1), (key1951, -1), (key1956, -1), (key1956, -1)]

def rawRow17512 : Integer.Sparse Key := [(key1950, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1951, 2), (key1939, 2), (key1951, 2), (key1950, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1950, 2), (key1956, 2), (key1941, 2), (key1956, 2), (key1941, 2), (key1950, 2), (key1951, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1942, -1), (key1951, -1), (key1951, 2), (key1939, 2), (key1951, 2), (key1951, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1942, -1), (key1951, -1)]

def rawRow17513 : Integer.Sparse Key := [(key1951, -1), (key1950, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1951, 2), (key1951, 2), (key1939, 2), (key1951, -1), (key1950, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1956, 2), (key1950, 2), (key1956, 2), (key1941, 2), (key1950, 2), (key1941, 2), (key1956, -1), (key1951, -1), (key1956, -1), (key1942, -1), (key1951, -1), (key1942, -1), (key1951, 2), (key1951, 2), (key1939, 2), (key1956, -1), (key1951, -1), (key1956, -1), (key1942, -1), (key1951, -1), (key1942, -1)]

def rawRow17514 : Integer.Sparse Key := [(key1938, -1), (key1939, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1938, 2), (key1938, 2), (key1950, 2), (key1941, -1), (key1942, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1938, 2), (key1942, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1951, 2), (key1938, -1), (key1941, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1950, -1), (key1942, 2), (key1942, 2), (key1956, 2), (key1939, -1), (key1942, -1), (key1939, -1), (key1951, -1), (key1942, -1), (key1951, -1)]

def rawRow17515 : Integer.Sparse Key := [(key1939, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1938, 2), (key1950, 2), (key1938, 2), (key1942, -1), (key1941, -1), (key1956, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1942, 2), (key1938, 2), (key1951, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1941, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1942, 2), (key1956, 2), (key1942, 2), (key1942, -1), (key1939, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1942, -1)]

def rawRow17516 : Integer.Sparse Key := [(key1951, -1), (key1951, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1950, 2), (key1938, 2), (key1938, 2), (key1956, -1), (key1956, -1), (key1942, -1), (key1942, -1), (key1941, -1), (key1941, -1), (key1951, 2), (key1951, 2), (key1942, 2), (key1942, 2), (key1938, 2), (key1938, 2), (key1950, -1), (key1950, -1), (key1941, -1), (key1941, -1), (key1938, -1), (key1938, -1), (key1956, 2), (key1942, 2), (key1942, 2), (key1951, -1), (key1951, -1), (key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1)]

def rawRow17517 : Integer.Sparse Key := [(key1941, -1), (key1942, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1942, 2), (key1942, 2), (key1956, 2), (key1938, -1), (key1939, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1938, 2), (key1942, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1951, 2), (key1939, -1), (key1942, -1), (key1939, -1), (key1951, -1), (key1942, -1), (key1951, -1), (key1938, 2), (key1938, 2), (key1950, 2), (key1938, -1), (key1941, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1950, -1)]

def rawRow17518 : Integer.Sparse Key := [(key1942, -1), (key1941, -1), (key1956, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1942, 2), (key1956, 2), (key1942, 2), (key1939, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1942, 2), (key1938, 2), (key1951, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1942, -1), (key1939, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1942, -1), (key1938, 2), (key1950, 2), (key1938, 2), (key1941, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1950, -1), (key1941, -1)]

def rawRow17519 : Integer.Sparse Key := [(key1956, -1), (key1956, -1), (key1942, -1), (key1942, -1), (key1941, -1), (key1941, -1), (key1956, 2), (key1942, 2), (key1942, 2), (key1951, -1), (key1951, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1951, 2), (key1951, 2), (key1942, 2), (key1942, 2), (key1938, 2), (key1938, 2), (key1951, -1), (key1951, -1), (key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1), (key1950, 2), (key1938, 2), (key1938, 2), (key1950, -1), (key1950, -1), (key1941, -1), (key1941, -1), (key1938, -1), (key1938, -1)]

def rawRow17520 : Integer.Sparse Key := [(key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1941, 2), (key1941, 2), (key1941, 2), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1939, 2), (key1939, 2), (key1939, 2), (key1939, 2), (key1939, 2), (key1939, 2), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1941, 2), (key1941, 2), (key1941, 2), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1)]

def rawRow17521 : Integer.Sparse Key := [(key517, -2), (key517, -2), (key524, -2), (key524, 6), (key517, -2), (key517, -2), (key524, -2), (key517, 2), (key517, 2), (key549, 2), (key549, 2), (key555, 2), (key555, 2), (key524, -2), (key555, -2), (key555, -2), (key524, 6), (key524, -2), (key555, -2), (key555, -2)]

def rawRow17522 : Integer.Sparse Key := [(key517, -2), (key524, -2), (key517, -2), (key524, 6), (key517, -2), (key524, -2), (key517, -2), (key549, 2), (key555, 2), (key517, 2), (key555, 2), (key517, 2), (key549, 2), (key555, -2), (key524, -2), (key555, -2), (key524, 6), (key555, -2), (key524, -2), (key555, -2)]

def rawRow17523 : Integer.Sparse Key := [(key524, -2), (key517, -2), (key517, -2), (key524, 6), (key524, -2), (key517, -2), (key517, -2), (key555, 2), (key549, 2), (key555, 2), (key517, 2), (key549, 2), (key517, 2), (key555, -2), (key555, -2), (key524, -2), (key524, 6), (key555, -2), (key555, -2), (key524, -2)]

def rawRow17524 : Integer.Sparse Key := [(key517, -2), (key524, -2), (key524, -2), (key517, 6), (key549, -2), (key555, -2), (key555, -2), (key517, 2), (key524, 2), (key517, 2), (key555, 2), (key524, 2), (key555, 2), (key517, -2), (key517, -2), (key549, -2), (key555, 6), (key524, -2), (key524, -2), (key555, -2)]

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

def rawRow162 : Integer.Sparse Key := [(key1903, -1), (key1911, -1), (key1903, 2), (key1918, 1), (key1926, 1), (key1896, -1), (key1918, -1), (key1920, -2), (key1899, 1), (key1920, 1), (key1472, 1), (key1480, 1), (key1472, -2), (key1681, -1), (key1689, -1), (key1351, 1), (key1681, 1), (key1683, 2), (key1354, -1), (key1683, -1), (key1426, -1), (key1444, -1), (key1393, 1), (key1426, 1), (key1575, 1), (key1593, 1), (key1298, -1), (key1575, -1), (key1556, -1), (key1624, -1), (key1326, 1), (key1624, 1), (key1420, 2), (key1387, -1), (key1420, -1), (key1569, -2), (key1292, 1), (key1569, 1), (key1542, 1), (key1618, 1), (key1312, -1), (key1618, -1)]

def rawRow163 : Integer.Sparse Key := [(key1911, -1), (key1903, -1), (key1903, 2), (key1926, 1), (key1918, 1), (key1918, -1), (key1896, -1), (key1920, -2), (key1920, 1), (key1899, 1), (key1480, 1), (key1472, 1), (key1472, -2), (key1689, -1), (key1681, -1), (key1681, 1), (key1351, 1), (key1683, 2), (key1683, -1), (key1354, -1), (key1444, -1), (key1426, -1), (key1426, 1), (key1393, 1), (key1593, 1), (key1575, 1), (key1575, -1), (key1298, -1), (key1624, -1), (key1556, -1), (key1624, 1), (key1326, 1), (key1420, 2), (key1420, -1), (key1387, -1), (key1569, -2), (key1569, 1), (key1292, 1), (key1618, 1), (key1542, 1), (key1618, -1), (key1312, -1)]

def rawRow164 : Integer.Sparse Key := [(key1918, -1), (key1920, -1), (key1926, 2), (key1896, 1), (key1899, 1), (key1911, -1), (key1926, -1), (key1896, -2), (key1903, 1), (key1918, 1), (key1681, 1), (key1683, 1), (key1689, -2), (key1351, -1), (key1354, -1), (key1480, 1), (key1689, 1), (key1351, 2), (key1472, -1), (key1681, -1), (key1548, -1), (key1556, -1), (key1593, 1), (key1633, 1), (key1318, 1), (key1326, 1), (key1444, -1), (key1633, -1), (key1298, -1), (key1318, -1), (key1393, 1), (key1548, 1), (key1542, 2), (key1569, -1), (key1618, -1), (key1312, -2), (key1420, 1), (key1618, 1), (key1292, 1), (key1312, 1), (key1387, -1), (key1542, -1)]

def rawRow165 : Integer.Sparse Key := [(key1920, -1), (key1918, -1), (key1926, 2), (key1899, 1), (key1896, 1), (key1926, -1), (key1911, -1), (key1896, -2), (key1918, 1), (key1903, 1), (key1683, 1), (key1681, 1), (key1689, -2), (key1354, -1), (key1351, -1), (key1689, 1), (key1480, 1), (key1351, 2), (key1681, -1), (key1472, -1), (key1556, -1), (key1548, -1), (key1633, 1), (key1593, 1), (key1326, 1), (key1318, 1), (key1633, -1), (key1444, -1), (key1318, -1), (key1298, -1), (key1548, 1), (key1393, 1), (key1542, 2), (key1618, -1), (key1569, -1), (key1312, -2), (key1618, 1), (key1420, 1), (key1312, 1), (key1292, 1), (key1542, -1), (key1387, -1)]

def rawRow166 : Integer.Sparse Key := [(key1918, -1), (key1926, -1), (key1920, 2), (key1903, 1), (key1911, 1), (key1899, -1), (key1920, -1), (key1903, -2), (key1896, 1), (key1918, 1), (key1681, 1), (key1689, 1), (key1683, -2), (key1472, -1), (key1480, -1), (key1354, 1), (key1683, 1), (key1472, 2), (key1351, -1), (key1681, -1), (key1575, -1), (key1593, -1), (key1556, 1), (key1624, 1), (key1426, 1), (key1444, 1), (key1326, -1), (key1624, -1), (key1393, -1), (key1426, -1), (key1298, 1), (key1575, 1), (key1569, 2), (key1542, -1), (key1618, -1), (key1420, -2), (key1312, 1), (key1618, 1), (key1387, 1), (key1420, 1), (key1292, -1), (key1569, -1)]

def rawRow167 : Integer.Sparse Key := [(key1926, -1), (key1918, -1), (key1920, 2), (key1911, 1), (key1903, 1), (key1920, -1), (key1899, -1), (key1903, -2), (key1918, 1), (key1896, 1), (key1689, 1), (key1681, 1), (key1683, -2), (key1480, -1), (key1472, -1), (key1683, 1), (key1354, 1), (key1472, 2), (key1681, -1), (key1351, -1), (key1593, -1), (key1575, -1), (key1624, 1), (key1556, 1), (key1444, 1), (key1426, 1), (key1624, -1), (key1326, -1), (key1426, -1), (key1393, -1), (key1575, 1), (key1298, 1), (key1569, 2), (key1618, -1), (key1542, -1), (key1420, -2), (key1618, 1), (key1312, 1), (key1420, 1), (key1387, 1), (key1569, -1), (key1292, -1)]

def rawRow168 : Integer.Sparse Key := [(key2612, -2), (key2612, 1), (key2618, 1), (key2628, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2648, -1), (key2646, 1), (key2653, 1), (key2667, 2), (key2667, -1), (key2673, -1), (key2702, -2), (key2702, 1), (key2728, 1), (key2735, 1), (key2737, 1), (key2735, -1), (key2747, -1), (key2782, -2), (key2782, 1), (key2795, 1), (key2805, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2897, -1), (key2893, 1), (key2904, 1), (key2936, 1), (key2938, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2950, -1), (key2948, 1), (key2960, 1), (key2972, 1), (key2976, 1), (key2972, -1), (key2983, -1)]

def rawRow169 : Integer.Sparse Key := [(key2616, -2), (key2618, 1), (key2612, 1), (key2628, 2), (key2641, -1), (key2628, -1), (key2648, -1), (key2646, -1), (key2653, 1), (key2646, 1), (key2667, 2), (key2673, -1), (key2667, -1), (key2702, -2), (key2728, 1), (key2702, 1), (key2737, 1), (key2735, 1), (key2747, -1), (key2735, -1), (key2782, -2), (key2795, 1), (key2782, 1), (key2805, 2), (key2831, -1), (key2805, -1), (key2897, -1), (key2893, -1), (key2904, 1), (key2893, 1), (key2938, 1), (key2936, 1), (key2943, -1), (key2936, -1), (key2950, -1), (key2948, -1), (key2960, 1), (key2948, 1), (key2976, 1), (key2972, 1), (key2983, -1), (key2972, -1)]

def rawRow170 : Integer.Sparse Key := [(key2621, -2), (key2616, 1), (key2616, 1), (key2641, 2), (key2628, -1), (key2628, -1), (key2653, -1), (key2653, -1), (key2648, 1), (key2648, 1), (key2673, 2), (key2667, -1), (key2667, -1), (key2728, -2), (key2702, 1), (key2702, 1), (key2747, 1), (key2747, 1), (key2737, -1), (key2737, -1), (key2795, -2), (key2782, 1), (key2782, 1), (key2831, 2), (key2805, -1), (key2805, -1), (key2904, -1), (key2904, -1), (key2897, 1), (key2897, 1), (key2943, 1), (key2943, 1), (key2938, -1), (key2938, -1), (key2960, -1), (key2960, -1), (key2950, 1), (key2950, 1), (key2983, 1), (key2983, 1), (key2976, -1), (key2976, -1)]

def rawRow171 : Integer.Sparse Key := [(key2632, -2), (key2640, 1), (key2644, 1), (key2612, 2), (key2646, -1), (key2653, -1), (key2612, -1), (key2618, -1), (key2628, 1), (key2641, 1), (key2702, 2), (key2735, -1), (key2737, -1), (key2667, -2), (key2735, 1), (key2747, 1), (key2667, 1), (key2673, 1), (key2702, -1), (key2728, -1), (key2805, -2), (key2893, 1), (key2897, 1), (key2782, 2), (key2893, -1), (key2904, -1), (key2782, -1), (key2795, -1), (key2805, 1), (key2831, 1), (key2948, 1), (key2950, 1), (key2972, -1), (key2976, -1), (key2936, -1), (key2938, -1), (key2972, 1), (key2983, 1), (key2936, 1), (key2943, 1), (key2948, -1), (key2960, -1)]

def rawRow172 : Integer.Sparse Key := [(key2632, -2), (key2644, 1), (key2640, 1), (key2616, 2), (key2653, -1), (key2646, -1), (key2618, -1), (key2612, -1), (key2641, 1), (key2628, 1), (key2702, 2), (key2737, -1), (key2735, -1), (key2667, -2), (key2747, 1), (key2735, 1), (key2673, 1), (key2667, 1), (key2728, -1), (key2702, -1), (key2805, -2), (key2897, 1), (key2893, 1), (key2782, 2), (key2904, -1), (key2893, -1), (key2795, -1), (key2782, -1), (key2831, 1), (key2805, 1), (key2950, 1), (key2948, 1), (key2976, -1), (key2972, -1), (key2938, -1), (key2936, -1), (key2983, 1), (key2972, 1), (key2943, 1), (key2936, 1), (key2960, -1), (key2948, -1)]

def rawRow173 : Integer.Sparse Key := [(key2644, -2), (key2632, 1), (key2640, 1), (key2660, 2), (key2616, -1), (key2640, -1), (key2641, -1), (key2653, -1), (key2618, 1), (key2648, 1), (key2737, 2), (key2702, -1), (key2735, -1), (key2747, -2), (key2667, 1), (key2735, 1), (key2728, 1), (key2747, 1), (key2673, -1), (key2737, -1), (key2897, -2), (key2805, 1), (key2893, 1), (key2904, 2), (key2782, -1), (key2893, -1), (key2831, -1), (key2904, -1), (key2795, 1), (key2897, 1), (key2976, 1), (key2998, 1), (key2950, -1), (key2997, -1), (key2983, -1), (key3000, -1), (key2938, 1), (key2997, 1), (key2960, 1), (key3000, 1), (key2943, -1), (key2998, -1)]

def rawRow174 : Integer.Sparse Key := [(key2644, -2), (key2640, 1), (key2632, 1), (key2660, 2), (key2640, -1), (key2616, -1), (key2653, -1), (key2641, -1), (key2648, 1), (key2618, 1), (key2737, 2), (key2735, -1), (key2702, -1), (key2747, -2), (key2735, 1), (key2667, 1), (key2747, 1), (key2728, 1), (key2737, -1), (key2673, -1), (key2897, -2), (key2893, 1), (key2805, 1), (key2904, 2), (key2893, -1), (key2782, -1), (key2904, -1), (key2831, -1), (key2897, 1), (key2795, 1), (key2998, 1), (key2976, 1), (key2997, -1), (key2950, -1), (key3000, -1), (key2983, -1), (key2997, 1), (key2938, 1), (key3000, 1), (key2960, 1), (key2998, -1), (key2943, -1)]

def rawRow175 : Integer.Sparse Key := [(key2658, -2), (key2660, 1), (key2660, 1), (key2621, 2), (key2644, -1), (key2644, -1), (key2616, -1), (key2616, -1), (key2632, 1), (key2632, 1), (key2728, 2), (key2747, -1), (key2747, -1), (key2673, -2), (key2737, 1), (key2737, 1), (key2667, 1), (key2667, 1), (key2702, -1), (key2702, -1), (key2831, -2), (key2904, 1), (key2904, 1), (key2795, 2), (key2897, -1), (key2897, -1), (key2782, -1), (key2782, -1), (key2805, 1), (key2805, 1), (key2960, 1), (key2960, 1), (key2983, -1), (key2983, -1), (key2943, -1), (key2943, -1), (key2976, 1), (key2976, 1), (key2938, 1), (key2938, 1), (key2950, -1), (key2950, -1)]

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

def rawRow1689 : Integer.Sparse Key := [(key1668, -2), (key1655, -2), (key1660, -2), (key1597, 1), (key1573, 1), (key1668, 1), (key1546, 1), (key1660, 1), (key1560, 1), (key1826, 2), (key1813, 2), (key1818, 2), (key1448, -1), (key1424, -1), (key1826, -1), (key1316, -1), (key1818, -1), (key1330, -1), (key1799, -1), (key1788, -1), (key1845, -1), (key1772, -1), (key1842, -1), (key1781, -1), (key1467, 1), (key1455, 1), (key1845, 1), (key1337, 1), (key1842, 1), (key1346, 1)]

def rawRow1690 : Integer.Sparse Key := [(key1660, -2), (key1668, -2), (key1655, -2), (key1660, 1), (key1668, 1), (key1560, 1), (key1597, 1), (key1546, 1), (key1573, 1), (key1818, 2), (key1826, 2), (key1813, 2), (key1818, -1), (key1826, -1), (key1330, -1), (key1448, -1), (key1316, -1), (key1424, -1), (key1842, -1), (key1845, -1), (key1781, -1), (key1799, -1), (key1772, -1), (key1788, -1), (key1842, 1), (key1845, 1), (key1346, 1), (key1467, 1), (key1337, 1), (key1455, 1)]

def rawRow1691 : Integer.Sparse Key := [(key1668, -2), (key1660, -2), (key1655, -2), (key1668, 1), (key1660, 1), (key1597, 1), (key1560, 1), (key1573, 1), (key1546, 1), (key1826, 2), (key1818, 2), (key1813, 2), (key1826, -1), (key1818, -1), (key1448, -1), (key1330, -1), (key1424, -1), (key1316, -1), (key1845, -1), (key1842, -1), (key1799, -1), (key1781, -1), (key1788, -1), (key1772, -1), (key1845, 1), (key1842, 1), (key1467, 1), (key1346, 1), (key1455, 1), (key1337, 1)]

def rawRow1692 : Integer.Sparse Key := [(key1772, -2), (key1775, -2), (key1781, -2), (key1788, 1), (key1791, 1), (key1813, 1), (key1840, 1), (key1818, 1), (key1842, 1), (key1337, 2), (key1340, 2), (key1346, 2), (key1455, -1), (key1458, -1), (key1655, -1), (key1840, -1), (key1660, -1), (key1842, -1), (key1296, -1), (key1303, -1), (key1316, -1), (key1340, -1), (key1330, -1), (key1346, -1), (key1391, 1), (key1398, 1), (key1546, 1), (key1775, 1), (key1560, 1), (key1781, 1)]

def rawRow1693 : Integer.Sparse Key := [(key1775, -2), (key1772, -2), (key1781, -2), (key1791, 1), (key1788, 1), (key1840, 1), (key1813, 1), (key1842, 1), (key1818, 1), (key1340, 2), (key1337, 2), (key1346, 2), (key1458, -1), (key1455, -1), (key1840, -1), (key1655, -1), (key1842, -1), (key1660, -1), (key1303, -1), (key1296, -1), (key1340, -1), (key1316, -1), (key1346, -1), (key1330, -1), (key1398, 1), (key1391, 1), (key1775, 1), (key1546, 1), (key1781, 1), (key1560, 1)]

def rawRow1694 : Integer.Sparse Key := [(key1772, -2), (key1781, -2), (key1775, -2), (key1813, 1), (key1818, 1), (key1788, 1), (key1842, 1), (key1791, 1), (key1840, 1), (key1337, 2), (key1346, 2), (key1340, 2), (key1655, -1), (key1660, -1), (key1455, -1), (key1842, -1), (key1458, -1), (key1840, -1), (key1316, -1), (key1330, -1), (key1296, -1), (key1346, -1), (key1303, -1), (key1340, -1), (key1546, 1), (key1560, 1), (key1391, 1), (key1781, 1), (key1398, 1), (key1775, 1)]

def rawRow1695 : Integer.Sparse Key := [(key1781, -2), (key1772, -2), (key1775, -2), (key1818, 1), (key1813, 1), (key1842, 1), (key1788, 1), (key1840, 1), (key1791, 1), (key1346, 2), (key1337, 2), (key1340, 2), (key1660, -1), (key1655, -1), (key1842, -1), (key1455, -1), (key1840, -1), (key1458, -1), (key1330, -1), (key1316, -1), (key1346, -1), (key1296, -1), (key1340, -1), (key1303, -1), (key1560, 1), (key1546, 1), (key1781, 1), (key1391, 1), (key1775, 1), (key1398, 1)]

def rawRow1696 : Integer.Sparse Key := [(key1775, -2), (key1781, -2), (key1772, -2), (key1840, 1), (key1842, 1), (key1791, 1), (key1818, 1), (key1788, 1), (key1813, 1), (key1340, 2), (key1346, 2), (key1337, 2), (key1840, -1), (key1842, -1), (key1458, -1), (key1660, -1), (key1455, -1), (key1655, -1), (key1340, -1), (key1346, -1), (key1303, -1), (key1330, -1), (key1296, -1), (key1316, -1), (key1775, 1), (key1781, 1), (key1398, 1), (key1560, 1), (key1391, 1), (key1546, 1)]

def rawRow1697 : Integer.Sparse Key := [(key1781, -2), (key1775, -2), (key1772, -2), (key1842, 1), (key1840, 1), (key1818, 1), (key1791, 1), (key1813, 1), (key1788, 1), (key1346, 2), (key1340, 2), (key1337, 2), (key1842, -1), (key1840, -1), (key1660, -1), (key1458, -1), (key1655, -1), (key1455, -1), (key1346, -1), (key1340, -1), (key1330, -1), (key1303, -1), (key1316, -1), (key1296, -1), (key1781, 1), (key1775, 1), (key1560, 1), (key1398, 1), (key1546, 1), (key1391, 1)]

def rawRow1698 : Integer.Sparse Key := [(key1813, -2), (key1818, -2), (key1826, -2), (key1772, 1), (key1781, 1), (key1788, 1), (key1842, 1), (key1799, 1), (key1845, 1), (key1655, 2), (key1660, 2), (key1668, 2), (key1337, -1), (key1346, -1), (key1455, -1), (key1842, -1), (key1467, -1), (key1845, -1), (key1546, -1), (key1560, -1), (key1573, -1), (key1660, -1), (key1597, -1), (key1668, -1), (key1316, 1), (key1330, 1), (key1424, 1), (key1818, 1), (key1448, 1), (key1826, 1)]

def rawRow1699 : Integer.Sparse Key := [(key1818, -2), (key1813, -2), (key1826, -2), (key1781, 1), (key1772, 1), (key1842, 1), (key1788, 1), (key1845, 1), (key1799, 1), (key1660, 2), (key1655, 2), (key1668, 2), (key1346, -1), (key1337, -1), (key1842, -1), (key1455, -1), (key1845, -1), (key1467, -1), (key1560, -1), (key1546, -1), (key1660, -1), (key1573, -1), (key1668, -1), (key1597, -1), (key1330, 1), (key1316, 1), (key1818, 1), (key1424, 1), (key1826, 1), (key1448, 1)]

def rawRow1700 : Integer.Sparse Key := [(key1813, -2), (key1826, -2), (key1818, -2), (key1788, 1), (key1799, 1), (key1772, 1), (key1845, 1), (key1781, 1), (key1842, 1), (key1655, 2), (key1668, 2), (key1660, 2), (key1455, -1), (key1467, -1), (key1337, -1), (key1845, -1), (key1346, -1), (key1842, -1), (key1573, -1), (key1597, -1), (key1546, -1), (key1668, -1), (key1560, -1), (key1660, -1), (key1424, 1), (key1448, 1), (key1316, 1), (key1826, 1), (key1330, 1), (key1818, 1)]

def rawRow1701 : Integer.Sparse Key := [(key1826, -2), (key1813, -2), (key1818, -2), (key1799, 1), (key1788, 1), (key1845, 1), (key1772, 1), (key1842, 1), (key1781, 1), (key1668, 2), (key1655, 2), (key1660, 2), (key1467, -1), (key1455, -1), (key1845, -1), (key1337, -1), (key1842, -1), (key1346, -1), (key1597, -1), (key1573, -1), (key1668, -1), (key1546, -1), (key1660, -1), (key1560, -1), (key1448, 1), (key1424, 1), (key1826, 1), (key1316, 1), (key1818, 1), (key1330, 1)]

def rawRow1702 : Integer.Sparse Key := [(key1818, -2), (key1826, -2), (key1813, -2), (key1842, 1), (key1845, 1), (key1781, 1), (key1799, 1), (key1772, 1), (key1788, 1), (key1660, 2), (key1668, 2), (key1655, 2), (key1842, -1), (key1845, -1), (key1346, -1), (key1467, -1), (key1337, -1), (key1455, -1), (key1660, -1), (key1668, -1), (key1560, -1), (key1597, -1), (key1546, -1), (key1573, -1), (key1818, 1), (key1826, 1), (key1330, 1), (key1448, 1), (key1316, 1), (key1424, 1)]

def rawRow1703 : Integer.Sparse Key := [(key1826, -2), (key1818, -2), (key1813, -2), (key1845, 1), (key1842, 1), (key1799, 1), (key1781, 1), (key1788, 1), (key1772, 1), (key1668, 2), (key1660, 2), (key1655, 2), (key1845, -1), (key1842, -1), (key1467, -1), (key1346, -1), (key1455, -1), (key1337, -1), (key1668, -1), (key1660, -1), (key1597, -1), (key1560, -1), (key1573, -1), (key1546, -1), (key1826, 1), (key1818, 1), (key1448, 1), (key1330, 1), (key1424, 1), (key1316, 1)]

def rawRow1704 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1018, -2), (key1005, 6), (key1111, 2), (key1111, 2), (key1126, 2), (key1040, -2), (key1192, -2), (key1192, -2), (key1154, -6), (key1075, 2), (key1211, 2), (key1211, 2)]

def rawRow1705 : Integer.Sparse Key := [(key998, -2), (key1018, -2), (key998, -2), (key1005, 6), (key1111, 2), (key1126, 2), (key1111, 2), (key1192, -2), (key1040, -2), (key1192, -2), (key1154, -6), (key1211, 2), (key1075, 2), (key1211, 2)]

def rawRow1706 : Integer.Sparse Key := [(key1018, -2), (key998, -2), (key998, -2), (key1005, 6), (key1126, 2), (key1111, 2), (key1111, 2), (key1192, -2), (key1192, -2), (key1040, -2), (key1154, -6), (key1211, 2), (key1211, 2), (key1075, 2)]

def rawRow1707 : Integer.Sparse Key := [(key998, -2), (key1005, -2), (key1018, -2), (key998, 6), (key1190, 2), (key1192, 2), (key1198, 2), (key1033, -2), (key1111, -2), (key1190, -2), (key1211, -6), (key1075, 2), (key1154, 2), (key1211, 2)]

def rawRow1708 : Integer.Sparse Key := [(key1005, -2), (key998, -2), (key1018, -2), (key998, 6), (key1192, 2), (key1190, 2), (key1198, 2), (key1033, -2), (key1190, -2), (key1111, -2), (key1211, -6), (key1075, 2), (key1211, 2), (key1154, 2)]

def rawRow1709 : Integer.Sparse Key := [(key998, -2), (key1018, -2), (key1005, -2), (key998, 6), (key1190, 2), (key1198, 2), (key1192, 2), (key1111, -2), (key1033, -2), (key1190, -2), (key1211, -6), (key1154, 2), (key1075, 2), (key1211, 2)]

def rawRow1710 : Integer.Sparse Key := [(key1018, -2), (key998, -2), (key1005, -2), (key998, 6), (key1198, 2), (key1190, 2), (key1192, 2), (key1111, -2), (key1190, -2), (key1033, -2), (key1211, -6), (key1154, 2), (key1211, 2), (key1075, 2)]

def rawRow1711 : Integer.Sparse Key := [(key1005, -2), (key1018, -2), (key998, -2), (key998, 6), (key1192, 2), (key1198, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key1111, -2), (key1211, -6), (key1211, 2), (key1075, 2), (key1154, 2)]

def rawRow1712 : Integer.Sparse Key := [(key1018, -2), (key1005, -2), (key998, -2), (key998, 6), (key1198, 2), (key1192, 2), (key1190, 2), (key1190, -2), (key1111, -2), (key1033, -2), (key1211, -6), (key1211, 2), (key1154, 2), (key1075, 2)]

def rawRow1713 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1126, -2), (key1154, 6), (key998, 2), (key998, 2), (key1018, 2), (key1075, -2), (key1211, -2), (key1211, -2), (key1005, -6), (key1040, 2), (key1192, 2), (key1192, 2)]

def rawRow1714 : Integer.Sparse Key := [(key1111, -2), (key1126, -2), (key1111, -2), (key1154, 6), (key998, 2), (key1018, 2), (key998, 2), (key1211, -2), (key1075, -2), (key1211, -2), (key1005, -6), (key1192, 2), (key1040, 2), (key1192, 2)]

def rawRow1715 : Integer.Sparse Key := [(key1126, -2), (key1111, -2), (key1111, -2), (key1154, 6), (key1018, 2), (key998, 2), (key998, 2), (key1211, -2), (key1211, -2), (key1075, -2), (key1005, -6), (key1192, 2), (key1192, 2), (key1040, 2)]

def rawRow1716 : Integer.Sparse Key := [(key1111, -2), (key1126, -2), (key1154, -2), (key1111, 6), (key1190, 2), (key1198, 2), (key1211, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1192, -6), (key1005, 2), (key1040, 2), (key1192, 2)]

def rawRow1717 : Integer.Sparse Key := [(key1126, -2), (key1111, -2), (key1154, -2), (key1111, 6), (key1198, 2), (key1190, 2), (key1211, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1192, -6), (key1005, 2), (key1192, 2), (key1040, 2)]

def rawRow1718 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1126, -2), (key1111, 6), (key1190, 2), (key1211, 2), (key1198, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1192, -6), (key1040, 2), (key1005, 2), (key1192, 2)]

def rawRow1719 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1126, -2), (key1111, 6), (key1211, 2), (key1190, 2), (key1198, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1192, -6), (key1040, 2), (key1192, 2), (key1005, 2)]

def rawRow1720 : Integer.Sparse Key := [(key1126, -2), (key1154, -2), (key1111, -2), (key1111, 6), (key1198, 2), (key1211, 2), (key1190, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1192, -6), (key1192, 2), (key1005, 2), (key1040, 2)]

def rawRow1721 : Integer.Sparse Key := [(key1154, -2), (key1126, -2), (key1111, -2), (key1111, 6), (key1211, 2), (key1198, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1192, -6), (key1192, 2), (key1040, 2), (key1005, 2)]

def rawRow1722 : Integer.Sparse Key := [(key1190, -2), (key1192, -2), (key1198, -2), (key1211, 6), (key998, 2), (key1005, 2), (key1018, 2), (key1075, -2), (key1154, -2), (key1211, -2), (key998, -6), (key1033, 2), (key1111, 2), (key1190, 2)]

def rawRow1723 : Integer.Sparse Key := [(key1192, -2), (key1190, -2), (key1198, -2), (key1211, 6), (key1005, 2), (key998, 2), (key1018, 2), (key1075, -2), (key1211, -2), (key1154, -2), (key998, -6), (key1033, 2), (key1190, 2), (key1111, 2)]

def rawRow1724 : Integer.Sparse Key := [(key1190, -2), (key1198, -2), (key1192, -2), (key1211, 6), (key998, 2), (key1018, 2), (key1005, 2), (key1154, -2), (key1075, -2), (key1211, -2), (key998, -6), (key1111, 2), (key1033, 2), (key1190, 2)]

def rawRow1725 : Integer.Sparse Key := [(key1198, -2), (key1190, -2), (key1192, -2), (key1211, 6), (key1018, 2), (key998, 2), (key1005, 2), (key1154, -2), (key1211, -2), (key1075, -2), (key998, -6), (key1111, 2), (key1190, 2), (key1033, 2)]

def rawRow1726 : Integer.Sparse Key := [(key1192, -2), (key1198, -2), (key1190, -2), (key1211, 6), (key1005, 2), (key1018, 2), (key998, 2), (key1211, -2), (key1075, -2), (key1154, -2), (key998, -6), (key1190, 2), (key1033, 2), (key1111, 2)]

def rawRow1727 : Integer.Sparse Key := [(key1198, -2), (key1192, -2), (key1190, -2), (key1211, 6), (key1018, 2), (key1005, 2), (key998, 2), (key1211, -2), (key1154, -2), (key1075, -2), (key998, -6), (key1190, 2), (key1111, 2), (key1033, 2)]

def rawRow1728 : Integer.Sparse Key := [(key1190, -2), (key1198, -2), (key1211, -2), (key1192, 6), (key1111, 2), (key1126, 2), (key1154, 2), (key1005, -2), (key1040, -2), (key1192, -2), (key1111, -6), (key998, 2), (key1033, 2), (key1190, 2)]

def rawRow1729 : Integer.Sparse Key := [(key1198, -2), (key1190, -2), (key1211, -2), (key1192, 6), (key1126, 2), (key1111, 2), (key1154, 2), (key1005, -2), (key1192, -2), (key1040, -2), (key1111, -6), (key998, 2), (key1190, 2), (key1033, 2)]

def rawRow1730 : Integer.Sparse Key := [(key1190, -2), (key1211, -2), (key1198, -2), (key1192, 6), (key1111, 2), (key1154, 2), (key1126, 2), (key1040, -2), (key1005, -2), (key1192, -2), (key1111, -6), (key1033, 2), (key998, 2), (key1190, 2)]

def rawRow1731 : Integer.Sparse Key := [(key1211, -2), (key1190, -2), (key1198, -2), (key1192, 6), (key1154, 2), (key1111, 2), (key1126, 2), (key1040, -2), (key1192, -2), (key1005, -2), (key1111, -6), (key1033, 2), (key1190, 2), (key998, 2)]

def rawRow1732 : Integer.Sparse Key := [(key1198, -2), (key1211, -2), (key1190, -2), (key1192, 6), (key1126, 2), (key1154, 2), (key1111, 2), (key1192, -2), (key1005, -2), (key1040, -2), (key1111, -6), (key1190, 2), (key998, 2), (key1033, 2)]

def rawRow1733 : Integer.Sparse Key := [(key1211, -2), (key1198, -2), (key1190, -2), (key1192, 6), (key1154, 2), (key1126, 2), (key1111, 2), (key1192, -2), (key1040, -2), (key1005, -2), (key1111, -6), (key1190, 2), (key1033, 2), (key998, 2)]

def rawRow1734 : Integer.Sparse Key := [(key2617, -2), (key2655, -2), (key2655, -2), (key2620, 1), (key2620, 1), (key2643, 1), (key2643, 1), (key2656, 1), (key2656, 1), (key2810, 2), (key2899, 2), (key2899, 2), (key2797, -1), (key2797, -1), (key2833, -1), (key2833, -1), (key2915, -1), (key2915, -1), (key2952, -1), (key2952, -1), (key2978, -1), (key2978, -1), (key2999, -1), (key2999, -1), (key2945, 1), (key2945, 1), (key2962, 1), (key2962, 1), (key3004, 1), (key3004, 1)]

def rawRow1735 : Integer.Sparse Key := [(key2655, -2), (key2617, -2), (key2655, -2), (key2643, 1), (key2656, 1), (key2620, 1), (key2656, 1), (key2620, 1), (key2643, 1), (key2899, 2), (key2810, 2), (key2899, 2), (key2833, -1), (key2915, -1), (key2797, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2978, -1), (key2999, -1), (key2952, -1), (key2999, -1), (key2952, -1), (key2978, -1), (key2962, 1), (key3004, 1), (key2945, 1), (key3004, 1), (key2945, 1), (key2962, 1)]

def rawRow1736 : Integer.Sparse Key := [(key2655, -2), (key2655, -2), (key2617, -2), (key2656, 1), (key2643, 1), (key2656, 1), (key2620, 1), (key2643, 1), (key2620, 1), (key2899, 2), (key2899, 2), (key2810, 2), (key2915, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2797, -1), (key2999, -1), (key2978, -1), (key2999, -1), (key2952, -1), (key2978, -1), (key2952, -1), (key3004, 1), (key2962, 1), (key3004, 1), (key2945, 1), (key2962, 1), (key2945, 1)]

def rawRow1737 : Integer.Sparse Key := [(key2620, -2), (key2643, -2), (key2656, -2), (key2617, 1), (key2620, 1), (key2633, 1), (key2643, 1), (key2650, 1), (key2655, 1), (key2833, 2), (key2906, 2), (key2915, 2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, -1), (key2899, -1), (key2906, -1), (key2962, -1), (key2964, -1), (key2985, -1), (key2994, -1), (key3001, -1), (key3004, -1), (key2940, 1), (key2946, 1), (key2952, 1), (key2964, 1), (key2999, 1), (key3001, 1)]

def rawRow1738 : Integer.Sparse Key := [(key2620, -2), (key2656, -2), (key2643, -2), (key2620, 1), (key2617, 1), (key2643, 1), (key2633, 1), (key2655, 1), (key2650, 1), (key2833, 2), (key2915, 2), (key2906, 2), (key2797, -1), (key2787, -1), (key2833, -1), (key2810, -1), (key2906, -1), (key2899, -1), (key2964, -1), (key2962, -1), (key2994, -1), (key2985, -1), (key3004, -1), (key3001, -1), (key2946, 1), (key2940, 1), (key2964, 1), (key2952, 1), (key3001, 1), (key2999, 1)]

def rawRow1739 : Integer.Sparse Key := [(key2643, -2), (key2620, -2), (key2656, -2), (key2633, 1), (key2643, 1), (key2617, 1), (key2655, 1), (key2620, 1), (key2643, 1), (key2906, 2), (key2833, 2), (key2915, 2), (key2810, -1), (key2899, -1), (key2787, -1), (key2906, -1), (key2797, -1), (key2833, -1), (key2985, -1), (key3001, -1), (key2962, -1), (key3004, -1), (key2964, -1), (key2994, -1), (key2952, 1), (key2999, 1), (key2940, 1), (key3001, 1), (key2946, 1), (key2964, 1)]

def rawRow1740 : Integer.Sparse Key := [(key2643, -2), (key2656, -2), (key2620, -2), (key2643, 1), (key2633, 1), (key2655, 1), (key2617, 1), (key2643, 1), (key2620, 1), (key2906, 2), (key2915, 2), (key2833, 2), (key2899, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2833, -1), (key2797, -1), (key3001, -1), (key2985, -1), (key3004, -1), (key2962, -1), (key2994, -1), (key2964, -1), (key2999, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2964, 1), (key2946, 1)]

def rawRow1741 : Integer.Sparse Key := [(key2656, -2), (key2620, -2), (key2643, -2), (key2650, 1), (key2655, 1), (key2620, 1), (key2643, 1), (key2617, 1), (key2633, 1), (key2915, 2), (key2833, 2), (key2906, 2), (key2833, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2787, -1), (key2810, -1), (key2994, -1), (key3004, -1), (key2964, -1), (key3001, -1), (key2962, -1), (key2985, -1), (key2964, 1), (key3001, 1), (key2946, 1), (key2999, 1), (key2940, 1), (key2952, 1)]

def rawRow1742 : Integer.Sparse Key := [(key2656, -2), (key2643, -2), (key2620, -2), (key2655, 1), (key2650, 1), (key2643, 1), (key2620, 1), (key2633, 1), (key2617, 1), (key2915, 2), (key2906, 2), (key2833, 2), (key2906, -1), (key2833, -1), (key2899, -1), (key2797, -1), (key2810, -1), (key2787, -1), (key3004, -1), (key2994, -1), (key3001, -1), (key2964, -1), (key2985, -1), (key2962, -1), (key3001, 1), (key2964, 1), (key2999, 1), (key2946, 1), (key2952, 1), (key2940, 1)]

def rawRow1743 : Integer.Sparse Key := [(key2810, -2), (key2899, -2), (key2899, -2), (key2833, 1), (key2833, 1), (key2906, 1), (key2906, 1), (key2915, 1), (key2915, 1), (key2617, 2), (key2655, 2), (key2655, 2), (key2945, -1), (key2945, -1), (key2962, -1), (key2962, -1), (key3004, -1), (key3004, -1), (key2620, -1), (key2620, -1), (key2643, -1), (key2643, -1), (key2656, -1), (key2656, -1), (key2797, 1), (key2797, 1), (key2833, 1), (key2833, 1), (key2915, 1), (key2915, 1)]

def rawRow1744 : Integer.Sparse Key := [(key2899, -2), (key2810, -2), (key2899, -2), (key2906, 1), (key2915, 1), (key2833, 1), (key2915, 1), (key2833, 1), (key2906, 1), (key2655, 2), (key2617, 2), (key2655, 2), (key2962, -1), (key3004, -1), (key2945, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2643, -1), (key2656, -1), (key2620, -1), (key2656, -1), (key2620, -1), (key2643, -1), (key2833, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, 1), (key2833, 1)]

def rawRow1745 : Integer.Sparse Key := [(key2899, -2), (key2899, -2), (key2810, -2), (key2915, 1), (key2906, 1), (key2915, 1), (key2833, 1), (key2906, 1), (key2833, 1), (key2655, 2), (key2655, 2), (key2617, 2), (key3004, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2945, -1), (key2656, -1), (key2643, -1), (key2656, -1), (key2620, -1), (key2643, -1), (key2620, -1), (key2915, 1), (key2833, 1), (key2915, 1), (key2797, 1), (key2833, 1), (key2797, 1)]

def rawRow1746 : Integer.Sparse Key := [(key2797, -2), (key2833, -2), (key2915, -2), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2833, 1), (key2906, 1), (key2945, 2), (key2962, 2), (key3004, 2), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2730, -1), (key2751, -1), (key2833, -1), (key2915, -1), (key2964, -1), (key2994, -1), (key2620, 1), (key2656, 1), (key2675, 1), (key2751, 1), (key2946, 1), (key2964, 1)]

def rawRow1747 : Integer.Sparse Key := [(key2797, -2), (key2915, -2), (key2833, -2), (key2797, 1), (key2787, 1), (key2899, 1), (key2810, 1), (key2906, 1), (key2833, 1), (key2945, 2), (key3004, 2), (key2962, 2), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2945, -1), (key2751, -1), (key2730, -1), (key2915, -1), (key2833, -1), (key2994, -1), (key2964, -1), (key2656, 1), (key2620, 1), (key2751, 1), (key2675, 1), (key2964, 1), (key2946, 1)]

def rawRow1748 : Integer.Sparse Key := [(key2833, -2), (key2797, -2), (key2915, -2), (key2810, 1), (key2833, 1), (key2787, 1), (key2906, 1), (key2797, 1), (key2899, 1), (key2962, 2), (key2945, 2), (key3004, 2), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2833, -1), (key2964, -1), (key2730, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2675, 1), (key2946, 1), (key2620, 1), (key2964, 1), (key2656, 1), (key2751, 1)]

def rawRow1749 : Integer.Sparse Key := [(key2833, -2), (key2915, -2), (key2797, -2), (key2833, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2899, 1), (key2797, 1), (key2962, 2), (key3004, 2), (key2945, 2), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, -1), (key2655, -1), (key2964, -1), (key2833, -1), (key2994, -1), (key2730, -1), (key2915, -1), (key2751, -1), (key2946, 1), (key2675, 1), (key2964, 1), (key2620, 1), (key2751, 1), (key2656, 1)]

def rawRow1750 : Integer.Sparse Key := [(key2915, -2), (key2797, -2), (key2833, -2), (key2899, 1), (key2906, 1), (key2797, 1), (key2833, 1), (key2787, 1), (key2810, 1), (key3004, 2), (key2945, 2), (key2962, 2), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, -1), (key2672, -1), (key2915, -1), (key2994, -1), (key2751, -1), (key2964, -1), (key2730, -1), (key2833, -1), (key2751, 1), (key2964, 1), (key2656, 1), (key2946, 1), (key2620, 1), (key2675, 1)]

def rawRow1751 : Integer.Sparse Key := [(key2915, -2), (key2833, -2), (key2797, -2), (key2906, 1), (key2899, 1), (key2833, 1), (key2797, 1), (key2810, 1), (key2787, 1), (key3004, 2), (key2962, 2), (key2945, 2), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, -1), (key2617, -1), (key2994, -1), (key2915, -1), (key2964, -1), (key2751, -1), (key2833, -1), (key2730, -1), (key2964, 1), (key2751, 1), (key2946, 1), (key2656, 1), (key2675, 1), (key2620, 1)]

def rawRow1752 : Integer.Sparse Key := [(key2952, -2), (key2978, -2), (key2999, -2), (key2962, 1), (key2964, 1), (key2985, 1), (key3001, 1), (key2994, 1), (key3004, 1), (key2620, 2), (key2643, 2), (key2656, 2), (key2730, -1), (key2751, -1), (key2833, -1), (key2964, -1), (key2915, -1), (key2994, -1), (key2617, -1), (key2620, -1), (key2633, -1), (key2643, -1), (key2650, -1), (key2655, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2833, 1), (key2899, 1), (key2906, 1)]

end MUB6.Certificate.GramRows

end OAI
end


