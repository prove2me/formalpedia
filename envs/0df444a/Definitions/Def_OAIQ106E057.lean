-- Prove2me | Definitions.Def_OAIQ106E057
-- name    : OAIQ106E057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:08:35.502339+00:00
-- url     : https://prove2.me/theorems/d7db5efa-1ace-4185-a3dd-131e21b66495
-- title:
--   Definitions bundle OAIQ106E057 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1088 declarations of OpenAI's Lean: 1088 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow9019`, `OAI.MUB6.Certificate.GramRows.rawRow902`, `OAI.MUB6.Certificate.GramRows.rawRow9020`, `OAI.MUB6.Certificate.GramRows.rawRow9021`, `OAI.MUB6.Certificate.GramRows.rawRow9022`, `OAI.MUB6.Certificate.GramRows.rawRow9023`, `OAI.MUB6.Certificate.GramRows.rawRow9024`, `OAI.MUB6.Certificate.GramRows.rawRow9025`, `OAI.MUB6.Certificate.GramRows.rawRow9026`, `OAI.MUB6.Certificate.GramRows.rawRow9027`, `OAI.MUB6.Certificate.GramRows.rawRow9028`, `OAI.MUB6.Certificate.GramRows.rawRow9029`, `OAI.MUB6.Certificate.GramRows.rawRow903`, `OAI.MUB6.Certificate.GramRows.rawRow9030`, `OAI.MUB6.Certificate.GramRows.rawRow9031`, `OAI.MUB6.Certificate.GramRows.rawRow9032`, `OAI.MUB6.Certificate.GramRows.rawRow9033`, `OAI.MUB6.Certificate.GramRows.rawRow9034`, `OAI.MUB6.Certificate.GramRows.rawRow9035`, `OAI.MUB6.Certificate.GramRows.rawRow9036`, `OAI.MUB6.Certificate.GramRows.rawRow9037`, `OAI.MUB6.Certificate.GramRows.rawRow9038`, `OAI.MUB6.Certificate.GramRows.rawRow9039`, `OAI.MUB6.Certificate.GramRows.rawRow904`, `OAI.MUB6.Certificate.GramRows.rawRow9040`, `OAI.MUB6.Certificate.GramRows.rawRow9041`, `OAI.MUB6.Certificate.GramRows.rawRow9042`, `OAI.MUB6.Certificate.GramRows.rawRow9043`, `OAI.MUB6.Certificate.GramRows.rawRow9044`, `OAI.MUB6.Certificate.GramRows.rawRow9045`, `OAI.MUB6.Certificate.GramRows.rawRow9046`, `OAI.MUB6.Certificate.GramRows.rawRow9047`, `OAI.MUB6.Certificate.GramRows.rawRow9048`, `OAI.MUB6.Certificate.GramRows.rawRow9049`, `OAI.MUB6.Certificate.GramRows.rawRow905`, `OAI.MUB6.Certificate.GramRows.rawRow9050`, `OAI.MUB6.Certificate.GramRows.rawRow9051`, `OAI.MUB6.Certificate.GramRows.rawRow9052`, `OAI.MUB6.Certificate.GramRows.rawRow9053`, `OAI.MUB6.Certificate.GramRows.rawRow9054` and 1048 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block100`, `MutuallyUnbiased_GramRows_Block101`, `MutuallyUnbiased_GramRows_Block102`, `MutuallyUnbiased_GramRows_Block25`, `MutuallyUnbiased_GramRows_Block26`, `MutuallyUnbiased_GramRows_Block27`, `MutuallyUnbiased_GramRows_Block28`, `MutuallyUnbiased_GramRows_Block94`, `MutuallyUnbiased_GramRows_Block95`, `MutuallyUnbiased_GramRows_Block96`, `MutuallyUnbiased_GramRows_Block97`, `MutuallyUnbiased_GramRows_Block98`, `MutuallyUnbiased_GramRows_Block99`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e`.
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

def rawRow91 : Integer.Sparse Key := [(key2650, -2), (key2656, 1), (key2655, 1), (key2620, 2), (key2656, -1), (key2643, -1), (key2620, -1), (key2617, -1), (key2643, 1), (key2633, 1), (key2730, 2), (key2751, -1), (key2749, -1), (key2675, -2), (key2751, 1), (key2739, 1), (key2675, 1), (key2672, 1), (key2730, -1), (key2707, -1), (key2833, -2), (key2915, 1), (key2906, 1), (key2797, 2), (key2915, -1), (key2899, -1), (key2797, -1), (key2787, -1), (key2833, 1), (key2810, 1), (key2964, 1), (key2962, 1), (key2994, -1), (key2985, -1), (key2946, -1), (key2945, -1), (key2994, 1), (key2978, 1), (key2946, 1), (key2940, 1), (key2964, -1), (key2952, -1)]

def rawRow92 : Integer.Sparse Key := [(key2655, -2), (key2650, 1), (key2656, 1), (key2643, 2), (key2620, -1), (key2656, -1), (key2633, -1), (key2643, -1), (key2617, 1), (key2655, 1), (key2749, 2), (key2730, -1), (key2751, -1), (key2739, -2), (key2675, 1), (key2751, 1), (key2707, 1), (key2739, 1), (key2672, -1), (key2749, -1), (key2906, -2), (key2833, 1), (key2915, 1), (key2899, 2), (key2797, -1), (key2915, -1), (key2810, -1), (key2899, -1), (key2787, 1), (key2906, 1), (key2985, 1), (key3001, 1), (key2962, -1), (key3004, -1), (key2978, -1), (key2999, -1), (key2945, 1), (key3004, 1), (key2952, 1), (key2999, 1), (key2940, -1), (key3001, -1)]

def rawRow93 : Integer.Sparse Key := [(key2655, -2), (key2656, 1), (key2650, 1), (key2643, 2), (key2656, -1), (key2620, -1), (key2643, -1), (key2633, -1), (key2655, 1), (key2617, 1), (key2749, 2), (key2751, -1), (key2730, -1), (key2739, -2), (key2751, 1), (key2675, 1), (key2739, 1), (key2707, 1), (key2749, -1), (key2672, -1), (key2906, -2), (key2915, 1), (key2833, 1), (key2899, 2), (key2915, -1), (key2797, -1), (key2899, -1), (key2810, -1), (key2906, 1), (key2787, 1), (key3001, 1), (key2985, 1), (key3004, -1), (key2962, -1), (key2999, -1), (key2978, -1), (key3004, 1), (key2945, 1), (key2999, 1), (key2952, 1), (key3001, -1), (key2940, -1)]

def rawRow94 : Integer.Sparse Key := [(key2672, -2), (key2675, 1), (key2675, 1), (key2707, 2), (key2739, -1), (key2739, -1), (key2730, -1), (key2730, -1), (key2749, 1), (key2749, 1), (key2617, 2), (key2620, -1), (key2620, -1), (key2810, -2), (key2833, 1), (key2833, 1), (key2952, 1), (key2952, 1), (key2962, -1), (key2962, -1), (key2633, -2), (key2643, 1), (key2643, 1), (key2707, 2), (key2730, -1), (key2730, -1), (key2978, -1), (key2978, -1), (key2985, 1), (key2985, 1), (key2650, 1), (key2650, 1), (key2655, -1), (key2655, -1), (key2739, -1), (key2739, -1), (key2749, 1), (key2749, 1), (key2899, 1), (key2899, 1), (key2906, -1), (key2906, -1)]

def rawRow95 : Integer.Sparse Key := [(key2675, -2), (key2672, 1), (key2675, 1), (key2739, 2), (key2707, -1), (key2739, -1), (key2749, -1), (key2751, -1), (key2730, 1), (key2751, 1), (key2620, 2), (key2617, -1), (key2620, -1), (key2833, -2), (key2810, 1), (key2833, 1), (key2962, 1), (key2964, 1), (key2952, -1), (key2964, -1), (key2643, -2), (key2633, 1), (key2643, 1), (key2730, 2), (key2707, -1), (key2730, -1), (key2985, -1), (key2994, -1), (key2978, 1), (key2994, 1), (key2655, 1), (key2656, 1), (key2650, -1), (key2656, -1), (key2749, -1), (key2751, -1), (key2739, 1), (key2751, 1), (key2906, 1), (key2915, 1), (key2899, -1), (key2915, -1)]

def rawRow96 : Integer.Sparse Key := [(key2675, -2), (key2675, 1), (key2672, 1), (key2739, 2), (key2739, -1), (key2707, -1), (key2751, -1), (key2749, -1), (key2751, 1), (key2730, 1), (key2620, 2), (key2620, -1), (key2617, -1), (key2833, -2), (key2833, 1), (key2810, 1), (key2964, 1), (key2962, 1), (key2964, -1), (key2952, -1), (key2643, -2), (key2643, 1), (key2633, 1), (key2730, 2), (key2730, -1), (key2707, -1), (key2994, -1), (key2985, -1), (key2994, 1), (key2978, 1), (key2656, 1), (key2655, 1), (key2656, -1), (key2650, -1), (key2751, -1), (key2749, -1), (key2751, 1), (key2739, 1), (key2915, 1), (key2906, 1), (key2915, -1), (key2899, -1)]

def rawRow97 : Integer.Sparse Key := [(key2707, -2), (key2730, 1), (key2730, 1), (key2672, 2), (key2749, -1), (key2749, -1), (key2675, -1), (key2675, -1), (key2739, 1), (key2739, 1), (key2810, 2), (key2833, -1), (key2833, -1), (key2617, -2), (key2962, 1), (key2962, 1), (key2620, 1), (key2620, 1), (key2833, -1), (key2833, -1), (key2707, -2), (key2978, 1), (key2978, 1), (key2633, 2), (key2985, -1), (key2985, -1), (key2643, -1), (key2643, -1), (key2730, 1), (key2730, 1), (key2739, 1), (key2739, 1), (key2899, -1), (key2899, -1), (key2650, -1), (key2650, -1), (key2906, 1), (key2906, 1), (key2655, 1), (key2655, 1), (key2749, -1), (key2749, -1)]

def rawRow98 : Integer.Sparse Key := [(key2730, -2), (key2707, 1), (key2730, 1), (key2749, 2), (key2672, -1), (key2749, -1), (key2739, -1), (key2751, -1), (key2675, 1), (key2751, 1), (key2833, 2), (key2810, -1), (key2833, -1), (key2962, -2), (key2617, 1), (key2962, 1), (key2833, 1), (key2964, 1), (key2620, -1), (key2964, -1), (key2978, -2), (key2707, 1), (key2978, 1), (key2985, 2), (key2633, -1), (key2985, -1), (key2730, -1), (key2994, -1), (key2643, 1), (key2994, 1), (key2899, 1), (key2999, 1), (key2739, -1), (key2999, -1), (key2906, -1), (key3001, -1), (key2650, 1), (key3001, 1), (key2749, 1), (key3004, 1), (key2655, -1), (key3004, -1)]

def rawRow99 : Integer.Sparse Key := [(key2730, -2), (key2730, 1), (key2707, 1), (key2749, 2), (key2749, -1), (key2672, -1), (key2751, -1), (key2739, -1), (key2751, 1), (key2675, 1), (key2833, 2), (key2833, -1), (key2810, -1), (key2962, -2), (key2962, 1), (key2617, 1), (key2964, 1), (key2833, 1), (key2964, -1), (key2620, -1), (key2978, -2), (key2978, 1), (key2707, 1), (key2985, 2), (key2985, -1), (key2633, -1), (key2994, -1), (key2730, -1), (key2994, 1), (key2643, 1), (key2999, 1), (key2899, 1), (key2999, -1), (key2739, -1), (key3001, -1), (key2906, -1), (key3001, 1), (key2650, 1), (key3004, 1), (key2749, 1), (key3004, -1), (key2655, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9728 : Integer.Sparse Key := [(key3030, 1), (key2885, 1), (key3026, 1), (key2732, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2885, 1), (key3023, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key3026, 1), (key2732, 1), (key3023, 1), (key2644, 1), (key2706, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key2860, 1), (key2640, 1), (key2706, 1), (key2632, 1), (key2927, -2), (key2923, -2), (key2758, -2), (key2927, -2), (key2920, -2), (key2660, -2), (key2923, -2), (key2758, -2), (key2920, -2), (key2660, -2), (key2753, -2), (key2658, -2)]

def rawRow9729 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2660, 1), (key2660, 1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1), (key2794, 1), (key2794, 1), (key2829, 1), (key2829, 1), (key2927, 1), (key2927, 1), (key3010, 1), (key3010, 1), (key3017, 1), (key3017, 1), (key3030, 1), (key3030, 1), (key2621, -2), (key2644, -2), (key2644, -2), (key2676, -2), (key2732, -2), (key2732, -2), (key2798, -2), (key2798, -2), (key2835, -2), (key2835, -2), (key2885, -2), (key2885, -2)]

def rawRow9730 : Integer.Sparse Key := [(key2646, 1), (key2653, 1), (key2612, 1), (key2653, 1), (key2616, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key2644, -2), (key2621, -2), (key2644, -2), (key2732, -2), (key2676, -2), (key2732, -2), (key2835, -2), (key2885, -2), (key2798, -2), (key2885, -2), (key2798, -2), (key2835, -2)]

def rawRow9731 : Integer.Sparse Key := [(key2653, 1), (key2646, 1), (key2653, 1), (key2612, 1), (key2640, 1), (key2616, 1), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2927, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key2794, 1), (key3030, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key3010, 1), (key2644, -2), (key2644, -2), (key2621, -2), (key2732, -2), (key2732, -2), (key2676, -2), (key2885, -2), (key2835, -2), (key2885, -2), (key2798, -2), (key2835, -2), (key2798, -2)]

def rawRow9732 : Integer.Sparse Key := [(key2667, 1), (key2667, 1), (key2735, 1), (key2735, 1), (key2747, 1), (key2747, 1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2660, 1), (key2660, 1), (key2758, 1), (key2758, 1), (key2927, 1), (key2927, 1), (key2676, -2), (key2798, -2), (key2798, -2), (key2621, -2), (key2835, -2), (key2835, -2), (key2644, -2), (key2644, -2), (key2732, -2), (key2732, -2), (key2885, -2), (key2885, -2)]

def rawRow9733 : Integer.Sparse Key := [(key2735, 1), (key2747, 1), (key2667, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2798, -2), (key2676, -2), (key2798, -2), (key2835, -2), (key2621, -2), (key2835, -2), (key2732, -2), (key2885, -2), (key2644, -2), (key2885, -2), (key2644, -2), (key2732, -2)]

def rawRow9734 : Integer.Sparse Key := [(key2747, 1), (key2735, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2667, 1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2927, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2660, 1), (key2798, -2), (key2798, -2), (key2676, -2), (key2835, -2), (key2835, -2), (key2621, -2), (key2885, -2), (key2732, -2), (key2885, -2), (key2644, -2), (key2732, -2), (key2644, -2)]

def rawRow9735 : Integer.Sparse Key := [(key2936, 1), (key2943, 1), (key2948, 1), (key2998, 1), (key2960, 1), (key3000, 1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2612, 1), (key2653, 1), (key2667, 1), (key2943, 1), (key2747, 1), (key2960, 1), (key2616, 1), (key2640, 1), (key2671, 1), (key2726, 1), (key2794, 1), (key2829, 1), (key2732, -2), (key2835, -2), (key2885, -2), (key2644, -2), (key2798, -2), (key2885, -2), (key2621, -2), (key2644, -2), (key2676, -2), (key2732, -2), (key2798, -2), (key2835, -2)]

def rawRow9736 : Integer.Sparse Key := [(key2943, 1), (key2936, 1), (key2998, 1), (key2948, 1), (key3000, 1), (key2960, 1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2653, 1), (key2612, 1), (key2943, 1), (key2667, 1), (key2960, 1), (key2747, 1), (key2640, 1), (key2616, 1), (key2726, 1), (key2671, 1), (key2829, 1), (key2794, 1), (key2732, -2), (key2885, -2), (key2835, -2), (key2644, -2), (key2885, -2), (key2798, -2), (key2644, -2), (key2621, -2), (key2732, -2), (key2676, -2), (key2835, -2), (key2798, -2)]

def rawRow9737 : Integer.Sparse Key := [(key2948, 1), (key2960, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2667, 1), (key2747, 1), (key2612, 1), (key2960, 1), (key2653, 1), (key2943, 1), (key2671, 1), (key2794, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2835, -2), (key2732, -2), (key2885, -2), (key2798, -2), (key2644, -2), (key2885, -2), (key2676, -2), (key2798, -2), (key2621, -2), (key2835, -2), (key2644, -2), (key2732, -2)]

def rawRow9738 : Integer.Sparse Key := [(key2960, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2998, 1), (key2943, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2747, 1), (key2667, 1), (key2960, 1), (key2612, 1), (key2943, 1), (key2653, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2726, 1), (key2640, 1), (key2835, -2), (key2885, -2), (key2732, -2), (key2798, -2), (key2885, -2), (key2644, -2), (key2798, -2), (key2676, -2), (key2835, -2), (key2621, -2), (key2732, -2), (key2644, -2)]

def rawRow9739 : Integer.Sparse Key := [(key2998, 1), (key3000, 1), (key2943, 1), (key2960, 1), (key2936, 1), (key2948, 1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2943, 1), (key2960, 1), (key2653, 1), (key2747, 1), (key2612, 1), (key2667, 1), (key2726, 1), (key2829, 1), (key2640, 1), (key2794, 1), (key2616, 1), (key2671, 1), (key2885, -2), (key2732, -2), (key2835, -2), (key2885, -2), (key2644, -2), (key2798, -2), (key2732, -2), (key2835, -2), (key2644, -2), (key2798, -2), (key2621, -2), (key2676, -2)]

def rawRow9740 : Integer.Sparse Key := [(key3000, 1), (key2998, 1), (key2960, 1), (key2943, 1), (key2948, 1), (key2936, 1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2960, 1), (key2943, 1), (key2747, 1), (key2653, 1), (key2667, 1), (key2612, 1), (key2829, 1), (key2726, 1), (key2794, 1), (key2640, 1), (key2671, 1), (key2616, 1), (key2885, -2), (key2835, -2), (key2732, -2), (key2885, -2), (key2798, -2), (key2644, -2), (key2835, -2), (key2732, -2), (key2798, -2), (key2644, -2), (key2676, -2), (key2621, -2)]

def rawRow9741 : Integer.Sparse Key := [(key1294, -6), (key1571, -6), (key1786, -6), (key1786, -6), (key1314, 2), (key1335, 2), (key1335, 2), (key1544, 2), (key1770, 2), (key1770, 2), (key1653, 2), (key1653, 2), (key1811, 2), (key1811, 2), (key1838, 2), (key1838, 2)]

def rawRow9742 : Integer.Sparse Key := [(key1294, -6), (key1786, -6), (key1571, -6), (key1786, -6), (key1335, 2), (key1314, 2), (key1335, 2), (key1770, 2), (key1544, 2), (key1770, 2), (key1811, 2), (key1838, 2), (key1653, 2), (key1838, 2), (key1653, 2), (key1811, 2)]

def rawRow9743 : Integer.Sparse Key := [(key1294, -6), (key1786, -6), (key1786, -6), (key1571, -6), (key1335, 2), (key1335, 2), (key1314, 2), (key1770, 2), (key1770, 2), (key1544, 2), (key1838, 2), (key1811, 2), (key1838, 2), (key1653, 2), (key1811, 2), (key1653, 2)]

def rawRow9744 : Integer.Sparse Key := [(key1571, -6), (key1294, -6), (key1786, -6), (key1786, -6), (key1544, 2), (key1653, 2), (key1653, 2), (key1314, 2), (key1811, 2), (key1811, 2), (key1335, 2), (key1335, 2), (key1770, 2), (key1770, 2), (key1838, 2), (key1838, 2)]

def rawRow9745 : Integer.Sparse Key := [(key1571, -6), (key1786, -6), (key1294, -6), (key1786, -6), (key1653, 2), (key1544, 2), (key1653, 2), (key1811, 2), (key1314, 2), (key1811, 2), (key1770, 2), (key1838, 2), (key1335, 2), (key1838, 2), (key1335, 2), (key1770, 2)]

def rawRow9746 : Integer.Sparse Key := [(key1571, -6), (key1786, -6), (key1786, -6), (key1294, -6), (key1653, 2), (key1653, 2), (key1544, 2), (key1811, 2), (key1811, 2), (key1314, 2), (key1838, 2), (key1770, 2), (key1838, 2), (key1335, 2), (key1770, 2), (key1335, 2)]

def rawRow9747 : Integer.Sparse Key := [(key1786, -6), (key1294, -6), (key1571, -6), (key1786, -6), (key1770, 2), (key1811, 2), (key1838, 2), (key1335, 2), (key1653, 2), (key1838, 2), (key1314, 2), (key1335, 2), (key1544, 2), (key1770, 2), (key1653, 2), (key1811, 2)]

def rawRow9748 : Integer.Sparse Key := [(key1786, -6), (key1294, -6), (key1786, -6), (key1571, -6), (key1770, 2), (key1838, 2), (key1811, 2), (key1335, 2), (key1838, 2), (key1653, 2), (key1335, 2), (key1314, 2), (key1770, 2), (key1544, 2), (key1811, 2), (key1653, 2)]

def rawRow9749 : Integer.Sparse Key := [(key1786, -6), (key1571, -6), (key1294, -6), (key1786, -6), (key1811, 2), (key1770, 2), (key1838, 2), (key1653, 2), (key1335, 2), (key1838, 2), (key1544, 2), (key1653, 2), (key1314, 2), (key1811, 2), (key1335, 2), (key1770, 2)]

def rawRow9750 : Integer.Sparse Key := [(key1786, -6), (key1571, -6), (key1786, -6), (key1294, -6), (key1811, 2), (key1838, 2), (key1770, 2), (key1653, 2), (key1838, 2), (key1335, 2), (key1653, 2), (key1544, 2), (key1811, 2), (key1314, 2), (key1770, 2), (key1335, 2)]

def rawRow9751 : Integer.Sparse Key := [(key1786, -6), (key1786, -6), (key1294, -6), (key1571, -6), (key1838, 2), (key1770, 2), (key1811, 2), (key1838, 2), (key1335, 2), (key1653, 2), (key1770, 2), (key1811, 2), (key1335, 2), (key1653, 2), (key1314, 2), (key1544, 2)]

def rawRow9752 : Integer.Sparse Key := [(key1786, -6), (key1786, -6), (key1571, -6), (key1294, -6), (key1838, 2), (key1811, 2), (key1770, 2), (key1838, 2), (key1653, 2), (key1335, 2), (key1811, 2), (key1770, 2), (key1653, 2), (key1335, 2), (key1544, 2), (key1314, 2)]

def rawRow9753 : Integer.Sparse Key := [(key1314, -6), (key1422, -6), (key1811, -6), (key1811, -6), (key1294, 2), (key1335, 2), (key1335, 2), (key1389, 2), (key1770, 2), (key1770, 2), (key1453, 2), (key1453, 2), (key1786, 2), (key1786, 2), (key1838, 2), (key1838, 2)]

def rawRow9754 : Integer.Sparse Key := [(key1314, -6), (key1811, -6), (key1422, -6), (key1811, -6), (key1335, 2), (key1294, 2), (key1335, 2), (key1770, 2), (key1389, 2), (key1770, 2), (key1786, 2), (key1838, 2), (key1453, 2), (key1838, 2), (key1453, 2), (key1786, 2)]

def rawRow9755 : Integer.Sparse Key := [(key1314, -6), (key1811, -6), (key1811, -6), (key1422, -6), (key1335, 2), (key1335, 2), (key1294, 2), (key1770, 2), (key1770, 2), (key1389, 2), (key1838, 2), (key1786, 2), (key1838, 2), (key1453, 2), (key1786, 2), (key1453, 2)]

def rawRow9756 : Integer.Sparse Key := [(key1422, -6), (key1314, -6), (key1811, -6), (key1811, -6), (key1389, 2), (key1453, 2), (key1453, 2), (key1294, 2), (key1786, 2), (key1786, 2), (key1335, 2), (key1335, 2), (key1770, 2), (key1770, 2), (key1838, 2), (key1838, 2)]

def rawRow9757 : Integer.Sparse Key := [(key1422, -6), (key1811, -6), (key1314, -6), (key1811, -6), (key1453, 2), (key1389, 2), (key1453, 2), (key1786, 2), (key1294, 2), (key1786, 2), (key1770, 2), (key1838, 2), (key1335, 2), (key1838, 2), (key1335, 2), (key1770, 2)]

def rawRow9758 : Integer.Sparse Key := [(key1422, -6), (key1811, -6), (key1811, -6), (key1314, -6), (key1453, 2), (key1453, 2), (key1389, 2), (key1786, 2), (key1786, 2), (key1294, 2), (key1838, 2), (key1770, 2), (key1838, 2), (key1335, 2), (key1770, 2), (key1335, 2)]

def rawRow9759 : Integer.Sparse Key := [(key1811, -6), (key1314, -6), (key1422, -6), (key1811, -6), (key1770, 2), (key1786, 2), (key1838, 2), (key1335, 2), (key1453, 2), (key1838, 2), (key1294, 2), (key1335, 2), (key1389, 2), (key1770, 2), (key1453, 2), (key1786, 2)]

def rawRow9760 : Integer.Sparse Key := [(key1811, -6), (key1314, -6), (key1811, -6), (key1422, -6), (key1770, 2), (key1838, 2), (key1786, 2), (key1335, 2), (key1838, 2), (key1453, 2), (key1335, 2), (key1294, 2), (key1770, 2), (key1389, 2), (key1786, 2), (key1453, 2)]

def rawRow9761 : Integer.Sparse Key := [(key1811, -6), (key1422, -6), (key1314, -6), (key1811, -6), (key1786, 2), (key1770, 2), (key1838, 2), (key1453, 2), (key1335, 2), (key1838, 2), (key1389, 2), (key1453, 2), (key1294, 2), (key1786, 2), (key1335, 2), (key1770, 2)]

def rawRow9762 : Integer.Sparse Key := [(key1811, -6), (key1422, -6), (key1811, -6), (key1314, -6), (key1786, 2), (key1838, 2), (key1770, 2), (key1453, 2), (key1838, 2), (key1335, 2), (key1453, 2), (key1389, 2), (key1786, 2), (key1294, 2), (key1770, 2), (key1335, 2)]

def rawRow9763 : Integer.Sparse Key := [(key1811, -6), (key1811, -6), (key1314, -6), (key1422, -6), (key1838, 2), (key1770, 2), (key1786, 2), (key1838, 2), (key1335, 2), (key1453, 2), (key1770, 2), (key1786, 2), (key1335, 2), (key1453, 2), (key1294, 2), (key1389, 2)]

def rawRow9764 : Integer.Sparse Key := [(key1811, -6), (key1811, -6), (key1422, -6), (key1314, -6), (key1838, 2), (key1786, 2), (key1770, 2), (key1838, 2), (key1453, 2), (key1335, 2), (key1786, 2), (key1770, 2), (key1453, 2), (key1335, 2), (key1389, 2), (key1294, 2)]

def rawRow9765 : Integer.Sparse Key := [(key2770, 6), (key2770, 6), (key2773, 6), (key2932, 6), (key2601, -6), (key2890, -6), (key2911, -6), (key2911, -6)]

def rawRow9766 : Integer.Sparse Key := [(key2770, 6), (key2773, 6), (key2770, 6), (key2932, 6), (key2601, -6), (key2911, -6), (key2890, -6), (key2911, -6)]

def rawRow9767 : Integer.Sparse Key := [(key2773, 6), (key2770, 6), (key2770, 6), (key2932, 6), (key2601, -6), (key2911, -6), (key2911, -6), (key2890, -6)]

def rawRow9768 : Integer.Sparse Key := [(key2770, 6), (key2770, 6), (key2932, 6), (key2773, 6), (key2890, -6), (key2601, -6), (key2911, -6), (key2911, -6)]

def rawRow9769 : Integer.Sparse Key := [(key2770, 6), (key2932, 6), (key2770, 6), (key2773, 6), (key2890, -6), (key2911, -6), (key2601, -6), (key2911, -6)]

def rawRow9770 : Integer.Sparse Key := [(key2932, 6), (key2770, 6), (key2770, 6), (key2773, 6), (key2890, -6), (key2911, -6), (key2911, -6), (key2601, -6)]

def rawRow9771 : Integer.Sparse Key := [(key2770, 6), (key2773, 6), (key2932, 6), (key2770, 6), (key2911, -6), (key2601, -6), (key2890, -6), (key2911, -6)]

def rawRow9772 : Integer.Sparse Key := [(key2773, 6), (key2770, 6), (key2932, 6), (key2770, 6), (key2911, -6), (key2601, -6), (key2911, -6), (key2890, -6)]

def rawRow9773 : Integer.Sparse Key := [(key2770, 6), (key2932, 6), (key2773, 6), (key2770, 6), (key2911, -6), (key2890, -6), (key2601, -6), (key2911, -6)]

def rawRow9774 : Integer.Sparse Key := [(key2932, 6), (key2770, 6), (key2773, 6), (key2770, 6), (key2911, -6), (key2890, -6), (key2911, -6), (key2601, -6)]

def rawRow9775 : Integer.Sparse Key := [(key2773, 6), (key2932, 6), (key2770, 6), (key2770, 6), (key2911, -6), (key2911, -6), (key2601, -6), (key2890, -6)]

def rawRow9776 : Integer.Sparse Key := [(key2932, 6), (key2773, 6), (key2770, 6), (key2770, 6), (key2911, -6), (key2911, -6), (key2890, -6), (key2601, -6)]

def rawRow9777 : Integer.Sparse Key := [(key2847, 6), (key2847, 6), (key2890, 6), (key2969, 6), (key2594, -6), (key2773, -6), (key2881, -6), (key2881, -6)]

def rawRow9778 : Integer.Sparse Key := [(key2847, 6), (key2890, 6), (key2847, 6), (key2969, 6), (key2594, -6), (key2881, -6), (key2773, -6), (key2881, -6)]

def rawRow9779 : Integer.Sparse Key := [(key2890, 6), (key2847, 6), (key2847, 6), (key2969, 6), (key2594, -6), (key2881, -6), (key2881, -6), (key2773, -6)]

def rawRow9780 : Integer.Sparse Key := [(key2847, 6), (key2847, 6), (key2969, 6), (key2890, 6), (key2773, -6), (key2594, -6), (key2881, -6), (key2881, -6)]

def rawRow9781 : Integer.Sparse Key := [(key2847, 6), (key2969, 6), (key2847, 6), (key2890, 6), (key2773, -6), (key2881, -6), (key2594, -6), (key2881, -6)]

def rawRow9782 : Integer.Sparse Key := [(key2969, 6), (key2847, 6), (key2847, 6), (key2890, 6), (key2773, -6), (key2881, -6), (key2881, -6), (key2594, -6)]

def rawRow9783 : Integer.Sparse Key := [(key2847, 6), (key2890, 6), (key2969, 6), (key2847, 6), (key2881, -6), (key2594, -6), (key2773, -6), (key2881, -6)]

def rawRow9784 : Integer.Sparse Key := [(key2890, 6), (key2847, 6), (key2969, 6), (key2847, 6), (key2881, -6), (key2594, -6), (key2881, -6), (key2773, -6)]

def rawRow9785 : Integer.Sparse Key := [(key2847, 6), (key2969, 6), (key2890, 6), (key2847, 6), (key2881, -6), (key2773, -6), (key2594, -6), (key2881, -6)]

def rawRow9786 : Integer.Sparse Key := [(key2969, 6), (key2847, 6), (key2890, 6), (key2847, 6), (key2881, -6), (key2773, -6), (key2881, -6), (key2594, -6)]

def rawRow9787 : Integer.Sparse Key := [(key2890, 6), (key2969, 6), (key2847, 6), (key2847, 6), (key2881, -6), (key2881, -6), (key2594, -6), (key2773, -6)]

def rawRow9788 : Integer.Sparse Key := [(key2969, 6), (key2890, 6), (key2847, 6), (key2847, 6), (key2881, -6), (key2881, -6), (key2773, -6), (key2594, -6)]

def rawRow9789 : Integer.Sparse Key := [(key2402, 6), (key2402, 6), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -6), (key2926, -6)]

def rawRow9790 : Integer.Sparse Key := [(key2402, 6), (key2408, 6), (key2402, 6), (key2439, 6), (key2605, -6), (key2926, -6), (key2917, -6), (key2926, -6)]

def rawRow9791 : Integer.Sparse Key := [(key2408, 6), (key2402, 6), (key2402, 6), (key2439, 6), (key2605, -6), (key2926, -6), (key2926, -6), (key2917, -6)]

def rawRow9792 : Integer.Sparse Key := [(key2402, 6), (key2402, 6), (key2439, 6), (key2408, 6), (key2917, -6), (key2605, -6), (key2926, -6), (key2926, -6)]

def rawRow9793 : Integer.Sparse Key := [(key2402, 6), (key2439, 6), (key2402, 6), (key2408, 6), (key2917, -6), (key2926, -6), (key2605, -6), (key2926, -6)]

def rawRow9794 : Integer.Sparse Key := [(key2439, 6), (key2402, 6), (key2402, 6), (key2408, 6), (key2917, -6), (key2926, -6), (key2926, -6), (key2605, -6)]

def rawRow9795 : Integer.Sparse Key := [(key2402, 6), (key2408, 6), (key2439, 6), (key2402, 6), (key2926, -6), (key2605, -6), (key2917, -6), (key2926, -6)]

def rawRow9796 : Integer.Sparse Key := [(key2408, 6), (key2402, 6), (key2439, 6), (key2402, 6), (key2926, -6), (key2605, -6), (key2926, -6), (key2917, -6)]

def rawRow9797 : Integer.Sparse Key := [(key2402, 6), (key2439, 6), (key2408, 6), (key2402, 6), (key2926, -6), (key2917, -6), (key2605, -6), (key2926, -6)]

def rawRow9798 : Integer.Sparse Key := [(key2439, 6), (key2402, 6), (key2408, 6), (key2402, 6), (key2926, -6), (key2917, -6), (key2926, -6), (key2605, -6)]

def rawRow9799 : Integer.Sparse Key := [(key2408, 6), (key2439, 6), (key2402, 6), (key2402, 6), (key2926, -6), (key2926, -6), (key2605, -6), (key2917, -6)]

def rawRow9800 : Integer.Sparse Key := [(key2439, 6), (key2408, 6), (key2402, 6), (key2402, 6), (key2926, -6), (key2926, -6), (key2917, -6), (key2605, -6)]

def rawRow9801 : Integer.Sparse Key := [(key2468, 6), (key2468, 6), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -6), (key2884, -6)]

def rawRow9802 : Integer.Sparse Key := [(key2468, 6), (key2481, 6), (key2468, 6), (key2505, 6), (key2596, -6), (key2884, -6), (key2775, -6), (key2884, -6)]

def rawRow9803 : Integer.Sparse Key := [(key2481, 6), (key2468, 6), (key2468, 6), (key2505, 6), (key2596, -6), (key2884, -6), (key2884, -6), (key2775, -6)]

def rawRow9804 : Integer.Sparse Key := [(key2468, 6), (key2468, 6), (key2505, 6), (key2481, 6), (key2775, -6), (key2596, -6), (key2884, -6), (key2884, -6)]

def rawRow9805 : Integer.Sparse Key := [(key2468, 6), (key2505, 6), (key2468, 6), (key2481, 6), (key2775, -6), (key2884, -6), (key2596, -6), (key2884, -6)]

def rawRow9806 : Integer.Sparse Key := [(key2505, 6), (key2468, 6), (key2468, 6), (key2481, 6), (key2775, -6), (key2884, -6), (key2884, -6), (key2596, -6)]

def rawRow9807 : Integer.Sparse Key := [(key2468, 6), (key2481, 6), (key2505, 6), (key2468, 6), (key2884, -6), (key2596, -6), (key2775, -6), (key2884, -6)]

def rawRow9808 : Integer.Sparse Key := [(key2481, 6), (key2468, 6), (key2505, 6), (key2468, 6), (key2884, -6), (key2596, -6), (key2884, -6), (key2775, -6)]

def rawRow9809 : Integer.Sparse Key := [(key2468, 6), (key2505, 6), (key2481, 6), (key2468, 6), (key2884, -6), (key2775, -6), (key2596, -6), (key2884, -6)]

def rawRow9810 : Integer.Sparse Key := [(key2505, 6), (key2468, 6), (key2481, 6), (key2468, 6), (key2884, -6), (key2775, -6), (key2884, -6), (key2596, -6)]

def rawRow9811 : Integer.Sparse Key := [(key2481, 6), (key2505, 6), (key2468, 6), (key2468, 6), (key2884, -6), (key2884, -6), (key2596, -6), (key2775, -6)]

def rawRow9812 : Integer.Sparse Key := [(key2505, 6), (key2481, 6), (key2468, 6), (key2468, 6), (key2884, -6), (key2884, -6), (key2775, -6), (key2596, -6)]

def rawRow9813 : Integer.Sparse Key := [(key2175, -6), (key2175, -6), (key2179, -6), (key2189, -6), (key2078, 2), (key2078, 2), (key2082, 2), (key2275, 2), (key2275, 2), (key2327, 2), (key2327, 2), (key2328, 2), (key2328, 2), (key2289, 2), (key2333, 2), (key2333, 2)]

def rawRow9814 : Integer.Sparse Key := [(key2175, -6), (key2179, -6), (key2175, -6), (key2189, -6), (key2078, 2), (key2082, 2), (key2078, 2), (key2327, 2), (key2328, 2), (key2275, 2), (key2328, 2), (key2275, 2), (key2327, 2), (key2333, 2), (key2289, 2), (key2333, 2)]

def rawRow9815 : Integer.Sparse Key := [(key2179, -6), (key2175, -6), (key2175, -6), (key2189, -6), (key2082, 2), (key2078, 2), (key2078, 2), (key2328, 2), (key2327, 2), (key2328, 2), (key2275, 2), (key2327, 2), (key2275, 2), (key2333, 2), (key2333, 2), (key2289, 2)]

def rawRow9816 : Integer.Sparse Key := [(key2175, -6), (key2175, -6), (key2189, -6), (key2179, -6), (key2275, 2), (key2275, 2), (key2289, 2), (key2078, 2), (key2078, 2), (key2327, 2), (key2327, 2), (key2333, 2), (key2333, 2), (key2082, 2), (key2328, 2), (key2328, 2)]

def rawRow9817 : Integer.Sparse Key := [(key2175, -6), (key2189, -6), (key2175, -6), (key2179, -6), (key2275, 2), (key2289, 2), (key2275, 2), (key2327, 2), (key2333, 2), (key2078, 2), (key2333, 2), (key2078, 2), (key2327, 2), (key2328, 2), (key2082, 2), (key2328, 2)]

def rawRow9818 : Integer.Sparse Key := [(key2189, -6), (key2175, -6), (key2175, -6), (key2179, -6), (key2289, 2), (key2275, 2), (key2275, 2), (key2333, 2), (key2327, 2), (key2333, 2), (key2078, 2), (key2327, 2), (key2078, 2), (key2328, 2), (key2328, 2), (key2082, 2)]

def rawRow9819 : Integer.Sparse Key := [(key2175, -6), (key2179, -6), (key2189, -6), (key2175, -6), (key2327, 2), (key2328, 2), (key2333, 2), (key2078, 2), (key2082, 2), (key2275, 2), (key2328, 2), (key2289, 2), (key2333, 2), (key2078, 2), (key2275, 2), (key2327, 2)]

def rawRow9820 : Integer.Sparse Key := [(key2179, -6), (key2175, -6), (key2189, -6), (key2175, -6), (key2328, 2), (key2327, 2), (key2333, 2), (key2082, 2), (key2078, 2), (key2328, 2), (key2275, 2), (key2333, 2), (key2289, 2), (key2078, 2), (key2327, 2), (key2275, 2)]

def rawRow9821 : Integer.Sparse Key := [(key2175, -6), (key2189, -6), (key2179, -6), (key2175, -6), (key2327, 2), (key2333, 2), (key2328, 2), (key2275, 2), (key2289, 2), (key2078, 2), (key2333, 2), (key2082, 2), (key2328, 2), (key2275, 2), (key2078, 2), (key2327, 2)]

def rawRow9822 : Integer.Sparse Key := [(key2189, -6), (key2175, -6), (key2179, -6), (key2175, -6), (key2333, 2), (key2327, 2), (key2328, 2), (key2289, 2), (key2275, 2), (key2333, 2), (key2078, 2), (key2328, 2), (key2082, 2), (key2275, 2), (key2327, 2), (key2078, 2)]

def rawRow9823 : Integer.Sparse Key := [(key2179, -6), (key2189, -6), (key2175, -6), (key2175, -6), (key2328, 2), (key2333, 2), (key2327, 2), (key2328, 2), (key2333, 2), (key2082, 2), (key2289, 2), (key2078, 2), (key2275, 2), (key2327, 2), (key2078, 2), (key2275, 2)]

def rawRow9824 : Integer.Sparse Key := [(key2189, -6), (key2179, -6), (key2175, -6), (key2175, -6), (key2333, 2), (key2328, 2), (key2327, 2), (key2333, 2), (key2328, 2), (key2289, 2), (key2082, 2), (key2275, 2), (key2078, 2), (key2327, 2), (key2275, 2), (key2078, 2)]

def rawRow9825 : Integer.Sparse Key := [(key2275, -6), (key2275, -6), (key2281, -6), (key2289, -6), (key2078, 2), (key2078, 2), (key2087, 2), (key2175, 2), (key2175, 2), (key2327, 2), (key2327, 2), (key2330, 2), (key2330, 2), (key2189, 2), (key2333, 2), (key2333, 2)]

def rawRow9826 : Integer.Sparse Key := [(key2275, -6), (key2281, -6), (key2275, -6), (key2289, -6), (key2078, 2), (key2087, 2), (key2078, 2), (key2327, 2), (key2330, 2), (key2175, 2), (key2330, 2), (key2175, 2), (key2327, 2), (key2333, 2), (key2189, 2), (key2333, 2)]

def rawRow9827 : Integer.Sparse Key := [(key2281, -6), (key2275, -6), (key2275, -6), (key2289, -6), (key2087, 2), (key2078, 2), (key2078, 2), (key2330, 2), (key2327, 2), (key2330, 2), (key2175, 2), (key2327, 2), (key2175, 2), (key2333, 2), (key2333, 2), (key2189, 2)]

def rawRow9828 : Integer.Sparse Key := [(key2275, -6), (key2275, -6), (key2289, -6), (key2281, -6), (key2175, 2), (key2175, 2), (key2189, 2), (key2078, 2), (key2078, 2), (key2327, 2), (key2327, 2), (key2333, 2), (key2333, 2), (key2087, 2), (key2330, 2), (key2330, 2)]

def rawRow9829 : Integer.Sparse Key := [(key2275, -6), (key2289, -6), (key2275, -6), (key2281, -6), (key2175, 2), (key2189, 2), (key2175, 2), (key2327, 2), (key2333, 2), (key2078, 2), (key2333, 2), (key2078, 2), (key2327, 2), (key2330, 2), (key2087, 2), (key2330, 2)]

def rawRow9830 : Integer.Sparse Key := [(key2289, -6), (key2275, -6), (key2275, -6), (key2281, -6), (key2189, 2), (key2175, 2), (key2175, 2), (key2333, 2), (key2327, 2), (key2333, 2), (key2078, 2), (key2327, 2), (key2078, 2), (key2330, 2), (key2330, 2), (key2087, 2)]

def rawRow9831 : Integer.Sparse Key := [(key2275, -6), (key2281, -6), (key2289, -6), (key2275, -6), (key2327, 2), (key2330, 2), (key2333, 2), (key2078, 2), (key2087, 2), (key2175, 2), (key2330, 2), (key2189, 2), (key2333, 2), (key2078, 2), (key2175, 2), (key2327, 2)]

def rawRow9832 : Integer.Sparse Key := [(key2281, -6), (key2275, -6), (key2289, -6), (key2275, -6), (key2330, 2), (key2327, 2), (key2333, 2), (key2087, 2), (key2078, 2), (key2330, 2), (key2175, 2), (key2333, 2), (key2189, 2), (key2078, 2), (key2327, 2), (key2175, 2)]

def rawRow9833 : Integer.Sparse Key := [(key2275, -6), (key2289, -6), (key2281, -6), (key2275, -6), (key2327, 2), (key2333, 2), (key2330, 2), (key2175, 2), (key2189, 2), (key2078, 2), (key2333, 2), (key2087, 2), (key2330, 2), (key2175, 2), (key2078, 2), (key2327, 2)]

def rawRow9834 : Integer.Sparse Key := [(key2289, -6), (key2275, -6), (key2281, -6), (key2275, -6), (key2333, 2), (key2327, 2), (key2330, 2), (key2189, 2), (key2175, 2), (key2333, 2), (key2078, 2), (key2330, 2), (key2087, 2), (key2175, 2), (key2327, 2), (key2078, 2)]

def rawRow9835 : Integer.Sparse Key := [(key2281, -6), (key2289, -6), (key2275, -6), (key2275, -6), (key2330, 2), (key2333, 2), (key2327, 2), (key2330, 2), (key2333, 2), (key2087, 2), (key2189, 2), (key2078, 2), (key2175, 2), (key2327, 2), (key2078, 2), (key2175, 2)]

def rawRow9836 : Integer.Sparse Key := [(key2289, -6), (key2281, -6), (key2275, -6), (key2275, -6), (key2333, 2), (key2330, 2), (key2327, 2), (key2333, 2), (key2330, 2), (key2189, 2), (key2087, 2), (key2175, 2), (key2078, 2), (key2327, 2), (key2175, 2), (key2078, 2)]

def rawRow9837 : Integer.Sparse Key := [(key1033, 6), (key1033, 6), (key1041, 6), (key1076, 6), (key1019, -6), (key1127, -6), (key1199, -6), (key1199, -6)]

def rawRow9838 : Integer.Sparse Key := [(key1033, 6), (key1041, 6), (key1033, 6), (key1076, 6), (key1019, -6), (key1199, -6), (key1127, -6), (key1199, -6)]

def rawRow9839 : Integer.Sparse Key := [(key1041, 6), (key1033, 6), (key1033, 6), (key1076, 6), (key1019, -6), (key1199, -6), (key1199, -6), (key1127, -6)]

def rawRow9840 : Integer.Sparse Key := [(key1033, 6), (key1033, 6), (key1076, 6), (key1041, 6), (key1127, -6), (key1019, -6), (key1199, -6), (key1199, -6)]

def rawRow9841 : Integer.Sparse Key := [(key1033, 6), (key1076, 6), (key1033, 6), (key1041, 6), (key1127, -6), (key1199, -6), (key1019, -6), (key1199, -6)]

def rawRow9842 : Integer.Sparse Key := [(key1076, 6), (key1033, 6), (key1033, 6), (key1041, 6), (key1127, -6), (key1199, -6), (key1199, -6), (key1019, -6)]

def rawRow9843 : Integer.Sparse Key := [(key1033, 6), (key1041, 6), (key1076, 6), (key1033, 6), (key1199, -6), (key1019, -6), (key1127, -6), (key1199, -6)]

def rawRow9844 : Integer.Sparse Key := [(key1041, 6), (key1033, 6), (key1076, 6), (key1033, 6), (key1199, -6), (key1019, -6), (key1199, -6), (key1127, -6)]

def rawRow9845 : Integer.Sparse Key := [(key1033, 6), (key1076, 6), (key1041, 6), (key1033, 6), (key1199, -6), (key1127, -6), (key1019, -6), (key1199, -6)]

def rawRow9846 : Integer.Sparse Key := [(key1076, 6), (key1033, 6), (key1041, 6), (key1033, 6), (key1199, -6), (key1127, -6), (key1199, -6), (key1019, -6)]

def rawRow9847 : Integer.Sparse Key := [(key1041, 6), (key1076, 6), (key1033, 6), (key1033, 6), (key1199, -6), (key1199, -6), (key1019, -6), (key1127, -6)]

def rawRow9848 : Integer.Sparse Key := [(key1076, 6), (key1041, 6), (key1033, 6), (key1033, 6), (key1199, -6), (key1199, -6), (key1127, -6), (key1019, -6)]

def rawRow9849 : Integer.Sparse Key := [(key1111, 6), (key1111, 6), (key1127, 6), (key1155, 6), (key1006, -6), (key1041, -6), (key1193, -6), (key1193, -6)]

def rawRow9850 : Integer.Sparse Key := [(key1111, 6), (key1127, 6), (key1111, 6), (key1155, 6), (key1006, -6), (key1193, -6), (key1041, -6), (key1193, -6)]

def rawRow9851 : Integer.Sparse Key := [(key1127, 6), (key1111, 6), (key1111, 6), (key1155, 6), (key1006, -6), (key1193, -6), (key1193, -6), (key1041, -6)]

def rawRow9852 : Integer.Sparse Key := [(key1111, 6), (key1111, 6), (key1155, 6), (key1127, 6), (key1041, -6), (key1006, -6), (key1193, -6), (key1193, -6)]

def rawRow9853 : Integer.Sparse Key := [(key1111, 6), (key1155, 6), (key1111, 6), (key1127, 6), (key1041, -6), (key1193, -6), (key1006, -6), (key1193, -6)]

def rawRow9854 : Integer.Sparse Key := [(key1155, 6), (key1111, 6), (key1111, 6), (key1127, 6), (key1041, -6), (key1193, -6), (key1193, -6), (key1006, -6)]

def rawRow9855 : Integer.Sparse Key := [(key1111, 6), (key1127, 6), (key1155, 6), (key1111, 6), (key1193, -6), (key1006, -6), (key1041, -6), (key1193, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9856 : Integer.Sparse Key := [(key1127, 6), (key1111, 6), (key1155, 6), (key1111, 6), (key1193, -6), (key1006, -6), (key1193, -6), (key1041, -6)]

def rawRow9857 : Integer.Sparse Key := [(key1111, 6), (key1155, 6), (key1127, 6), (key1111, 6), (key1193, -6), (key1041, -6), (key1006, -6), (key1193, -6)]

def rawRow9858 : Integer.Sparse Key := [(key1155, 6), (key1111, 6), (key1127, 6), (key1111, 6), (key1193, -6), (key1041, -6), (key1193, -6), (key1006, -6)]

def rawRow9859 : Integer.Sparse Key := [(key1127, 6), (key1155, 6), (key1111, 6), (key1111, 6), (key1193, -6), (key1193, -6), (key1006, -6), (key1041, -6)]

def rawRow9860 : Integer.Sparse Key := [(key1155, 6), (key1127, 6), (key1111, 6), (key1111, 6), (key1193, -6), (key1193, -6), (key1041, -6), (key1006, -6)]

def rawRow9861 : Integer.Sparse Key := [(key2770, -6), (key2770, -6), (key2773, -6), (key2932, -6), (key2591, 2), (key2591, 2), (key2594, 2), (key2847, 2), (key2847, 2), (key2878, 2), (key2878, 2), (key2881, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2990, 2)]

def rawRow9862 : Integer.Sparse Key := [(key2770, -6), (key2773, -6), (key2770, -6), (key2932, -6), (key2591, 2), (key2594, 2), (key2591, 2), (key2878, 2), (key2881, 2), (key2847, 2), (key2881, 2), (key2847, 2), (key2878, 2), (key2990, 2), (key2969, 2), (key2990, 2)]

def rawRow9863 : Integer.Sparse Key := [(key2773, -6), (key2770, -6), (key2770, -6), (key2932, -6), (key2594, 2), (key2591, 2), (key2591, 2), (key2881, 2), (key2878, 2), (key2881, 2), (key2847, 2), (key2878, 2), (key2847, 2), (key2990, 2), (key2990, 2), (key2969, 2)]

def rawRow9864 : Integer.Sparse Key := [(key2770, -6), (key2770, -6), (key2932, -6), (key2773, -6), (key2847, 2), (key2847, 2), (key2969, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2881, 2)]

def rawRow9865 : Integer.Sparse Key := [(key2770, -6), (key2932, -6), (key2770, -6), (key2773, -6), (key2847, 2), (key2969, 2), (key2847, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2881, 2), (key2594, 2), (key2881, 2)]

def rawRow9866 : Integer.Sparse Key := [(key2932, -6), (key2770, -6), (key2770, -6), (key2773, -6), (key2969, 2), (key2847, 2), (key2847, 2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2881, 2), (key2881, 2), (key2594, 2)]

def rawRow9867 : Integer.Sparse Key := [(key2770, -6), (key2773, -6), (key2932, -6), (key2770, -6), (key2878, 2), (key2881, 2), (key2990, 2), (key2591, 2), (key2594, 2), (key2847, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2591, 2), (key2847, 2), (key2878, 2)]

def rawRow9868 : Integer.Sparse Key := [(key2773, -6), (key2770, -6), (key2932, -6), (key2770, -6), (key2881, 2), (key2878, 2), (key2990, 2), (key2594, 2), (key2591, 2), (key2881, 2), (key2847, 2), (key2990, 2), (key2969, 2), (key2591, 2), (key2878, 2), (key2847, 2)]

def rawRow9869 : Integer.Sparse Key := [(key2770, -6), (key2932, -6), (key2773, -6), (key2770, -6), (key2878, 2), (key2990, 2), (key2881, 2), (key2847, 2), (key2969, 2), (key2591, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2847, 2), (key2591, 2), (key2878, 2)]

def rawRow9870 : Integer.Sparse Key := [(key2932, -6), (key2770, -6), (key2773, -6), (key2770, -6), (key2990, 2), (key2878, 2), (key2881, 2), (key2969, 2), (key2847, 2), (key2990, 2), (key2591, 2), (key2881, 2), (key2594, 2), (key2847, 2), (key2878, 2), (key2591, 2)]

def rawRow9871 : Integer.Sparse Key := [(key2773, -6), (key2932, -6), (key2770, -6), (key2770, -6), (key2881, 2), (key2990, 2), (key2878, 2), (key2881, 2), (key2990, 2), (key2594, 2), (key2969, 2), (key2591, 2), (key2847, 2), (key2878, 2), (key2591, 2), (key2847, 2)]

def rawRow9872 : Integer.Sparse Key := [(key2932, -6), (key2773, -6), (key2770, -6), (key2770, -6), (key2990, 2), (key2881, 2), (key2878, 2), (key2990, 2), (key2881, 2), (key2969, 2), (key2594, 2), (key2847, 2), (key2591, 2), (key2878, 2), (key2847, 2), (key2591, 2)]

def rawRow9873 : Integer.Sparse Key := [(key2847, -6), (key2847, -6), (key2890, -6), (key2969, -6), (key2591, 2), (key2591, 2), (key2601, 2), (key2770, 2), (key2770, 2), (key2878, 2), (key2878, 2), (key2911, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2990, 2)]

def rawRow9874 : Integer.Sparse Key := [(key2847, -6), (key2890, -6), (key2847, -6), (key2969, -6), (key2591, 2), (key2601, 2), (key2591, 2), (key2878, 2), (key2911, 2), (key2770, 2), (key2911, 2), (key2770, 2), (key2878, 2), (key2990, 2), (key2932, 2), (key2990, 2)]

def rawRow9875 : Integer.Sparse Key := [(key2890, -6), (key2847, -6), (key2847, -6), (key2969, -6), (key2601, 2), (key2591, 2), (key2591, 2), (key2911, 2), (key2878, 2), (key2911, 2), (key2770, 2), (key2878, 2), (key2770, 2), (key2990, 2), (key2990, 2), (key2932, 2)]

def rawRow9876 : Integer.Sparse Key := [(key2847, -6), (key2847, -6), (key2969, -6), (key2890, -6), (key2770, 2), (key2770, 2), (key2932, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2911, 2)]

def rawRow9877 : Integer.Sparse Key := [(key2847, -6), (key2969, -6), (key2847, -6), (key2890, -6), (key2770, 2), (key2932, 2), (key2770, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2911, 2), (key2601, 2), (key2911, 2)]

def rawRow9878 : Integer.Sparse Key := [(key2969, -6), (key2847, -6), (key2847, -6), (key2890, -6), (key2932, 2), (key2770, 2), (key2770, 2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2911, 2), (key2911, 2), (key2601, 2)]

def rawRow9879 : Integer.Sparse Key := [(key2847, -6), (key2890, -6), (key2969, -6), (key2847, -6), (key2878, 2), (key2911, 2), (key2990, 2), (key2591, 2), (key2601, 2), (key2770, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2591, 2), (key2770, 2), (key2878, 2)]

def rawRow9880 : Integer.Sparse Key := [(key2890, -6), (key2847, -6), (key2969, -6), (key2847, -6), (key2911, 2), (key2878, 2), (key2990, 2), (key2601, 2), (key2591, 2), (key2911, 2), (key2770, 2), (key2990, 2), (key2932, 2), (key2591, 2), (key2878, 2), (key2770, 2)]

def rawRow9881 : Integer.Sparse Key := [(key2847, -6), (key2969, -6), (key2890, -6), (key2847, -6), (key2878, 2), (key2990, 2), (key2911, 2), (key2770, 2), (key2932, 2), (key2591, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2770, 2), (key2591, 2), (key2878, 2)]

def rawRow9882 : Integer.Sparse Key := [(key2969, -6), (key2847, -6), (key2890, -6), (key2847, -6), (key2990, 2), (key2878, 2), (key2911, 2), (key2932, 2), (key2770, 2), (key2990, 2), (key2591, 2), (key2911, 2), (key2601, 2), (key2770, 2), (key2878, 2), (key2591, 2)]

def rawRow9883 : Integer.Sparse Key := [(key2890, -6), (key2969, -6), (key2847, -6), (key2847, -6), (key2911, 2), (key2990, 2), (key2878, 2), (key2911, 2), (key2990, 2), (key2601, 2), (key2932, 2), (key2591, 2), (key2770, 2), (key2878, 2), (key2591, 2), (key2770, 2)]

def rawRow9884 : Integer.Sparse Key := [(key2969, -6), (key2890, -6), (key2847, -6), (key2847, -6), (key2990, 2), (key2911, 2), (key2878, 2), (key2990, 2), (key2911, 2), (key2932, 2), (key2601, 2), (key2770, 2), (key2591, 2), (key2878, 2), (key2770, 2), (key2591, 2)]

def rawRow9885 : Integer.Sparse Key := [(key2670, -6), (key2785, -6), (key2793, -6), (key2793, -6), (key2615, 6), (key2808, 6), (key2828, 6), (key2828, 6)]

def rawRow9886 : Integer.Sparse Key := [(key2670, -6), (key2793, -6), (key2785, -6), (key2793, -6), (key2615, 6), (key2828, 6), (key2808, 6), (key2828, 6)]

def rawRow9887 : Integer.Sparse Key := [(key2670, -6), (key2793, -6), (key2793, -6), (key2785, -6), (key2615, 6), (key2828, 6), (key2828, 6), (key2808, 6)]

def rawRow9888 : Integer.Sparse Key := [(key2785, -6), (key2670, -6), (key2793, -6), (key2793, -6), (key2808, 6), (key2615, 6), (key2828, 6), (key2828, 6)]

def rawRow9889 : Integer.Sparse Key := [(key2785, -6), (key2793, -6), (key2670, -6), (key2793, -6), (key2808, 6), (key2828, 6), (key2615, 6), (key2828, 6)]

def rawRow9890 : Integer.Sparse Key := [(key2785, -6), (key2793, -6), (key2793, -6), (key2670, -6), (key2808, 6), (key2828, 6), (key2828, 6), (key2615, 6)]

def rawRow9891 : Integer.Sparse Key := [(key2793, -6), (key2670, -6), (key2785, -6), (key2793, -6), (key2828, 6), (key2615, 6), (key2808, 6), (key2828, 6)]

def rawRow9892 : Integer.Sparse Key := [(key2793, -6), (key2670, -6), (key2793, -6), (key2785, -6), (key2828, 6), (key2615, 6), (key2828, 6), (key2808, 6)]

def rawRow9893 : Integer.Sparse Key := [(key2793, -6), (key2785, -6), (key2670, -6), (key2793, -6), (key2828, 6), (key2808, 6), (key2615, 6), (key2828, 6)]

def rawRow9894 : Integer.Sparse Key := [(key2793, -6), (key2785, -6), (key2793, -6), (key2670, -6), (key2828, 6), (key2808, 6), (key2828, 6), (key2615, 6)]

def rawRow9895 : Integer.Sparse Key := [(key2793, -6), (key2793, -6), (key2670, -6), (key2785, -6), (key2828, 6), (key2828, 6), (key2615, 6), (key2808, 6)]

def rawRow9896 : Integer.Sparse Key := [(key2793, -6), (key2793, -6), (key2785, -6), (key2670, -6), (key2828, 6), (key2828, 6), (key2808, 6), (key2615, 6)]

def rawRow9897 : Integer.Sparse Key := [(key2705, -6), (key2808, -6), (key2859, -6), (key2859, -6), (key2631, 6), (key2785, 6), (key2869, 6), (key2869, 6)]

def rawRow9898 : Integer.Sparse Key := [(key2705, -6), (key2859, -6), (key2808, -6), (key2859, -6), (key2631, 6), (key2869, 6), (key2785, 6), (key2869, 6)]

def rawRow9899 : Integer.Sparse Key := [(key2705, -6), (key2859, -6), (key2859, -6), (key2808, -6), (key2631, 6), (key2869, 6), (key2869, 6), (key2785, 6)]

def rawRow9900 : Integer.Sparse Key := [(key2808, -6), (key2705, -6), (key2859, -6), (key2859, -6), (key2785, 6), (key2631, 6), (key2869, 6), (key2869, 6)]

def rawRow9901 : Integer.Sparse Key := [(key2808, -6), (key2859, -6), (key2705, -6), (key2859, -6), (key2785, 6), (key2869, 6), (key2631, 6), (key2869, 6)]

def rawRow9902 : Integer.Sparse Key := [(key2808, -6), (key2859, -6), (key2859, -6), (key2705, -6), (key2785, 6), (key2869, 6), (key2869, 6), (key2631, 6)]

def rawRow9903 : Integer.Sparse Key := [(key2859, -6), (key2705, -6), (key2808, -6), (key2859, -6), (key2869, 6), (key2631, 6), (key2785, 6), (key2869, 6)]

def rawRow9904 : Integer.Sparse Key := [(key2859, -6), (key2705, -6), (key2859, -6), (key2808, -6), (key2869, 6), (key2631, 6), (key2869, 6), (key2785, 6)]

def rawRow9905 : Integer.Sparse Key := [(key2859, -6), (key2808, -6), (key2705, -6), (key2859, -6), (key2869, 6), (key2785, 6), (key2631, 6), (key2869, 6)]

def rawRow9906 : Integer.Sparse Key := [(key2859, -6), (key2808, -6), (key2859, -6), (key2705, -6), (key2869, 6), (key2785, 6), (key2869, 6), (key2631, 6)]

def rawRow9907 : Integer.Sparse Key := [(key2859, -6), (key2859, -6), (key2705, -6), (key2808, -6), (key2869, 6), (key2869, 6), (key2631, 6), (key2785, 6)]

def rawRow9908 : Integer.Sparse Key := [(key2859, -6), (key2859, -6), (key2808, -6), (key2705, -6), (key2869, 6), (key2869, 6), (key2785, 6), (key2631, 6)]

def rawRow9909 : Integer.Sparse Key := [(key2617, -2), (key2620, -2), (key2620, -2), (key2810, -2), (key2833, -2), (key2833, -2), (key2952, -2), (key2952, -2), (key2962, -2), (key2962, -2), (key2964, -2), (key2964, -2), (key2633, 2), (key2643, 2), (key2643, 2), (key2707, 2), (key2730, 2), (key2730, 2), (key2978, 2), (key2978, 2), (key2985, 2), (key2985, 2), (key2994, 2), (key2994, 2)]

def rawRow9910 : Integer.Sparse Key := [(key2620, -2), (key2617, -2), (key2620, -2), (key2833, -2), (key2810, -2), (key2833, -2), (key2962, -2), (key2964, -2), (key2952, -2), (key2964, -2), (key2952, -2), (key2962, -2), (key2643, 2), (key2633, 2), (key2643, 2), (key2730, 2), (key2707, 2), (key2730, 2), (key2985, 2), (key2994, 2), (key2978, 2), (key2994, 2), (key2978, 2), (key2985, 2)]

def rawRow9911 : Integer.Sparse Key := [(key2620, -2), (key2620, -2), (key2617, -2), (key2833, -2), (key2833, -2), (key2810, -2), (key2964, -2), (key2962, -2), (key2964, -2), (key2952, -2), (key2962, -2), (key2952, -2), (key2643, 2), (key2643, 2), (key2633, 2), (key2730, 2), (key2730, 2), (key2707, 2), (key2994, 2), (key2985, 2), (key2994, 2), (key2978, 2), (key2985, 2), (key2978, 2)]

def rawRow9912 : Integer.Sparse Key := [(key2810, -2), (key2833, -2), (key2833, -2), (key2617, -2), (key2962, -2), (key2962, -2), (key2620, -2), (key2620, -2), (key2833, -2), (key2833, -2), (key2964, -2), (key2964, -2), (key2707, 2), (key2978, 2), (key2978, 2), (key2633, 2), (key2985, 2), (key2985, 2), (key2643, 2), (key2643, 2), (key2730, 2), (key2730, 2), (key2994, 2), (key2994, 2)]

def rawRow9913 : Integer.Sparse Key := [(key2833, -2), (key2810, -2), (key2833, -2), (key2962, -2), (key2617, -2), (key2962, -2), (key2833, -2), (key2964, -2), (key2620, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2978, 2), (key2707, 2), (key2978, 2), (key2985, 2), (key2633, 2), (key2985, 2), (key2730, 2), (key2994, 2), (key2643, 2), (key2994, 2), (key2643, 2), (key2730, 2)]

def rawRow9914 : Integer.Sparse Key := [(key2833, -2), (key2833, -2), (key2810, -2), (key2962, -2), (key2962, -2), (key2617, -2), (key2964, -2), (key2833, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2620, -2), (key2978, 2), (key2978, 2), (key2707, 2), (key2985, 2), (key2985, 2), (key2633, 2), (key2994, 2), (key2730, 2), (key2994, 2), (key2643, 2), (key2730, 2), (key2643, 2)]

def rawRow9915 : Integer.Sparse Key := [(key2952, -2), (key2962, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2964, -2), (key2617, -2), (key2620, -2), (key2810, -2), (key2833, -2), (key2952, -2), (key2962, -2), (key2730, 2), (key2985, 2), (key2994, 2), (key2643, 2), (key2978, 2), (key2994, 2), (key2633, 2), (key2643, 2), (key2707, 2), (key2730, 2), (key2978, 2), (key2985, 2)]

def rawRow9916 : Integer.Sparse Key := [(key2952, -2), (key2964, -2), (key2962, -2), (key2620, -2), (key2964, -2), (key2833, -2), (key2620, -2), (key2617, -2), (key2833, -2), (key2810, -2), (key2962, -2), (key2952, -2), (key2730, 2), (key2994, 2), (key2985, 2), (key2643, 2), (key2994, 2), (key2978, 2), (key2643, 2), (key2633, 2), (key2730, 2), (key2707, 2), (key2985, 2), (key2978, 2)]

def rawRow9917 : Integer.Sparse Key := [(key2962, -2), (key2952, -2), (key2964, -2), (key2833, -2), (key2620, -2), (key2964, -2), (key2810, -2), (key2833, -2), (key2617, -2), (key2962, -2), (key2620, -2), (key2833, -2), (key2985, 2), (key2730, 2), (key2994, 2), (key2978, 2), (key2643, 2), (key2994, 2), (key2707, 2), (key2978, 2), (key2633, 2), (key2985, 2), (key2643, 2), (key2730, 2)]

def rawRow9918 : Integer.Sparse Key := [(key2962, -2), (key2964, -2), (key2952, -2), (key2833, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2810, -2), (key2962, -2), (key2617, -2), (key2833, -2), (key2620, -2), (key2985, 2), (key2994, 2), (key2730, 2), (key2978, 2), (key2994, 2), (key2643, 2), (key2978, 2), (key2707, 2), (key2985, 2), (key2633, 2), (key2730, 2), (key2643, 2)]

def rawRow9919 : Integer.Sparse Key := [(key2964, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2952, -2), (key2962, -2), (key2620, -2), (key2833, -2), (key2617, -2), (key2810, -2), (key2994, 2), (key2730, 2), (key2985, 2), (key2994, 2), (key2643, 2), (key2978, 2), (key2730, 2), (key2985, 2), (key2643, 2), (key2978, 2), (key2633, 2), (key2707, 2)]

def rawRow9920 : Integer.Sparse Key := [(key2964, -2), (key2962, -2), (key2952, -2), (key2964, -2), (key2833, -2), (key2620, -2), (key2962, -2), (key2952, -2), (key2833, -2), (key2620, -2), (key2810, -2), (key2617, -2), (key2994, 2), (key2985, 2), (key2730, 2), (key2994, 2), (key2978, 2), (key2643, 2), (key2985, 2), (key2730, 2), (key2978, 2), (key2643, 2), (key2707, 2), (key2633, 2)]

def rawRow9921 : Integer.Sparse Key := [(key2633, -2), (key2643, -2), (key2643, -2), (key2707, -2), (key2978, -2), (key2978, -2), (key2730, -2), (key2730, -2), (key2985, -2), (key2985, -2), (key2994, -2), (key2994, -2), (key2617, 2), (key2655, 2), (key2655, 2), (key2672, 2), (key2749, 2), (key2749, 2), (key2945, 2), (key2945, 2), (key2962, 2), (key2962, 2), (key3004, 2), (key3004, 2)]

def rawRow9922 : Integer.Sparse Key := [(key2643, -2), (key2633, -2), (key2643, -2), (key2978, -2), (key2707, -2), (key2978, -2), (key2985, -2), (key2994, -2), (key2730, -2), (key2994, -2), (key2730, -2), (key2985, -2), (key2655, 2), (key2617, 2), (key2655, 2), (key2749, 2), (key2672, 2), (key2749, 2), (key2962, 2), (key3004, 2), (key2945, 2), (key3004, 2), (key2945, 2), (key2962, 2)]

def rawRow9923 : Integer.Sparse Key := [(key2643, -2), (key2643, -2), (key2633, -2), (key2978, -2), (key2978, -2), (key2707, -2), (key2994, -2), (key2985, -2), (key2994, -2), (key2730, -2), (key2985, -2), (key2730, -2), (key2655, 2), (key2655, 2), (key2617, 2), (key2749, 2), (key2749, 2), (key2672, 2), (key3004, 2), (key2962, 2), (key3004, 2), (key2945, 2), (key2962, 2), (key2945, 2)]

def rawRow9924 : Integer.Sparse Key := [(key2707, -2), (key2730, -2), (key2730, -2), (key2633, -2), (key2985, -2), (key2985, -2), (key2643, -2), (key2643, -2), (key2978, -2), (key2978, -2), (key2994, -2), (key2994, -2), (key2672, 2), (key2749, 2), (key2749, 2), (key2617, 2), (key2962, 2), (key2962, 2), (key2655, 2), (key2655, 2), (key2749, 2), (key2749, 2), (key3004, 2), (key3004, 2)]

def rawRow9925 : Integer.Sparse Key := [(key2730, -2), (key2707, -2), (key2730, -2), (key2985, -2), (key2633, -2), (key2985, -2), (key2978, -2), (key2994, -2), (key2643, -2), (key2994, -2), (key2643, -2), (key2978, -2), (key2749, 2), (key2672, 2), (key2749, 2), (key2962, 2), (key2617, 2), (key2962, 2), (key2749, 2), (key3004, 2), (key2655, 2), (key3004, 2), (key2655, 2), (key2749, 2)]

def rawRow9926 : Integer.Sparse Key := [(key2730, -2), (key2730, -2), (key2707, -2), (key2985, -2), (key2985, -2), (key2633, -2), (key2994, -2), (key2978, -2), (key2994, -2), (key2643, -2), (key2978, -2), (key2643, -2), (key2749, 2), (key2749, 2), (key2672, 2), (key2962, 2), (key2962, 2), (key2617, 2), (key3004, 2), (key2749, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key2655, 2)]

def rawRow9927 : Integer.Sparse Key := [(key2978, -2), (key2985, -2), (key2994, -2), (key2643, -2), (key2730, -2), (key2994, -2), (key2633, -2), (key2643, -2), (key2707, -2), (key2978, -2), (key2730, -2), (key2985, -2), (key2945, 2), (key2962, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key3004, 2), (key2617, 2), (key2655, 2), (key2672, 2), (key2749, 2), (key2945, 2), (key2962, 2)]

def rawRow9928 : Integer.Sparse Key := [(key2978, -2), (key2994, -2), (key2985, -2), (key2643, -2), (key2994, -2), (key2730, -2), (key2643, -2), (key2633, -2), (key2978, -2), (key2707, -2), (key2985, -2), (key2730, -2), (key2945, 2), (key3004, 2), (key2962, 2), (key2655, 2), (key3004, 2), (key2749, 2), (key2655, 2), (key2617, 2), (key2749, 2), (key2672, 2), (key2962, 2), (key2945, 2)]

def rawRow9929 : Integer.Sparse Key := [(key2985, -2), (key2978, -2), (key2994, -2), (key2730, -2), (key2643, -2), (key2994, -2), (key2707, -2), (key2730, -2), (key2633, -2), (key2985, -2), (key2643, -2), (key2978, -2), (key2962, 2), (key2945, 2), (key3004, 2), (key2749, 2), (key2655, 2), (key3004, 2), (key2672, 2), (key2749, 2), (key2617, 2), (key2962, 2), (key2655, 2), (key2749, 2)]

def rawRow9930 : Integer.Sparse Key := [(key2985, -2), (key2994, -2), (key2978, -2), (key2730, -2), (key2994, -2), (key2643, -2), (key2730, -2), (key2707, -2), (key2985, -2), (key2633, -2), (key2978, -2), (key2643, -2), (key2962, 2), (key3004, 2), (key2945, 2), (key2749, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key2672, 2), (key2962, 2), (key2617, 2), (key2749, 2), (key2655, 2)]

def rawRow9931 : Integer.Sparse Key := [(key2994, -2), (key2978, -2), (key2985, -2), (key2994, -2), (key2643, -2), (key2730, -2), (key2978, -2), (key2985, -2), (key2643, -2), (key2730, -2), (key2633, -2), (key2707, -2), (key3004, 2), (key2945, 2), (key2962, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key2945, 2), (key2962, 2), (key2655, 2), (key2749, 2), (key2617, 2), (key2672, 2)]

def rawRow9932 : Integer.Sparse Key := [(key2994, -2), (key2985, -2), (key2978, -2), (key2994, -2), (key2730, -2), (key2643, -2), (key2985, -2), (key2978, -2), (key2730, -2), (key2643, -2), (key2707, -2), (key2633, -2), (key3004, 2), (key2962, 2), (key2945, 2), (key3004, 2), (key2749, 2), (key2655, 2), (key2962, 2), (key2945, 2), (key2749, 2), (key2655, 2), (key2672, 2), (key2617, 2)]

def rawRow9933 : Integer.Sparse Key := [(key982, 2), (key986, 2), (key986, 2), (key1096, 2), (key1171, 2), (key1171, 2), (key1185, 2), (key1185, 2), (key1222, 2), (key1222, 2), (key1224, 2), (key1224, 2), (key986, -2), (key986, -2), (key988, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key1171, -2), (key1175, -2), (key1175, -2), (key1186, -2), (key1224, -2), (key1224, -2)]

def rawRow9934 : Integer.Sparse Key := [(key986, 2), (key982, 2), (key986, 2), (key1171, 2), (key1096, 2), (key1171, 2), (key1222, 2), (key1224, 2), (key1185, 2), (key1224, 2), (key1185, 2), (key1222, 2), (key986, -2), (key988, -2), (key986, -2), (key1171, -2), (key1175, -2), (key1100, -2), (key1175, -2), (key1100, -2), (key1171, -2), (key1224, -2), (key1186, -2), (key1224, -2)]

def rawRow9935 : Integer.Sparse Key := [(key986, 2), (key986, 2), (key982, 2), (key1171, 2), (key1171, 2), (key1096, 2), (key1224, 2), (key1222, 2), (key1224, 2), (key1185, 2), (key1222, 2), (key1185, 2), (key988, -2), (key986, -2), (key986, -2), (key1175, -2), (key1171, -2), (key1175, -2), (key1100, -2), (key1171, -2), (key1100, -2), (key1224, -2), (key1224, -2), (key1186, -2)]

def rawRow9936 : Integer.Sparse Key := [(key1096, 2), (key1185, 2), (key1185, 2), (key982, 2), (key1222, 2), (key1222, 2), (key986, 2), (key986, 2), (key1171, 2), (key1171, 2), (key1224, 2), (key1224, 2), (key1100, -2), (key1100, -2), (key1186, -2), (key986, -2), (key986, -2), (key1171, -2), (key1171, -2), (key1224, -2), (key1224, -2), (key988, -2), (key1175, -2), (key1175, -2)]

def rawRow9937 : Integer.Sparse Key := [(key1185, 2), (key1096, 2), (key1185, 2), (key1222, 2), (key982, 2), (key1222, 2), (key1171, 2), (key1224, 2), (key986, 2), (key1224, 2), (key986, 2), (key1171, 2), (key1100, -2), (key1186, -2), (key1100, -2), (key1171, -2), (key1224, -2), (key986, -2), (key1224, -2), (key986, -2), (key1171, -2), (key1175, -2), (key988, -2), (key1175, -2)]

def rawRow9938 : Integer.Sparse Key := [(key1185, 2), (key1185, 2), (key1096, 2), (key1222, 2), (key1222, 2), (key982, 2), (key1224, 2), (key1171, 2), (key1224, 2), (key986, 2), (key1171, 2), (key986, 2), (key1186, -2), (key1100, -2), (key1100, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key986, -2), (key1171, -2), (key986, -2), (key1175, -2), (key1175, -2), (key988, -2)]

def rawRow9939 : Integer.Sparse Key := [(key1171, 2), (key1222, 2), (key1224, 2), (key986, 2), (key1185, 2), (key1224, 2), (key982, 2), (key986, 2), (key1096, 2), (key1171, 2), (key1185, 2), (key1222, 2), (key1171, -2), (key1175, -2), (key1224, -2), (key986, -2), (key988, -2), (key1100, -2), (key1175, -2), (key1186, -2), (key1224, -2), (key986, -2), (key1100, -2), (key1171, -2)]

def rawRow9940 : Integer.Sparse Key := [(key1171, 2), (key1224, 2), (key1222, 2), (key986, 2), (key1224, 2), (key1185, 2), (key986, 2), (key982, 2), (key1171, 2), (key1096, 2), (key1222, 2), (key1185, 2), (key1175, -2), (key1171, -2), (key1224, -2), (key988, -2), (key986, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key1186, -2), (key986, -2), (key1171, -2), (key1100, -2)]

def rawRow9941 : Integer.Sparse Key := [(key1222, 2), (key1171, 2), (key1224, 2), (key1185, 2), (key986, 2), (key1224, 2), (key1096, 2), (key1185, 2), (key982, 2), (key1222, 2), (key986, 2), (key1171, 2), (key1171, -2), (key1224, -2), (key1175, -2), (key1100, -2), (key1186, -2), (key986, -2), (key1224, -2), (key988, -2), (key1175, -2), (key1100, -2), (key986, -2), (key1171, -2)]

def rawRow9942 : Integer.Sparse Key := [(key1222, 2), (key1224, 2), (key1171, 2), (key1185, 2), (key1224, 2), (key986, 2), (key1185, 2), (key1096, 2), (key1222, 2), (key982, 2), (key1171, 2), (key986, 2), (key1224, -2), (key1171, -2), (key1175, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1175, -2), (key988, -2), (key1100, -2), (key1171, -2), (key986, -2)]

def rawRow9943 : Integer.Sparse Key := [(key1224, 2), (key1171, 2), (key1222, 2), (key1224, 2), (key986, 2), (key1185, 2), (key1171, 2), (key1222, 2), (key986, 2), (key1185, 2), (key982, 2), (key1096, 2), (key1175, -2), (key1224, -2), (key1171, -2), (key1175, -2), (key1224, -2), (key988, -2), (key1186, -2), (key986, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1100, -2)]

def rawRow9944 : Integer.Sparse Key := [(key1224, 2), (key1222, 2), (key1171, 2), (key1224, 2), (key1185, 2), (key986, 2), (key1222, 2), (key1171, 2), (key1185, 2), (key986, 2), (key1096, 2), (key982, 2), (key1224, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1186, -2), (key988, -2), (key1100, -2), (key986, -2), (key1171, -2), (key1100, -2), (key986, -2)]

def rawRow9945 : Integer.Sparse Key := [(key986, 2), (key986, 2), (key988, 2), (key1100, 2), (key1100, 2), (key1175, 2), (key1185, 2), (key1186, 2), (key1185, 2), (key1224, 2), (key1186, 2), (key1224, 2), (key982, -2), (key986, -2), (key986, -2), (key1096, -2), (key1100, -2), (key1096, -2), (key1171, -2), (key1100, -2), (key1171, -2), (key1185, -2), (key1185, -2), (key1222, -2)]

def rawRow9946 : Integer.Sparse Key := [(key986, 2), (key988, 2), (key986, 2), (key1100, 2), (key1175, 2), (key1100, 2), (key1186, 2), (key1185, 2), (key1224, 2), (key1185, 2), (key1224, 2), (key1186, 2), (key986, -2), (key982, -2), (key986, -2), (key1100, -2), (key1096, -2), (key1171, -2), (key1096, -2), (key1171, -2), (key1100, -2), (key1185, -2), (key1222, -2), (key1185, -2)]

def rawRow9947 : Integer.Sparse Key := [(key988, 2), (key986, 2), (key986, 2), (key1175, 2), (key1100, 2), (key1100, 2), (key1224, 2), (key1224, 2), (key1186, 2), (key1186, 2), (key1185, 2), (key1185, 2), (key986, -2), (key986, -2), (key982, -2), (key1171, -2), (key1171, -2), (key1100, -2), (key1100, -2), (key1096, -2), (key1096, -2), (key1222, -2), (key1185, -2), (key1185, -2)]

def rawRow9948 : Integer.Sparse Key := [(key1100, 2), (key1185, 2), (key1186, 2), (key986, 2), (key1185, 2), (key1224, 2), (key986, 2), (key988, 2), (key1100, 2), (key1175, 2), (key1186, 2), (key1224, 2), (key1096, -2), (key1100, -2), (key1185, -2), (key982, -2), (key986, -2), (key1096, -2), (key1171, -2), (key1185, -2), (key1222, -2), (key986, -2), (key1100, -2), (key1171, -2)]

def rawRow9949 : Integer.Sparse Key := [(key1100, 2), (key1186, 2), (key1185, 2), (key986, 2), (key1224, 2), (key1185, 2), (key988, 2), (key986, 2), (key1175, 2), (key1100, 2), (key1224, 2), (key1186, 2), (key1100, -2), (key1096, -2), (key1185, -2), (key986, -2), (key982, -2), (key1171, -2), (key1096, -2), (key1222, -2), (key1185, -2), (key986, -2), (key1171, -2), (key1100, -2)]

def rawRow9950 : Integer.Sparse Key := [(key1185, 2), (key1100, 2), (key1186, 2), (key1185, 2), (key986, 2), (key1224, 2), (key1100, 2), (key1186, 2), (key986, 2), (key1224, 2), (key988, 2), (key1175, 2), (key1096, -2), (key1185, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key982, -2), (key1222, -2), (key986, -2), (key1171, -2), (key1100, -2), (key986, -2), (key1171, -2)]

def rawRow9951 : Integer.Sparse Key := [(key1185, 2), (key1186, 2), (key1100, 2), (key1185, 2), (key1224, 2), (key986, 2), (key1186, 2), (key1100, 2), (key1224, 2), (key986, 2), (key1175, 2), (key988, 2), (key1185, -2), (key1096, -2), (key1100, -2), (key1185, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1171, -2), (key986, -2), (key1100, -2), (key1171, -2), (key986, -2)]

def rawRow9952 : Integer.Sparse Key := [(key1186, 2), (key1100, 2), (key1185, 2), (key1224, 2), (key986, 2), (key1185, 2), (key1175, 2), (key1224, 2), (key988, 2), (key1186, 2), (key986, 2), (key1100, 2), (key1100, -2), (key1185, -2), (key1096, -2), (key1171, -2), (key1222, -2), (key986, -2), (key1185, -2), (key982, -2), (key1096, -2), (key1171, -2), (key986, -2), (key1100, -2)]

def rawRow9953 : Integer.Sparse Key := [(key1186, 2), (key1185, 2), (key1100, 2), (key1224, 2), (key1185, 2), (key986, 2), (key1224, 2), (key1175, 2), (key1186, 2), (key988, 2), (key1100, 2), (key986, 2), (key1185, -2), (key1100, -2), (key1096, -2), (key1222, -2), (key1171, -2), (key1185, -2), (key986, -2), (key1096, -2), (key982, -2), (key1171, -2), (key1100, -2), (key986, -2)]

def rawRow9954 : Integer.Sparse Key := [(key1175, 2), (key1224, 2), (key1224, 2), (key988, 2), (key1186, 2), (key1186, 2), (key986, 2), (key986, 2), (key1100, 2), (key1100, 2), (key1185, 2), (key1185, 2), (key1171, -2), (key1171, -2), (key1222, -2), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key982, -2), (key1096, -2), (key1096, -2)]

def rawRow9955 : Integer.Sparse Key := [(key1224, 2), (key1175, 2), (key1224, 2), (key1186, 2), (key988, 2), (key1186, 2), (key1100, 2), (key1185, 2), (key986, 2), (key1185, 2), (key986, 2), (key1100, 2), (key1171, -2), (key1222, -2), (key1171, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1185, -2), (key986, -2), (key1100, -2), (key1096, -2), (key982, -2), (key1096, -2)]

def rawRow9956 : Integer.Sparse Key := [(key1224, 2), (key1224, 2), (key1175, 2), (key1186, 2), (key1186, 2), (key988, 2), (key1185, 2), (key1100, 2), (key1185, 2), (key986, 2), (key1100, 2), (key986, 2), (key1222, -2), (key1171, -2), (key1171, -2), (key1185, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1100, -2), (key986, -2), (key1096, -2), (key1096, -2), (key982, -2)]

def rawRow9957 : Integer.Sparse Key := [(key91, -24), (key8, 6), (key91, 6), (key152, 6), (key152, 6)]

def rawRow9958 : Integer.Sparse Key := [(key91, -24), (key8, 6), (key152, 6), (key91, 6), (key152, 6)]

def rawRow9959 : Integer.Sparse Key := [(key91, -24), (key8, 6), (key152, 6), (key152, 6), (key91, 6)]

def rawRow9960 : Integer.Sparse Key := [(key91, -24), (key91, 6), (key8, 6), (key152, 6), (key152, 6)]

def rawRow9961 : Integer.Sparse Key := [(key91, -24), (key91, 6), (key152, 6), (key8, 6), (key152, 6)]

def rawRow9962 : Integer.Sparse Key := [(key91, -24), (key91, 6), (key152, 6), (key152, 6), (key8, 6)]

def rawRow9963 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key8, 6), (key91, 6), (key152, 6)]

def rawRow9964 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key8, 6), (key152, 6), (key91, 6)]

def rawRow9965 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key91, 6), (key8, 6), (key152, 6)]

def rawRow9966 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key91, 6), (key152, 6), (key8, 6)]

def rawRow9967 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key152, 6), (key8, 6), (key91, 6)]

def rawRow9968 : Integer.Sparse Key := [(key91, -24), (key152, 6), (key152, 6), (key91, 6), (key8, 6)]

def rawRow9969 : Integer.Sparse Key := [(key152, -24), (key8, 6), (key91, 6), (key91, 6), (key152, 6)]

def rawRow9970 : Integer.Sparse Key := [(key152, -24), (key8, 6), (key91, 6), (key152, 6), (key91, 6)]

def rawRow9971 : Integer.Sparse Key := [(key152, -24), (key8, 6), (key152, 6), (key91, 6), (key91, 6)]

def rawRow9972 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key8, 6), (key91, 6), (key152, 6)]

def rawRow9973 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key8, 6), (key152, 6), (key91, 6)]

def rawRow9974 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key91, 6), (key8, 6), (key152, 6)]

def rawRow9975 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key91, 6), (key152, 6), (key8, 6)]

def rawRow9976 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key152, 6), (key8, 6), (key91, 6)]

def rawRow9977 : Integer.Sparse Key := [(key152, -24), (key91, 6), (key152, 6), (key91, 6), (key8, 6)]

def rawRow9978 : Integer.Sparse Key := [(key152, -24), (key152, 6), (key8, 6), (key91, 6), (key91, 6)]

def rawRow9979 : Integer.Sparse Key := [(key152, -24), (key152, 6), (key91, 6), (key8, 6), (key91, 6)]

def rawRow9980 : Integer.Sparse Key := [(key152, -24), (key152, 6), (key91, 6), (key91, 6), (key8, 6)]

def rawRow9981 : Integer.Sparse Key := [(key88, -6), (key88, -6), (key94, -6), (key156, -6), (key5, 2), (key9, 2), (key14, 2), (key92, 2), (key92, 2), (key153, 2), (key153, 2), (key161, 2), (key161, 2), (key194, 2), (key203, 2), (key203, 2)]

def rawRow9982 : Integer.Sparse Key := [(key88, -6), (key94, -6), (key88, -6), (key156, -6), (key5, 2), (key11, 2), (key9, 2), (key153, 2), (key161, 2), (key92, 2), (key161, 2), (key92, 2), (key153, 2), (key203, 2), (key194, 2), (key203, 2)]

def rawRow9983 : Integer.Sparse Key := [(key94, -6), (key88, -6), (key88, -6), (key156, -6), (key11, 2), (key5, 2), (key9, 2), (key161, 2), (key153, 2), (key161, 2), (key92, 2), (key153, 2), (key92, 2), (key203, 2), (key203, 2), (key194, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9984 : Integer.Sparse Key := [(key88, -6), (key88, -6), (key156, -6), (key94, -6), (key88, 2), (key88, 2), (key156, 2), (key5, 2), (key9, 2), (key153, 2), (key153, 2), (key203, 2), (key203, 2), (key14, 2), (key161, 2), (key161, 2)]

def rawRow9985 : Integer.Sparse Key := [(key88, -6), (key156, -6), (key88, -6), (key94, -6), (key88, 2), (key156, 2), (key88, 2), (key165, 2), (key187, 2), (key5, 2), (key187, 2), (key9, 2), (key153, 2), (key161, 2), (key14, 2), (key161, 2)]

def rawRow9986 : Integer.Sparse Key := [(key156, -6), (key88, -6), (key88, -6), (key94, -6), (key156, 2), (key88, 2), (key88, 2), (key187, 2), (key165, 2), (key187, 2), (key5, 2), (key153, 2), (key9, 2), (key161, 2), (key161, 2), (key14, 2)]

def rawRow9987 : Integer.Sparse Key := [(key88, -6), (key94, -6), (key156, -6), (key88, -6), (key165, 2), (key167, 2), (key187, 2), (key5, 2), (key11, 2), (key88, 2), (key167, 2), (key156, 2), (key187, 2), (key9, 2), (key92, 2), (key153, 2)]

def rawRow9988 : Integer.Sparse Key := [(key94, -6), (key88, -6), (key156, -6), (key88, -6), (key167, 2), (key165, 2), (key187, 2), (key11, 2), (key5, 2), (key167, 2), (key88, 2), (key187, 2), (key156, 2), (key9, 2), (key153, 2), (key92, 2)]

def rawRow9989 : Integer.Sparse Key := [(key88, -6), (key156, -6), (key94, -6), (key88, -6), (key165, 2), (key187, 2), (key167, 2), (key88, 2), (key156, 2), (key5, 2), (key187, 2), (key11, 2), (key167, 2), (key92, 2), (key9, 2), (key153, 2)]

def rawRow9990 : Integer.Sparse Key := [(key156, -6), (key88, -6), (key94, -6), (key88, -6), (key187, 2), (key165, 2), (key167, 2), (key156, 2), (key88, 2), (key187, 2), (key5, 2), (key167, 2), (key11, 2), (key92, 2), (key153, 2), (key9, 2)]

def rawRow9991 : Integer.Sparse Key := [(key94, -6), (key156, -6), (key88, -6), (key88, -6), (key167, 2), (key187, 2), (key165, 2), (key167, 2), (key187, 2), (key11, 2), (key156, 2), (key5, 2), (key88, 2), (key153, 2), (key9, 2), (key92, 2)]

def rawRow9992 : Integer.Sparse Key := [(key156, -6), (key94, -6), (key88, -6), (key88, -6), (key187, 2), (key167, 2), (key165, 2), (key187, 2), (key167, 2), (key156, 2), (key11, 2), (key88, 2), (key5, 2), (key153, 2), (key92, 2), (key9, 2)]

def rawRow9993 : Integer.Sparse Key := [(key165, -6), (key167, -6), (key167, -6), (key187, -6), (key5, 2), (key11, 2), (key11, 2), (key88, 2), (key94, 2), (key88, 2), (key167, 2), (key94, 2), (key167, 2), (key156, 2), (key156, 2), (key187, 2)]

def rawRow9994 : Integer.Sparse Key := [(key167, -6), (key165, -6), (key167, -6), (key187, -6), (key11, 2), (key5, 2), (key11, 2), (key94, 2), (key88, 2), (key167, 2), (key88, 2), (key167, 2), (key94, 2), (key156, 2), (key187, 2), (key156, 2)]

def rawRow9995 : Integer.Sparse Key := [(key167, -6), (key167, -6), (key165, -6), (key187, -6), (key11, 2), (key11, 2), (key5, 2), (key167, 2), (key167, 2), (key94, 2), (key94, 2), (key88, 2), (key88, 2), (key187, 2), (key156, 2), (key156, 2)]

def rawRow9996 : Integer.Sparse Key := [(key165, -6), (key167, -6), (key187, -6), (key167, -6), (key88, 2), (key94, 2), (key156, 2), (key5, 2), (key11, 2), (key88, 2), (key167, 2), (key156, 2), (key187, 2), (key11, 2), (key94, 2), (key167, 2)]

def rawRow9997 : Integer.Sparse Key := [(key167, -6), (key165, -6), (key187, -6), (key167, -6), (key94, 2), (key88, 2), (key156, 2), (key11, 2), (key5, 2), (key167, 2), (key88, 2), (key187, 2), (key156, 2), (key11, 2), (key167, 2), (key94, 2)]

def rawRow9998 : Integer.Sparse Key := [(key165, -6), (key187, -6), (key167, -6), (key167, -6), (key88, 2), (key156, 2), (key94, 2), (key88, 2), (key156, 2), (key5, 2), (key187, 2), (key11, 2), (key167, 2), (key94, 2), (key11, 2), (key167, 2)]

def rawRow9999 : Integer.Sparse Key := [(key187, -6), (key165, -6), (key167, -6), (key167, -6), (key156, 2), (key88, 2), (key94, 2), (key156, 2), (key88, 2), (key187, 2), (key5, 2), (key167, 2), (key11, 2), (key94, 2), (key167, 2), (key11, 2)]

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

def rawRow902 : Integer.Sparse Key := [(key2799, -6), (key2849, 2), (key2776, 2), (key2849, 2), (key2696, 6), (key2849, -2), (key2622, -2), (key2849, -2), (key2696, -2), (key2661, -2), (key2696, -2), (key2799, 2), (key2606, 2), (key2799, 2)]

def rawRow903 : Integer.Sparse Key := [(key2799, -6), (key2849, 2), (key2849, 2), (key2776, 2), (key2696, 6), (key2849, -2), (key2849, -2), (key2622, -2), (key2696, -2), (key2696, -2), (key2661, -2), (key2799, 2), (key2799, 2), (key2606, 2)]

def rawRow904 : Integer.Sparse Key := [(key1296, -2), (key1788, -2), (key1799, -2), (key1296, 1), (key1303, 1), (key1573, 1), (key1597, 1), (key1791, 1), (key1799, 1), (key1316, 2), (key1813, 2), (key1826, 2), (key1316, -1), (key1330, -1), (key1424, -1), (key1448, -1), (key1818, -1), (key1826, -1), (key1337, -1), (key1340, -1), (key1655, -1), (key1668, -1), (key1840, -1), (key1845, -1), (key1337, 1), (key1346, 1), (key1455, 1), (key1467, 1), (key1842, 1), (key1845, 1)]

def rawRow905 : Integer.Sparse Key := [(key1296, -2), (key1799, -2), (key1788, -2), (key1303, 1), (key1296, 1), (key1597, 1), (key1573, 1), (key1799, 1), (key1791, 1), (key1316, 2), (key1826, 2), (key1813, 2), (key1330, -1), (key1316, -1), (key1448, -1), (key1424, -1), (key1826, -1), (key1818, -1), (key1340, -1), (key1337, -1), (key1668, -1), (key1655, -1), (key1845, -1), (key1840, -1), (key1346, 1), (key1337, 1), (key1467, 1), (key1455, 1), (key1845, 1), (key1842, 1)]

def rawRow906 : Integer.Sparse Key := [(key1788, -2), (key1296, -2), (key1799, -2), (key1573, 1), (key1791, 1), (key1296, 1), (key1799, 1), (key1303, 1), (key1597, 1), (key1813, 2), (key1316, 2), (key1826, 2), (key1424, -1), (key1818, -1), (key1316, -1), (key1826, -1), (key1330, -1), (key1448, -1), (key1655, -1), (key1840, -1), (key1337, -1), (key1845, -1), (key1340, -1), (key1668, -1), (key1455, 1), (key1842, 1), (key1337, 1), (key1845, 1), (key1346, 1), (key1467, 1)]

def rawRow907 : Integer.Sparse Key := [(key1788, -2), (key1799, -2), (key1296, -2), (key1791, 1), (key1573, 1), (key1799, 1), (key1296, 1), (key1597, 1), (key1303, 1), (key1813, 2), (key1826, 2), (key1316, 2), (key1818, -1), (key1424, -1), (key1826, -1), (key1316, -1), (key1448, -1), (key1330, -1), (key1840, -1), (key1655, -1), (key1845, -1), (key1337, -1), (key1668, -1), (key1340, -1), (key1842, 1), (key1455, 1), (key1845, 1), (key1337, 1), (key1467, 1), (key1346, 1)]

def rawRow908 : Integer.Sparse Key := [(key1799, -2), (key1296, -2), (key1788, -2), (key1597, 1), (key1799, 1), (key1303, 1), (key1791, 1), (key1296, 1), (key1573, 1), (key1826, 2), (key1316, 2), (key1813, 2), (key1448, -1), (key1826, -1), (key1330, -1), (key1818, -1), (key1316, -1), (key1424, -1), (key1668, -1), (key1845, -1), (key1340, -1), (key1840, -1), (key1337, -1), (key1655, -1), (key1467, 1), (key1845, 1), (key1346, 1), (key1842, 1), (key1337, 1), (key1455, 1)]

def rawRow909 : Integer.Sparse Key := [(key1799, -2), (key1788, -2), (key1296, -2), (key1799, 1), (key1597, 1), (key1791, 1), (key1303, 1), (key1573, 1), (key1296, 1), (key1826, 2), (key1813, 2), (key1316, 2), (key1826, -1), (key1448, -1), (key1818, -1), (key1330, -1), (key1424, -1), (key1316, -1), (key1845, -1), (key1668, -1), (key1840, -1), (key1340, -1), (key1655, -1), (key1337, -1), (key1845, 1), (key1467, 1), (key1842, 1), (key1346, 1), (key1455, 1), (key1337, 1)]

def rawRow910 : Integer.Sparse Key := [(key1303, -2), (key1791, -2), (key1791, -2), (key1296, 1), (key1296, 1), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1330, 2), (key1818, 2), (key1818, 2), (key1316, -1), (key1316, -1), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1346, -1), (key1346, -1), (key1660, -1), (key1660, -1), (key1842, -1), (key1842, -1), (key1340, 1), (key1340, 1), (key1458, 1), (key1458, 1), (key1840, 1), (key1840, 1)]

def rawRow911 : Integer.Sparse Key := [(key1791, -2), (key1303, -2), (key1791, -2), (key1573, 1), (key1788, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1818, 2), (key1330, 2), (key1818, 2), (key1424, -1), (key1813, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1660, -1), (key1842, -1), (key1346, -1), (key1842, -1), (key1346, -1), (key1660, -1), (key1458, 1), (key1840, 1), (key1340, 1), (key1840, 1), (key1340, 1), (key1458, 1)]

def rawRow912 : Integer.Sparse Key := [(key1791, -2), (key1791, -2), (key1303, -2), (key1788, 1), (key1573, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1296, 1), (key1818, 2), (key1818, 2), (key1330, 2), (key1813, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1316, -1), (key1842, -1), (key1660, -1), (key1842, -1), (key1346, -1), (key1660, -1), (key1346, -1), (key1840, 1), (key1458, 1), (key1840, 1), (key1340, 1), (key1458, 1), (key1340, 1)]

def rawRow913 : Integer.Sparse Key := [(key1316, -2), (key1813, -2), (key1826, -2), (key1337, 1), (key1340, 1), (key1655, 1), (key1668, 1), (key1840, 1), (key1845, 1), (key1296, 2), (key1788, 2), (key1799, 2), (key1337, -1), (key1346, -1), (key1455, -1), (key1467, -1), (key1842, -1), (key1845, -1), (key1296, -1), (key1303, -1), (key1573, -1), (key1597, -1), (key1791, -1), (key1799, -1), (key1316, 1), (key1330, 1), (key1424, 1), (key1448, 1), (key1818, 1), (key1826, 1)]

def rawRow914 : Integer.Sparse Key := [(key1316, -2), (key1826, -2), (key1813, -2), (key1340, 1), (key1337, 1), (key1668, 1), (key1655, 1), (key1845, 1), (key1840, 1), (key1296, 2), (key1799, 2), (key1788, 2), (key1346, -1), (key1337, -1), (key1467, -1), (key1455, -1), (key1845, -1), (key1842, -1), (key1303, -1), (key1296, -1), (key1597, -1), (key1573, -1), (key1799, -1), (key1791, -1), (key1330, 1), (key1316, 1), (key1448, 1), (key1424, 1), (key1826, 1), (key1818, 1)]

def rawRow915 : Integer.Sparse Key := [(key1813, -2), (key1316, -2), (key1826, -2), (key1655, 1), (key1840, 1), (key1337, 1), (key1845, 1), (key1340, 1), (key1668, 1), (key1788, 2), (key1296, 2), (key1799, 2), (key1455, -1), (key1842, -1), (key1337, -1), (key1845, -1), (key1346, -1), (key1467, -1), (key1573, -1), (key1791, -1), (key1296, -1), (key1799, -1), (key1303, -1), (key1597, -1), (key1424, 1), (key1818, 1), (key1316, 1), (key1826, 1), (key1330, 1), (key1448, 1)]

def rawRow916 : Integer.Sparse Key := [(key1813, -2), (key1826, -2), (key1316, -2), (key1840, 1), (key1655, 1), (key1845, 1), (key1337, 1), (key1668, 1), (key1340, 1), (key1788, 2), (key1799, 2), (key1296, 2), (key1842, -1), (key1455, -1), (key1845, -1), (key1337, -1), (key1467, -1), (key1346, -1), (key1791, -1), (key1573, -1), (key1799, -1), (key1296, -1), (key1597, -1), (key1303, -1), (key1818, 1), (key1424, 1), (key1826, 1), (key1316, 1), (key1448, 1), (key1330, 1)]

def rawRow917 : Integer.Sparse Key := [(key1826, -2), (key1316, -2), (key1813, -2), (key1668, 1), (key1845, 1), (key1340, 1), (key1840, 1), (key1337, 1), (key1655, 1), (key1799, 2), (key1296, 2), (key1788, 2), (key1467, -1), (key1845, -1), (key1346, -1), (key1842, -1), (key1337, -1), (key1455, -1), (key1597, -1), (key1799, -1), (key1303, -1), (key1791, -1), (key1296, -1), (key1573, -1), (key1448, 1), (key1826, 1), (key1330, 1), (key1818, 1), (key1316, 1), (key1424, 1)]

def rawRow918 : Integer.Sparse Key := [(key1826, -2), (key1813, -2), (key1316, -2), (key1845, 1), (key1668, 1), (key1840, 1), (key1340, 1), (key1655, 1), (key1337, 1), (key1799, 2), (key1788, 2), (key1296, 2), (key1845, -1), (key1467, -1), (key1842, -1), (key1346, -1), (key1455, -1), (key1337, -1), (key1799, -1), (key1597, -1), (key1791, -1), (key1303, -1), (key1573, -1), (key1296, -1), (key1826, 1), (key1448, 1), (key1818, 1), (key1330, 1), (key1424, 1), (key1316, 1)]

def rawRow919 : Integer.Sparse Key := [(key1340, -2), (key1775, -2), (key1840, -2), (key1316, 1), (key1337, 1), (key1546, 1), (key1655, 1), (key1772, 1), (key1813, 1), (key1346, 2), (key1781, 2), (key1842, 2), (key1296, -1), (key1337, -1), (key1391, -1), (key1455, -1), (key1772, -1), (key1788, -1), (key1330, -1), (key1346, -1), (key1560, -1), (key1660, -1), (key1781, -1), (key1818, -1), (key1303, 1), (key1340, 1), (key1398, 1), (key1458, 1), (key1775, 1), (key1791, 1)]

def rawRow920 : Integer.Sparse Key := [(key1340, -2), (key1840, -2), (key1775, -2), (key1337, 1), (key1316, 1), (key1655, 1), (key1546, 1), (key1813, 1), (key1772, 1), (key1346, 2), (key1842, 2), (key1781, 2), (key1337, -1), (key1296, -1), (key1455, -1), (key1391, -1), (key1788, -1), (key1772, -1), (key1346, -1), (key1330, -1), (key1660, -1), (key1560, -1), (key1818, -1), (key1781, -1), (key1340, 1), (key1303, 1), (key1458, 1), (key1398, 1), (key1791, 1), (key1775, 1)]

def rawRow921 : Integer.Sparse Key := [(key1775, -2), (key1340, -2), (key1840, -2), (key1546, 1), (key1772, 1), (key1316, 1), (key1813, 1), (key1337, 1), (key1655, 1), (key1781, 2), (key1346, 2), (key1842, 2), (key1391, -1), (key1772, -1), (key1296, -1), (key1788, -1), (key1337, -1), (key1455, -1), (key1560, -1), (key1781, -1), (key1330, -1), (key1818, -1), (key1346, -1), (key1660, -1), (key1398, 1), (key1775, 1), (key1303, 1), (key1791, 1), (key1340, 1), (key1458, 1)]

def rawRow922 : Integer.Sparse Key := [(key1775, -2), (key1840, -2), (key1340, -2), (key1772, 1), (key1546, 1), (key1813, 1), (key1316, 1), (key1655, 1), (key1337, 1), (key1781, 2), (key1842, 2), (key1346, 2), (key1772, -1), (key1391, -1), (key1788, -1), (key1296, -1), (key1455, -1), (key1337, -1), (key1781, -1), (key1560, -1), (key1818, -1), (key1330, -1), (key1660, -1), (key1346, -1), (key1775, 1), (key1398, 1), (key1791, 1), (key1303, 1), (key1458, 1), (key1340, 1)]

def rawRow923 : Integer.Sparse Key := [(key1840, -2), (key1340, -2), (key1775, -2), (key1655, 1), (key1813, 1), (key1337, 1), (key1772, 1), (key1316, 1), (key1546, 1), (key1842, 2), (key1346, 2), (key1781, 2), (key1455, -1), (key1788, -1), (key1337, -1), (key1772, -1), (key1296, -1), (key1391, -1), (key1660, -1), (key1818, -1), (key1346, -1), (key1781, -1), (key1330, -1), (key1560, -1), (key1458, 1), (key1791, 1), (key1340, 1), (key1775, 1), (key1303, 1), (key1398, 1)]

def rawRow924 : Integer.Sparse Key := [(key1840, -2), (key1775, -2), (key1340, -2), (key1813, 1), (key1655, 1), (key1772, 1), (key1337, 1), (key1546, 1), (key1316, 1), (key1842, 2), (key1781, 2), (key1346, 2), (key1788, -1), (key1455, -1), (key1772, -1), (key1337, -1), (key1391, -1), (key1296, -1), (key1818, -1), (key1660, -1), (key1781, -1), (key1346, -1), (key1560, -1), (key1330, -1), (key1791, 1), (key1458, 1), (key1775, 1), (key1340, 1), (key1398, 1), (key1303, 1)]

def rawRow925 : Integer.Sparse Key := [(key1330, -2), (key1818, -2), (key1818, -2), (key1346, 1), (key1346, 1), (key1660, 1), (key1660, 1), (key1842, 1), (key1842, 1), (key1303, 2), (key1791, 2), (key1791, 2), (key1340, -1), (key1340, -1), (key1458, -1), (key1458, -1), (key1840, -1), (key1840, -1), (key1296, -1), (key1296, -1), (key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1316, 1), (key1316, 1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1)]

def rawRow926 : Integer.Sparse Key := [(key1818, -2), (key1330, -2), (key1818, -2), (key1660, 1), (key1842, 1), (key1346, 1), (key1842, 1), (key1346, 1), (key1660, 1), (key1791, 2), (key1303, 2), (key1791, 2), (key1458, -1), (key1840, -1), (key1340, -1), (key1840, -1), (key1340, -1), (key1458, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1424, 1), (key1813, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1424, 1)]

def rawRow927 : Integer.Sparse Key := [(key1818, -2), (key1818, -2), (key1330, -2), (key1842, 1), (key1660, 1), (key1842, 1), (key1346, 1), (key1660, 1), (key1346, 1), (key1791, 2), (key1791, 2), (key1303, 2), (key1840, -1), (key1458, -1), (key1840, -1), (key1340, -1), (key1458, -1), (key1340, -1), (key1788, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1296, -1), (key1813, 1), (key1424, 1), (key1813, 1), (key1316, 1), (key1424, 1), (key1316, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow928 : Integer.Sparse Key := [(key1346, -2), (key1781, -2), (key1842, -2), (key1330, 1), (key1346, 1), (key1560, 1), (key1660, 1), (key1781, 1), (key1818, 1), (key1340, 2), (key1775, 2), (key1840, 2), (key1303, -1), (key1340, -1), (key1398, -1), (key1458, -1), (key1775, -1), (key1791, -1), (key1316, -1), (key1337, -1), (key1546, -1), (key1655, -1), (key1772, -1), (key1813, -1), (key1296, 1), (key1337, 1), (key1391, 1), (key1455, 1), (key1772, 1), (key1788, 1)]

def rawRow929 : Integer.Sparse Key := [(key1346, -2), (key1842, -2), (key1781, -2), (key1346, 1), (key1330, 1), (key1660, 1), (key1560, 1), (key1818, 1), (key1781, 1), (key1340, 2), (key1840, 2), (key1775, 2), (key1340, -1), (key1303, -1), (key1458, -1), (key1398, -1), (key1791, -1), (key1775, -1), (key1337, -1), (key1316, -1), (key1655, -1), (key1546, -1), (key1813, -1), (key1772, -1), (key1337, 1), (key1296, 1), (key1455, 1), (key1391, 1), (key1788, 1), (key1772, 1)]

def rawRow930 : Integer.Sparse Key := [(key1781, -2), (key1346, -2), (key1842, -2), (key1560, 1), (key1781, 1), (key1330, 1), (key1818, 1), (key1346, 1), (key1660, 1), (key1775, 2), (key1340, 2), (key1840, 2), (key1398, -1), (key1775, -1), (key1303, -1), (key1791, -1), (key1340, -1), (key1458, -1), (key1546, -1), (key1772, -1), (key1316, -1), (key1813, -1), (key1337, -1), (key1655, -1), (key1391, 1), (key1772, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1455, 1)]

def rawRow931 : Integer.Sparse Key := [(key1781, -2), (key1842, -2), (key1346, -2), (key1781, 1), (key1560, 1), (key1818, 1), (key1330, 1), (key1660, 1), (key1346, 1), (key1775, 2), (key1840, 2), (key1340, 2), (key1775, -1), (key1398, -1), (key1791, -1), (key1303, -1), (key1458, -1), (key1340, -1), (key1772, -1), (key1546, -1), (key1813, -1), (key1316, -1), (key1655, -1), (key1337, -1), (key1772, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1455, 1), (key1337, 1)]

def rawRow932 : Integer.Sparse Key := [(key1842, -2), (key1346, -2), (key1781, -2), (key1660, 1), (key1818, 1), (key1346, 1), (key1781, 1), (key1330, 1), (key1560, 1), (key1840, 2), (key1340, 2), (key1775, 2), (key1458, -1), (key1791, -1), (key1340, -1), (key1775, -1), (key1303, -1), (key1398, -1), (key1655, -1), (key1813, -1), (key1337, -1), (key1772, -1), (key1316, -1), (key1546, -1), (key1455, 1), (key1788, 1), (key1337, 1), (key1772, 1), (key1296, 1), (key1391, 1)]

def rawRow933 : Integer.Sparse Key := [(key1842, -2), (key1781, -2), (key1346, -2), (key1818, 1), (key1660, 1), (key1781, 1), (key1346, 1), (key1560, 1), (key1330, 1), (key1840, 2), (key1775, 2), (key1340, 2), (key1791, -1), (key1458, -1), (key1775, -1), (key1340, -1), (key1398, -1), (key1303, -1), (key1813, -1), (key1655, -1), (key1772, -1), (key1337, -1), (key1546, -1), (key1316, -1), (key1788, 1), (key1455, 1), (key1772, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

def rawRow934 : Integer.Sparse Key := [(key387, -6), (key304, 2), (key387, 2), (key396, 2), (key408, 6), (key238, -2), (key408, -2), (key417, -2), (key318, -2), (key437, -2), (key441, -2), (key250, 2), (key437, 2), (key449, 2)]

def rawRow935 : Integer.Sparse Key := [(key387, -6), (key304, 2), (key396, 2), (key387, 2), (key408, 6), (key238, -2), (key417, -2), (key408, -2), (key318, -2), (key441, -2), (key437, -2), (key250, 2), (key449, 2), (key437, 2)]

def rawRow936 : Integer.Sparse Key := [(key387, -6), (key387, 2), (key304, 2), (key396, 2), (key408, 6), (key408, -2), (key238, -2), (key417, -2), (key437, -2), (key318, -2), (key441, -2), (key437, 2), (key250, 2), (key449, 2)]

def rawRow937 : Integer.Sparse Key := [(key387, -6), (key387, 2), (key396, 2), (key304, 2), (key408, 6), (key408, -2), (key417, -2), (key238, -2), (key437, -2), (key441, -2), (key318, -2), (key437, 2), (key449, 2), (key250, 2)]

def rawRow938 : Integer.Sparse Key := [(key387, -6), (key396, 2), (key304, 2), (key387, 2), (key408, 6), (key417, -2), (key238, -2), (key408, -2), (key441, -2), (key318, -2), (key437, -2), (key449, 2), (key250, 2), (key437, 2)]

def rawRow939 : Integer.Sparse Key := [(key387, -6), (key396, 2), (key387, 2), (key304, 2), (key408, 6), (key417, -2), (key408, -2), (key238, -2), (key441, -2), (key437, -2), (key318, -2), (key449, 2), (key437, 2), (key250, 2)]

def rawRow940 : Integer.Sparse Key := [(key396, -6), (key304, 2), (key387, 2), (key387, 2), (key417, 6), (key238, -2), (key408, -2), (key408, -2), (key327, -2), (key449, -2), (key449, -2), (key259, 2), (key441, 2), (key441, 2)]

def rawRow941 : Integer.Sparse Key := [(key396, -6), (key387, 2), (key304, 2), (key387, 2), (key417, 6), (key408, -2), (key238, -2), (key408, -2), (key449, -2), (key327, -2), (key449, -2), (key441, 2), (key259, 2), (key441, 2)]

def rawRow942 : Integer.Sparse Key := [(key396, -6), (key387, 2), (key387, 2), (key304, 2), (key417, 6), (key408, -2), (key408, -2), (key238, -2), (key449, -2), (key449, -2), (key327, -2), (key441, 2), (key441, 2), (key259, 2)]

def rawRow943 : Integer.Sparse Key := [(key408, -6), (key318, 2), (key437, 2), (key441, 2), (key387, 6), (key250, -2), (key437, -2), (key449, -2), (key304, -2), (key387, -2), (key396, -2), (key238, 2), (key408, 2), (key417, 2)]

def rawRow944 : Integer.Sparse Key := [(key408, -6), (key318, 2), (key441, 2), (key437, 2), (key387, 6), (key250, -2), (key449, -2), (key437, -2), (key304, -2), (key396, -2), (key387, -2), (key238, 2), (key417, 2), (key408, 2)]

def rawRow945 : Integer.Sparse Key := [(key408, -6), (key437, 2), (key318, 2), (key441, 2), (key387, 6), (key437, -2), (key250, -2), (key449, -2), (key387, -2), (key304, -2), (key396, -2), (key408, 2), (key238, 2), (key417, 2)]

def rawRow946 : Integer.Sparse Key := [(key408, -6), (key437, 2), (key441, 2), (key318, 2), (key387, 6), (key437, -2), (key449, -2), (key250, -2), (key387, -2), (key396, -2), (key304, -2), (key408, 2), (key417, 2), (key238, 2)]

def rawRow947 : Integer.Sparse Key := [(key408, -6), (key441, 2), (key318, 2), (key437, 2), (key387, 6), (key449, -2), (key250, -2), (key437, -2), (key396, -2), (key304, -2), (key387, -2), (key417, 2), (key238, 2), (key408, 2)]

def rawRow948 : Integer.Sparse Key := [(key408, -6), (key441, 2), (key437, 2), (key318, 2), (key387, 6), (key449, -2), (key437, -2), (key250, -2), (key396, -2), (key387, -2), (key304, -2), (key417, 2), (key408, 2), (key238, 2)]

def rawRow949 : Integer.Sparse Key := [(key441, -6), (key318, 2), (key408, 2), (key437, 2), (key449, 6), (key250, -2), (key387, -2), (key437, -2), (key327, -2), (key417, -2), (key449, -2), (key259, 2), (key396, 2), (key441, 2)]

def rawRow950 : Integer.Sparse Key := [(key441, -6), (key318, 2), (key437, 2), (key408, 2), (key449, 6), (key250, -2), (key437, -2), (key387, -2), (key327, -2), (key449, -2), (key417, -2), (key259, 2), (key441, 2), (key396, 2)]

def rawRow951 : Integer.Sparse Key := [(key441, -6), (key408, 2), (key318, 2), (key437, 2), (key449, 6), (key387, -2), (key250, -2), (key437, -2), (key417, -2), (key327, -2), (key449, -2), (key396, 2), (key259, 2), (key441, 2)]

def rawRow952 : Integer.Sparse Key := [(key441, -6), (key408, 2), (key437, 2), (key318, 2), (key449, 6), (key387, -2), (key437, -2), (key250, -2), (key417, -2), (key449, -2), (key327, -2), (key396, 2), (key441, 2), (key259, 2)]

def rawRow953 : Integer.Sparse Key := [(key441, -6), (key437, 2), (key318, 2), (key408, 2), (key449, 6), (key437, -2), (key250, -2), (key387, -2), (key449, -2), (key327, -2), (key417, -2), (key441, 2), (key259, 2), (key396, 2)]

def rawRow954 : Integer.Sparse Key := [(key441, -6), (key437, 2), (key408, 2), (key318, 2), (key449, 6), (key437, -2), (key387, -2), (key250, -2), (key449, -2), (key417, -2), (key327, -2), (key441, 2), (key396, 2), (key259, 2)]

def rawRow955 : Integer.Sparse Key := [(key417, -6), (key327, 2), (key449, 2), (key449, 2), (key396, 6), (key259, -2), (key441, -2), (key441, -2), (key304, -2), (key387, -2), (key387, -2), (key238, 2), (key408, 2), (key408, 2)]

def rawRow956 : Integer.Sparse Key := [(key417, -6), (key449, 2), (key327, 2), (key449, 2), (key396, 6), (key441, -2), (key259, -2), (key441, -2), (key387, -2), (key304, -2), (key387, -2), (key408, 2), (key238, 2), (key408, 2)]

def rawRow957 : Integer.Sparse Key := [(key417, -6), (key449, 2), (key449, 2), (key327, 2), (key396, 6), (key441, -2), (key441, -2), (key259, -2), (key387, -2), (key387, -2), (key304, -2), (key408, 2), (key408, 2), (key238, 2)]

def rawRow958 : Integer.Sparse Key := [(key449, -6), (key327, 2), (key417, 2), (key449, 2), (key441, 6), (key259, -2), (key396, -2), (key441, -2), (key318, -2), (key408, -2), (key437, -2), (key250, 2), (key387, 2), (key437, 2)]

def rawRow959 : Integer.Sparse Key := [(key449, -6), (key327, 2), (key449, 2), (key417, 2), (key441, 6), (key259, -2), (key441, -2), (key396, -2), (key318, -2), (key437, -2), (key408, -2), (key250, 2), (key437, 2), (key387, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow960 : Integer.Sparse Key := [(key449, -6), (key417, 2), (key327, 2), (key449, 2), (key441, 6), (key396, -2), (key259, -2), (key441, -2), (key408, -2), (key318, -2), (key437, -2), (key387, 2), (key250, 2), (key437, 2)]

def rawRow961 : Integer.Sparse Key := [(key449, -6), (key417, 2), (key449, 2), (key327, 2), (key441, 6), (key396, -2), (key441, -2), (key259, -2), (key408, -2), (key437, -2), (key318, -2), (key387, 2), (key437, 2), (key250, 2)]

def rawRow962 : Integer.Sparse Key := [(key449, -6), (key449, 2), (key327, 2), (key417, 2), (key441, 6), (key441, -2), (key259, -2), (key396, -2), (key437, -2), (key318, -2), (key408, -2), (key437, 2), (key250, 2), (key387, 2)]

def rawRow963 : Integer.Sparse Key := [(key449, -6), (key449, 2), (key417, 2), (key327, 2), (key441, 6), (key441, -2), (key396, -2), (key259, -2), (key437, -2), (key408, -2), (key318, -2), (key437, 2), (key387, 2), (key250, 2)]

def rawRow964 : Integer.Sparse Key := [(key1541, -2), (key1549, -2), (key1897, -2), (key1386, 1), (key1394, 1), (key1541, 1), (key1557, 1), (key1897, 1), (key1900, 1), (key1568, 2), (key1576, 2), (key1904, 2), (key1291, -1), (key1299, -1), (key1568, -1), (key1594, -1), (key1904, -1), (key1912, -1), (key1419, -1), (key1427, -1), (key1617, -1), (key1625, -1), (key1919, -1), (key1921, -1), (key1311, 1), (key1319, 1), (key1617, 1), (key1634, 1), (key1919, 1), (key1927, 1)]

def rawRow965 : Integer.Sparse Key := [(key1549, -2), (key1541, -2), (key1897, -2), (key1394, 1), (key1386, 1), (key1557, 1), (key1541, 1), (key1900, 1), (key1897, 1), (key1576, 2), (key1568, 2), (key1904, 2), (key1299, -1), (key1291, -1), (key1594, -1), (key1568, -1), (key1912, -1), (key1904, -1), (key1427, -1), (key1419, -1), (key1625, -1), (key1617, -1), (key1921, -1), (key1919, -1), (key1319, 1), (key1311, 1), (key1634, 1), (key1617, 1), (key1927, 1), (key1919, 1)]

def rawRow966 : Integer.Sparse Key := [(key1541, -2), (key1897, -2), (key1549, -2), (key1541, 1), (key1897, 1), (key1386, 1), (key1900, 1), (key1394, 1), (key1557, 1), (key1568, 2), (key1904, 2), (key1576, 2), (key1568, -1), (key1904, -1), (key1291, -1), (key1912, -1), (key1299, -1), (key1594, -1), (key1617, -1), (key1919, -1), (key1419, -1), (key1921, -1), (key1427, -1), (key1625, -1), (key1617, 1), (key1919, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1634, 1)]

def rawRow967 : Integer.Sparse Key := [(key1897, -2), (key1541, -2), (key1549, -2), (key1897, 1), (key1541, 1), (key1900, 1), (key1386, 1), (key1557, 1), (key1394, 1), (key1904, 2), (key1568, 2), (key1576, 2), (key1904, -1), (key1568, -1), (key1912, -1), (key1291, -1), (key1594, -1), (key1299, -1), (key1919, -1), (key1617, -1), (key1921, -1), (key1419, -1), (key1625, -1), (key1427, -1), (key1919, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1634, 1), (key1319, 1)]

def rawRow968 : Integer.Sparse Key := [(key1549, -2), (key1897, -2), (key1541, -2), (key1557, 1), (key1900, 1), (key1394, 1), (key1897, 1), (key1386, 1), (key1541, 1), (key1576, 2), (key1904, 2), (key1568, 2), (key1594, -1), (key1912, -1), (key1299, -1), (key1904, -1), (key1291, -1), (key1568, -1), (key1625, -1), (key1921, -1), (key1427, -1), (key1919, -1), (key1419, -1), (key1617, -1), (key1634, 1), (key1927, 1), (key1319, 1), (key1919, 1), (key1311, 1), (key1617, 1)]

def rawRow969 : Integer.Sparse Key := [(key1897, -2), (key1549, -2), (key1541, -2), (key1900, 1), (key1557, 1), (key1897, 1), (key1394, 1), (key1541, 1), (key1386, 1), (key1904, 2), (key1576, 2), (key1568, 2), (key1912, -1), (key1594, -1), (key1904, -1), (key1299, -1), (key1568, -1), (key1291, -1), (key1921, -1), (key1625, -1), (key1919, -1), (key1427, -1), (key1617, -1), (key1419, -1), (key1927, 1), (key1634, 1), (key1919, 1), (key1319, 1), (key1617, 1), (key1311, 1)]

def rawRow970 : Integer.Sparse Key := [(key1557, -2), (key1557, -2), (key1900, -2), (key1394, 1), (key1394, 1), (key1549, 1), (key1549, 1), (key1897, 1), (key1897, 1), (key1594, 2), (key1594, 2), (key1912, 2), (key1299, -1), (key1299, -1), (key1576, -1), (key1576, -1), (key1904, -1), (key1904, -1), (key1445, -1), (key1445, -1), (key1634, -1), (key1634, -1), (key1927, -1), (key1927, -1), (key1327, 1), (key1327, 1), (key1625, 1), (key1625, 1), (key1921, 1), (key1921, 1)]

def rawRow971 : Integer.Sparse Key := [(key1557, -2), (key1900, -2), (key1557, -2), (key1549, 1), (key1897, 1), (key1394, 1), (key1897, 1), (key1394, 1), (key1549, 1), (key1594, 2), (key1912, 2), (key1594, 2), (key1576, -1), (key1904, -1), (key1299, -1), (key1904, -1), (key1299, -1), (key1576, -1), (key1634, -1), (key1927, -1), (key1445, -1), (key1927, -1), (key1445, -1), (key1634, -1), (key1625, 1), (key1921, 1), (key1327, 1), (key1921, 1), (key1327, 1), (key1625, 1)]

def rawRow972 : Integer.Sparse Key := [(key1900, -2), (key1557, -2), (key1557, -2), (key1897, 1), (key1549, 1), (key1897, 1), (key1394, 1), (key1549, 1), (key1394, 1), (key1912, 2), (key1594, 2), (key1594, 2), (key1904, -1), (key1576, -1), (key1904, -1), (key1299, -1), (key1576, -1), (key1299, -1), (key1927, -1), (key1634, -1), (key1927, -1), (key1445, -1), (key1634, -1), (key1445, -1), (key1921, 1), (key1625, 1), (key1921, 1), (key1327, 1), (key1625, 1), (key1327, 1)]

def rawRow973 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1904, -2), (key1419, 1), (key1427, 1), (key1617, 1), (key1625, 1), (key1919, 1), (key1921, 1), (key1541, 2), (key1549, 2), (key1897, 2), (key1311, -1), (key1319, -1), (key1617, -1), (key1634, -1), (key1919, -1), (key1927, -1), (key1386, -1), (key1394, -1), (key1541, -1), (key1557, -1), (key1897, -1), (key1900, -1), (key1291, 1), (key1299, 1), (key1568, 1), (key1594, 1), (key1904, 1), (key1912, 1)]

def rawRow974 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1904, -2), (key1427, 1), (key1419, 1), (key1625, 1), (key1617, 1), (key1921, 1), (key1919, 1), (key1549, 2), (key1541, 2), (key1897, 2), (key1319, -1), (key1311, -1), (key1634, -1), (key1617, -1), (key1927, -1), (key1919, -1), (key1394, -1), (key1386, -1), (key1557, -1), (key1541, -1), (key1900, -1), (key1897, -1), (key1299, 1), (key1291, 1), (key1594, 1), (key1568, 1), (key1912, 1), (key1904, 1)]

def rawRow975 : Integer.Sparse Key := [(key1568, -2), (key1904, -2), (key1576, -2), (key1617, 1), (key1919, 1), (key1419, 1), (key1921, 1), (key1427, 1), (key1625, 1), (key1541, 2), (key1897, 2), (key1549, 2), (key1617, -1), (key1919, -1), (key1311, -1), (key1927, -1), (key1319, -1), (key1634, -1), (key1541, -1), (key1897, -1), (key1386, -1), (key1900, -1), (key1394, -1), (key1557, -1), (key1568, 1), (key1904, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1594, 1)]

def rawRow976 : Integer.Sparse Key := [(key1904, -2), (key1568, -2), (key1576, -2), (key1919, 1), (key1617, 1), (key1921, 1), (key1419, 1), (key1625, 1), (key1427, 1), (key1897, 2), (key1541, 2), (key1549, 2), (key1919, -1), (key1617, -1), (key1927, -1), (key1311, -1), (key1634, -1), (key1319, -1), (key1897, -1), (key1541, -1), (key1900, -1), (key1386, -1), (key1557, -1), (key1394, -1), (key1904, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1594, 1), (key1299, 1)]

def rawRow977 : Integer.Sparse Key := [(key1576, -2), (key1904, -2), (key1568, -2), (key1625, 1), (key1921, 1), (key1427, 1), (key1919, 1), (key1419, 1), (key1617, 1), (key1549, 2), (key1897, 2), (key1541, 2), (key1634, -1), (key1927, -1), (key1319, -1), (key1919, -1), (key1311, -1), (key1617, -1), (key1557, -1), (key1900, -1), (key1394, -1), (key1897, -1), (key1386, -1), (key1541, -1), (key1594, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1291, 1), (key1568, 1)]

def rawRow978 : Integer.Sparse Key := [(key1904, -2), (key1576, -2), (key1568, -2), (key1921, 1), (key1625, 1), (key1919, 1), (key1427, 1), (key1617, 1), (key1419, 1), (key1897, 2), (key1549, 2), (key1541, 2), (key1927, -1), (key1634, -1), (key1919, -1), (key1319, -1), (key1617, -1), (key1311, -1), (key1900, -1), (key1557, -1), (key1897, -1), (key1394, -1), (key1541, -1), (key1386, -1), (key1912, 1), (key1594, 1), (key1904, 1), (key1299, 1), (key1568, 1), (key1291, 1)]

def rawRow979 : Integer.Sparse Key := [(key1625, -2), (key1684, -2), (key1921, -2), (key1427, 1), (key1473, 1), (key1576, 1), (key1682, 1), (key1904, 1), (key1919, 1), (key1634, 2), (key1690, 2), (key1927, 2), (key1319, -1), (key1352, -1), (key1549, -1), (key1682, -1), (key1897, -1), (key1919, -1), (key1445, -1), (key1481, -1), (key1594, -1), (key1690, -1), (key1912, -1), (key1927, -1), (key1327, 1), (key1355, 1), (key1557, 1), (key1684, 1), (key1900, 1), (key1921, 1)]

def rawRow980 : Integer.Sparse Key := [(key1684, -2), (key1625, -2), (key1921, -2), (key1473, 1), (key1427, 1), (key1682, 1), (key1576, 1), (key1919, 1), (key1904, 1), (key1690, 2), (key1634, 2), (key1927, 2), (key1352, -1), (key1319, -1), (key1682, -1), (key1549, -1), (key1919, -1), (key1897, -1), (key1481, -1), (key1445, -1), (key1690, -1), (key1594, -1), (key1927, -1), (key1912, -1), (key1355, 1), (key1327, 1), (key1684, 1), (key1557, 1), (key1921, 1), (key1900, 1)]

def rawRow981 : Integer.Sparse Key := [(key1625, -2), (key1921, -2), (key1684, -2), (key1576, 1), (key1904, 1), (key1427, 1), (key1919, 1), (key1473, 1), (key1682, 1), (key1634, 2), (key1927, 2), (key1690, 2), (key1549, -1), (key1897, -1), (key1319, -1), (key1919, -1), (key1352, -1), (key1682, -1), (key1594, -1), (key1912, -1), (key1445, -1), (key1927, -1), (key1481, -1), (key1690, -1), (key1557, 1), (key1900, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1684, 1)]

def rawRow982 : Integer.Sparse Key := [(key1921, -2), (key1625, -2), (key1684, -2), (key1904, 1), (key1576, 1), (key1919, 1), (key1427, 1), (key1682, 1), (key1473, 1), (key1927, 2), (key1634, 2), (key1690, 2), (key1897, -1), (key1549, -1), (key1919, -1), (key1319, -1), (key1682, -1), (key1352, -1), (key1912, -1), (key1594, -1), (key1927, -1), (key1445, -1), (key1690, -1), (key1481, -1), (key1900, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1684, 1), (key1355, 1)]

def rawRow983 : Integer.Sparse Key := [(key1684, -2), (key1921, -2), (key1625, -2), (key1682, 1), (key1919, 1), (key1473, 1), (key1904, 1), (key1427, 1), (key1576, 1), (key1690, 2), (key1927, 2), (key1634, 2), (key1682, -1), (key1919, -1), (key1352, -1), (key1897, -1), (key1319, -1), (key1549, -1), (key1690, -1), (key1927, -1), (key1481, -1), (key1912, -1), (key1445, -1), (key1594, -1), (key1684, 1), (key1921, 1), (key1355, 1), (key1900, 1), (key1327, 1), (key1557, 1)]

def rawRow984 : Integer.Sparse Key := [(key1921, -2), (key1684, -2), (key1625, -2), (key1919, 1), (key1682, 1), (key1904, 1), (key1473, 1), (key1576, 1), (key1427, 1), (key1927, 2), (key1690, 2), (key1634, 2), (key1919, -1), (key1682, -1), (key1897, -1), (key1352, -1), (key1549, -1), (key1319, -1), (key1927, -1), (key1690, -1), (key1912, -1), (key1481, -1), (key1594, -1), (key1445, -1), (key1921, 1), (key1684, 1), (key1900, 1), (key1355, 1), (key1557, 1), (key1327, 1)]

def rawRow985 : Integer.Sparse Key := [(key1594, -2), (key1594, -2), (key1912, -2), (key1445, 1), (key1445, 1), (key1634, 1), (key1634, 1), (key1927, 1), (key1927, 1), (key1557, 2), (key1557, 2), (key1900, 2), (key1327, -1), (key1327, -1), (key1625, -1), (key1625, -1), (key1921, -1), (key1921, -1), (key1394, -1), (key1394, -1), (key1549, -1), (key1549, -1), (key1897, -1), (key1897, -1), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1904, 1), (key1904, 1)]

def rawRow986 : Integer.Sparse Key := [(key1594, -2), (key1912, -2), (key1594, -2), (key1634, 1), (key1927, 1), (key1445, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1557, 2), (key1900, 2), (key1557, 2), (key1625, -1), (key1921, -1), (key1327, -1), (key1921, -1), (key1327, -1), (key1625, -1), (key1549, -1), (key1897, -1), (key1394, -1), (key1897, -1), (key1394, -1), (key1549, -1), (key1576, 1), (key1904, 1), (key1299, 1), (key1904, 1), (key1299, 1), (key1576, 1)]

def rawRow987 : Integer.Sparse Key := [(key1912, -2), (key1594, -2), (key1594, -2), (key1927, 1), (key1634, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1445, 1), (key1900, 2), (key1557, 2), (key1557, 2), (key1921, -1), (key1625, -1), (key1921, -1), (key1327, -1), (key1625, -1), (key1327, -1), (key1897, -1), (key1549, -1), (key1897, -1), (key1394, -1), (key1549, -1), (key1394, -1), (key1904, 1), (key1576, 1), (key1904, 1), (key1299, 1), (key1576, 1), (key1299, 1)]

def rawRow988 : Integer.Sparse Key := [(key1634, -2), (key1690, -2), (key1927, -2), (key1445, 1), (key1481, 1), (key1594, 1), (key1690, 1), (key1912, 1), (key1927, 1), (key1625, 2), (key1684, 2), (key1921, 2), (key1327, -1), (key1355, -1), (key1557, -1), (key1684, -1), (key1900, -1), (key1921, -1), (key1427, -1), (key1473, -1), (key1576, -1), (key1682, -1), (key1904, -1), (key1919, -1), (key1319, 1), (key1352, 1), (key1549, 1), (key1682, 1), (key1897, 1), (key1919, 1)]

def rawRow989 : Integer.Sparse Key := [(key1690, -2), (key1634, -2), (key1927, -2), (key1481, 1), (key1445, 1), (key1690, 1), (key1594, 1), (key1927, 1), (key1912, 1), (key1684, 2), (key1625, 2), (key1921, 2), (key1355, -1), (key1327, -1), (key1684, -1), (key1557, -1), (key1921, -1), (key1900, -1), (key1473, -1), (key1427, -1), (key1682, -1), (key1576, -1), (key1919, -1), (key1904, -1), (key1352, 1), (key1319, 1), (key1682, 1), (key1549, 1), (key1919, 1), (key1897, 1)]

def rawRow990 : Integer.Sparse Key := [(key1634, -2), (key1927, -2), (key1690, -2), (key1594, 1), (key1912, 1), (key1445, 1), (key1927, 1), (key1481, 1), (key1690, 1), (key1625, 2), (key1921, 2), (key1684, 2), (key1557, -1), (key1900, -1), (key1327, -1), (key1921, -1), (key1355, -1), (key1684, -1), (key1576, -1), (key1904, -1), (key1427, -1), (key1919, -1), (key1473, -1), (key1682, -1), (key1549, 1), (key1897, 1), (key1319, 1), (key1919, 1), (key1352, 1), (key1682, 1)]

def rawRow991 : Integer.Sparse Key := [(key1927, -2), (key1634, -2), (key1690, -2), (key1912, 1), (key1594, 1), (key1927, 1), (key1445, 1), (key1690, 1), (key1481, 1), (key1921, 2), (key1625, 2), (key1684, 2), (key1900, -1), (key1557, -1), (key1921, -1), (key1327, -1), (key1684, -1), (key1355, -1), (key1904, -1), (key1576, -1), (key1919, -1), (key1427, -1), (key1682, -1), (key1473, -1), (key1897, 1), (key1549, 1), (key1919, 1), (key1319, 1), (key1682, 1), (key1352, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow992 : Integer.Sparse Key := [(key1690, -2), (key1927, -2), (key1634, -2), (key1690, 1), (key1927, 1), (key1481, 1), (key1912, 1), (key1445, 1), (key1594, 1), (key1684, 2), (key1921, 2), (key1625, 2), (key1684, -1), (key1921, -1), (key1355, -1), (key1900, -1), (key1327, -1), (key1557, -1), (key1682, -1), (key1919, -1), (key1473, -1), (key1904, -1), (key1427, -1), (key1576, -1), (key1682, 1), (key1919, 1), (key1352, 1), (key1897, 1), (key1319, 1), (key1549, 1)]

def rawRow993 : Integer.Sparse Key := [(key1927, -2), (key1690, -2), (key1634, -2), (key1927, 1), (key1690, 1), (key1912, 1), (key1481, 1), (key1594, 1), (key1445, 1), (key1921, 2), (key1684, 2), (key1625, 2), (key1921, -1), (key1684, -1), (key1900, -1), (key1355, -1), (key1557, -1), (key1327, -1), (key1919, -1), (key1682, -1), (key1904, -1), (key1473, -1), (key1576, -1), (key1427, -1), (key1919, 1), (key1682, 1), (key1897, 1), (key1352, 1), (key1549, 1), (key1319, 1)]

def rawRow994 : Integer.Sparse Key := [(key43, -2), (key48, -2), (key74, -2), (key48, 6), (key426, 2), (key432, 2), (key659, 2), (key212, -2), (key432, -2), (key460, -2), (key486, -6), (key218, 2), (key486, 2), (key490, 2)]

def rawRow995 : Integer.Sparse Key := [(key48, -2), (key43, -2), (key74, -2), (key48, 6), (key432, 2), (key426, 2), (key659, 2), (key212, -2), (key460, -2), (key432, -2), (key486, -6), (key218, 2), (key490, 2), (key486, 2)]

def rawRow996 : Integer.Sparse Key := [(key43, -2), (key74, -2), (key48, -2), (key48, 6), (key426, 2), (key659, 2), (key432, 2), (key432, -2), (key212, -2), (key460, -2), (key486, -6), (key486, 2), (key218, 2), (key490, 2)]

def rawRow997 : Integer.Sparse Key := [(key74, -2), (key43, -2), (key48, -2), (key48, 6), (key659, 2), (key426, 2), (key432, 2), (key432, -2), (key460, -2), (key212, -2), (key486, -6), (key486, 2), (key490, 2), (key218, 2)]

def rawRow998 : Integer.Sparse Key := [(key48, -2), (key74, -2), (key43, -2), (key48, 6), (key432, 2), (key659, 2), (key426, 2), (key460, -2), (key212, -2), (key432, -2), (key486, -6), (key490, 2), (key218, 2), (key486, 2)]

def rawRow999 : Integer.Sparse Key := [(key74, -2), (key48, -2), (key43, -2), (key48, 6), (key659, 2), (key432, 2), (key426, 2), (key460, -2), (key432, -2), (key212, -2), (key486, -6), (key490, 2), (key486, 2), (key218, 2)]

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

def rawRow9019 : Integer.Sparse Key := [(key2007, 6), (key2007, 6), (key2006, 6), (key2007, 6), (key2340, -6), (key2349, -6), (key2340, -6), (key2340, -6)]

def rawRow9020 : Integer.Sparse Key := [(key2007, 6), (key2007, 6), (key2007, 6), (key2006, 6), (key2349, -6), (key2340, -6), (key2340, -6), (key2340, -6)]

def rawRow9021 : Integer.Sparse Key := [(key2299, 6), (key2300, 6), (key2300, 6), (key2340, 6), (key2007, -6), (key2300, -6), (key2300, -6), (key2313, -6)]

def rawRow9022 : Integer.Sparse Key := [(key2300, 6), (key2299, 6), (key2300, 6), (key2340, 6), (key2007, -6), (key2300, -6), (key2313, -6), (key2300, -6)]

def rawRow9023 : Integer.Sparse Key := [(key2300, 6), (key2300, 6), (key2299, 6), (key2340, 6), (key2007, -6), (key2313, -6), (key2300, -6), (key2300, -6)]

def rawRow9024 : Integer.Sparse Key := [(key2299, 6), (key2300, 6), (key2340, 6), (key2300, 6), (key2300, -6), (key2007, -6), (key2300, -6), (key2313, -6)]

def rawRow9025 : Integer.Sparse Key := [(key2300, 6), (key2299, 6), (key2340, 6), (key2300, 6), (key2300, -6), (key2007, -6), (key2313, -6), (key2300, -6)]

def rawRow9026 : Integer.Sparse Key := [(key2299, 6), (key2340, 6), (key2300, 6), (key2300, 6), (key2300, -6), (key2300, -6), (key2007, -6), (key2313, -6)]

def rawRow9027 : Integer.Sparse Key := [(key2340, 6), (key2299, 6), (key2300, 6), (key2300, 6), (key2300, -6), (key2300, -6), (key2313, -6), (key2007, -6)]

def rawRow9028 : Integer.Sparse Key := [(key2300, 6), (key2340, 6), (key2299, 6), (key2300, 6), (key2300, -6), (key2313, -6), (key2007, -6), (key2300, -6)]

def rawRow9029 : Integer.Sparse Key := [(key2340, 6), (key2300, 6), (key2299, 6), (key2300, 6), (key2300, -6), (key2313, -6), (key2300, -6), (key2007, -6)]

def rawRow9030 : Integer.Sparse Key := [(key2300, 6), (key2300, 6), (key2340, 6), (key2299, 6), (key2313, -6), (key2007, -6), (key2300, -6), (key2300, -6)]

def rawRow9031 : Integer.Sparse Key := [(key2300, 6), (key2340, 6), (key2300, 6), (key2299, 6), (key2313, -6), (key2300, -6), (key2007, -6), (key2300, -6)]

def rawRow9032 : Integer.Sparse Key := [(key2340, 6), (key2300, 6), (key2300, 6), (key2299, 6), (key2313, -6), (key2300, -6), (key2300, -6), (key2007, -6)]

def rawRow9033 : Integer.Sparse Key := [(key1998, 6), (key2000, 6), (key2000, 6), (key2000, 6), (key2340, -6), (key2340, -6), (key2340, -6), (key2349, -6)]

def rawRow9034 : Integer.Sparse Key := [(key2000, 6), (key1998, 6), (key2000, 6), (key2000, 6), (key2340, -6), (key2340, -6), (key2349, -6), (key2340, -6)]

def rawRow9035 : Integer.Sparse Key := [(key2000, 6), (key2000, 6), (key1998, 6), (key2000, 6), (key2340, -6), (key2349, -6), (key2340, -6), (key2340, -6)]

def rawRow9036 : Integer.Sparse Key := [(key2000, 6), (key2000, 6), (key2000, 6), (key1998, 6), (key2349, -6), (key2340, -6), (key2340, -6), (key2340, -6)]

def rawRow9037 : Integer.Sparse Key := [(key2267, 6), (key2269, 6), (key2269, 6), (key2340, 6), (key2000, -6), (key2269, -6), (key2269, -6), (key2292, -6)]

def rawRow9038 : Integer.Sparse Key := [(key2269, 6), (key2267, 6), (key2269, 6), (key2340, 6), (key2000, -6), (key2269, -6), (key2292, -6), (key2269, -6)]

def rawRow9039 : Integer.Sparse Key := [(key2269, 6), (key2269, 6), (key2267, 6), (key2340, 6), (key2000, -6), (key2292, -6), (key2269, -6), (key2269, -6)]

def rawRow9040 : Integer.Sparse Key := [(key2267, 6), (key2269, 6), (key2340, 6), (key2269, 6), (key2269, -6), (key2000, -6), (key2269, -6), (key2292, -6)]

def rawRow9041 : Integer.Sparse Key := [(key2269, 6), (key2267, 6), (key2340, 6), (key2269, 6), (key2269, -6), (key2000, -6), (key2292, -6), (key2269, -6)]

def rawRow9042 : Integer.Sparse Key := [(key2267, 6), (key2340, 6), (key2269, 6), (key2269, 6), (key2269, -6), (key2269, -6), (key2000, -6), (key2292, -6)]

def rawRow9043 : Integer.Sparse Key := [(key2340, 6), (key2267, 6), (key2269, 6), (key2269, 6), (key2269, -6), (key2269, -6), (key2292, -6), (key2000, -6)]

def rawRow9044 : Integer.Sparse Key := [(key2269, 6), (key2340, 6), (key2267, 6), (key2269, 6), (key2269, -6), (key2292, -6), (key2000, -6), (key2269, -6)]

def rawRow9045 : Integer.Sparse Key := [(key2340, 6), (key2269, 6), (key2267, 6), (key2269, 6), (key2269, -6), (key2292, -6), (key2269, -6), (key2000, -6)]

def rawRow9046 : Integer.Sparse Key := [(key2269, 6), (key2269, 6), (key2340, 6), (key2267, 6), (key2292, -6), (key2000, -6), (key2269, -6), (key2269, -6)]

def rawRow9047 : Integer.Sparse Key := [(key2269, 6), (key2340, 6), (key2269, 6), (key2267, 6), (key2292, -6), (key2269, -6), (key2000, -6), (key2269, -6)]

def rawRow9048 : Integer.Sparse Key := [(key2340, 6), (key2269, 6), (key2269, 6), (key2267, 6), (key2292, -6), (key2269, -6), (key2269, -6), (key2000, -6)]

def rawRow9049 : Integer.Sparse Key := [(key776, -6), (key778, -6), (key778, -6), (key778, -6), (key801, 2), (key803, 2), (key803, 2), (key801, 2), (key803, 2), (key801, 2), (key811, 2), (key803, 2), (key811, 2), (key803, 2), (key803, 2), (key811, 2)]

def rawRow9050 : Integer.Sparse Key := [(key778, -6), (key776, -6), (key778, -6), (key778, -6), (key803, 2), (key801, 2), (key803, 2), (key803, 2), (key801, 2), (key811, 2), (key801, 2), (key811, 2), (key803, 2), (key803, 2), (key811, 2), (key803, 2)]

def rawRow9051 : Integer.Sparse Key := [(key778, -6), (key778, -6), (key776, -6), (key778, -6), (key803, 2), (key803, 2), (key801, 2), (key811, 2), (key811, 2), (key803, 2), (key803, 2), (key801, 2), (key801, 2), (key811, 2), (key803, 2), (key803, 2)]

def rawRow9052 : Integer.Sparse Key := [(key778, -6), (key778, -6), (key778, -6), (key776, -6), (key811, 2), (key811, 2), (key811, 2), (key803, 2), (key803, 2), (key803, 2), (key803, 2), (key803, 2), (key803, 2), (key801, 2), (key801, 2), (key801, 2)]

def rawRow9053 : Integer.Sparse Key := [(key801, -6), (key803, -6), (key803, -6), (key811, -6), (key776, 2), (key778, 2), (key778, 2), (key801, 2), (key803, 2), (key801, 2), (key811, 2), (key803, 2), (key811, 2), (key836, 2), (key836, 2), (key839, 2)]

def rawRow9054 : Integer.Sparse Key := [(key803, -6), (key801, -6), (key803, -6), (key811, -6), (key778, 2), (key776, 2), (key778, 2), (key803, 2), (key801, 2), (key811, 2), (key801, 2), (key811, 2), (key803, 2), (key836, 2), (key839, 2), (key836, 2)]

def rawRow9055 : Integer.Sparse Key := [(key803, -6), (key803, -6), (key801, -6), (key811, -6), (key778, 2), (key778, 2), (key776, 2), (key811, 2), (key811, 2), (key803, 2), (key803, 2), (key801, 2), (key801, 2), (key839, 2), (key836, 2), (key836, 2)]

def rawRow9056 : Integer.Sparse Key := [(key801, -6), (key803, -6), (key811, -6), (key803, -6), (key801, 2), (key803, 2), (key811, 2), (key776, 2), (key778, 2), (key801, 2), (key811, 2), (key836, 2), (key839, 2), (key778, 2), (key803, 2), (key811, 2)]

def rawRow9057 : Integer.Sparse Key := [(key803, -6), (key801, -6), (key811, -6), (key803, -6), (key803, 2), (key801, 2), (key811, 2), (key778, 2), (key776, 2), (key811, 2), (key801, 2), (key839, 2), (key836, 2), (key778, 2), (key811, 2), (key803, 2)]

def rawRow9058 : Integer.Sparse Key := [(key801, -6), (key811, -6), (key803, -6), (key803, -6), (key801, 2), (key811, 2), (key803, 2), (key801, 2), (key811, 2), (key776, 2), (key839, 2), (key778, 2), (key811, 2), (key803, 2), (key778, 2), (key811, 2)]

def rawRow9059 : Integer.Sparse Key := [(key811, -6), (key801, -6), (key803, -6), (key803, -6), (key811, 2), (key801, 2), (key803, 2), (key811, 2), (key801, 2), (key839, 2), (key776, 2), (key811, 2), (key778, 2), (key803, 2), (key811, 2), (key778, 2)]

def rawRow9060 : Integer.Sparse Key := [(key803, -6), (key811, -6), (key801, -6), (key803, -6), (key803, 2), (key811, 2), (key801, 2), (key836, 2), (key839, 2), (key778, 2), (key811, 2), (key776, 2), (key801, 2), (key811, 2), (key778, 2), (key803, 2)]

def rawRow9061 : Integer.Sparse Key := [(key811, -6), (key803, -6), (key801, -6), (key803, -6), (key811, 2), (key803, 2), (key801, 2), (key839, 2), (key836, 2), (key811, 2), (key778, 2), (key801, 2), (key776, 2), (key811, 2), (key803, 2), (key778, 2)]

def rawRow9062 : Integer.Sparse Key := [(key803, -6), (key803, -6), (key811, -6), (key801, -6), (key836, 2), (key836, 2), (key839, 2), (key778, 2), (key778, 2), (key803, 2), (key803, 2), (key811, 2), (key811, 2), (key776, 2), (key801, 2), (key801, 2)]

def rawRow9063 : Integer.Sparse Key := [(key803, -6), (key811, -6), (key803, -6), (key801, -6), (key836, 2), (key839, 2), (key836, 2), (key803, 2), (key811, 2), (key778, 2), (key811, 2), (key778, 2), (key803, 2), (key801, 2), (key776, 2), (key801, 2)]

def rawRow9064 : Integer.Sparse Key := [(key811, -6), (key803, -6), (key803, -6), (key801, -6), (key839, 2), (key836, 2), (key836, 2), (key811, 2), (key803, 2), (key811, 2), (key778, 2), (key803, 2), (key778, 2), (key801, 2), (key801, 2), (key776, 2)]

def rawRow9065 : Integer.Sparse Key := [(key984, 2), (key984, 2), (key984, 2), (key1098, 2), (key1098, 2), (key1098, 2), (key1183, 2), (key1183, 2), (key1183, 2), (key1183, 2), (key1183, 2), (key1183, 2), (key976, -2), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key1180, -2)]

def rawRow9066 : Integer.Sparse Key := [(key1098, 2), (key1183, 2), (key1183, 2), (key984, 2), (key1183, 2), (key1183, 2), (key984, 2), (key984, 2), (key1098, 2), (key1098, 2), (key1183, 2), (key1183, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1090, -2)]

def rawRow9067 : Integer.Sparse Key := [(key1183, 2), (key1098, 2), (key1183, 2), (key1183, 2), (key984, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key984, 2), (key1183, 2), (key984, 2), (key1098, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1090, -2), (key976, -2), (key1090, -2)]

def rawRow9068 : Integer.Sparse Key := [(key1183, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1183, 2), (key984, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key984, 2), (key1098, 2), (key984, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1090, -2), (key976, -2), (key1090, -2), (key1090, -2), (key976, -2)]

def rawRow9069 : Integer.Sparse Key := [(key147, -24), (key3, 6), (key86, 6), (key86, 6), (key86, 6)]

def rawRow9070 : Integer.Sparse Key := [(key147, -24), (key86, 6), (key3, 6), (key86, 6), (key86, 6)]

def rawRow9071 : Integer.Sparse Key := [(key147, -24), (key86, 6), (key86, 6), (key3, 6), (key86, 6)]

def rawRow9072 : Integer.Sparse Key := [(key147, -24), (key86, 6), (key86, 6), (key86, 6), (key3, 6)]

def rawRow9073 : Integer.Sparse Key := [(key193, -6), (key193, -6), (key193, -6), (key202, -6), (key7, 2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key151, 2)]

def rawRow9074 : Integer.Sparse Key := [(key193, -6), (key193, -6), (key202, -6), (key193, -6), (key90, 2), (key90, 2), (key151, 2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key7, 2), (key90, 2), (key90, 2)]

def rawRow9075 : Integer.Sparse Key := [(key193, -6), (key202, -6), (key193, -6), (key193, -6), (key90, 2), (key151, 2), (key90, 2), (key90, 2), (key151, 2), (key7, 2), (key151, 2), (key7, 2), (key90, 2), (key90, 2), (key7, 2), (key90, 2)]

def rawRow9076 : Integer.Sparse Key := [(key202, -6), (key193, -6), (key193, -6), (key193, -6), (key151, 2), (key90, 2), (key90, 2), (key151, 2), (key90, 2), (key151, 2), (key7, 2), (key90, 2), (key7, 2), (key90, 2), (key90, 2), (key7, 2)]

def rawRow9077 : Integer.Sparse Key := [(key1030, -6), (key1030, -6), (key1030, -6), (key1067, -6), (key1108, 2), (key1108, 2), (key1119, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1119, 2), (key1108, 2), (key1146, 2), (key1119, 2), (key1146, 2)]

def rawRow9078 : Integer.Sparse Key := [(key1030, -6), (key1030, -6), (key1067, -6), (key1030, -6), (key1108, 2), (key1119, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1119, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1146, 2), (key1119, 2)]

def rawRow9079 : Integer.Sparse Key := [(key1030, -6), (key1067, -6), (key1030, -6), (key1030, -6), (key1119, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1108, 2), (key1108, 2), (key1146, 2), (key1146, 2), (key1119, 2), (key1119, 2), (key1108, 2), (key1108, 2)]

def rawRow9080 : Integer.Sparse Key := [(key1067, -6), (key1030, -6), (key1030, -6), (key1030, -6), (key1146, 2), (key1146, 2), (key1146, 2), (key1119, 2), (key1119, 2), (key1119, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2)]

def rawRow9081 : Integer.Sparse Key := [(key1011, -6), (key1119, -6), (key1119, -6), (key1119, -6), (key995, 2), (key995, 2), (key995, 2), (key1030, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2)]

def rawRow9082 : Integer.Sparse Key := [(key1119, -6), (key1011, -6), (key1119, -6), (key1119, -6), (key1030, 2), (key1108, 2), (key1108, 2), (key995, 2), (key1108, 2), (key1108, 2), (key995, 2), (key995, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2)]

def rawRow9083 : Integer.Sparse Key := [(key1119, -6), (key1119, -6), (key1011, -6), (key1119, -6), (key1108, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key995, 2), (key1108, 2), (key1030, 2), (key1108, 2), (key995, 2), (key1108, 2), (key995, 2), (key1030, 2)]

def rawRow9084 : Integer.Sparse Key := [(key1119, -6), (key1119, -6), (key1119, -6), (key1011, -6), (key1108, 2), (key1108, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key995, 2), (key1108, 2), (key1030, 2), (key1108, 2), (key995, 2), (key1030, 2), (key995, 2)]

def rawRow9085 : Integer.Sparse Key := [(key971, -6), (key979, -6), (key979, -6), (key979, -6), (key1085, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1093, 2), (key1085, 2), (key1164, 2), (key1093, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1164, 2)]

def rawRow9086 : Integer.Sparse Key := [(key979, -6), (key971, -6), (key979, -6), (key979, -6), (key1093, 2), (key1085, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1164, 2), (key1085, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1093, 2)]

def rawRow9087 : Integer.Sparse Key := [(key979, -6), (key979, -6), (key971, -6), (key979, -6), (key1093, 2), (key1093, 2), (key1085, 2), (key1164, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1164, 2), (key1093, 2), (key1093, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9088 : Integer.Sparse Key := [(key979, -6), (key979, -6), (key979, -6), (key971, -6), (key1164, 2), (key1164, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1085, 2)]

def rawRow9089 : Integer.Sparse Key := [(key1164, -6), (key1164, -6), (key1164, -6), (key1245, -6), (key979, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key1228, 2), (key1228, 2)]

def rawRow9090 : Integer.Sparse Key := [(key1164, -6), (key1164, -6), (key1245, -6), (key1164, -6), (key1093, 2), (key1093, 2), (key1228, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key1228, 2), (key979, 2), (key1093, 2), (key1093, 2)]

def rawRow9091 : Integer.Sparse Key := [(key1164, -6), (key1245, -6), (key1164, -6), (key1164, -6), (key1093, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key979, 2), (key1228, 2), (key979, 2), (key1093, 2), (key1093, 2), (key979, 2), (key1093, 2)]

def rawRow9092 : Integer.Sparse Key := [(key1245, -6), (key1164, -6), (key1164, -6), (key1164, -6), (key1228, 2), (key1093, 2), (key1093, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key979, 2), (key1093, 2), (key979, 2), (key1093, 2), (key1093, 2), (key979, 2)]

def rawRow9093 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1036, -2), (key1028, -2), (key1036, -2), (key1028, -2), (key1071, -2), (key1036, -2), (key1071, -2), (key1036, -2), (key1036, -2), (key1071, -2), (key1106, 1), (key1114, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1123, 1), (key1106, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1150, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1150, 1), (key1123, 1), (key1150, 1), (key1114, 1), (key1123, 1), (key1114, 1), (key1150, 1), (key1123, 1), (key1150, 1)]

def rawRow9094 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1036, -2), (key1036, -2), (key1028, -2), (key1071, -2), (key1028, -2), (key1071, -2), (key1036, -2), (key1036, -2), (key1071, -2), (key1036, -2), (key1114, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1123, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1150, 1), (key1114, 1), (key1150, 1), (key1123, 1)]

def rawRow9095 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1028, -2), (key1071, -2), (key1071, -2), (key1036, -2), (key1036, -2), (key1028, -2), (key1028, -2), (key1071, -2), (key1036, -2), (key1036, -2), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1)]

def rawRow9096 : Integer.Sparse Key := [(key1071, -2), (key1071, -2), (key1071, -2), (key1036, -2), (key1036, -2), (key1036, -2), (key1036, -2), (key1036, -2), (key1036, -2), (key1028, -2), (key1028, -2), (key1028, -2), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1)]

def rawRow9097 : Integer.Sparse Key := [(key1015, -2), (key1015, -2), (key1015, -2), (key1123, -2), (key1123, -2), (key1123, -2), (key1123, -2), (key1123, -2), (key1123, -2), (key1235, -2), (key1235, -2), (key1235, -2), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1)]

def rawRow9098 : Integer.Sparse Key := [(key1123, -2), (key1123, -2), (key1235, -2), (key1015, -2), (key1015, -2), (key1123, -2), (key1123, -2), (key1235, -2), (key1235, -2), (key1015, -2), (key1123, -2), (key1123, -2), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1)]

def rawRow9099 : Integer.Sparse Key := [(key1123, -2), (key1235, -2), (key1123, -2), (key1123, -2), (key1235, -2), (key1015, -2), (key1235, -2), (key1015, -2), (key1123, -2), (key1123, -2), (key1015, -2), (key1123, -2), (key1114, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1036, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1001, 1), (key1114, 1), (key1001, 1), (key1036, 1)]

def rawRow9100 : Integer.Sparse Key := [(key1235, -2), (key1123, -2), (key1123, -2), (key1235, -2), (key1123, -2), (key1235, -2), (key1015, -2), (key1123, -2), (key1015, -2), (key1123, -2), (key1123, -2), (key1015, -2), (key1232, 1), (key1114, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1036, 1), (key1232, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1001, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1001, 1), (key1036, 1), (key1001, 1), (key1114, 1), (key1036, 1), (key1114, 1), (key1001, 1), (key1036, 1), (key1001, 1)]

def rawRow9101 : Integer.Sparse Key := [(key973, -24), (key1087, 6), (key1087, 6), (key1087, 6), (key1160, 6)]

def rawRow9102 : Integer.Sparse Key := [(key973, -24), (key1087, 6), (key1087, 6), (key1160, 6), (key1087, 6)]

def rawRow9103 : Integer.Sparse Key := [(key973, -24), (key1087, 6), (key1160, 6), (key1087, 6), (key1087, 6)]

def rawRow9104 : Integer.Sparse Key := [(key973, -24), (key1160, 6), (key1087, 6), (key1087, 6), (key1087, 6)]

def rawRow9105 : Integer.Sparse Key := [(key1160, -24), (key973, 6), (key1087, 6), (key1087, 6), (key1087, 6)]

def rawRow9106 : Integer.Sparse Key := [(key1160, -24), (key1087, 6), (key973, 6), (key1087, 6), (key1087, 6)]

def rawRow9107 : Integer.Sparse Key := [(key1160, -24), (key1087, 6), (key1087, 6), (key973, 6), (key1087, 6)]

def rawRow9108 : Integer.Sparse Key := [(key1160, -24), (key1087, 6), (key1087, 6), (key1087, 6), (key973, 6)]

def rawRow9109 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1001, -2), (key993, -2), (key1001, -2), (key993, -2), (key1015, -2), (key1001, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1015, -2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2)]

def rawRow9110 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1001, -2), (key1001, -2), (key993, -2), (key1015, -2), (key993, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1015, -2), (key1001, -2), (key1036, 2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1036, 2)]

def rawRow9111 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key993, -2), (key1015, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key993, -2), (key993, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2)]

def rawRow9112 : Integer.Sparse Key := [(key1015, -2), (key1015, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key993, -2), (key993, -2), (key993, -2), (key1071, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1028, 2)]

def rawRow9113 : Integer.Sparse Key := [(key1071, -2), (key1071, -2), (key1071, -2), (key1150, -2), (key1150, -2), (key1150, -2), (key1150, -2), (key1150, -2), (key1150, -2), (key1242, -2), (key1242, -2), (key1242, -2), (key1015, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1235, 2)]

def rawRow9114 : Integer.Sparse Key := [(key1150, -2), (key1150, -2), (key1242, -2), (key1071, -2), (key1071, -2), (key1150, -2), (key1150, -2), (key1242, -2), (key1242, -2), (key1071, -2), (key1150, -2), (key1150, -2), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1123, 2)]

def rawRow9115 : Integer.Sparse Key := [(key1150, -2), (key1242, -2), (key1150, -2), (key1150, -2), (key1242, -2), (key1071, -2), (key1242, -2), (key1071, -2), (key1150, -2), (key1150, -2), (key1071, -2), (key1150, -2), (key1123, 2), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1123, 2)]

def rawRow9116 : Integer.Sparse Key := [(key1242, -2), (key1150, -2), (key1150, -2), (key1242, -2), (key1150, -2), (key1242, -2), (key1071, -2), (key1150, -2), (key1071, -2), (key1150, -2), (key1150, -2), (key1071, -2), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1015, 2)]

def rawRow9117 : Integer.Sparse Key := [(key43, -2), (key48, -2), (key48, -2), (key43, -2), (key48, -2), (key43, -2), (key74, -2), (key48, -2), (key74, -2), (key48, -2), (key48, -2), (key74, -2), (key100, 1), (key105, 1), (key100, 1), (key115, 1), (key105, 1), (key115, 1), (key100, 1), (key105, 1), (key100, 1), (key137, 1), (key105, 1), (key137, 1), (key100, 1), (key115, 1), (key100, 1), (key137, 1), (key115, 1), (key137, 1), (key105, 1), (key115, 1), (key105, 1), (key137, 1), (key115, 1), (key137, 1)]

def rawRow9118 : Integer.Sparse Key := [(key48, -2), (key43, -2), (key48, -2), (key48, -2), (key43, -2), (key74, -2), (key43, -2), (key74, -2), (key48, -2), (key48, -2), (key74, -2), (key48, -2), (key105, 1), (key100, 1), (key115, 1), (key100, 1), (key115, 1), (key105, 1), (key105, 1), (key100, 1), (key137, 1), (key100, 1), (key137, 1), (key105, 1), (key115, 1), (key100, 1), (key137, 1), (key100, 1), (key137, 1), (key115, 1), (key115, 1), (key105, 1), (key137, 1), (key105, 1), (key137, 1), (key115, 1)]

def rawRow9119 : Integer.Sparse Key := [(key48, -2), (key48, -2), (key43, -2), (key74, -2), (key74, -2), (key48, -2), (key48, -2), (key43, -2), (key43, -2), (key74, -2), (key48, -2), (key48, -2), (key115, 1), (key115, 1), (key105, 1), (key105, 1), (key100, 1), (key100, 1), (key137, 1), (key137, 1), (key105, 1), (key105, 1), (key100, 1), (key100, 1), (key137, 1), (key137, 1), (key115, 1), (key115, 1), (key100, 1), (key100, 1), (key137, 1), (key137, 1), (key115, 1), (key115, 1), (key105, 1), (key105, 1)]

def rawRow9120 : Integer.Sparse Key := [(key74, -2), (key74, -2), (key74, -2), (key48, -2), (key48, -2), (key48, -2), (key48, -2), (key48, -2), (key48, -2), (key43, -2), (key43, -2), (key43, -2), (key137, 1), (key137, 1), (key137, 1), (key137, 1), (key137, 1), (key137, 1), (key115, 1), (key115, 1), (key115, 1), (key115, 1), (key115, 1), (key115, 1), (key105, 1), (key105, 1), (key105, 1), (key105, 1), (key105, 1), (key105, 1), (key100, 1), (key100, 1), (key100, 1), (key100, 1), (key100, 1), (key100, 1)]

def rawRow9121 : Integer.Sparse Key := [(key218, -2), (key218, -2), (key218, -2), (key486, -2), (key486, -2), (key486, -2), (key486, -2), (key486, -2), (key486, -2), (key490, -2), (key490, -2), (key490, -2), (key212, 1), (key212, 1), (key212, 1), (key212, 1), (key212, 1), (key212, 1), (key381, 1), (key381, 1), (key381, 1), (key381, 1), (key381, 1), (key381, 1), (key432, 1), (key432, 1), (key432, 1), (key432, 1), (key432, 1), (key432, 1), (key460, 1), (key460, 1), (key460, 1), (key460, 1), (key460, 1), (key460, 1)]

def rawRow9122 : Integer.Sparse Key := [(key486, -2), (key486, -2), (key490, -2), (key218, -2), (key218, -2), (key486, -2), (key486, -2), (key490, -2), (key490, -2), (key218, -2), (key486, -2), (key486, -2), (key381, 1), (key381, 1), (key432, 1), (key432, 1), (key460, 1), (key460, 1), (key212, 1), (key212, 1), (key432, 1), (key432, 1), (key460, 1), (key460, 1), (key212, 1), (key212, 1), (key381, 1), (key381, 1), (key460, 1), (key460, 1), (key212, 1), (key212, 1), (key381, 1), (key381, 1), (key432, 1), (key432, 1)]

def rawRow9123 : Integer.Sparse Key := [(key486, -2), (key490, -2), (key486, -2), (key486, -2), (key490, -2), (key218, -2), (key490, -2), (key218, -2), (key486, -2), (key486, -2), (key218, -2), (key486, -2), (key432, 1), (key460, 1), (key381, 1), (key460, 1), (key381, 1), (key432, 1), (key432, 1), (key460, 1), (key212, 1), (key460, 1), (key212, 1), (key432, 1), (key381, 1), (key460, 1), (key212, 1), (key460, 1), (key212, 1), (key381, 1), (key381, 1), (key432, 1), (key212, 1), (key432, 1), (key212, 1), (key381, 1)]

def rawRow9124 : Integer.Sparse Key := [(key490, -2), (key486, -2), (key486, -2), (key490, -2), (key486, -2), (key490, -2), (key218, -2), (key486, -2), (key218, -2), (key486, -2), (key486, -2), (key218, -2), (key460, 1), (key432, 1), (key460, 1), (key381, 1), (key432, 1), (key381, 1), (key460, 1), (key432, 1), (key460, 1), (key212, 1), (key432, 1), (key212, 1), (key460, 1), (key381, 1), (key460, 1), (key212, 1), (key381, 1), (key212, 1), (key432, 1), (key381, 1), (key432, 1), (key212, 1), (key381, 1), (key212, 1)]

def rawRow9125 : Integer.Sparse Key := [(key1106, 1), (key1114, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1123, 1), (key1106, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1150, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1150, 1), (key1123, 1), (key1150, 1), (key1114, 1), (key1123, 1), (key1114, 1), (key1150, 1), (key1123, 1), (key1150, 1), (key1232, -2), (key1232, -2), (key1235, -2), (key1232, -2), (key1232, -2), (key1242, -2), (key1232, -2), (key1235, -2), (key1232, -2), (key1242, -2), (key1235, -2), (key1242, -2)]

def rawRow9126 : Integer.Sparse Key := [(key1114, 1), (key1106, 1), (key1123, 1), (key1106, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1114, 1), (key1123, 1), (key1106, 1), (key1150, 1), (key1106, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1150, 1), (key1114, 1), (key1150, 1), (key1123, 1), (key1232, -2), (key1235, -2), (key1232, -2), (key1232, -2), (key1242, -2), (key1232, -2), (key1235, -2), (key1232, -2), (key1242, -2), (key1232, -2), (key1242, -2), (key1235, -2)]

def rawRow9127 : Integer.Sparse Key := [(key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1106, 1), (key1106, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1235, -2), (key1232, -2), (key1232, -2), (key1242, -2), (key1232, -2), (key1232, -2), (key1242, -2), (key1242, -2), (key1235, -2), (key1235, -2), (key1232, -2), (key1232, -2)]

def rawRow9128 : Integer.Sparse Key := [(key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1106, 1), (key1242, -2), (key1242, -2), (key1242, -2), (key1235, -2), (key1235, -2), (key1235, -2), (key1232, -2), (key1232, -2), (key1232, -2), (key1232, -2), (key1232, -2), (key1232, -2)]

def rawRow9129 : Integer.Sparse Key := [(key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key1232, 1), (key993, -2), (key993, -2), (key993, -2), (key1028, -2), (key1028, -2), (key1028, -2), (key1106, -2), (key1106, -2), (key1106, -2), (key1106, -2), (key1106, -2), (key1106, -2)]

def rawRow9130 : Integer.Sparse Key := [(key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1232, 1), (key1232, 1), (key1001, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1028, -2), (key1106, -2), (key1106, -2), (key993, -2), (key1106, -2), (key1106, -2), (key993, -2), (key993, -2), (key1028, -2), (key1028, -2), (key1106, -2), (key1106, -2)]

def rawRow9131 : Integer.Sparse Key := [(key1114, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1036, 1), (key1232, 1), (key1001, 1), (key1232, 1), (key1001, 1), (key1036, 1), (key1036, 1), (key1114, 1), (key1001, 1), (key1114, 1), (key1001, 1), (key1036, 1), (key1106, -2), (key1028, -2), (key1106, -2), (key1106, -2), (key993, -2), (key1106, -2), (key1028, -2), (key1106, -2), (key993, -2), (key1106, -2), (key993, -2), (key1028, -2)]

def rawRow9132 : Integer.Sparse Key := [(key1232, 1), (key1114, 1), (key1232, 1), (key1036, 1), (key1114, 1), (key1036, 1), (key1232, 1), (key1114, 1), (key1232, 1), (key1001, 1), (key1114, 1), (key1001, 1), (key1232, 1), (key1036, 1), (key1232, 1), (key1001, 1), (key1036, 1), (key1001, 1), (key1114, 1), (key1036, 1), (key1114, 1), (key1001, 1), (key1036, 1), (key1001, 1), (key1106, -2), (key1106, -2), (key1028, -2), (key1106, -2), (key1106, -2), (key993, -2), (key1106, -2), (key1028, -2), (key1106, -2), (key993, -2), (key1028, -2), (key993, -2)]

def rawRow9133 : Integer.Sparse Key := [(key45, -6), (key45, -6), (key45, -6), (key70, -6), (key102, 2), (key102, 2), (key111, 2), (key102, 2), (key102, 2), (key133, 2), (key102, 2), (key111, 2), (key102, 2), (key133, 2), (key111, 2), (key133, 2)]

def rawRow9134 : Integer.Sparse Key := [(key45, -6), (key45, -6), (key70, -6), (key45, -6), (key102, 2), (key111, 2), (key102, 2), (key102, 2), (key133, 2), (key102, 2), (key111, 2), (key102, 2), (key133, 2), (key102, 2), (key133, 2), (key111, 2)]

def rawRow9135 : Integer.Sparse Key := [(key45, -6), (key70, -6), (key45, -6), (key45, -6), (key111, 2), (key102, 2), (key102, 2), (key133, 2), (key102, 2), (key102, 2), (key133, 2), (key133, 2), (key111, 2), (key111, 2), (key102, 2), (key102, 2)]

def rawRow9136 : Integer.Sparse Key := [(key70, -6), (key45, -6), (key45, -6), (key45, -6), (key133, 2), (key133, 2), (key133, 2), (key111, 2), (key111, 2), (key111, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2)]

def rawRow9137 : Integer.Sparse Key := [(key31, -6), (key111, -6), (key111, -6), (key111, -6), (key20, 2), (key20, 2), (key20, 2), (key45, 2), (key45, 2), (key45, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2), (key102, 2)]

def rawRow9138 : Integer.Sparse Key := [(key111, -6), (key31, -6), (key111, -6), (key111, -6), (key45, 2), (key102, 2), (key102, 2), (key20, 2), (key102, 2), (key102, 2), (key20, 2), (key20, 2), (key45, 2), (key45, 2), (key102, 2), (key102, 2)]

def rawRow9139 : Integer.Sparse Key := [(key111, -6), (key111, -6), (key31, -6), (key111, -6), (key102, 2), (key45, 2), (key102, 2), (key102, 2), (key20, 2), (key102, 2), (key45, 2), (key102, 2), (key20, 2), (key102, 2), (key20, 2), (key45, 2)]

def rawRow9140 : Integer.Sparse Key := [(key111, -6), (key111, -6), (key111, -6), (key31, -6), (key102, 2), (key102, 2), (key45, 2), (key102, 2), (key102, 2), (key20, 2), (key102, 2), (key45, 2), (key102, 2), (key20, 2), (key45, 2), (key20, 2)]

def rawRow9141 : Integer.Sparse Key := [(key972, 6), (key977, 6), (key977, 6), (key977, 6), (key1181, -6), (key1181, -6), (key1181, -6), (key1218, -6)]

def rawRow9142 : Integer.Sparse Key := [(key977, 6), (key972, 6), (key977, 6), (key977, 6), (key1181, -6), (key1181, -6), (key1218, -6), (key1181, -6)]

def rawRow9143 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key972, 6), (key977, 6), (key1181, -6), (key1218, -6), (key1181, -6), (key1181, -6)]

def rawRow9144 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key977, 6), (key972, 6), (key1218, -6), (key1181, -6), (key1181, -6), (key1181, -6)]

def rawRow9145 : Integer.Sparse Key := [(key1162, 6), (key1162, 6), (key1162, 6), (key1218, 6), (key972, -6), (key1086, -6), (key1086, -6), (key1086, -6)]

def rawRow9146 : Integer.Sparse Key := [(key1162, 6), (key1162, 6), (key1218, 6), (key1162, 6), (key1086, -6), (key972, -6), (key1086, -6), (key1086, -6)]

def rawRow9147 : Integer.Sparse Key := [(key1162, 6), (key1218, 6), (key1162, 6), (key1162, 6), (key1086, -6), (key1086, -6), (key972, -6), (key1086, -6)]

def rawRow9148 : Integer.Sparse Key := [(key1218, 6), (key1162, 6), (key1162, 6), (key1162, 6), (key1086, -6), (key1086, -6), (key1086, -6), (key972, -6)]

def rawRow9149 : Integer.Sparse Key := [(key971, 6), (key979, 6), (key979, 6), (key979, 6), (key1228, -6), (key1228, -6), (key1228, -6), (key1245, -6)]

def rawRow9150 : Integer.Sparse Key := [(key979, 6), (key971, 6), (key979, 6), (key979, 6), (key1228, -6), (key1228, -6), (key1245, -6), (key1228, -6)]

def rawRow9151 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key971, 6), (key979, 6), (key1228, -6), (key1245, -6), (key1228, -6), (key1228, -6)]

def rawRow9152 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key979, 6), (key971, 6), (key1245, -6), (key1228, -6), (key1228, -6), (key1228, -6)]

def rawRow9153 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1164, 6), (key1245, 6), (key971, -6), (key1085, -6), (key1085, -6), (key1085, -6)]

def rawRow9154 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1245, 6), (key1164, 6), (key1085, -6), (key971, -6), (key1085, -6), (key1085, -6)]

def rawRow9155 : Integer.Sparse Key := [(key1164, 6), (key1245, 6), (key1164, 6), (key1164, 6), (key1085, -6), (key1085, -6), (key971, -6), (key1085, -6)]

def rawRow9156 : Integer.Sparse Key := [(key1245, 6), (key1164, 6), (key1164, 6), (key1164, 6), (key1085, -6), (key1085, -6), (key1085, -6), (key971, -6)]

def rawRow9157 : Integer.Sparse Key := [(key713, -6), (key715, -6), (key715, -6), (key715, -6), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key892, 2), (key890, 2), (key959, 2), (key892, 2), (key959, 2), (key892, 2), (key892, 2), (key959, 2)]

def rawRow9158 : Integer.Sparse Key := [(key715, -6), (key713, -6), (key715, -6), (key715, -6), (key892, 2), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key959, 2), (key890, 2), (key959, 2), (key892, 2), (key892, 2), (key959, 2), (key892, 2)]

def rawRow9159 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key713, -6), (key715, -6), (key892, 2), (key892, 2), (key890, 2), (key959, 2), (key959, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key959, 2), (key892, 2), (key892, 2)]

def rawRow9160 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key715, -6), (key713, -6), (key959, 2), (key959, 2), (key959, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key890, 2)]

def rawRow9161 : Integer.Sparse Key := [(key959, -6), (key959, -6), (key959, -6), (key966, -6), (key715, 2), (key715, 2), (key715, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key914, 2), (key914, 2), (key914, 2)]

def rawRow9162 : Integer.Sparse Key := [(key959, -6), (key959, -6), (key966, -6), (key959, -6), (key892, 2), (key892, 2), (key914, 2), (key715, 2), (key715, 2), (key892, 2), (key892, 2), (key914, 2), (key914, 2), (key715, 2), (key892, 2), (key892, 2)]

def rawRow9163 : Integer.Sparse Key := [(key959, -6), (key966, -6), (key959, -6), (key959, -6), (key892, 2), (key914, 2), (key892, 2), (key892, 2), (key914, 2), (key715, 2), (key914, 2), (key715, 2), (key892, 2), (key892, 2), (key715, 2), (key892, 2)]

def rawRow9164 : Integer.Sparse Key := [(key966, -6), (key959, -6), (key959, -6), (key959, -6), (key914, 2), (key892, 2), (key892, 2), (key914, 2), (key892, 2), (key914, 2), (key715, 2), (key892, 2), (key715, 2), (key892, 2), (key892, 2), (key715, 2)]

def rawRow9165 : Integer.Sparse Key := [(key1, 6), (key7, 6), (key7, 6), (key7, 6), (key193, -6), (key193, -6), (key193, -6), (key202, -6)]

def rawRow9166 : Integer.Sparse Key := [(key7, 6), (key1, 6), (key7, 6), (key7, 6), (key193, -6), (key193, -6), (key202, -6), (key193, -6)]

def rawRow9167 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key1, 6), (key7, 6), (key193, -6), (key202, -6), (key193, -6), (key193, -6)]

def rawRow9168 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key7, 6), (key1, 6), (key202, -6), (key193, -6), (key193, -6), (key193, -6)]

def rawRow9169 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key193, 6), (key202, 6), (key1, -6), (key84, -6), (key84, -6), (key84, -6)]

def rawRow9170 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key202, 6), (key193, 6), (key84, -6), (key1, -6), (key84, -6), (key84, -6)]

def rawRow9171 : Integer.Sparse Key := [(key193, 6), (key202, 6), (key193, 6), (key193, 6), (key84, -6), (key84, -6), (key1, -6), (key84, -6)]

def rawRow9172 : Integer.Sparse Key := [(key202, 6), (key193, 6), (key193, 6), (key193, 6), (key84, -6), (key84, -6), (key84, -6), (key1, -6)]

def rawRow9173 : Integer.Sparse Key := [(key2361, 2), (key2361, 2), (key2364, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2517, 2), (key2520, 2), (key2517, 2), (key2561, 2), (key2520, 2), (key2561, 2), (key2361, -2), (key2364, -2), (key2364, -2), (key2456, -2), (key2459, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2531, -2), (key2520, -2), (key2520, -2), (key2561, -2)]

def rawRow9174 : Integer.Sparse Key := [(key2361, 2), (key2364, 2), (key2361, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2520, 2), (key2517, 2), (key2561, 2), (key2517, 2), (key2561, 2), (key2520, 2), (key2364, -2), (key2361, -2), (key2364, -2), (key2459, -2), (key2456, -2), (key2531, -2), (key2456, -2), (key2531, -2), (key2459, -2), (key2520, -2), (key2561, -2), (key2520, -2)]

def rawRow9175 : Integer.Sparse Key := [(key2364, 2), (key2361, 2), (key2361, 2), (key2531, 2), (key2456, 2), (key2456, 2), (key2561, 2), (key2561, 2), (key2520, 2), (key2520, 2), (key2517, 2), (key2517, 2), (key2364, -2), (key2364, -2), (key2361, -2), (key2531, -2), (key2531, -2), (key2459, -2), (key2459, -2), (key2456, -2), (key2456, -2), (key2561, -2), (key2520, -2), (key2520, -2)]

def rawRow9176 : Integer.Sparse Key := [(key2456, 2), (key2517, 2), (key2520, 2), (key2361, 2), (key2517, 2), (key2561, 2), (key2361, 2), (key2364, 2), (key2456, 2), (key2531, 2), (key2520, 2), (key2561, 2), (key2456, -2), (key2459, -2), (key2520, -2), (key2361, -2), (key2364, -2), (key2456, -2), (key2531, -2), (key2520, -2), (key2561, -2), (key2364, -2), (key2459, -2), (key2531, -2)]

def rawRow9177 : Integer.Sparse Key := [(key2456, 2), (key2520, 2), (key2517, 2), (key2361, 2), (key2561, 2), (key2517, 2), (key2364, 2), (key2361, 2), (key2531, 2), (key2456, 2), (key2561, 2), (key2520, 2), (key2459, -2), (key2456, -2), (key2520, -2), (key2364, -2), (key2361, -2), (key2531, -2), (key2456, -2), (key2561, -2), (key2520, -2), (key2364, -2), (key2531, -2), (key2459, -2)]

def rawRow9178 : Integer.Sparse Key := [(key2517, 2), (key2456, 2), (key2520, 2), (key2517, 2), (key2361, 2), (key2561, 2), (key2456, 2), (key2520, 2), (key2361, 2), (key2561, 2), (key2364, 2), (key2531, 2), (key2456, -2), (key2520, -2), (key2459, -2), (key2456, -2), (key2520, -2), (key2361, -2), (key2561, -2), (key2364, -2), (key2531, -2), (key2459, -2), (key2364, -2), (key2531, -2)]

def rawRow9179 : Integer.Sparse Key := [(key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2561, 2), (key2361, 2), (key2520, 2), (key2456, 2), (key2561, 2), (key2361, 2), (key2531, 2), (key2364, 2), (key2520, -2), (key2456, -2), (key2459, -2), (key2520, -2), (key2456, -2), (key2561, -2), (key2361, -2), (key2531, -2), (key2364, -2), (key2459, -2), (key2531, -2), (key2364, -2)]

def rawRow9180 : Integer.Sparse Key := [(key2520, 2), (key2456, 2), (key2517, 2), (key2561, 2), (key2361, 2), (key2517, 2), (key2531, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2361, 2), (key2456, 2), (key2459, -2), (key2520, -2), (key2456, -2), (key2531, -2), (key2561, -2), (key2364, -2), (key2520, -2), (key2361, -2), (key2456, -2), (key2531, -2), (key2364, -2), (key2459, -2)]

def rawRow9181 : Integer.Sparse Key := [(key2520, 2), (key2517, 2), (key2456, 2), (key2561, 2), (key2517, 2), (key2361, 2), (key2561, 2), (key2531, 2), (key2520, 2), (key2364, 2), (key2456, 2), (key2361, 2), (key2520, -2), (key2459, -2), (key2456, -2), (key2561, -2), (key2531, -2), (key2520, -2), (key2364, -2), (key2456, -2), (key2361, -2), (key2531, -2), (key2459, -2), (key2364, -2)]

def rawRow9182 : Integer.Sparse Key := [(key2531, 2), (key2561, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2520, 2), (key2361, 2), (key2361, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2531, -2), (key2531, -2), (key2561, -2), (key2364, -2), (key2364, -2), (key2459, -2), (key2459, -2), (key2520, -2), (key2520, -2), (key2361, -2), (key2456, -2), (key2456, -2)]

def rawRow9183 : Integer.Sparse Key := [(key2561, 2), (key2531, 2), (key2561, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2517, 2), (key2361, 2), (key2456, 2), (key2531, -2), (key2561, -2), (key2531, -2), (key2459, -2), (key2520, -2), (key2364, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, -2), (key2361, -2), (key2456, -2)]

def rawRow9184 : Integer.Sparse Key := [(key2561, 2), (key2561, 2), (key2531, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2517, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2456, 2), (key2361, 2), (key2561, -2), (key2531, -2), (key2531, -2), (key2520, -2), (key2459, -2), (key2520, -2), (key2364, -2), (key2459, -2), (key2364, -2), (key2456, -2), (key2456, -2), (key2361, -2)]

def rawRow9185 : Integer.Sparse Key := [(key1083, -24), (key969, 6), (key1083, 6), (key1083, 6), (key1177, 6)]

def rawRow9186 : Integer.Sparse Key := [(key1083, -24), (key969, 6), (key1083, 6), (key1177, 6), (key1083, 6)]

def rawRow9187 : Integer.Sparse Key := [(key1083, -24), (key969, 6), (key1177, 6), (key1083, 6), (key1083, 6)]

def rawRow9188 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key969, 6), (key1083, 6), (key1177, 6)]

def rawRow9189 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key969, 6), (key1177, 6), (key1083, 6)]

def rawRow9190 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key1083, 6), (key969, 6), (key1177, 6)]

def rawRow9191 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key1083, 6), (key1177, 6), (key969, 6)]

def rawRow9192 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key1177, 6), (key969, 6), (key1083, 6)]

def rawRow9193 : Integer.Sparse Key := [(key1083, -24), (key1083, 6), (key1177, 6), (key1083, 6), (key969, 6)]

def rawRow9194 : Integer.Sparse Key := [(key1083, -24), (key1177, 6), (key969, 6), (key1083, 6), (key1083, 6)]

def rawRow9195 : Integer.Sparse Key := [(key1083, -24), (key1177, 6), (key1083, 6), (key969, 6), (key1083, 6)]

def rawRow9196 : Integer.Sparse Key := [(key1083, -24), (key1177, 6), (key1083, 6), (key1083, 6), (key969, 6)]

def rawRow9197 : Integer.Sparse Key := [(key1086, -6), (key1091, -6), (key1091, -6), (key1162, -6), (key972, 2), (key977, 2), (key977, 2), (key1086, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1181, 2), (key1162, 2), (key1162, 2), (key1218, 2)]

def rawRow9198 : Integer.Sparse Key := [(key1091, -6), (key1086, -6), (key1091, -6), (key1162, -6), (key977, 2), (key972, 2), (key977, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1162, 2), (key1218, 2), (key1162, 2)]

def rawRow9199 : Integer.Sparse Key := [(key1091, -6), (key1091, -6), (key1086, -6), (key1162, -6), (key977, 2), (key977, 2), (key972, 2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1218, 2), (key1162, 2), (key1162, 2)]

def rawRow9200 : Integer.Sparse Key := [(key1086, -6), (key1091, -6), (key1162, -6), (key1091, -6), (key1086, 2), (key1091, 2), (key1162, 2), (key972, 2), (key977, 2), (key1086, 2), (key1181, 2), (key1162, 2), (key1218, 2), (key977, 2), (key1091, 2), (key1181, 2)]

def rawRow9201 : Integer.Sparse Key := [(key1091, -6), (key1086, -6), (key1162, -6), (key1091, -6), (key1091, 2), (key1086, 2), (key1162, 2), (key977, 2), (key972, 2), (key1181, 2), (key1086, 2), (key1218, 2), (key1162, 2), (key977, 2), (key1181, 2), (key1091, 2)]

def rawRow9202 : Integer.Sparse Key := [(key1086, -6), (key1162, -6), (key1091, -6), (key1091, -6), (key1086, 2), (key1162, 2), (key1091, 2), (key1086, 2), (key1162, 2), (key972, 2), (key1218, 2), (key977, 2), (key1181, 2), (key1091, 2), (key977, 2), (key1181, 2)]

def rawRow9203 : Integer.Sparse Key := [(key1162, -6), (key1086, -6), (key1091, -6), (key1091, -6), (key1162, 2), (key1086, 2), (key1091, 2), (key1162, 2), (key1086, 2), (key1218, 2), (key972, 2), (key1181, 2), (key977, 2), (key1091, 2), (key1181, 2), (key977, 2)]

def rawRow9204 : Integer.Sparse Key := [(key1091, -6), (key1162, -6), (key1086, -6), (key1091, -6), (key1091, 2), (key1162, 2), (key1086, 2), (key1181, 2), (key1218, 2), (key977, 2), (key1162, 2), (key972, 2), (key1086, 2), (key1181, 2), (key977, 2), (key1091, 2)]

def rawRow9205 : Integer.Sparse Key := [(key1162, -6), (key1091, -6), (key1086, -6), (key1091, -6), (key1162, 2), (key1091, 2), (key1086, 2), (key1218, 2), (key1181, 2), (key1162, 2), (key977, 2), (key1086, 2), (key972, 2), (key1181, 2), (key1091, 2), (key977, 2)]

def rawRow9206 : Integer.Sparse Key := [(key1091, -6), (key1091, -6), (key1162, -6), (key1086, -6), (key1181, 2), (key1181, 2), (key1218, 2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key972, 2), (key1086, 2), (key1086, 2)]

def rawRow9207 : Integer.Sparse Key := [(key1091, -6), (key1162, -6), (key1091, -6), (key1086, -6), (key1181, 2), (key1218, 2), (key1181, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1086, 2), (key972, 2), (key1086, 2)]

def rawRow9208 : Integer.Sparse Key := [(key1162, -6), (key1091, -6), (key1091, -6), (key1086, -6), (key1218, 2), (key1181, 2), (key1181, 2), (key1162, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1091, 2), (key977, 2), (key1086, 2), (key1086, 2), (key972, 2)]

def rawRow9209 : Integer.Sparse Key := [(key2369, -6), (key2463, -6), (key2463, -6), (key2497, -6), (key2369, 2), (key2369, 2), (key2384, 2), (key2397, 2), (key2397, 2), (key2431, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2474, 2), (key2497, 2)]

def rawRow9210 : Integer.Sparse Key := [(key2369, -6), (key2463, -6), (key2497, -6), (key2463, -6), (key2369, 2), (key2384, 2), (key2369, 2), (key2397, 2), (key2431, 2), (key2397, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2474, 2)]

def rawRow9211 : Integer.Sparse Key := [(key2369, -6), (key2497, -6), (key2463, -6), (key2463, -6), (key2384, 2), (key2369, 2), (key2369, 2), (key2431, 2), (key2397, 2), (key2397, 2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2)]

def rawRow9212 : Integer.Sparse Key := [(key2463, -6), (key2369, -6), (key2463, -6), (key2497, -6), (key2397, 2), (key2463, 2), (key2474, 2), (key2369, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2384, 2), (key2397, 2), (key2431, 2), (key2474, 2), (key2497, 2)]

def rawRow9213 : Integer.Sparse Key := [(key2463, -6), (key2369, -6), (key2497, -6), (key2463, -6), (key2397, 2), (key2474, 2), (key2463, 2), (key2369, 2), (key2497, 2), (key2463, 2), (key2384, 2), (key2369, 2), (key2431, 2), (key2397, 2), (key2497, 2), (key2474, 2)]

def rawRow9214 : Integer.Sparse Key := [(key2463, -6), (key2463, -6), (key2369, -6), (key2497, -6), (key2463, 2), (key2397, 2), (key2474, 2), (key2463, 2), (key2369, 2), (key2497, 2), (key2397, 2), (key2474, 2), (key2369, 2), (key2497, 2), (key2384, 2), (key2431, 2)]

def rawRow9215 : Integer.Sparse Key := [(key2463, -6), (key2463, -6), (key2497, -6), (key2369, -6), (key2463, 2), (key2474, 2), (key2397, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2474, 2), (key2397, 2), (key2497, 2), (key2369, 2), (key2431, 2), (key2384, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9216 : Integer.Sparse Key := [(key2463, -6), (key2497, -6), (key2369, -6), (key2463, -6), (key2474, 2), (key2397, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2463, 2), (key2431, 2), (key2497, 2), (key2384, 2), (key2474, 2), (key2369, 2), (key2397, 2)]

def rawRow9217 : Integer.Sparse Key := [(key2463, -6), (key2497, -6), (key2463, -6), (key2369, -6), (key2474, 2), (key2463, 2), (key2397, 2), (key2497, 2), (key2463, 2), (key2369, 2), (key2497, 2), (key2431, 2), (key2474, 2), (key2384, 2), (key2397, 2), (key2369, 2)]

def rawRow9218 : Integer.Sparse Key := [(key2497, -6), (key2369, -6), (key2463, -6), (key2463, -6), (key2431, 2), (key2497, 2), (key2497, 2), (key2384, 2), (key2474, 2), (key2474, 2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

def rawRow9219 : Integer.Sparse Key := [(key2497, -6), (key2463, -6), (key2369, -6), (key2463, -6), (key2497, 2), (key2431, 2), (key2497, 2), (key2474, 2), (key2384, 2), (key2474, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2397, 2)]

def rawRow9220 : Integer.Sparse Key := [(key2497, -6), (key2463, -6), (key2463, -6), (key2369, -6), (key2497, 2), (key2497, 2), (key2431, 2), (key2474, 2), (key2474, 2), (key2384, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2397, 2), (key2369, 2)]

def rawRow9221 : Integer.Sparse Key := [(key2449, -6), (key2453, -6), (key2453, -6), (key2514, -6), (key2354, 2), (key2358, 2), (key2358, 2), (key2449, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2529, 2), (key2514, 2), (key2514, 2), (key2559, 2)]

def rawRow9222 : Integer.Sparse Key := [(key2453, -6), (key2449, -6), (key2453, -6), (key2514, -6), (key2358, 2), (key2354, 2), (key2358, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2514, 2), (key2559, 2), (key2514, 2)]

def rawRow9223 : Integer.Sparse Key := [(key2453, -6), (key2453, -6), (key2449, -6), (key2514, -6), (key2358, 2), (key2358, 2), (key2354, 2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2559, 2), (key2514, 2), (key2514, 2)]

def rawRow9224 : Integer.Sparse Key := [(key2449, -6), (key2453, -6), (key2514, -6), (key2453, -6), (key2449, 2), (key2453, 2), (key2514, 2), (key2354, 2), (key2358, 2), (key2449, 2), (key2529, 2), (key2514, 2), (key2559, 2), (key2358, 2), (key2453, 2), (key2529, 2)]

def rawRow9225 : Integer.Sparse Key := [(key2453, -6), (key2449, -6), (key2514, -6), (key2453, -6), (key2453, 2), (key2449, 2), (key2514, 2), (key2358, 2), (key2354, 2), (key2529, 2), (key2449, 2), (key2559, 2), (key2514, 2), (key2358, 2), (key2529, 2), (key2453, 2)]

def rawRow9226 : Integer.Sparse Key := [(key2449, -6), (key2514, -6), (key2453, -6), (key2453, -6), (key2449, 2), (key2514, 2), (key2453, 2), (key2449, 2), (key2514, 2), (key2354, 2), (key2559, 2), (key2358, 2), (key2529, 2), (key2453, 2), (key2358, 2), (key2529, 2)]

def rawRow9227 : Integer.Sparse Key := [(key2514, -6), (key2449, -6), (key2453, -6), (key2453, -6), (key2514, 2), (key2449, 2), (key2453, 2), (key2514, 2), (key2449, 2), (key2559, 2), (key2354, 2), (key2529, 2), (key2358, 2), (key2453, 2), (key2529, 2), (key2358, 2)]

def rawRow9228 : Integer.Sparse Key := [(key2453, -6), (key2514, -6), (key2449, -6), (key2453, -6), (key2453, 2), (key2514, 2), (key2449, 2), (key2529, 2), (key2559, 2), (key2358, 2), (key2514, 2), (key2354, 2), (key2449, 2), (key2529, 2), (key2358, 2), (key2453, 2)]

def rawRow9229 : Integer.Sparse Key := [(key2514, -6), (key2453, -6), (key2449, -6), (key2453, -6), (key2514, 2), (key2453, 2), (key2449, 2), (key2559, 2), (key2529, 2), (key2514, 2), (key2358, 2), (key2449, 2), (key2354, 2), (key2529, 2), (key2453, 2), (key2358, 2)]

def rawRow9230 : Integer.Sparse Key := [(key2453, -6), (key2453, -6), (key2514, -6), (key2449, -6), (key2529, 2), (key2529, 2), (key2559, 2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2354, 2), (key2449, 2), (key2449, 2)]

def rawRow9231 : Integer.Sparse Key := [(key2453, -6), (key2514, -6), (key2453, -6), (key2449, -6), (key2529, 2), (key2559, 2), (key2529, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2449, 2), (key2354, 2), (key2449, 2)]

def rawRow9232 : Integer.Sparse Key := [(key2514, -6), (key2453, -6), (key2453, -6), (key2449, -6), (key2559, 2), (key2529, 2), (key2529, 2), (key2514, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2358, 2), (key2449, 2), (key2449, 2), (key2354, 2)]

def rawRow9233 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2840, -2), (key2844, -2), (key2840, -2), (key2967, -2), (key2844, -2), (key2967, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2584, 1), (key2588, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2599, 1), (key2763, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2930, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2875, 1), (key2909, 1), (key2875, 1), (key2988, 1), (key2909, 1), (key2988, 1)]

def rawRow9234 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2844, -2), (key2840, -2), (key2967, -2), (key2840, -2), (key2967, -2), (key2844, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2588, 1), (key2584, 1), (key2599, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2909, 1), (key2875, 1), (key2988, 1), (key2875, 1), (key2988, 1), (key2909, 1)]

def rawRow9235 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2967, -2), (key2967, -2), (key2844, -2), (key2844, -2), (key2840, -2), (key2840, -2), (key2988, -2), (key2875, -2), (key2875, -2), (key2599, 1), (key2599, 1), (key2588, 1), (key2588, 1), (key2584, 1), (key2584, 1), (key2930, 1), (key2930, 1), (key2767, 1), (key2767, 1), (key2763, 1), (key2763, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2840, 1), (key2840, 1), (key2988, 1), (key2988, 1), (key2909, 1), (key2909, 1), (key2875, 1), (key2875, 1)]

def rawRow9236 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2875, -2), (key2584, -2), (key2588, -2), (key2840, -2), (key2967, -2), (key2875, -2), (key2988, -2), (key2588, -2), (key2844, -2), (key2967, -2), (key2763, 1), (key2767, 1), (key2840, 1), (key2888, 1), (key2875, 1), (key2909, 1), (key2584, 1), (key2588, 1), (key2840, 1), (key2967, 1), (key2875, 1), (key2988, 1), (key2584, 1), (key2599, 1), (key2763, 1), (key2930, 1), (key2909, 1), (key2988, 1), (key2588, 1), (key2599, 1), (key2767, 1), (key2930, 1), (key2888, 1), (key2967, 1)]

def rawRow9237 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2875, -2), (key2588, -2), (key2584, -2), (key2967, -2), (key2840, -2), (key2988, -2), (key2875, -2), (key2588, -2), (key2967, -2), (key2844, -2), (key2767, 1), (key2763, 1), (key2888, 1), (key2840, 1), (key2909, 1), (key2875, 1), (key2588, 1), (key2584, 1), (key2967, 1), (key2840, 1), (key2988, 1), (key2875, 1), (key2599, 1), (key2584, 1), (key2930, 1), (key2763, 1), (key2988, 1), (key2909, 1), (key2599, 1), (key2588, 1), (key2930, 1), (key2767, 1), (key2967, 1), (key2888, 1)]

def rawRow9238 : Integer.Sparse Key := [(key2840, -2), (key2875, -2), (key2844, -2), (key2840, -2), (key2875, -2), (key2584, -2), (key2988, -2), (key2588, -2), (key2967, -2), (key2844, -2), (key2588, -2), (key2967, -2), (key2840, 1), (key2875, 1), (key2763, 1), (key2909, 1), (key2767, 1), (key2888, 1), (key2840, 1), (key2875, 1), (key2584, 1), (key2988, 1), (key2588, 1), (key2967, 1), (key2763, 1), (key2909, 1), (key2584, 1), (key2988, 1), (key2599, 1), (key2930, 1), (key2767, 1), (key2888, 1), (key2588, 1), (key2967, 1), (key2599, 1), (key2930, 1)]

def rawRow9239 : Integer.Sparse Key := [(key2875, -2), (key2840, -2), (key2844, -2), (key2875, -2), (key2840, -2), (key2988, -2), (key2584, -2), (key2967, -2), (key2588, -2), (key2844, -2), (key2967, -2), (key2588, -2), (key2875, 1), (key2840, 1), (key2909, 1), (key2763, 1), (key2888, 1), (key2767, 1), (key2875, 1), (key2840, 1), (key2988, 1), (key2584, 1), (key2967, 1), (key2588, 1), (key2909, 1), (key2763, 1), (key2988, 1), (key2584, 1), (key2930, 1), (key2599, 1), (key2888, 1), (key2767, 1), (key2967, 1), (key2588, 1), (key2930, 1), (key2599, 1)]

def rawRow9240 : Integer.Sparse Key := [(key2844, -2), (key2875, -2), (key2840, -2), (key2967, -2), (key2988, -2), (key2588, -2), (key2875, -2), (key2584, -2), (key2840, -2), (key2967, -2), (key2588, -2), (key2844, -2), (key2888, 1), (key2909, 1), (key2767, 1), (key2875, 1), (key2763, 1), (key2840, 1), (key2967, 1), (key2988, 1), (key2588, 1), (key2875, 1), (key2584, 1), (key2840, 1), (key2930, 1), (key2988, 1), (key2599, 1), (key2909, 1), (key2584, 1), (key2763, 1), (key2930, 1), (key2967, 1), (key2599, 1), (key2888, 1), (key2588, 1), (key2767, 1)]

def rawRow9241 : Integer.Sparse Key := [(key2875, -2), (key2844, -2), (key2840, -2), (key2988, -2), (key2967, -2), (key2875, -2), (key2588, -2), (key2840, -2), (key2584, -2), (key2967, -2), (key2844, -2), (key2588, -2), (key2909, 1), (key2888, 1), (key2875, 1), (key2767, 1), (key2840, 1), (key2763, 1), (key2988, 1), (key2967, 1), (key2875, 1), (key2588, 1), (key2840, 1), (key2584, 1), (key2988, 1), (key2930, 1), (key2909, 1), (key2599, 1), (key2763, 1), (key2584, 1), (key2967, 1), (key2930, 1), (key2888, 1), (key2599, 1), (key2767, 1), (key2588, 1)]

def rawRow9242 : Integer.Sparse Key := [(key2967, -2), (key2967, -2), (key2988, -2), (key2588, -2), (key2588, -2), (key2844, -2), (key2844, -2), (key2875, -2), (key2875, -2), (key2584, -2), (key2840, -2), (key2840, -2), (key2930, 1), (key2930, 1), (key2967, 1), (key2967, 1), (key2988, 1), (key2988, 1), (key2599, 1), (key2599, 1), (key2888, 1), (key2888, 1), (key2909, 1), (key2909, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2875, 1), (key2875, 1), (key2584, 1), (key2584, 1), (key2763, 1), (key2763, 1), (key2840, 1), (key2840, 1)]

def rawRow9243 : Integer.Sparse Key := [(key2967, -2), (key2988, -2), (key2967, -2), (key2844, -2), (key2875, -2), (key2588, -2), (key2875, -2), (key2588, -2), (key2844, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2967, 1), (key2988, 1), (key2930, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2763, 1), (key2840, 1), (key2584, 1), (key2840, 1), (key2584, 1), (key2763, 1)]

def rawRow9244 : Integer.Sparse Key := [(key2988, -2), (key2967, -2), (key2967, -2), (key2875, -2), (key2844, -2), (key2875, -2), (key2588, -2), (key2844, -2), (key2588, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2988, 1), (key2967, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2930, 1), (key2909, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2599, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2840, 1), (key2763, 1), (key2840, 1), (key2584, 1), (key2763, 1), (key2584, 1)]

def rawRow9245 : Integer.Sparse Key := [(key2447, -24), (key2352, 6), (key2447, 6), (key2447, 6), (key2511, 6)]

def rawRow9246 : Integer.Sparse Key := [(key2447, -24), (key2352, 6), (key2447, 6), (key2511, 6), (key2447, 6)]

def rawRow9247 : Integer.Sparse Key := [(key2447, -24), (key2352, 6), (key2511, 6), (key2447, 6), (key2447, 6)]

def rawRow9248 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2352, 6), (key2447, 6), (key2511, 6)]

def rawRow9249 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2352, 6), (key2511, 6), (key2447, 6)]

def rawRow9250 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2447, 6), (key2352, 6), (key2511, 6)]

def rawRow9251 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2447, 6), (key2511, 6), (key2352, 6)]

def rawRow9252 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2511, 6), (key2352, 6), (key2447, 6)]

def rawRow9253 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2511, 6), (key2447, 6), (key2352, 6)]

def rawRow9254 : Integer.Sparse Key := [(key2447, -24), (key2511, 6), (key2352, 6), (key2447, 6), (key2447, 6)]

def rawRow9255 : Integer.Sparse Key := [(key2447, -24), (key2511, 6), (key2447, 6), (key2352, 6), (key2447, 6)]

def rawRow9256 : Integer.Sparse Key := [(key2447, -24), (key2511, 6), (key2447, 6), (key2447, 6), (key2352, 6)]

def rawRow9257 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2840, -2), (key2844, -2), (key2840, -2), (key2888, -2), (key2844, -2), (key2888, -2), (key2875, -2), (key2875, -2), (key2909, -2), (key2584, 2), (key2588, 2), (key2588, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2875, 2), (key2875, 2), (key2988, 2)]

def rawRow9258 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2844, -2), (key2840, -2), (key2888, -2), (key2840, -2), (key2888, -2), (key2844, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2588, 2), (key2584, 2), (key2588, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2875, 2), (key2988, 2), (key2875, 2)]

def rawRow9259 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2888, -2), (key2888, -2), (key2844, -2), (key2844, -2), (key2840, -2), (key2840, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2588, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2967, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2875, 2)]

def rawRow9260 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2875, -2), (key2763, -2), (key2767, -2), (key2840, -2), (key2888, -2), (key2875, -2), (key2909, -2), (key2767, -2), (key2844, -2), (key2888, -2), (key2840, 2), (key2844, 2), (key2875, 2), (key2584, 2), (key2588, 2), (key2840, 2), (key2967, 2), (key2875, 2), (key2988, 2), (key2588, 2), (key2844, 2), (key2967, 2)]

def rawRow9261 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2875, -2), (key2767, -2), (key2763, -2), (key2888, -2), (key2840, -2), (key2909, -2), (key2875, -2), (key2767, -2), (key2888, -2), (key2844, -2), (key2844, 2), (key2840, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2588, 2), (key2967, 2), (key2844, 2)]

def rawRow9262 : Integer.Sparse Key := [(key2840, -2), (key2875, -2), (key2844, -2), (key2840, -2), (key2875, -2), (key2763, -2), (key2909, -2), (key2767, -2), (key2888, -2), (key2844, -2), (key2767, -2), (key2888, -2), (key2840, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2967, 2)]

def rawRow9263 : Integer.Sparse Key := [(key2875, -2), (key2840, -2), (key2844, -2), (key2875, -2), (key2840, -2), (key2909, -2), (key2763, -2), (key2888, -2), (key2767, -2), (key2844, -2), (key2888, -2), (key2767, -2), (key2875, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2588, 2)]

def rawRow9264 : Integer.Sparse Key := [(key2844, -2), (key2875, -2), (key2840, -2), (key2888, -2), (key2909, -2), (key2767, -2), (key2875, -2), (key2763, -2), (key2840, -2), (key2888, -2), (key2767, -2), (key2844, -2), (key2844, 2), (key2875, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2967, 2), (key2588, 2), (key2844, 2)]

def rawRow9265 : Integer.Sparse Key := [(key2875, -2), (key2844, -2), (key2840, -2), (key2909, -2), (key2888, -2), (key2875, -2), (key2767, -2), (key2840, -2), (key2763, -2), (key2888, -2), (key2844, -2), (key2767, -2), (key2875, 2), (key2844, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2875, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2967, 2), (key2844, 2), (key2588, 2)]

def rawRow9266 : Integer.Sparse Key := [(key2888, -2), (key2888, -2), (key2909, -2), (key2767, -2), (key2767, -2), (key2844, -2), (key2844, -2), (key2875, -2), (key2875, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2967, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2840, 2)]

def rawRow9267 : Integer.Sparse Key := [(key2888, -2), (key2909, -2), (key2888, -2), (key2844, -2), (key2875, -2), (key2767, -2), (key2875, -2), (key2767, -2), (key2844, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2967, 2), (key2988, 2), (key2967, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2840, 2), (key2584, 2), (key2840, 2)]

def rawRow9268 : Integer.Sparse Key := [(key2909, -2), (key2888, -2), (key2888, -2), (key2875, -2), (key2844, -2), (key2875, -2), (key2767, -2), (key2844, -2), (key2767, -2), (key2840, -2), (key2840, -2), (key2763, -2), (key2988, 2), (key2967, 2), (key2967, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2840, 2), (key2840, 2), (key2584, 2)]

def rawRow9269 : Integer.Sparse Key := [(key1252, -2), (key1257, -2), (key1257, -2), (key1605, -2), (key1610, -2), (key1605, -2), (key1807, -2), (key1610, -2), (key1807, -2), (key1638, -2), (key1638, -2), (key1830, -2), (key1252, 1), (key1257, 1), (key1252, 1), (key1266, 1), (key1257, 1), (key1266, 1), (key1527, 1), (key1532, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1766, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1807, 1), (key1649, 1), (key1807, 1), (key1638, 1), (key1672, 1), (key1638, 1), (key1830, 1), (key1672, 1), (key1830, 1)]

def rawRow9270 : Integer.Sparse Key := [(key1257, -2), (key1252, -2), (key1257, -2), (key1610, -2), (key1605, -2), (key1807, -2), (key1605, -2), (key1807, -2), (key1610, -2), (key1638, -2), (key1830, -2), (key1638, -2), (key1257, 1), (key1252, 1), (key1266, 1), (key1252, 1), (key1266, 1), (key1257, 1), (key1532, 1), (key1527, 1), (key1766, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1649, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1649, 1), (key1672, 1), (key1638, 1), (key1830, 1), (key1638, 1), (key1830, 1), (key1672, 1)]

def rawRow9271 : Integer.Sparse Key := [(key1257, -2), (key1257, -2), (key1252, -2), (key1807, -2), (key1807, -2), (key1610, -2), (key1610, -2), (key1605, -2), (key1605, -2), (key1830, -2), (key1638, -2), (key1638, -2), (key1266, 1), (key1266, 1), (key1257, 1), (key1257, 1), (key1252, 1), (key1252, 1), (key1766, 1), (key1766, 1), (key1532, 1), (key1532, 1), (key1527, 1), (key1527, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1605, 1), (key1605, 1), (key1830, 1), (key1830, 1), (key1672, 1), (key1672, 1), (key1638, 1), (key1638, 1)]

def rawRow9272 : Integer.Sparse Key := [(key1605, -2), (key1610, -2), (key1638, -2), (key1252, -2), (key1257, -2), (key1605, -2), (key1807, -2), (key1638, -2), (key1830, -2), (key1257, -2), (key1610, -2), (key1807, -2), (key1527, 1), (key1532, 1), (key1605, 1), (key1649, 1), (key1638, 1), (key1672, 1), (key1252, 1), (key1257, 1), (key1605, 1), (key1807, 1), (key1638, 1), (key1830, 1), (key1252, 1), (key1266, 1), (key1527, 1), (key1766, 1), (key1672, 1), (key1830, 1), (key1257, 1), (key1266, 1), (key1532, 1), (key1766, 1), (key1649, 1), (key1807, 1)]

def rawRow9273 : Integer.Sparse Key := [(key1610, -2), (key1605, -2), (key1638, -2), (key1257, -2), (key1252, -2), (key1807, -2), (key1605, -2), (key1830, -2), (key1638, -2), (key1257, -2), (key1807, -2), (key1610, -2), (key1532, 1), (key1527, 1), (key1649, 1), (key1605, 1), (key1672, 1), (key1638, 1), (key1257, 1), (key1252, 1), (key1807, 1), (key1605, 1), (key1830, 1), (key1638, 1), (key1266, 1), (key1252, 1), (key1766, 1), (key1527, 1), (key1830, 1), (key1672, 1), (key1266, 1), (key1257, 1), (key1766, 1), (key1532, 1), (key1807, 1), (key1649, 1)]

def rawRow9274 : Integer.Sparse Key := [(key1605, -2), (key1638, -2), (key1610, -2), (key1605, -2), (key1638, -2), (key1252, -2), (key1830, -2), (key1257, -2), (key1807, -2), (key1610, -2), (key1257, -2), (key1807, -2), (key1605, 1), (key1638, 1), (key1527, 1), (key1672, 1), (key1532, 1), (key1649, 1), (key1605, 1), (key1638, 1), (key1252, 1), (key1830, 1), (key1257, 1), (key1807, 1), (key1527, 1), (key1672, 1), (key1252, 1), (key1830, 1), (key1266, 1), (key1766, 1), (key1532, 1), (key1649, 1), (key1257, 1), (key1807, 1), (key1266, 1), (key1766, 1)]

def rawRow9275 : Integer.Sparse Key := [(key1638, -2), (key1605, -2), (key1610, -2), (key1638, -2), (key1605, -2), (key1830, -2), (key1252, -2), (key1807, -2), (key1257, -2), (key1610, -2), (key1807, -2), (key1257, -2), (key1638, 1), (key1605, 1), (key1672, 1), (key1527, 1), (key1649, 1), (key1532, 1), (key1638, 1), (key1605, 1), (key1830, 1), (key1252, 1), (key1807, 1), (key1257, 1), (key1672, 1), (key1527, 1), (key1830, 1), (key1252, 1), (key1766, 1), (key1266, 1), (key1649, 1), (key1532, 1), (key1807, 1), (key1257, 1), (key1766, 1), (key1266, 1)]

def rawRow9276 : Integer.Sparse Key := [(key1610, -2), (key1638, -2), (key1605, -2), (key1807, -2), (key1830, -2), (key1257, -2), (key1638, -2), (key1252, -2), (key1605, -2), (key1807, -2), (key1257, -2), (key1610, -2), (key1649, 1), (key1672, 1), (key1532, 1), (key1638, 1), (key1527, 1), (key1605, 1), (key1807, 1), (key1830, 1), (key1257, 1), (key1638, 1), (key1252, 1), (key1605, 1), (key1766, 1), (key1830, 1), (key1266, 1), (key1672, 1), (key1252, 1), (key1527, 1), (key1766, 1), (key1807, 1), (key1266, 1), (key1649, 1), (key1257, 1), (key1532, 1)]

def rawRow9277 : Integer.Sparse Key := [(key1638, -2), (key1610, -2), (key1605, -2), (key1830, -2), (key1807, -2), (key1638, -2), (key1257, -2), (key1605, -2), (key1252, -2), (key1807, -2), (key1610, -2), (key1257, -2), (key1672, 1), (key1649, 1), (key1638, 1), (key1532, 1), (key1605, 1), (key1527, 1), (key1830, 1), (key1807, 1), (key1638, 1), (key1257, 1), (key1605, 1), (key1252, 1), (key1830, 1), (key1766, 1), (key1672, 1), (key1266, 1), (key1527, 1), (key1252, 1), (key1807, 1), (key1766, 1), (key1649, 1), (key1266, 1), (key1532, 1), (key1257, 1)]

def rawRow9278 : Integer.Sparse Key := [(key1807, -2), (key1807, -2), (key1830, -2), (key1257, -2), (key1257, -2), (key1610, -2), (key1610, -2), (key1638, -2), (key1638, -2), (key1252, -2), (key1605, -2), (key1605, -2), (key1766, 1), (key1766, 1), (key1807, 1), (key1807, 1), (key1830, 1), (key1830, 1), (key1266, 1), (key1266, 1), (key1649, 1), (key1649, 1), (key1672, 1), (key1672, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1638, 1), (key1638, 1), (key1252, 1), (key1252, 1), (key1527, 1), (key1527, 1), (key1605, 1), (key1605, 1)]

def rawRow9279 : Integer.Sparse Key := [(key1807, -2), (key1830, -2), (key1807, -2), (key1610, -2), (key1638, -2), (key1257, -2), (key1638, -2), (key1257, -2), (key1610, -2), (key1605, -2), (key1252, -2), (key1605, -2), (key1807, 1), (key1830, 1), (key1766, 1), (key1830, 1), (key1766, 1), (key1807, 1), (key1649, 1), (key1672, 1), (key1266, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1532, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1532, 1), (key1527, 1), (key1605, 1), (key1252, 1), (key1605, 1), (key1252, 1), (key1527, 1)]

def rawRow9280 : Integer.Sparse Key := [(key1830, -2), (key1807, -2), (key1807, -2), (key1638, -2), (key1610, -2), (key1638, -2), (key1257, -2), (key1610, -2), (key1257, -2), (key1605, -2), (key1605, -2), (key1252, -2), (key1830, 1), (key1807, 1), (key1830, 1), (key1766, 1), (key1807, 1), (key1766, 1), (key1672, 1), (key1649, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1266, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1257, 1), (key1532, 1), (key1257, 1), (key1605, 1), (key1527, 1), (key1605, 1), (key1252, 1), (key1527, 1), (key1252, 1)]

def rawRow9281 : Integer.Sparse Key := [(key2584, 1), (key2588, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2599, 1), (key2763, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2930, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2875, 1), (key2909, 1), (key2875, 1), (key2988, 1), (key2909, 1), (key2988, 1), (key2588, -2), (key2588, -2), (key2599, -2), (key2767, -2), (key2767, -2), (key2930, -2), (key2844, -2), (key2888, -2), (key2844, -2), (key2967, -2), (key2888, -2), (key2967, -2)]

def rawRow9282 : Integer.Sparse Key := [(key2588, 1), (key2584, 1), (key2599, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2909, 1), (key2875, 1), (key2988, 1), (key2875, 1), (key2988, 1), (key2909, 1), (key2588, -2), (key2599, -2), (key2588, -2), (key2767, -2), (key2930, -2), (key2767, -2), (key2888, -2), (key2844, -2), (key2967, -2), (key2844, -2), (key2967, -2), (key2888, -2)]

def rawRow9283 : Integer.Sparse Key := [(key2599, 1), (key2599, 1), (key2588, 1), (key2588, 1), (key2584, 1), (key2584, 1), (key2930, 1), (key2930, 1), (key2767, 1), (key2767, 1), (key2763, 1), (key2763, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2840, 1), (key2840, 1), (key2988, 1), (key2988, 1), (key2909, 1), (key2909, 1), (key2875, 1), (key2875, 1), (key2599, -2), (key2588, -2), (key2588, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2967, -2), (key2967, -2), (key2888, -2), (key2888, -2), (key2844, -2), (key2844, -2)]

def rawRow9284 : Integer.Sparse Key := [(key2763, 1), (key2767, 1), (key2840, 1), (key2888, 1), (key2875, 1), (key2909, 1), (key2584, 1), (key2588, 1), (key2840, 1), (key2967, 1), (key2875, 1), (key2988, 1), (key2584, 1), (key2599, 1), (key2763, 1), (key2930, 1), (key2909, 1), (key2988, 1), (key2588, 1), (key2599, 1), (key2767, 1), (key2930, 1), (key2888, 1), (key2967, 1), (key2767, -2), (key2844, -2), (key2888, -2), (key2588, -2), (key2844, -2), (key2967, -2), (key2588, -2), (key2599, -2), (key2767, -2), (key2930, -2), (key2888, -2), (key2967, -2)]

def rawRow9285 : Integer.Sparse Key := [(key2767, 1), (key2763, 1), (key2888, 1), (key2840, 1), (key2909, 1), (key2875, 1), (key2588, 1), (key2584, 1), (key2967, 1), (key2840, 1), (key2988, 1), (key2875, 1), (key2599, 1), (key2584, 1), (key2930, 1), (key2763, 1), (key2988, 1), (key2909, 1), (key2599, 1), (key2588, 1), (key2930, 1), (key2767, 1), (key2967, 1), (key2888, 1), (key2767, -2), (key2888, -2), (key2844, -2), (key2588, -2), (key2967, -2), (key2844, -2), (key2599, -2), (key2588, -2), (key2930, -2), (key2767, -2), (key2967, -2), (key2888, -2)]

def rawRow9286 : Integer.Sparse Key := [(key2840, 1), (key2875, 1), (key2763, 1), (key2909, 1), (key2767, 1), (key2888, 1), (key2840, 1), (key2875, 1), (key2584, 1), (key2988, 1), (key2588, 1), (key2967, 1), (key2763, 1), (key2909, 1), (key2584, 1), (key2988, 1), (key2599, 1), (key2930, 1), (key2767, 1), (key2888, 1), (key2588, 1), (key2967, 1), (key2599, 1), (key2930, 1), (key2844, -2), (key2767, -2), (key2888, -2), (key2844, -2), (key2588, -2), (key2967, -2), (key2767, -2), (key2888, -2), (key2588, -2), (key2967, -2), (key2599, -2), (key2930, -2)]

def rawRow9287 : Integer.Sparse Key := [(key2875, 1), (key2840, 1), (key2909, 1), (key2763, 1), (key2888, 1), (key2767, 1), (key2875, 1), (key2840, 1), (key2988, 1), (key2584, 1), (key2967, 1), (key2588, 1), (key2909, 1), (key2763, 1), (key2988, 1), (key2584, 1), (key2930, 1), (key2599, 1), (key2888, 1), (key2767, 1), (key2967, 1), (key2588, 1), (key2930, 1), (key2599, 1), (key2844, -2), (key2888, -2), (key2767, -2), (key2844, -2), (key2967, -2), (key2588, -2), (key2888, -2), (key2767, -2), (key2967, -2), (key2588, -2), (key2930, -2), (key2599, -2)]

def rawRow9288 : Integer.Sparse Key := [(key2888, 1), (key2909, 1), (key2767, 1), (key2875, 1), (key2763, 1), (key2840, 1), (key2967, 1), (key2988, 1), (key2588, 1), (key2875, 1), (key2584, 1), (key2840, 1), (key2930, 1), (key2988, 1), (key2599, 1), (key2909, 1), (key2584, 1), (key2763, 1), (key2930, 1), (key2967, 1), (key2599, 1), (key2888, 1), (key2588, 1), (key2767, 1), (key2888, -2), (key2767, -2), (key2844, -2), (key2967, -2), (key2588, -2), (key2844, -2), (key2930, -2), (key2967, -2), (key2599, -2), (key2888, -2), (key2588, -2), (key2767, -2)]

def rawRow9289 : Integer.Sparse Key := [(key2909, 1), (key2888, 1), (key2875, 1), (key2767, 1), (key2840, 1), (key2763, 1), (key2988, 1), (key2967, 1), (key2875, 1), (key2588, 1), (key2840, 1), (key2584, 1), (key2988, 1), (key2930, 1), (key2909, 1), (key2599, 1), (key2763, 1), (key2584, 1), (key2967, 1), (key2930, 1), (key2888, 1), (key2599, 1), (key2767, 1), (key2588, 1), (key2888, -2), (key2844, -2), (key2767, -2), (key2967, -2), (key2844, -2), (key2588, -2), (key2967, -2), (key2930, -2), (key2888, -2), (key2599, -2), (key2767, -2), (key2588, -2)]

def rawRow9290 : Integer.Sparse Key := [(key2930, 1), (key2930, 1), (key2967, 1), (key2967, 1), (key2988, 1), (key2988, 1), (key2599, 1), (key2599, 1), (key2888, 1), (key2888, 1), (key2909, 1), (key2909, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2875, 1), (key2875, 1), (key2584, 1), (key2584, 1), (key2763, 1), (key2763, 1), (key2840, 1), (key2840, 1), (key2930, -2), (key2967, -2), (key2967, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2588, -2), (key2588, -2), (key2767, -2), (key2767, -2), (key2844, -2), (key2844, -2)]

def rawRow9291 : Integer.Sparse Key := [(key2967, 1), (key2988, 1), (key2930, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2763, 1), (key2840, 1), (key2584, 1), (key2840, 1), (key2584, 1), (key2763, 1), (key2967, -2), (key2930, -2), (key2967, -2), (key2888, -2), (key2599, -2), (key2888, -2), (key2767, -2), (key2844, -2), (key2588, -2), (key2844, -2), (key2588, -2), (key2767, -2)]

def rawRow9292 : Integer.Sparse Key := [(key2988, 1), (key2967, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2930, 1), (key2909, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2599, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2840, 1), (key2763, 1), (key2840, 1), (key2584, 1), (key2763, 1), (key2584, 1), (key2967, -2), (key2967, -2), (key2930, -2), (key2888, -2), (key2888, -2), (key2599, -2), (key2844, -2), (key2767, -2), (key2844, -2), (key2588, -2), (key2767, -2), (key2588, -2)]

def rawRow9293 : Integer.Sparse Key := [(key1249, -6), (key1602, -6), (key1602, -6), (key1803, -6), (key1249, 2), (key1249, 2), (key1262, 2), (key1524, 2), (key1524, 2), (key1762, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1803, 2), (key1645, 2), (key1803, 2)]

def rawRow9294 : Integer.Sparse Key := [(key1249, -6), (key1602, -6), (key1803, -6), (key1602, -6), (key1249, 2), (key1262, 2), (key1249, 2), (key1524, 2), (key1762, 2), (key1524, 2), (key1645, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1803, 2), (key1645, 2)]

def rawRow9295 : Integer.Sparse Key := [(key1249, -6), (key1803, -6), (key1602, -6), (key1602, -6), (key1262, 2), (key1249, 2), (key1249, 2), (key1762, 2), (key1524, 2), (key1524, 2), (key1803, 2), (key1803, 2), (key1645, 2), (key1645, 2), (key1602, 2), (key1602, 2)]

def rawRow9296 : Integer.Sparse Key := [(key1602, -6), (key1249, -6), (key1602, -6), (key1803, -6), (key1524, 2), (key1602, 2), (key1645, 2), (key1249, 2), (key1602, 2), (key1803, 2), (key1249, 2), (key1262, 2), (key1524, 2), (key1762, 2), (key1645, 2), (key1803, 2)]

def rawRow9297 : Integer.Sparse Key := [(key1602, -6), (key1249, -6), (key1803, -6), (key1602, -6), (key1524, 2), (key1645, 2), (key1602, 2), (key1249, 2), (key1803, 2), (key1602, 2), (key1262, 2), (key1249, 2), (key1762, 2), (key1524, 2), (key1803, 2), (key1645, 2)]

def rawRow9298 : Integer.Sparse Key := [(key1602, -6), (key1602, -6), (key1249, -6), (key1803, -6), (key1602, 2), (key1524, 2), (key1645, 2), (key1602, 2), (key1249, 2), (key1803, 2), (key1524, 2), (key1645, 2), (key1249, 2), (key1803, 2), (key1262, 2), (key1762, 2)]

def rawRow9299 : Integer.Sparse Key := [(key1602, -6), (key1602, -6), (key1803, -6), (key1249, -6), (key1602, 2), (key1645, 2), (key1524, 2), (key1602, 2), (key1803, 2), (key1249, 2), (key1645, 2), (key1524, 2), (key1803, 2), (key1249, 2), (key1762, 2), (key1262, 2)]

def rawRow9300 : Integer.Sparse Key := [(key1602, -6), (key1803, -6), (key1249, -6), (key1602, -6), (key1645, 2), (key1524, 2), (key1602, 2), (key1803, 2), (key1249, 2), (key1602, 2), (key1762, 2), (key1803, 2), (key1262, 2), (key1645, 2), (key1249, 2), (key1524, 2)]

def rawRow9301 : Integer.Sparse Key := [(key1602, -6), (key1803, -6), (key1602, -6), (key1249, -6), (key1645, 2), (key1602, 2), (key1524, 2), (key1803, 2), (key1602, 2), (key1249, 2), (key1803, 2), (key1762, 2), (key1645, 2), (key1262, 2), (key1524, 2), (key1249, 2)]

def rawRow9302 : Integer.Sparse Key := [(key1803, -6), (key1249, -6), (key1602, -6), (key1602, -6), (key1762, 2), (key1803, 2), (key1803, 2), (key1262, 2), (key1645, 2), (key1645, 2), (key1249, 2), (key1249, 2), (key1524, 2), (key1524, 2), (key1602, 2), (key1602, 2)]

def rawRow9303 : Integer.Sparse Key := [(key1803, -6), (key1602, -6), (key1249, -6), (key1602, -6), (key1803, 2), (key1762, 2), (key1803, 2), (key1645, 2), (key1262, 2), (key1645, 2), (key1524, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1249, 2), (key1524, 2)]

def rawRow9304 : Integer.Sparse Key := [(key1803, -6), (key1602, -6), (key1602, -6), (key1249, -6), (key1803, 2), (key1803, 2), (key1762, 2), (key1645, 2), (key1645, 2), (key1262, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1249, 2), (key1524, 2), (key1249, 2)]

def rawRow9305 : Integer.Sparse Key := [(key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, -6), (key2451, -6), (key2451, -6), (key2513, -6)]

def rawRow9306 : Integer.Sparse Key := [(key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2356, -6), (key2451, -6), (key2513, -6), (key2451, -6)]

def rawRow9307 : Integer.Sparse Key := [(key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2356, -6), (key2513, -6), (key2451, -6), (key2451, -6)]

def rawRow9308 : Integer.Sparse Key := [(key2448, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2451, -6), (key2356, -6), (key2451, -6), (key2513, -6)]

def rawRow9309 : Integer.Sparse Key := [(key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, -6), (key2356, -6), (key2513, -6), (key2451, -6)]

def rawRow9310 : Integer.Sparse Key := [(key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2451, -6), (key2451, -6), (key2356, -6), (key2513, -6)]

def rawRow9311 : Integer.Sparse Key := [(key2513, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2451, -6), (key2451, -6), (key2513, -6), (key2356, -6)]

def rawRow9312 : Integer.Sparse Key := [(key2451, 6), (key2513, 6), (key2448, 6), (key2451, 6), (key2451, -6), (key2513, -6), (key2356, -6), (key2451, -6)]

def rawRow9313 : Integer.Sparse Key := [(key2513, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2451, -6), (key2513, -6), (key2451, -6), (key2356, -6)]

def rawRow9314 : Integer.Sparse Key := [(key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2513, -6), (key2356, -6), (key2451, -6), (key2451, -6)]

def rawRow9315 : Integer.Sparse Key := [(key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2513, -6), (key2451, -6), (key2356, -6), (key2451, -6)]

def rawRow9316 : Integer.Sparse Key := [(key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, -6), (key2451, -6), (key2451, -6), (key2356, -6)]

def rawRow9317 : Integer.Sparse Key := [(key2354, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2514, -6), (key2514, -6), (key2514, -6), (key2559, -6)]

def rawRow9318 : Integer.Sparse Key := [(key2358, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2514, -6), (key2514, -6), (key2559, -6), (key2514, -6)]

def rawRow9319 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2514, -6), (key2559, -6), (key2514, -6), (key2514, -6)]

def rawRow9320 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2559, -6), (key2514, -6), (key2514, -6), (key2514, -6)]

def rawRow9321 : Integer.Sparse Key := [(key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2358, -6), (key2453, -6), (key2453, -6), (key2529, -6)]

def rawRow9322 : Integer.Sparse Key := [(key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2358, -6), (key2453, -6), (key2529, -6), (key2453, -6)]

def rawRow9323 : Integer.Sparse Key := [(key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2358, -6), (key2529, -6), (key2453, -6), (key2453, -6)]

def rawRow9324 : Integer.Sparse Key := [(key2449, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2453, -6), (key2358, -6), (key2453, -6), (key2529, -6)]

def rawRow9325 : Integer.Sparse Key := [(key2453, 6), (key2449, 6), (key2514, 6), (key2453, 6), (key2453, -6), (key2358, -6), (key2529, -6), (key2453, -6)]

def rawRow9326 : Integer.Sparse Key := [(key2449, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2453, -6), (key2453, -6), (key2358, -6), (key2529, -6)]

def rawRow9327 : Integer.Sparse Key := [(key2514, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2453, -6), (key2453, -6), (key2529, -6), (key2358, -6)]

def rawRow9328 : Integer.Sparse Key := [(key2453, 6), (key2514, 6), (key2449, 6), (key2453, 6), (key2453, -6), (key2529, -6), (key2358, -6), (key2453, -6)]

def rawRow9329 : Integer.Sparse Key := [(key2514, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2453, -6), (key2529, -6), (key2453, -6), (key2358, -6)]

def rawRow9330 : Integer.Sparse Key := [(key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2529, -6), (key2358, -6), (key2453, -6), (key2453, -6)]

def rawRow9331 : Integer.Sparse Key := [(key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2529, -6), (key2453, -6), (key2358, -6), (key2453, -6)]

def rawRow9332 : Integer.Sparse Key := [(key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2529, -6), (key2453, -6), (key2453, -6), (key2358, -6)]

def rawRow9333 : Integer.Sparse Key := [(key2006, -6), (key2007, -6), (key2007, -6), (key2007, -6), (key2299, 2), (key2300, 2), (key2300, 2), (key2299, 2), (key2300, 2), (key2299, 2), (key2340, 2), (key2300, 2), (key2340, 2), (key2300, 2), (key2300, 2), (key2340, 2)]

def rawRow9334 : Integer.Sparse Key := [(key2007, -6), (key2006, -6), (key2007, -6), (key2007, -6), (key2300, 2), (key2299, 2), (key2300, 2), (key2300, 2), (key2299, 2), (key2340, 2), (key2299, 2), (key2340, 2), (key2300, 2), (key2300, 2), (key2340, 2), (key2300, 2)]

def rawRow9335 : Integer.Sparse Key := [(key2007, -6), (key2007, -6), (key2006, -6), (key2007, -6), (key2300, 2), (key2300, 2), (key2299, 2), (key2340, 2), (key2340, 2), (key2300, 2), (key2300, 2), (key2299, 2), (key2299, 2), (key2340, 2), (key2300, 2), (key2300, 2)]

def rawRow9336 : Integer.Sparse Key := [(key2007, -6), (key2007, -6), (key2007, -6), (key2006, -6), (key2340, 2), (key2340, 2), (key2340, 2), (key2300, 2), (key2300, 2), (key2300, 2), (key2300, 2), (key2300, 2), (key2300, 2), (key2299, 2), (key2299, 2), (key2299, 2)]

def rawRow9337 : Integer.Sparse Key := [(key2299, -6), (key2300, -6), (key2300, -6), (key2313, -6), (key2006, 2), (key2007, 2), (key2007, 2), (key2299, 2), (key2300, 2), (key2299, 2), (key2340, 2), (key2300, 2), (key2340, 2), (key2313, 2), (key2313, 2), (key2349, 2)]

def rawRow9338 : Integer.Sparse Key := [(key2300, -6), (key2299, -6), (key2300, -6), (key2313, -6), (key2007, 2), (key2006, 2), (key2007, 2), (key2300, 2), (key2299, 2), (key2340, 2), (key2299, 2), (key2340, 2), (key2300, 2), (key2313, 2), (key2349, 2), (key2313, 2)]

def rawRow9339 : Integer.Sparse Key := [(key2300, -6), (key2300, -6), (key2299, -6), (key2313, -6), (key2007, 2), (key2007, 2), (key2006, 2), (key2340, 2), (key2340, 2), (key2300, 2), (key2300, 2), (key2299, 2), (key2299, 2), (key2349, 2), (key2313, 2), (key2313, 2)]

def rawRow9340 : Integer.Sparse Key := [(key2299, -6), (key2300, -6), (key2313, -6), (key2300, -6), (key2299, 2), (key2300, 2), (key2313, 2), (key2006, 2), (key2007, 2), (key2299, 2), (key2340, 2), (key2313, 2), (key2349, 2), (key2007, 2), (key2300, 2), (key2340, 2)]

def rawRow9341 : Integer.Sparse Key := [(key2300, -6), (key2299, -6), (key2313, -6), (key2300, -6), (key2300, 2), (key2299, 2), (key2313, 2), (key2007, 2), (key2006, 2), (key2340, 2), (key2299, 2), (key2349, 2), (key2313, 2), (key2007, 2), (key2340, 2), (key2300, 2)]

def rawRow9342 : Integer.Sparse Key := [(key2299, -6), (key2313, -6), (key2300, -6), (key2300, -6), (key2299, 2), (key2313, 2), (key2300, 2), (key2299, 2), (key2313, 2), (key2006, 2), (key2349, 2), (key2007, 2), (key2340, 2), (key2300, 2), (key2007, 2), (key2340, 2)]

def rawRow9343 : Integer.Sparse Key := [(key2313, -6), (key2299, -6), (key2300, -6), (key2300, -6), (key2313, 2), (key2299, 2), (key2300, 2), (key2313, 2), (key2299, 2), (key2349, 2), (key2006, 2), (key2340, 2), (key2007, 2), (key2300, 2), (key2340, 2), (key2007, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9344 : Integer.Sparse Key := [(key2300, -6), (key2313, -6), (key2299, -6), (key2300, -6), (key2300, 2), (key2313, 2), (key2299, 2), (key2340, 2), (key2349, 2), (key2007, 2), (key2313, 2), (key2006, 2), (key2299, 2), (key2340, 2), (key2007, 2), (key2300, 2)]

def rawRow9345 : Integer.Sparse Key := [(key2313, -6), (key2300, -6), (key2299, -6), (key2300, -6), (key2313, 2), (key2300, 2), (key2299, 2), (key2349, 2), (key2340, 2), (key2313, 2), (key2007, 2), (key2299, 2), (key2006, 2), (key2340, 2), (key2300, 2), (key2007, 2)]

def rawRow9346 : Integer.Sparse Key := [(key2300, -6), (key2300, -6), (key2313, -6), (key2299, -6), (key2340, 2), (key2340, 2), (key2349, 2), (key2007, 2), (key2007, 2), (key2300, 2), (key2300, 2), (key2313, 2), (key2313, 2), (key2006, 2), (key2299, 2), (key2299, 2)]

def rawRow9347 : Integer.Sparse Key := [(key2300, -6), (key2313, -6), (key2300, -6), (key2299, -6), (key2340, 2), (key2349, 2), (key2340, 2), (key2300, 2), (key2313, 2), (key2007, 2), (key2313, 2), (key2007, 2), (key2300, 2), (key2299, 2), (key2006, 2), (key2299, 2)]

def rawRow9348 : Integer.Sparse Key := [(key2313, -6), (key2300, -6), (key2300, -6), (key2299, -6), (key2349, 2), (key2340, 2), (key2340, 2), (key2313, 2), (key2300, 2), (key2313, 2), (key2007, 2), (key2300, 2), (key2007, 2), (key2299, 2), (key2299, 2), (key2006, 2)]

def rawRow9349 : Integer.Sparse Key := [(key972, 6), (key977, 6), (key977, 6), (key977, 6), (key1162, -6), (key1162, -6), (key1162, -6), (key1218, -6)]

def rawRow9350 : Integer.Sparse Key := [(key977, 6), (key972, 6), (key977, 6), (key977, 6), (key1162, -6), (key1162, -6), (key1218, -6), (key1162, -6)]

def rawRow9351 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key972, 6), (key977, 6), (key1162, -6), (key1218, -6), (key1162, -6), (key1162, -6)]

def rawRow9352 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key977, 6), (key972, 6), (key1218, -6), (key1162, -6), (key1162, -6), (key1162, -6)]

def rawRow9353 : Integer.Sparse Key := [(key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key977, -6), (key1091, -6), (key1091, -6), (key1181, -6)]

def rawRow9354 : Integer.Sparse Key := [(key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key977, -6), (key1091, -6), (key1181, -6), (key1091, -6)]

def rawRow9355 : Integer.Sparse Key := [(key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key977, -6), (key1181, -6), (key1091, -6), (key1091, -6)]

def rawRow9356 : Integer.Sparse Key := [(key1086, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1091, -6), (key977, -6), (key1091, -6), (key1181, -6)]

def rawRow9357 : Integer.Sparse Key := [(key1091, 6), (key1086, 6), (key1162, 6), (key1091, 6), (key1091, -6), (key977, -6), (key1181, -6), (key1091, -6)]

def rawRow9358 : Integer.Sparse Key := [(key1086, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1091, -6), (key1091, -6), (key977, -6), (key1181, -6)]

def rawRow9359 : Integer.Sparse Key := [(key1162, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1091, -6), (key1091, -6), (key1181, -6), (key977, -6)]

def rawRow9360 : Integer.Sparse Key := [(key1091, 6), (key1162, 6), (key1086, 6), (key1091, 6), (key1091, -6), (key1181, -6), (key977, -6), (key1091, -6)]

def rawRow9361 : Integer.Sparse Key := [(key1162, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1091, -6), (key1181, -6), (key1091, -6), (key977, -6)]

def rawRow9362 : Integer.Sparse Key := [(key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1181, -6), (key977, -6), (key1091, -6), (key1091, -6)]

def rawRow9363 : Integer.Sparse Key := [(key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1181, -6), (key1091, -6), (key977, -6), (key1091, -6)]

def rawRow9364 : Integer.Sparse Key := [(key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1181, -6), (key1091, -6), (key1091, -6), (key977, -6)]

def rawRow9365 : Integer.Sparse Key := [(key2353, -6), (key2356, -6), (key2356, -6), (key2356, -6), (key2448, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2513, 2)]

def rawRow9366 : Integer.Sparse Key := [(key2356, -6), (key2353, -6), (key2356, -6), (key2356, -6), (key2451, 2), (key2448, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2513, 2), (key2451, 2)]

def rawRow9367 : Integer.Sparse Key := [(key2356, -6), (key2356, -6), (key2353, -6), (key2356, -6), (key2451, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2451, 2)]

def rawRow9368 : Integer.Sparse Key := [(key2356, -6), (key2356, -6), (key2356, -6), (key2353, -6), (key2513, 2), (key2513, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2448, 2), (key2448, 2)]

def rawRow9369 : Integer.Sparse Key := [(key2448, -6), (key2451, -6), (key2451, -6), (key2513, -6), (key2353, 2), (key2356, 2), (key2356, 2), (key2448, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2513, 2), (key2527, 2), (key2527, 2), (key2558, 2)]

def rawRow9370 : Integer.Sparse Key := [(key2451, -6), (key2448, -6), (key2451, -6), (key2513, -6), (key2356, 2), (key2353, 2), (key2356, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2448, 2), (key2513, 2), (key2451, 2), (key2527, 2), (key2558, 2), (key2527, 2)]

def rawRow9371 : Integer.Sparse Key := [(key2451, -6), (key2451, -6), (key2448, -6), (key2513, -6), (key2356, 2), (key2356, 2), (key2353, 2), (key2513, 2), (key2513, 2), (key2451, 2), (key2451, 2), (key2448, 2), (key2448, 2), (key2558, 2), (key2527, 2), (key2527, 2)]

def rawRow9372 : Integer.Sparse Key := [(key2448, -6), (key2451, -6), (key2513, -6), (key2451, -6), (key2448, 2), (key2451, 2), (key2513, 2), (key2353, 2), (key2356, 2), (key2448, 2), (key2513, 2), (key2527, 2), (key2558, 2), (key2356, 2), (key2451, 2), (key2513, 2)]

def rawRow9373 : Integer.Sparse Key := [(key2451, -6), (key2448, -6), (key2513, -6), (key2451, -6), (key2451, 2), (key2448, 2), (key2513, 2), (key2356, 2), (key2353, 2), (key2513, 2), (key2448, 2), (key2558, 2), (key2527, 2), (key2356, 2), (key2513, 2), (key2451, 2)]

def rawRow9374 : Integer.Sparse Key := [(key2448, -6), (key2513, -6), (key2451, -6), (key2451, -6), (key2448, 2), (key2513, 2), (key2451, 2), (key2448, 2), (key2513, 2), (key2353, 2), (key2558, 2), (key2356, 2), (key2513, 2), (key2451, 2), (key2356, 2), (key2513, 2)]

def rawRow9375 : Integer.Sparse Key := [(key2513, -6), (key2448, -6), (key2451, -6), (key2451, -6), (key2513, 2), (key2448, 2), (key2451, 2), (key2513, 2), (key2448, 2), (key2558, 2), (key2353, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2513, 2), (key2356, 2)]

def rawRow9376 : Integer.Sparse Key := [(key2451, -6), (key2513, -6), (key2448, -6), (key2451, -6), (key2451, 2), (key2513, 2), (key2448, 2), (key2527, 2), (key2558, 2), (key2356, 2), (key2513, 2), (key2353, 2), (key2448, 2), (key2513, 2), (key2356, 2), (key2451, 2)]

def rawRow9377 : Integer.Sparse Key := [(key2513, -6), (key2451, -6), (key2448, -6), (key2451, -6), (key2513, 2), (key2451, 2), (key2448, 2), (key2558, 2), (key2527, 2), (key2513, 2), (key2356, 2), (key2448, 2), (key2353, 2), (key2513, 2), (key2451, 2), (key2356, 2)]

def rawRow9378 : Integer.Sparse Key := [(key2451, -6), (key2451, -6), (key2513, -6), (key2448, -6), (key2527, 2), (key2527, 2), (key2558, 2), (key2356, 2), (key2356, 2), (key2451, 2), (key2451, 2), (key2513, 2), (key2513, 2), (key2353, 2), (key2448, 2), (key2448, 2)]

def rawRow9379 : Integer.Sparse Key := [(key2451, -6), (key2513, -6), (key2451, -6), (key2448, -6), (key2527, 2), (key2558, 2), (key2527, 2), (key2451, 2), (key2513, 2), (key2356, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2448, 2), (key2353, 2), (key2448, 2)]

def rawRow9380 : Integer.Sparse Key := [(key2513, -6), (key2451, -6), (key2451, -6), (key2448, -6), (key2558, 2), (key2527, 2), (key2527, 2), (key2513, 2), (key2451, 2), (key2513, 2), (key2356, 2), (key2451, 2), (key2356, 2), (key2448, 2), (key2448, 2), (key2353, 2)]

def rawRow9381 : Integer.Sparse Key := [(key2405, 2), (key2405, 2), (key2405, 2), (key2471, 2), (key2471, 2), (key2471, 2), (key2479, 2), (key2479, 2), (key2479, 2), (key2479, 2), (key2479, 2), (key2479, 2), (key2436, -2), (key2436, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2518, -2), (key2518, -2)]

def rawRow9382 : Integer.Sparse Key := [(key2471, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2405, 2), (key2471, 2), (key2471, 2), (key2479, 2), (key2479, 2), (key2502, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2502, -2)]

def rawRow9383 : Integer.Sparse Key := [(key2479, 2), (key2471, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2471, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2405, 2), (key2471, 2), (key2502, -2), (key2518, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2502, -2)]

def rawRow9384 : Integer.Sparse Key := [(key2479, 2), (key2479, 2), (key2471, 2), (key2479, 2), (key2479, 2), (key2405, 2), (key2479, 2), (key2471, 2), (key2479, 2), (key2405, 2), (key2471, 2), (key2405, 2), (key2518, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2436, -2)]

def rawRow9385 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 6), (key1102, 6), (key1102, 6)]

def rawRow9386 : Integer.Sparse Key := [(key989, -24), (key1102, 6), (key1024, 6), (key1102, 6), (key1102, 6)]

def rawRow9387 : Integer.Sparse Key := [(key989, -24), (key1102, 6), (key1102, 6), (key1024, 6), (key1102, 6)]

def rawRow9388 : Integer.Sparse Key := [(key989, -24), (key1102, 6), (key1102, 6), (key1102, 6), (key1024, 6)]

def rawRow9389 : Integer.Sparse Key := [(key995, -6), (key995, -6), (key995, -6), (key1011, -6), (key1030, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1119, 2)]

def rawRow9390 : Integer.Sparse Key := [(key995, -6), (key995, -6), (key1011, -6), (key995, -6), (key1108, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1108, 2)]

def rawRow9391 : Integer.Sparse Key := [(key995, -6), (key1011, -6), (key995, -6), (key995, -6), (key1108, 2), (key1119, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1030, 2), (key1108, 2)]

def rawRow9392 : Integer.Sparse Key := [(key1011, -6), (key995, -6), (key995, -6), (key995, -6), (key1119, 2), (key1108, 2), (key1108, 2), (key1119, 2), (key1108, 2), (key1119, 2), (key1030, 2), (key1108, 2), (key1030, 2), (key1108, 2), (key1108, 2), (key1030, 2)]

def rawRow9393 : Integer.Sparse Key := [(key2661, -6), (key2696, -6), (key2696, -6), (key2696, -6), (key2776, 2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2), (key2849, 2)]

def rawRow9394 : Integer.Sparse Key := [(key2696, -6), (key2661, -6), (key2696, -6), (key2696, -6), (key2799, 2), (key2849, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2849, 2), (key2776, 2), (key2776, 2), (key2799, 2), (key2799, 2), (key2849, 2), (key2849, 2)]

def rawRow9395 : Integer.Sparse Key := [(key2696, -6), (key2696, -6), (key2661, -6), (key2696, -6), (key2849, 2), (key2799, 2), (key2849, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2776, 2), (key2799, 2)]

def rawRow9396 : Integer.Sparse Key := [(key2696, -6), (key2696, -6), (key2696, -6), (key2661, -6), (key2849, 2), (key2849, 2), (key2799, 2), (key2849, 2), (key2849, 2), (key2776, 2), (key2849, 2), (key2799, 2), (key2849, 2), (key2776, 2), (key2799, 2), (key2776, 2)]

def rawRow9397 : Integer.Sparse Key := [(key2372, -6), (key2372, -6), (key2372, -6), (key2385, -6), (key2400, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2475, 2), (key2475, 2)]

def rawRow9398 : Integer.Sparse Key := [(key2372, -6), (key2372, -6), (key2385, -6), (key2372, -6), (key2466, 2), (key2466, 2), (key2475, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2466, 2)]

def rawRow9399 : Integer.Sparse Key := [(key2372, -6), (key2385, -6), (key2372, -6), (key2372, -6), (key2466, 2), (key2475, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2400, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2400, 2), (key2466, 2)]

def rawRow9400 : Integer.Sparse Key := [(key2385, -6), (key2372, -6), (key2372, -6), (key2372, -6), (key2475, 2), (key2466, 2), (key2466, 2), (key2475, 2), (key2466, 2), (key2475, 2), (key2400, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2400, 2)]

def rawRow9401 : Integer.Sparse Key := [(key2400, -6), (key2400, -6), (key2400, -6), (key2432, -6), (key2372, 2), (key2372, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2498, 2)]

def rawRow9402 : Integer.Sparse Key := [(key2400, -6), (key2400, -6), (key2432, -6), (key2400, -6), (key2466, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2466, 2)]

def rawRow9403 : Integer.Sparse Key := [(key2400, -6), (key2432, -6), (key2400, -6), (key2400, -6), (key2466, 2), (key2498, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2)]

def rawRow9404 : Integer.Sparse Key := [(key2432, -6), (key2400, -6), (key2400, -6), (key2400, -6), (key2498, 2), (key2466, 2), (key2466, 2), (key2498, 2), (key2466, 2), (key2498, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2372, 2)]

def rawRow9405 : Integer.Sparse Key := [(key2665, -2), (key2665, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2780, -2), (key2780, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2789, -2), (key2789, -2), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1)]

def rawRow9406 : Integer.Sparse Key := [(key2780, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1)]

def rawRow9407 : Integer.Sparse Key := [(key2780, -2), (key2789, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2665, -2), (key2780, -2), (key2853, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2803, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2700, 1), (key2853, 1), (key2700, 1), (key2803, 1)]

def rawRow9408 : Integer.Sparse Key := [(key2789, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2665, -2), (key2855, 1), (key2853, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2803, 1), (key2855, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2700, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2700, 1), (key2803, 1), (key2700, 1), (key2853, 1), (key2803, 1), (key2853, 1), (key2700, 1), (key2803, 1), (key2700, 1)]

def rawRow9409 : Integer.Sparse Key := [(key2610, -2), (key2610, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2803, -2), (key2803, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2824, -2), (key2824, -2), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1)]

def rawRow9410 : Integer.Sparse Key := [(key2803, -2), (key2803, -2), (key2824, -2), (key2610, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2824, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1)]

def rawRow9411 : Integer.Sparse Key := [(key2803, -2), (key2824, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2610, -2), (key2824, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2610, -2), (key2803, -2), (key2853, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2780, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2626, 1), (key2853, 1), (key2626, 1), (key2780, 1)]

def rawRow9412 : Integer.Sparse Key := [(key2824, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2803, -2), (key2824, -2), (key2610, -2), (key2803, -2), (key2610, -2), (key2803, -2), (key2803, -2), (key2610, -2), (key2865, 1), (key2853, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2780, 1), (key2865, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2626, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2626, 1), (key2780, 1), (key2626, 1), (key2853, 1), (key2780, 1), (key2853, 1), (key2626, 1), (key2780, 1), (key2626, 1)]

def rawRow9413 : Integer.Sparse Key := [(key2368, -24), (key2760, 6), (key2837, 6), (key2837, 6), (key2837, 6)]

def rawRow9414 : Integer.Sparse Key := [(key2368, -24), (key2837, 6), (key2760, 6), (key2837, 6), (key2837, 6)]

def rawRow9415 : Integer.Sparse Key := [(key2368, -24), (key2837, 6), (key2837, 6), (key2760, 6), (key2837, 6)]

def rawRow9416 : Integer.Sparse Key := [(key2368, -24), (key2837, 6), (key2837, 6), (key2837, 6), (key2760, 6)]

def rawRow9417 : Integer.Sparse Key := [(key2396, -24), (key2581, 6), (key2837, 6), (key2837, 6), (key2837, 6)]

def rawRow9418 : Integer.Sparse Key := [(key2396, -24), (key2837, 6), (key2581, 6), (key2837, 6), (key2837, 6)]

def rawRow9419 : Integer.Sparse Key := [(key2396, -24), (key2837, 6), (key2837, 6), (key2581, 6), (key2837, 6)]

def rawRow9420 : Integer.Sparse Key := [(key2396, -24), (key2837, 6), (key2837, 6), (key2837, 6), (key2581, 6)]

def rawRow9421 : Integer.Sparse Key := [(key2610, -2), (key2610, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2626, -2), (key2626, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2635, -2), (key2635, -2), (key2665, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2789, 2)]

def rawRow9422 : Integer.Sparse Key := [(key2626, -2), (key2626, -2), (key2635, -2), (key2610, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2635, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2780, 2)]

def rawRow9423 : Integer.Sparse Key := [(key2626, -2), (key2635, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2610, -2), (key2635, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2610, -2), (key2626, -2), (key2780, 2), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2780, 2)]

def rawRow9424 : Integer.Sparse Key := [(key2635, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2626, -2), (key2635, -2), (key2610, -2), (key2626, -2), (key2610, -2), (key2626, -2), (key2626, -2), (key2610, -2), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2665, 2)]

def rawRow9425 : Integer.Sparse Key := [(key2665, -2), (key2665, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2700, -2), (key2700, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2721, -2), (key2721, -2), (key2610, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2824, 2)]

def rawRow9426 : Integer.Sparse Key := [(key2700, -2), (key2700, -2), (key2721, -2), (key2665, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2721, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2803, 2)]

def rawRow9427 : Integer.Sparse Key := [(key2700, -2), (key2721, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2665, -2), (key2721, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2665, -2), (key2700, -2), (key2803, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2803, 2)]

def rawRow9428 : Integer.Sparse Key := [(key2721, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2700, -2), (key2721, -2), (key2665, -2), (key2700, -2), (key2665, -2), (key2700, -2), (key2700, -2), (key2665, -2), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2610, 2)]

def rawRow9429 : Integer.Sparse Key := [(key1388, -2), (key1388, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1543, -2), (key1543, -2), (key1543, -2), (key1543, -2), (key1553, -2), (key1553, -2), (key1553, -2), (key1421, 1), (key1421, 1), (key1421, 1), (key1421, 1), (key1421, 1), (key1421, 1), (key1570, 1), (key1570, 1), (key1570, 1), (key1570, 1), (key1570, 1), (key1570, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1621, 1), (key1621, 1), (key1621, 1), (key1621, 1), (key1621, 1), (key1621, 1)]

def rawRow9430 : Integer.Sparse Key := [(key1543, -2), (key1543, -2), (key1553, -2), (key1388, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1553, -2), (key1553, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1570, 1), (key1570, 1), (key1619, 1), (key1619, 1), (key1621, 1), (key1621, 1), (key1421, 1), (key1421, 1), (key1619, 1), (key1619, 1), (key1621, 1), (key1621, 1), (key1421, 1), (key1421, 1), (key1570, 1), (key1570, 1), (key1621, 1), (key1621, 1), (key1421, 1), (key1421, 1), (key1570, 1), (key1570, 1), (key1619, 1), (key1619, 1)]

def rawRow9431 : Integer.Sparse Key := [(key1543, -2), (key1553, -2), (key1543, -2), (key1543, -2), (key1553, -2), (key1388, -2), (key1553, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1388, -2), (key1543, -2), (key1619, 1), (key1621, 1), (key1570, 1), (key1621, 1), (key1570, 1), (key1619, 1), (key1619, 1), (key1621, 1), (key1421, 1), (key1621, 1), (key1421, 1), (key1619, 1), (key1570, 1), (key1621, 1), (key1421, 1), (key1621, 1), (key1421, 1), (key1570, 1), (key1570, 1), (key1619, 1), (key1421, 1), (key1619, 1), (key1421, 1), (key1570, 1)]

def rawRow9432 : Integer.Sparse Key := [(key1553, -2), (key1543, -2), (key1543, -2), (key1553, -2), (key1543, -2), (key1553, -2), (key1388, -2), (key1543, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1388, -2), (key1621, 1), (key1619, 1), (key1621, 1), (key1570, 1), (key1619, 1), (key1570, 1), (key1621, 1), (key1619, 1), (key1621, 1), (key1421, 1), (key1619, 1), (key1421, 1), (key1621, 1), (key1570, 1), (key1621, 1), (key1421, 1), (key1570, 1), (key1421, 1), (key1619, 1), (key1570, 1), (key1619, 1), (key1421, 1), (key1570, 1), (key1421, 1)]

def rawRow9433 : Integer.Sparse Key := [(key1293, -2), (key1293, -2), (key1293, -2), (key1570, -2), (key1570, -2), (key1570, -2), (key1570, -2), (key1570, -2), (key1570, -2), (key1590, -2), (key1590, -2), (key1590, -2), (key1313, 1), (key1313, 1), (key1313, 1), (key1313, 1), (key1313, 1), (key1313, 1), (key1543, 1), (key1543, 1), (key1543, 1), (key1543, 1), (key1543, 1), (key1543, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1619, 1), (key1630, 1), (key1630, 1), (key1630, 1), (key1630, 1), (key1630, 1), (key1630, 1)]

def rawRow9434 : Integer.Sparse Key := [(key1570, -2), (key1570, -2), (key1590, -2), (key1293, -2), (key1293, -2), (key1570, -2), (key1570, -2), (key1590, -2), (key1590, -2), (key1293, -2), (key1570, -2), (key1570, -2), (key1543, 1), (key1543, 1), (key1619, 1), (key1619, 1), (key1630, 1), (key1630, 1), (key1313, 1), (key1313, 1), (key1619, 1), (key1619, 1), (key1630, 1), (key1630, 1), (key1313, 1), (key1313, 1), (key1543, 1), (key1543, 1), (key1630, 1), (key1630, 1), (key1313, 1), (key1313, 1), (key1543, 1), (key1543, 1), (key1619, 1), (key1619, 1)]

def rawRow9435 : Integer.Sparse Key := [(key1570, -2), (key1590, -2), (key1570, -2), (key1570, -2), (key1590, -2), (key1293, -2), (key1590, -2), (key1293, -2), (key1570, -2), (key1570, -2), (key1293, -2), (key1570, -2), (key1619, 1), (key1630, 1), (key1543, 1), (key1630, 1), (key1543, 1), (key1619, 1), (key1619, 1), (key1630, 1), (key1313, 1), (key1630, 1), (key1313, 1), (key1619, 1), (key1543, 1), (key1630, 1), (key1313, 1), (key1630, 1), (key1313, 1), (key1543, 1), (key1543, 1), (key1619, 1), (key1313, 1), (key1619, 1), (key1313, 1), (key1543, 1)]

def rawRow9436 : Integer.Sparse Key := [(key1590, -2), (key1570, -2), (key1570, -2), (key1590, -2), (key1570, -2), (key1590, -2), (key1293, -2), (key1570, -2), (key1293, -2), (key1570, -2), (key1570, -2), (key1293, -2), (key1630, 1), (key1619, 1), (key1630, 1), (key1543, 1), (key1619, 1), (key1543, 1), (key1630, 1), (key1619, 1), (key1630, 1), (key1313, 1), (key1619, 1), (key1313, 1), (key1630, 1), (key1543, 1), (key1630, 1), (key1313, 1), (key1543, 1), (key1313, 1), (key1619, 1), (key1543, 1), (key1619, 1), (key1313, 1), (key1543, 1), (key1313, 1)]

def rawRow9437 : Integer.Sparse Key := [(key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2855, 1), (key2721, -2), (key2721, -2), (key2721, -2), (key2824, -2), (key2824, -2), (key2824, -2), (key2865, -2), (key2865, -2), (key2865, -2), (key2865, -2), (key2865, -2), (key2865, -2)]

def rawRow9438 : Integer.Sparse Key := [(key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2855, 1), (key2855, 1), (key2700, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2824, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2721, -2), (key2824, -2), (key2824, -2), (key2865, -2), (key2865, -2)]

def rawRow9439 : Integer.Sparse Key := [(key2853, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2803, 1), (key2855, 1), (key2700, 1), (key2855, 1), (key2700, 1), (key2803, 1), (key2803, 1), (key2853, 1), (key2700, 1), (key2853, 1), (key2700, 1), (key2803, 1), (key2865, -2), (key2824, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2824, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2721, -2), (key2824, -2)]

def rawRow9440 : Integer.Sparse Key := [(key2855, 1), (key2853, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2803, 1), (key2855, 1), (key2853, 1), (key2855, 1), (key2700, 1), (key2853, 1), (key2700, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2700, 1), (key2803, 1), (key2700, 1), (key2853, 1), (key2803, 1), (key2853, 1), (key2700, 1), (key2803, 1), (key2700, 1), (key2865, -2), (key2865, -2), (key2824, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2824, -2), (key2865, -2), (key2721, -2), (key2824, -2), (key2721, -2)]

def rawRow9441 : Integer.Sparse Key := [(key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2865, 1), (key2635, -2), (key2635, -2), (key2635, -2), (key2789, -2), (key2789, -2), (key2789, -2), (key2855, -2), (key2855, -2), (key2855, -2), (key2855, -2), (key2855, -2), (key2855, -2)]

def rawRow9442 : Integer.Sparse Key := [(key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2865, 1), (key2865, 1), (key2626, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2789, -2), (key2855, -2), (key2855, -2), (key2635, -2), (key2855, -2), (key2855, -2), (key2635, -2), (key2635, -2), (key2789, -2), (key2789, -2), (key2855, -2), (key2855, -2)]

def rawRow9443 : Integer.Sparse Key := [(key2853, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2780, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2780, 1), (key2780, 1), (key2853, 1), (key2626, 1), (key2853, 1), (key2626, 1), (key2780, 1), (key2855, -2), (key2789, -2), (key2855, -2), (key2855, -2), (key2635, -2), (key2855, -2), (key2789, -2), (key2855, -2), (key2635, -2), (key2855, -2), (key2635, -2), (key2789, -2)]

def rawRow9444 : Integer.Sparse Key := [(key2865, 1), (key2853, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2780, 1), (key2865, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2626, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2626, 1), (key2780, 1), (key2626, 1), (key2853, 1), (key2780, 1), (key2853, 1), (key2626, 1), (key2780, 1), (key2626, 1), (key2855, -2), (key2855, -2), (key2789, -2), (key2855, -2), (key2855, -2), (key2635, -2), (key2855, -2), (key2789, -2), (key2855, -2), (key2635, -2), (key2789, -2), (key2635, -2)]

def rawRow9445 : Integer.Sparse Key := [(key1382, -6), (key1537, -6), (key1537, -6), (key1537, -6), (key1415, 2), (key1415, 2), (key1415, 2), (key1564, 2), (key1564, 2), (key1564, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2)]

def rawRow9446 : Integer.Sparse Key := [(key1537, -6), (key1382, -6), (key1537, -6), (key1537, -6), (key1564, 2), (key1613, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1613, 2), (key1415, 2), (key1415, 2), (key1564, 2), (key1564, 2), (key1613, 2), (key1613, 2)]

def rawRow9447 : Integer.Sparse Key := [(key1537, -6), (key1537, -6), (key1382, -6), (key1537, -6), (key1613, 2), (key1564, 2), (key1613, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1564, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1415, 2), (key1564, 2)]

def rawRow9448 : Integer.Sparse Key := [(key1537, -6), (key1537, -6), (key1537, -6), (key1382, -6), (key1613, 2), (key1613, 2), (key1564, 2), (key1613, 2), (key1613, 2), (key1415, 2), (key1613, 2), (key1564, 2), (key1613, 2), (key1415, 2), (key1564, 2), (key1415, 2)]

def rawRow9449 : Integer.Sparse Key := [(key1287, -6), (key1564, -6), (key1564, -6), (key1564, -6), (key1307, 2), (key1307, 2), (key1307, 2), (key1537, 2), (key1537, 2), (key1537, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2), (key1613, 2)]

def rawRow9450 : Integer.Sparse Key := [(key1564, -6), (key1287, -6), (key1564, -6), (key1564, -6), (key1537, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1307, 2), (key1537, 2), (key1537, 2), (key1613, 2), (key1613, 2)]

def rawRow9451 : Integer.Sparse Key := [(key1564, -6), (key1564, -6), (key1287, -6), (key1564, -6), (key1613, 2), (key1537, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1537, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1307, 2), (key1537, 2)]

def rawRow9452 : Integer.Sparse Key := [(key1564, -6), (key1564, -6), (key1564, -6), (key1287, -6), (key1613, 2), (key1613, 2), (key1537, 2), (key1613, 2), (key1613, 2), (key1307, 2), (key1613, 2), (key1537, 2), (key1613, 2), (key1307, 2), (key1537, 2), (key1307, 2)]

def rawRow9453 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2369, 6), (key2384, 6), (key2431, -6), (key2497, -6), (key2497, -6), (key2497, -6)]

def rawRow9454 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2384, 6), (key2369, 6), (key2497, -6), (key2431, -6), (key2497, -6), (key2497, -6)]

def rawRow9455 : Integer.Sparse Key := [(key2369, 6), (key2384, 6), (key2369, 6), (key2369, 6), (key2497, -6), (key2497, -6), (key2431, -6), (key2497, -6)]

def rawRow9456 : Integer.Sparse Key := [(key2384, 6), (key2369, 6), (key2369, 6), (key2369, 6), (key2497, -6), (key2497, -6), (key2497, -6), (key2431, -6)]

def rawRow9457 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2397, 6), (key2431, 6), (key2384, -6), (key2474, -6), (key2474, -6), (key2474, -6)]

def rawRow9458 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2431, 6), (key2397, 6), (key2474, -6), (key2384, -6), (key2474, -6), (key2474, -6)]

def rawRow9459 : Integer.Sparse Key := [(key2397, 6), (key2431, 6), (key2397, 6), (key2397, 6), (key2474, -6), (key2474, -6), (key2384, -6), (key2474, -6)]

def rawRow9460 : Integer.Sparse Key := [(key2431, 6), (key2397, 6), (key2397, 6), (key2397, 6), (key2474, -6), (key2474, -6), (key2474, -6), (key2384, -6)]

def rawRow9461 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2372, 6), (key2385, 6), (key2432, -6), (key2498, -6), (key2498, -6), (key2498, -6)]

def rawRow9462 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2385, 6), (key2372, 6), (key2498, -6), (key2432, -6), (key2498, -6), (key2498, -6)]

def rawRow9463 : Integer.Sparse Key := [(key2372, 6), (key2385, 6), (key2372, 6), (key2372, 6), (key2498, -6), (key2498, -6), (key2432, -6), (key2498, -6)]

def rawRow9464 : Integer.Sparse Key := [(key2385, 6), (key2372, 6), (key2372, 6), (key2372, 6), (key2498, -6), (key2498, -6), (key2498, -6), (key2432, -6)]

def rawRow9465 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2400, 6), (key2432, 6), (key2385, -6), (key2475, -6), (key2475, -6), (key2475, -6)]

def rawRow9466 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2432, 6), (key2400, 6), (key2475, -6), (key2385, -6), (key2475, -6), (key2475, -6)]

def rawRow9467 : Integer.Sparse Key := [(key2400, 6), (key2432, 6), (key2400, 6), (key2400, 6), (key2475, -6), (key2475, -6), (key2385, -6), (key2475, -6)]

def rawRow9468 : Integer.Sparse Key := [(key2432, 6), (key2400, 6), (key2400, 6), (key2400, 6), (key2475, -6), (key2475, -6), (key2475, -6), (key2385, -6)]

def rawRow9469 : Integer.Sparse Key := [(key2098, -6), (key2098, -6), (key2098, -6), (key2099, -6), (key2203, 2), (key2203, 2), (key2203, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2318, 2), (key2318, 2), (key2318, 2)]

def rawRow9470 : Integer.Sparse Key := [(key2098, -6), (key2098, -6), (key2099, -6), (key2098, -6), (key2317, 2), (key2317, 2), (key2318, 2), (key2203, 2), (key2203, 2), (key2317, 2), (key2317, 2), (key2318, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2317, 2)]

def rawRow9471 : Integer.Sparse Key := [(key2098, -6), (key2099, -6), (key2098, -6), (key2098, -6), (key2317, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2318, 2), (key2203, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2317, 2), (key2203, 2), (key2317, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9472 : Integer.Sparse Key := [(key2099, -6), (key2098, -6), (key2098, -6), (key2098, -6), (key2318, 2), (key2317, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2203, 2), (key2317, 2), (key2317, 2), (key2203, 2)]

def rawRow9473 : Integer.Sparse Key := [(key2203, -6), (key2203, -6), (key2203, -6), (key2206, -6), (key2098, 2), (key2098, 2), (key2098, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2321, 2), (key2321, 2)]

def rawRow9474 : Integer.Sparse Key := [(key2203, -6), (key2203, -6), (key2206, -6), (key2203, -6), (key2317, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2098, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2321, 2), (key2098, 2), (key2317, 2), (key2317, 2)]

def rawRow9475 : Integer.Sparse Key := [(key2203, -6), (key2206, -6), (key2203, -6), (key2203, -6), (key2317, 2), (key2321, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2321, 2), (key2098, 2), (key2317, 2), (key2317, 2), (key2098, 2), (key2317, 2)]

def rawRow9476 : Integer.Sparse Key := [(key2206, -6), (key2203, -6), (key2203, -6), (key2203, -6), (key2321, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2317, 2), (key2098, 2), (key2317, 2), (key2317, 2), (key2098, 2)]

def rawRow9477 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key995, 6), (key1011, 6), (key1067, -6), (key1146, -6), (key1146, -6), (key1146, -6)]

def rawRow9478 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key1011, 6), (key995, 6), (key1146, -6), (key1067, -6), (key1146, -6), (key1146, -6)]

def rawRow9479 : Integer.Sparse Key := [(key995, 6), (key1011, 6), (key995, 6), (key995, 6), (key1146, -6), (key1146, -6), (key1067, -6), (key1146, -6)]

def rawRow9480 : Integer.Sparse Key := [(key1011, 6), (key995, 6), (key995, 6), (key995, 6), (key1146, -6), (key1146, -6), (key1146, -6), (key1067, -6)]

def rawRow9481 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1030, 6), (key1067, 6), (key1011, -6), (key1119, -6), (key1119, -6), (key1119, -6)]

def rawRow9482 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1067, 6), (key1030, 6), (key1119, -6), (key1011, -6), (key1119, -6), (key1119, -6)]

def rawRow9483 : Integer.Sparse Key := [(key1030, 6), (key1067, 6), (key1030, 6), (key1030, 6), (key1119, -6), (key1119, -6), (key1011, -6), (key1119, -6)]

def rawRow9484 : Integer.Sparse Key := [(key1067, 6), (key1030, 6), (key1030, 6), (key1030, 6), (key1119, -6), (key1119, -6), (key1119, -6), (key1011, -6)]

def rawRow9485 : Integer.Sparse Key := [(key2369, -6), (key2369, -6), (key2369, -6), (key2384, -6), (key2397, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2474, 2), (key2474, 2), (key2474, 2)]

def rawRow9486 : Integer.Sparse Key := [(key2369, -6), (key2369, -6), (key2384, -6), (key2369, -6), (key2463, 2), (key2463, 2), (key2474, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2474, 2), (key2474, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

def rawRow9487 : Integer.Sparse Key := [(key2369, -6), (key2384, -6), (key2369, -6), (key2369, -6), (key2463, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2474, 2), (key2397, 2), (key2474, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2397, 2), (key2463, 2)]

def rawRow9488 : Integer.Sparse Key := [(key2384, -6), (key2369, -6), (key2369, -6), (key2369, -6), (key2474, 2), (key2463, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2474, 2), (key2397, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2397, 2)]

def rawRow9489 : Integer.Sparse Key := [(key2397, -6), (key2397, -6), (key2397, -6), (key2431, -6), (key2369, 2), (key2369, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2497, 2), (key2497, 2)]

def rawRow9490 : Integer.Sparse Key := [(key2397, -6), (key2397, -6), (key2431, -6), (key2397, -6), (key2463, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2497, 2), (key2369, 2), (key2463, 2), (key2463, 2)]

def rawRow9491 : Integer.Sparse Key := [(key2397, -6), (key2431, -6), (key2397, -6), (key2397, -6), (key2463, 2), (key2497, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2497, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2)]

def rawRow9492 : Integer.Sparse Key := [(key2431, -6), (key2397, -6), (key2397, -6), (key2397, -6), (key2497, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2369, 2)]

def rawRow9493 : Integer.Sparse Key := [(key2606, -6), (key2622, -6), (key2622, -6), (key2622, -6), (key2661, 6), (key2696, 6), (key2696, 6), (key2696, 6)]

def rawRow9494 : Integer.Sparse Key := [(key2622, -6), (key2606, -6), (key2622, -6), (key2622, -6), (key2696, 6), (key2661, 6), (key2696, 6), (key2696, 6)]

def rawRow9495 : Integer.Sparse Key := [(key2622, -6), (key2622, -6), (key2606, -6), (key2622, -6), (key2696, 6), (key2696, 6), (key2661, 6), (key2696, 6)]

def rawRow9496 : Integer.Sparse Key := [(key2622, -6), (key2622, -6), (key2622, -6), (key2606, -6), (key2696, 6), (key2696, 6), (key2696, 6), (key2661, 6)]

def rawRow9497 : Integer.Sparse Key := [(key2661, -6), (key2696, -6), (key2696, -6), (key2696, -6), (key2606, 6), (key2799, 6), (key2799, 6), (key2799, 6)]

def rawRow9498 : Integer.Sparse Key := [(key2696, -6), (key2661, -6), (key2696, -6), (key2696, -6), (key2799, 6), (key2606, 6), (key2799, 6), (key2799, 6)]

def rawRow9499 : Integer.Sparse Key := [(key2696, -6), (key2696, -6), (key2661, -6), (key2696, -6), (key2799, 6), (key2799, 6), (key2606, 6), (key2799, 6)]

def rawRow9500 : Integer.Sparse Key := [(key2696, -6), (key2696, -6), (key2696, -6), (key2661, -6), (key2799, 6), (key2799, 6), (key2799, 6), (key2606, 6)]

def rawRow9501 : Integer.Sparse Key := [(key2592, 2), (key2595, 2), (key2595, 2), (key2848, 2), (key2882, 2), (key2882, 2), (key2970, 2), (key2970, 2), (key2991, 2), (key2991, 2), (key2993, 2), (key2993, 2), (key2602, -2), (key2602, -2), (key2603, -2), (key2891, -2), (key2891, -2), (key2912, -2), (key2912, -2), (key2914, -2), (key2914, -2), (key2996, -2), (key3003, -2), (key3003, -2)]

def rawRow9502 : Integer.Sparse Key := [(key2595, 2), (key2592, 2), (key2595, 2), (key2882, 2), (key2848, 2), (key2882, 2), (key2991, 2), (key2993, 2), (key2970, 2), (key2993, 2), (key2970, 2), (key2991, 2), (key2602, -2), (key2603, -2), (key2602, -2), (key2912, -2), (key2914, -2), (key2891, -2), (key2914, -2), (key2891, -2), (key2912, -2), (key3003, -2), (key2996, -2), (key3003, -2)]

def rawRow9503 : Integer.Sparse Key := [(key2595, 2), (key2595, 2), (key2592, 2), (key2882, 2), (key2882, 2), (key2848, 2), (key2993, 2), (key2991, 2), (key2993, 2), (key2970, 2), (key2991, 2), (key2970, 2), (key2603, -2), (key2602, -2), (key2602, -2), (key2914, -2), (key2912, -2), (key2914, -2), (key2891, -2), (key2912, -2), (key2891, -2), (key3003, -2), (key3003, -2), (key2996, -2)]

def rawRow9504 : Integer.Sparse Key := [(key2848, 2), (key2970, 2), (key2970, 2), (key2592, 2), (key2991, 2), (key2991, 2), (key2595, 2), (key2595, 2), (key2882, 2), (key2882, 2), (key2993, 2), (key2993, 2), (key2891, -2), (key2891, -2), (key2996, -2), (key2602, -2), (key2602, -2), (key2912, -2), (key2912, -2), (key3003, -2), (key3003, -2), (key2603, -2), (key2914, -2), (key2914, -2)]

def rawRow9505 : Integer.Sparse Key := [(key2970, 2), (key2848, 2), (key2970, 2), (key2991, 2), (key2592, 2), (key2991, 2), (key2882, 2), (key2993, 2), (key2595, 2), (key2993, 2), (key2595, 2), (key2882, 2), (key2891, -2), (key2996, -2), (key2891, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2914, -2), (key2603, -2), (key2914, -2)]

def rawRow9506 : Integer.Sparse Key := [(key2970, 2), (key2970, 2), (key2848, 2), (key2991, 2), (key2991, 2), (key2592, 2), (key2993, 2), (key2882, 2), (key2993, 2), (key2595, 2), (key2882, 2), (key2595, 2), (key2996, -2), (key2891, -2), (key2891, -2), (key3003, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2602, -2), (key2914, -2), (key2914, -2), (key2603, -2)]

def rawRow9507 : Integer.Sparse Key := [(key2882, 2), (key2991, 2), (key2993, 2), (key2595, 2), (key2970, 2), (key2993, 2), (key2592, 2), (key2595, 2), (key2848, 2), (key2882, 2), (key2970, 2), (key2991, 2), (key2912, -2), (key2914, -2), (key3003, -2), (key2602, -2), (key2603, -2), (key2891, -2), (key2914, -2), (key2996, -2), (key3003, -2), (key2602, -2), (key2891, -2), (key2912, -2)]

def rawRow9508 : Integer.Sparse Key := [(key2882, 2), (key2993, 2), (key2991, 2), (key2595, 2), (key2993, 2), (key2970, 2), (key2595, 2), (key2592, 2), (key2882, 2), (key2848, 2), (key2991, 2), (key2970, 2), (key2914, -2), (key2912, -2), (key3003, -2), (key2603, -2), (key2602, -2), (key2914, -2), (key2891, -2), (key3003, -2), (key2996, -2), (key2602, -2), (key2912, -2), (key2891, -2)]

def rawRow9509 : Integer.Sparse Key := [(key2991, 2), (key2882, 2), (key2993, 2), (key2970, 2), (key2595, 2), (key2993, 2), (key2848, 2), (key2970, 2), (key2592, 2), (key2991, 2), (key2595, 2), (key2882, 2), (key2912, -2), (key3003, -2), (key2914, -2), (key2891, -2), (key2996, -2), (key2602, -2), (key3003, -2), (key2603, -2), (key2914, -2), (key2891, -2), (key2602, -2), (key2912, -2)]

def rawRow9510 : Integer.Sparse Key := [(key2991, 2), (key2993, 2), (key2882, 2), (key2970, 2), (key2993, 2), (key2595, 2), (key2970, 2), (key2848, 2), (key2991, 2), (key2592, 2), (key2882, 2), (key2595, 2), (key3003, -2), (key2912, -2), (key2914, -2), (key2996, -2), (key2891, -2), (key3003, -2), (key2602, -2), (key2914, -2), (key2603, -2), (key2891, -2), (key2912, -2), (key2602, -2)]

def rawRow9511 : Integer.Sparse Key := [(key2993, 2), (key2882, 2), (key2991, 2), (key2993, 2), (key2595, 2), (key2970, 2), (key2882, 2), (key2991, 2), (key2595, 2), (key2970, 2), (key2592, 2), (key2848, 2), (key2914, -2), (key3003, -2), (key2912, -2), (key2914, -2), (key3003, -2), (key2603, -2), (key2996, -2), (key2602, -2), (key2891, -2), (key2912, -2), (key2602, -2), (key2891, -2)]

def rawRow9512 : Integer.Sparse Key := [(key2993, 2), (key2991, 2), (key2882, 2), (key2993, 2), (key2970, 2), (key2595, 2), (key2991, 2), (key2882, 2), (key2970, 2), (key2595, 2), (key2848, 2), (key2592, 2), (key3003, -2), (key2914, -2), (key2912, -2), (key3003, -2), (key2914, -2), (key2996, -2), (key2603, -2), (key2891, -2), (key2602, -2), (key2912, -2), (key2891, -2), (key2602, -2)]

def rawRow9513 : Integer.Sparse Key := [(key2379, 2), (key2393, 2), (key2393, 2), (key2771, 2), (key2912, 2), (key2912, 2), (key2933, 2), (key2933, 2), (key2991, 2), (key2991, 2), (key3003, 2), (key3003, 2), (key2595, -2), (key2595, -2), (key2603, -2), (key2774, -2), (key2774, -2), (key2882, -2), (key2882, -2), (key2914, -2), (key2914, -2), (key2934, -2), (key2993, -2), (key2993, -2)]

def rawRow9514 : Integer.Sparse Key := [(key2393, 2), (key2379, 2), (key2393, 2), (key2912, 2), (key2771, 2), (key2912, 2), (key2991, 2), (key3003, 2), (key2933, 2), (key3003, 2), (key2933, 2), (key2991, 2), (key2595, -2), (key2603, -2), (key2595, -2), (key2882, -2), (key2914, -2), (key2774, -2), (key2914, -2), (key2774, -2), (key2882, -2), (key2993, -2), (key2934, -2), (key2993, -2)]

def rawRow9515 : Integer.Sparse Key := [(key2393, 2), (key2393, 2), (key2379, 2), (key2912, 2), (key2912, 2), (key2771, 2), (key3003, 2), (key2991, 2), (key3003, 2), (key2933, 2), (key2991, 2), (key2933, 2), (key2603, -2), (key2595, -2), (key2595, -2), (key2914, -2), (key2882, -2), (key2914, -2), (key2774, -2), (key2882, -2), (key2774, -2), (key2993, -2), (key2993, -2), (key2934, -2)]

def rawRow9516 : Integer.Sparse Key := [(key2407, 2), (key2441, 2), (key2441, 2), (key2592, 2), (key2991, 2), (key2991, 2), (key2602, 2), (key2602, 2), (key2912, 2), (key2912, 2), (key3003, 2), (key3003, 2), (key2774, -2), (key2774, -2), (key2934, -2), (key2595, -2), (key2595, -2), (key2882, -2), (key2882, -2), (key2993, -2), (key2993, -2), (key2603, -2), (key2914, -2), (key2914, -2)]

def rawRow9517 : Integer.Sparse Key := [(key2441, 2), (key2407, 2), (key2441, 2), (key2991, 2), (key2592, 2), (key2991, 2), (key2912, 2), (key3003, 2), (key2602, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2774, -2), (key2934, -2), (key2774, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2914, -2), (key2603, -2), (key2914, -2)]

def rawRow9518 : Integer.Sparse Key := [(key2441, 2), (key2441, 2), (key2407, 2), (key2991, 2), (key2991, 2), (key2592, 2), (key3003, 2), (key2912, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2602, 2), (key2934, -2), (key2774, -2), (key2774, -2), (key2993, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2595, -2), (key2914, -2), (key2914, -2), (key2603, -2)]

def rawRow9519 : Integer.Sparse Key := [(key2544, 2), (key2555, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2565, 2), (key2379, 2), (key2393, 2), (key2771, 2), (key2912, 2), (key2933, 2), (key2991, 2), (key2882, -2), (key2914, -2), (key2993, -2), (key2595, -2), (key2603, -2), (key2774, -2), (key2914, -2), (key2934, -2), (key2993, -2), (key2595, -2), (key2774, -2), (key2882, -2)]

def rawRow9520 : Integer.Sparse Key := [(key2544, 2), (key2565, 2), (key2555, 2), (key2393, 2), (key2565, 2), (key2441, 2), (key2393, 2), (key2379, 2), (key2912, 2), (key2771, 2), (key2991, 2), (key2933, 2), (key2914, -2), (key2882, -2), (key2993, -2), (key2603, -2), (key2595, -2), (key2914, -2), (key2774, -2), (key2993, -2), (key2934, -2), (key2595, -2), (key2882, -2), (key2774, -2)]

def rawRow9521 : Integer.Sparse Key := [(key2555, 2), (key2544, 2), (key2565, 2), (key2441, 2), (key2393, 2), (key2565, 2), (key2407, 2), (key2441, 2), (key2592, 2), (key2991, 2), (key2602, 2), (key2912, 2), (key2882, -2), (key2993, -2), (key2914, -2), (key2774, -2), (key2934, -2), (key2595, -2), (key2993, -2), (key2603, -2), (key2914, -2), (key2774, -2), (key2595, -2), (key2882, -2)]

def rawRow9522 : Integer.Sparse Key := [(key2555, 2), (key2565, 2), (key2544, 2), (key2441, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2407, 2), (key2991, 2), (key2592, 2), (key2912, 2), (key2602, 2), (key2993, -2), (key2882, -2), (key2914, -2), (key2934, -2), (key2774, -2), (key2993, -2), (key2595, -2), (key2914, -2), (key2603, -2), (key2774, -2), (key2882, -2), (key2595, -2)]

def rawRow9523 : Integer.Sparse Key := [(key2565, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2544, 2), (key2555, 2), (key2393, 2), (key2441, 2), (key2379, 2), (key2771, 2), (key2914, -2), (key2993, -2), (key2882, -2), (key2914, -2), (key2993, -2), (key2603, -2), (key2934, -2), (key2595, -2), (key2774, -2), (key2882, -2), (key2595, -2), (key2774, -2)]

def rawRow9524 : Integer.Sparse Key := [(key2565, 2), (key2555, 2), (key2544, 2), (key2565, 2), (key2441, 2), (key2393, 2), (key2555, 2), (key2544, 2), (key2441, 2), (key2393, 2), (key2407, 2), (key2592, 2), (key2993, -2), (key2914, -2), (key2882, -2), (key2993, -2), (key2914, -2), (key2934, -2), (key2603, -2), (key2774, -2), (key2595, -2), (key2882, -2), (key2774, -2), (key2595, -2)]

def rawRow9525 : Integer.Sparse Key := [(key1031, -24), (key996, 6), (key1109, 6), (key1188, 6), (key1188, 6)]

def rawRow9526 : Integer.Sparse Key := [(key1031, -24), (key996, 6), (key1188, 6), (key1109, 6), (key1188, 6)]

def rawRow9527 : Integer.Sparse Key := [(key1031, -24), (key996, 6), (key1188, 6), (key1188, 6), (key1109, 6)]

def rawRow9528 : Integer.Sparse Key := [(key1031, -24), (key1109, 6), (key996, 6), (key1188, 6), (key1188, 6)]

def rawRow9529 : Integer.Sparse Key := [(key1031, -24), (key1109, 6), (key1188, 6), (key996, 6), (key1188, 6)]

def rawRow9530 : Integer.Sparse Key := [(key1031, -24), (key1109, 6), (key1188, 6), (key1188, 6), (key996, 6)]

def rawRow9531 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key996, 6), (key1109, 6), (key1188, 6)]

def rawRow9532 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key996, 6), (key1188, 6), (key1109, 6)]

def rawRow9533 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key1109, 6), (key996, 6), (key1188, 6)]

def rawRow9534 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key1109, 6), (key1188, 6), (key996, 6)]

def rawRow9535 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key1188, 6), (key996, 6), (key1109, 6)]

def rawRow9536 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key1188, 6), (key1109, 6), (key996, 6)]

def rawRow9537 : Integer.Sparse Key := [(key1109, -24), (key996, 6), (key1031, 6), (key1188, 6), (key1188, 6)]

def rawRow9538 : Integer.Sparse Key := [(key1109, -24), (key996, 6), (key1188, 6), (key1031, 6), (key1188, 6)]

def rawRow9539 : Integer.Sparse Key := [(key1109, -24), (key996, 6), (key1188, 6), (key1188, 6), (key1031, 6)]

def rawRow9540 : Integer.Sparse Key := [(key1109, -24), (key1031, 6), (key996, 6), (key1188, 6), (key1188, 6)]

def rawRow9541 : Integer.Sparse Key := [(key1109, -24), (key1031, 6), (key1188, 6), (key996, 6), (key1188, 6)]

def rawRow9542 : Integer.Sparse Key := [(key1109, -24), (key1031, 6), (key1188, 6), (key1188, 6), (key996, 6)]

def rawRow9543 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key996, 6), (key1031, 6), (key1188, 6)]

def rawRow9544 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key996, 6), (key1188, 6), (key1031, 6)]

def rawRow9545 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key1031, 6), (key996, 6), (key1188, 6)]

def rawRow9546 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key1031, 6), (key1188, 6), (key996, 6)]

def rawRow9547 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key1188, 6), (key996, 6), (key1031, 6)]

def rawRow9548 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key1188, 6), (key1031, 6), (key996, 6)]

def rawRow9549 : Integer.Sparse Key := [(key1033, -6), (key1033, -6), (key1041, -6), (key1076, -6), (key998, 2), (key998, 2), (key1006, 2), (key1111, 2), (key1111, 2), (key1190, 2), (key1190, 2), (key1193, 2), (key1193, 2), (key1155, 2), (key1212, 2), (key1212, 2)]

def rawRow9550 : Integer.Sparse Key := [(key1033, -6), (key1041, -6), (key1033, -6), (key1076, -6), (key998, 2), (key1006, 2), (key998, 2), (key1190, 2), (key1193, 2), (key1111, 2), (key1193, 2), (key1111, 2), (key1190, 2), (key1212, 2), (key1155, 2), (key1212, 2)]

def rawRow9551 : Integer.Sparse Key := [(key1041, -6), (key1033, -6), (key1033, -6), (key1076, -6), (key1006, 2), (key998, 2), (key998, 2), (key1193, 2), (key1190, 2), (key1193, 2), (key1111, 2), (key1190, 2), (key1111, 2), (key1212, 2), (key1212, 2), (key1155, 2)]

def rawRow9552 : Integer.Sparse Key := [(key1033, -6), (key1033, -6), (key1076, -6), (key1041, -6), (key1111, 2), (key1111, 2), (key1155, 2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1212, 2), (key1212, 2), (key1006, 2), (key1193, 2), (key1193, 2)]

def rawRow9553 : Integer.Sparse Key := [(key1033, -6), (key1076, -6), (key1033, -6), (key1041, -6), (key1111, 2), (key1155, 2), (key1111, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1212, 2), (key998, 2), (key1190, 2), (key1193, 2), (key1006, 2), (key1193, 2)]

def rawRow9554 : Integer.Sparse Key := [(key1076, -6), (key1033, -6), (key1033, -6), (key1041, -6), (key1155, 2), (key1111, 2), (key1111, 2), (key1212, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1190, 2), (key998, 2), (key1193, 2), (key1193, 2), (key1006, 2)]

def rawRow9555 : Integer.Sparse Key := [(key1033, -6), (key1041, -6), (key1076, -6), (key1033, -6), (key1190, 2), (key1193, 2), (key1212, 2), (key998, 2), (key1006, 2), (key1111, 2), (key1193, 2), (key1155, 2), (key1212, 2), (key998, 2), (key1111, 2), (key1190, 2)]

def rawRow9556 : Integer.Sparse Key := [(key1041, -6), (key1033, -6), (key1076, -6), (key1033, -6), (key1193, 2), (key1190, 2), (key1212, 2), (key1006, 2), (key998, 2), (key1193, 2), (key1111, 2), (key1212, 2), (key1155, 2), (key998, 2), (key1190, 2), (key1111, 2)]

def rawRow9557 : Integer.Sparse Key := [(key1033, -6), (key1076, -6), (key1041, -6), (key1033, -6), (key1190, 2), (key1212, 2), (key1193, 2), (key1111, 2), (key1155, 2), (key998, 2), (key1212, 2), (key1006, 2), (key1193, 2), (key1111, 2), (key998, 2), (key1190, 2)]

def rawRow9558 : Integer.Sparse Key := [(key1076, -6), (key1033, -6), (key1041, -6), (key1033, -6), (key1212, 2), (key1190, 2), (key1193, 2), (key1155, 2), (key1111, 2), (key1212, 2), (key998, 2), (key1193, 2), (key1006, 2), (key1111, 2), (key1190, 2), (key998, 2)]

def rawRow9559 : Integer.Sparse Key := [(key1041, -6), (key1076, -6), (key1033, -6), (key1033, -6), (key1193, 2), (key1212, 2), (key1190, 2), (key1193, 2), (key1212, 2), (key1006, 2), (key1155, 2), (key998, 2), (key1111, 2), (key1190, 2), (key998, 2), (key1111, 2)]

def rawRow9560 : Integer.Sparse Key := [(key1076, -6), (key1041, -6), (key1033, -6), (key1033, -6), (key1212, 2), (key1193, 2), (key1190, 2), (key1212, 2), (key1193, 2), (key1155, 2), (key1006, 2), (key1111, 2), (key998, 2), (key1190, 2), (key1111, 2), (key998, 2)]

def rawRow9561 : Integer.Sparse Key := [(key1111, -6), (key1111, -6), (key1127, -6), (key1155, -6), (key998, 2), (key998, 2), (key1019, 2), (key1033, 2), (key1033, 2), (key1190, 2), (key1190, 2), (key1199, 2), (key1199, 2), (key1076, 2), (key1212, 2), (key1212, 2)]

def rawRow9562 : Integer.Sparse Key := [(key1111, -6), (key1127, -6), (key1111, -6), (key1155, -6), (key998, 2), (key1019, 2), (key998, 2), (key1190, 2), (key1199, 2), (key1033, 2), (key1199, 2), (key1033, 2), (key1190, 2), (key1212, 2), (key1076, 2), (key1212, 2)]

def rawRow9563 : Integer.Sparse Key := [(key1127, -6), (key1111, -6), (key1111, -6), (key1155, -6), (key1019, 2), (key998, 2), (key998, 2), (key1199, 2), (key1190, 2), (key1199, 2), (key1033, 2), (key1190, 2), (key1033, 2), (key1212, 2), (key1212, 2), (key1076, 2)]

def rawRow9564 : Integer.Sparse Key := [(key1111, -6), (key1111, -6), (key1155, -6), (key1127, -6), (key1033, 2), (key1033, 2), (key1076, 2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1212, 2), (key1212, 2), (key1019, 2), (key1199, 2), (key1199, 2)]

def rawRow9565 : Integer.Sparse Key := [(key1111, -6), (key1155, -6), (key1111, -6), (key1127, -6), (key1033, 2), (key1076, 2), (key1033, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1212, 2), (key998, 2), (key1190, 2), (key1199, 2), (key1019, 2), (key1199, 2)]

def rawRow9566 : Integer.Sparse Key := [(key1155, -6), (key1111, -6), (key1111, -6), (key1127, -6), (key1076, 2), (key1033, 2), (key1033, 2), (key1212, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1190, 2), (key998, 2), (key1199, 2), (key1199, 2), (key1019, 2)]

def rawRow9567 : Integer.Sparse Key := [(key1111, -6), (key1127, -6), (key1155, -6), (key1111, -6), (key1190, 2), (key1199, 2), (key1212, 2), (key998, 2), (key1019, 2), (key1033, 2), (key1199, 2), (key1076, 2), (key1212, 2), (key998, 2), (key1033, 2), (key1190, 2)]

def rawRow9568 : Integer.Sparse Key := [(key1127, -6), (key1111, -6), (key1155, -6), (key1111, -6), (key1199, 2), (key1190, 2), (key1212, 2), (key1019, 2), (key998, 2), (key1199, 2), (key1033, 2), (key1212, 2), (key1076, 2), (key998, 2), (key1190, 2), (key1033, 2)]

def rawRow9569 : Integer.Sparse Key := [(key1111, -6), (key1155, -6), (key1127, -6), (key1111, -6), (key1190, 2), (key1212, 2), (key1199, 2), (key1033, 2), (key1076, 2), (key998, 2), (key1212, 2), (key1019, 2), (key1199, 2), (key1033, 2), (key998, 2), (key1190, 2)]

def rawRow9570 : Integer.Sparse Key := [(key1155, -6), (key1111, -6), (key1127, -6), (key1111, -6), (key1212, 2), (key1190, 2), (key1199, 2), (key1076, 2), (key1033, 2), (key1212, 2), (key998, 2), (key1199, 2), (key1019, 2), (key1033, 2), (key1190, 2), (key998, 2)]

def rawRow9571 : Integer.Sparse Key := [(key1127, -6), (key1155, -6), (key1111, -6), (key1111, -6), (key1199, 2), (key1212, 2), (key1190, 2), (key1199, 2), (key1212, 2), (key1019, 2), (key1076, 2), (key998, 2), (key1033, 2), (key1190, 2), (key998, 2), (key1033, 2)]

def rawRow9572 : Integer.Sparse Key := [(key1155, -6), (key1127, -6), (key1111, -6), (key1111, -6), (key1212, 2), (key1199, 2), (key1190, 2), (key1212, 2), (key1199, 2), (key1076, 2), (key1019, 2), (key1033, 2), (key998, 2), (key1190, 2), (key1033, 2), (key998, 2)]

def rawRow9573 : Integer.Sparse Key := [(key2615, -6), (key2808, -6), (key2828, -6), (key2828, -6), (key2631, 2), (key2639, 2), (key2639, 2), (key2705, 2), (key2725, 2), (key2725, 2), (key2859, 2), (key2859, 2), (key2869, 2), (key2869, 2), (key2879, 2), (key2879, 2)]

def rawRow9574 : Integer.Sparse Key := [(key2615, -6), (key2828, -6), (key2808, -6), (key2828, -6), (key2639, 2), (key2631, 2), (key2639, 2), (key2725, 2), (key2705, 2), (key2725, 2), (key2869, 2), (key2879, 2), (key2859, 2), (key2879, 2), (key2859, 2), (key2869, 2)]

def rawRow9575 : Integer.Sparse Key := [(key2615, -6), (key2828, -6), (key2828, -6), (key2808, -6), (key2639, 2), (key2639, 2), (key2631, 2), (key2725, 2), (key2725, 2), (key2705, 2), (key2879, 2), (key2869, 2), (key2879, 2), (key2859, 2), (key2869, 2), (key2859, 2)]

def rawRow9576 : Integer.Sparse Key := [(key2808, -6), (key2615, -6), (key2828, -6), (key2828, -6), (key2705, 2), (key2859, 2), (key2859, 2), (key2631, 2), (key2869, 2), (key2869, 2), (key2639, 2), (key2639, 2), (key2725, 2), (key2725, 2), (key2879, 2), (key2879, 2)]

def rawRow9577 : Integer.Sparse Key := [(key2808, -6), (key2828, -6), (key2615, -6), (key2828, -6), (key2859, 2), (key2705, 2), (key2859, 2), (key2869, 2), (key2631, 2), (key2869, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2879, 2), (key2639, 2), (key2725, 2)]

def rawRow9578 : Integer.Sparse Key := [(key2808, -6), (key2828, -6), (key2828, -6), (key2615, -6), (key2859, 2), (key2859, 2), (key2705, 2), (key2869, 2), (key2869, 2), (key2631, 2), (key2879, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2725, 2), (key2639, 2)]

def rawRow9579 : Integer.Sparse Key := [(key2828, -6), (key2615, -6), (key2808, -6), (key2828, -6), (key2725, 2), (key2869, 2), (key2879, 2), (key2639, 2), (key2859, 2), (key2879, 2), (key2631, 2), (key2639, 2), (key2705, 2), (key2725, 2), (key2859, 2), (key2869, 2)]

def rawRow9580 : Integer.Sparse Key := [(key2828, -6), (key2615, -6), (key2828, -6), (key2808, -6), (key2725, 2), (key2879, 2), (key2869, 2), (key2639, 2), (key2879, 2), (key2859, 2), (key2639, 2), (key2631, 2), (key2725, 2), (key2705, 2), (key2869, 2), (key2859, 2)]

def rawRow9581 : Integer.Sparse Key := [(key2828, -6), (key2808, -6), (key2615, -6), (key2828, -6), (key2869, 2), (key2725, 2), (key2879, 2), (key2859, 2), (key2639, 2), (key2879, 2), (key2705, 2), (key2859, 2), (key2631, 2), (key2869, 2), (key2639, 2), (key2725, 2)]

def rawRow9582 : Integer.Sparse Key := [(key2828, -6), (key2808, -6), (key2828, -6), (key2615, -6), (key2869, 2), (key2879, 2), (key2725, 2), (key2859, 2), (key2879, 2), (key2639, 2), (key2859, 2), (key2705, 2), (key2869, 2), (key2631, 2), (key2725, 2), (key2639, 2)]

def rawRow9583 : Integer.Sparse Key := [(key2828, -6), (key2828, -6), (key2615, -6), (key2808, -6), (key2879, 2), (key2725, 2), (key2869, 2), (key2879, 2), (key2639, 2), (key2859, 2), (key2725, 2), (key2869, 2), (key2639, 2), (key2859, 2), (key2631, 2), (key2705, 2)]

def rawRow9584 : Integer.Sparse Key := [(key2828, -6), (key2828, -6), (key2808, -6), (key2615, -6), (key2879, 2), (key2869, 2), (key2725, 2), (key2879, 2), (key2859, 2), (key2639, 2), (key2869, 2), (key2725, 2), (key2859, 2), (key2639, 2), (key2705, 2), (key2631, 2)]

def rawRow9585 : Integer.Sparse Key := [(key2631, -6), (key2785, -6), (key2869, -6), (key2869, -6), (key2615, 2), (key2639, 2), (key2639, 2), (key2670, 2), (key2725, 2), (key2725, 2), (key2793, 2), (key2793, 2), (key2828, 2), (key2828, 2), (key2879, 2), (key2879, 2)]

def rawRow9586 : Integer.Sparse Key := [(key2631, -6), (key2869, -6), (key2785, -6), (key2869, -6), (key2639, 2), (key2615, 2), (key2639, 2), (key2725, 2), (key2670, 2), (key2725, 2), (key2828, 2), (key2879, 2), (key2793, 2), (key2879, 2), (key2793, 2), (key2828, 2)]

def rawRow9587 : Integer.Sparse Key := [(key2631, -6), (key2869, -6), (key2869, -6), (key2785, -6), (key2639, 2), (key2639, 2), (key2615, 2), (key2725, 2), (key2725, 2), (key2670, 2), (key2879, 2), (key2828, 2), (key2879, 2), (key2793, 2), (key2828, 2), (key2793, 2)]

def rawRow9588 : Integer.Sparse Key := [(key2785, -6), (key2631, -6), (key2869, -6), (key2869, -6), (key2670, 2), (key2793, 2), (key2793, 2), (key2615, 2), (key2828, 2), (key2828, 2), (key2639, 2), (key2639, 2), (key2725, 2), (key2725, 2), (key2879, 2), (key2879, 2)]

def rawRow9589 : Integer.Sparse Key := [(key2785, -6), (key2869, -6), (key2631, -6), (key2869, -6), (key2793, 2), (key2670, 2), (key2793, 2), (key2828, 2), (key2615, 2), (key2828, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2879, 2), (key2639, 2), (key2725, 2)]

def rawRow9590 : Integer.Sparse Key := [(key2785, -6), (key2869, -6), (key2869, -6), (key2631, -6), (key2793, 2), (key2793, 2), (key2670, 2), (key2828, 2), (key2828, 2), (key2615, 2), (key2879, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2725, 2), (key2639, 2)]

def rawRow9591 : Integer.Sparse Key := [(key2869, -6), (key2631, -6), (key2785, -6), (key2869, -6), (key2725, 2), (key2828, 2), (key2879, 2), (key2639, 2), (key2793, 2), (key2879, 2), (key2615, 2), (key2639, 2), (key2670, 2), (key2725, 2), (key2793, 2), (key2828, 2)]

def rawRow9592 : Integer.Sparse Key := [(key2869, -6), (key2631, -6), (key2869, -6), (key2785, -6), (key2725, 2), (key2879, 2), (key2828, 2), (key2639, 2), (key2879, 2), (key2793, 2), (key2639, 2), (key2615, 2), (key2725, 2), (key2670, 2), (key2828, 2), (key2793, 2)]

def rawRow9593 : Integer.Sparse Key := [(key2869, -6), (key2785, -6), (key2631, -6), (key2869, -6), (key2828, 2), (key2725, 2), (key2879, 2), (key2793, 2), (key2639, 2), (key2879, 2), (key2670, 2), (key2793, 2), (key2615, 2), (key2828, 2), (key2639, 2), (key2725, 2)]

def rawRow9594 : Integer.Sparse Key := [(key2869, -6), (key2785, -6), (key2869, -6), (key2631, -6), (key2828, 2), (key2879, 2), (key2725, 2), (key2793, 2), (key2879, 2), (key2639, 2), (key2793, 2), (key2670, 2), (key2828, 2), (key2615, 2), (key2725, 2), (key2639, 2)]

def rawRow9595 : Integer.Sparse Key := [(key2869, -6), (key2869, -6), (key2631, -6), (key2785, -6), (key2879, 2), (key2725, 2), (key2828, 2), (key2879, 2), (key2639, 2), (key2793, 2), (key2725, 2), (key2828, 2), (key2639, 2), (key2793, 2), (key2615, 2), (key2670, 2)]

def rawRow9596 : Integer.Sparse Key := [(key2869, -6), (key2869, -6), (key2785, -6), (key2631, -6), (key2879, 2), (key2828, 2), (key2725, 2), (key2879, 2), (key2793, 2), (key2639, 2), (key2828, 2), (key2725, 2), (key2793, 2), (key2639, 2), (key2670, 2), (key2615, 2)]

def rawRow9597 : Integer.Sparse Key := [(key2402, -6), (key2402, -6), (key2408, -6), (key2439, -6), (key2591, 2), (key2591, 2), (key2596, 2), (key2847, 2), (key2847, 2), (key2878, 2), (key2878, 2), (key2884, 2), (key2884, 2), (key3020, 2), (key3029, 2), (key3029, 2)]

def rawRow9598 : Integer.Sparse Key := [(key2402, -6), (key2408, -6), (key2402, -6), (key2439, -6), (key2591, 2), (key2596, 2), (key2591, 2), (key2878, 2), (key2884, 2), (key2847, 2), (key2884, 2), (key2847, 2), (key2878, 2), (key3029, 2), (key3020, 2), (key3029, 2)]

def rawRow9599 : Integer.Sparse Key := [(key2408, -6), (key2402, -6), (key2402, -6), (key2439, -6), (key2596, 2), (key2591, 2), (key2591, 2), (key2884, 2), (key2878, 2), (key2884, 2), (key2847, 2), (key2878, 2), (key2847, 2), (key3029, 2), (key3029, 2), (key3020, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9600 : Integer.Sparse Key := [(key2402, -6), (key2402, -6), (key2439, -6), (key2408, -6), (key2847, 2), (key2847, 2), (key3020, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2596, 2), (key2884, 2), (key2884, 2)]

def rawRow9601 : Integer.Sparse Key := [(key2402, -6), (key2439, -6), (key2402, -6), (key2408, -6), (key2847, 2), (key3020, 2), (key2847, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2884, 2), (key2596, 2), (key2884, 2)]

def rawRow9602 : Integer.Sparse Key := [(key2439, -6), (key2402, -6), (key2402, -6), (key2408, -6), (key3020, 2), (key2847, 2), (key2847, 2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2884, 2), (key2884, 2), (key2596, 2)]

def rawRow9603 : Integer.Sparse Key := [(key2402, -6), (key2408, -6), (key2439, -6), (key2402, -6), (key2878, 2), (key2884, 2), (key3029, 2), (key2591, 2), (key2596, 2), (key2847, 2), (key2884, 2), (key3020, 2), (key3029, 2), (key2591, 2), (key2847, 2), (key2878, 2)]

def rawRow9604 : Integer.Sparse Key := [(key2408, -6), (key2402, -6), (key2439, -6), (key2402, -6), (key2884, 2), (key2878, 2), (key3029, 2), (key2596, 2), (key2591, 2), (key2884, 2), (key2847, 2), (key3029, 2), (key3020, 2), (key2591, 2), (key2878, 2), (key2847, 2)]

def rawRow9605 : Integer.Sparse Key := [(key2402, -6), (key2439, -6), (key2408, -6), (key2402, -6), (key2878, 2), (key3029, 2), (key2884, 2), (key2847, 2), (key3020, 2), (key2591, 2), (key3029, 2), (key2596, 2), (key2884, 2), (key2847, 2), (key2591, 2), (key2878, 2)]

def rawRow9606 : Integer.Sparse Key := [(key2439, -6), (key2402, -6), (key2408, -6), (key2402, -6), (key3029, 2), (key2878, 2), (key2884, 2), (key3020, 2), (key2847, 2), (key3029, 2), (key2591, 2), (key2884, 2), (key2596, 2), (key2847, 2), (key2878, 2), (key2591, 2)]

def rawRow9607 : Integer.Sparse Key := [(key2408, -6), (key2439, -6), (key2402, -6), (key2402, -6), (key2884, 2), (key3029, 2), (key2878, 2), (key2884, 2), (key3029, 2), (key2596, 2), (key3020, 2), (key2591, 2), (key2847, 2), (key2878, 2), (key2591, 2), (key2847, 2)]

def rawRow9608 : Integer.Sparse Key := [(key2439, -6), (key2408, -6), (key2402, -6), (key2402, -6), (key3029, 2), (key2884, 2), (key2878, 2), (key3029, 2), (key2884, 2), (key3020, 2), (key2596, 2), (key2847, 2), (key2591, 2), (key2878, 2), (key2847, 2), (key2591, 2)]

def rawRow9609 : Integer.Sparse Key := [(key2468, -6), (key2468, -6), (key2481, -6), (key2505, -6), (key2374, 2), (key2374, 2), (key2391, 2), (key2770, 2), (key2770, 2), (key2878, 2), (key2878, 2), (key2926, 2), (key2926, 2), (key3006, 2), (key3029, 2), (key3029, 2)]

def rawRow9610 : Integer.Sparse Key := [(key2468, -6), (key2481, -6), (key2468, -6), (key2505, -6), (key2374, 2), (key2391, 2), (key2374, 2), (key2878, 2), (key2926, 2), (key2770, 2), (key2926, 2), (key2770, 2), (key2878, 2), (key3029, 2), (key3006, 2), (key3029, 2)]

def rawRow9611 : Integer.Sparse Key := [(key2481, -6), (key2468, -6), (key2468, -6), (key2505, -6), (key2391, 2), (key2374, 2), (key2374, 2), (key2926, 2), (key2878, 2), (key2926, 2), (key2770, 2), (key2878, 2), (key2770, 2), (key3029, 2), (key3029, 2), (key3006, 2)]

def rawRow9612 : Integer.Sparse Key := [(key2468, -6), (key2468, -6), (key2505, -6), (key2481, -6), (key2402, 2), (key2402, 2), (key2439, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2605, 2), (key2926, 2), (key2926, 2)]

def rawRow9613 : Integer.Sparse Key := [(key2468, -6), (key2505, -6), (key2468, -6), (key2481, -6), (key2402, 2), (key2439, 2), (key2402, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2926, 2), (key2605, 2), (key2926, 2)]

def rawRow9614 : Integer.Sparse Key := [(key2505, -6), (key2468, -6), (key2468, -6), (key2481, -6), (key2439, 2), (key2402, 2), (key2402, 2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2926, 2), (key2926, 2), (key2605, 2)]

def rawRow9615 : Integer.Sparse Key := [(key2468, -6), (key2481, -6), (key2505, -6), (key2468, -6), (key2535, 2), (key2542, 2), (key2553, 2), (key2374, 2), (key2391, 2), (key2402, 2), (key2542, 2), (key2439, 2), (key2553, 2), (key2591, 2), (key2770, 2), (key2878, 2)]

def rawRow9616 : Integer.Sparse Key := [(key2481, -6), (key2468, -6), (key2505, -6), (key2468, -6), (key2542, 2), (key2535, 2), (key2553, 2), (key2391, 2), (key2374, 2), (key2542, 2), (key2402, 2), (key2553, 2), (key2439, 2), (key2591, 2), (key2878, 2), (key2770, 2)]

def rawRow9617 : Integer.Sparse Key := [(key2468, -6), (key2505, -6), (key2481, -6), (key2468, -6), (key2535, 2), (key2553, 2), (key2542, 2), (key2402, 2), (key2439, 2), (key2374, 2), (key2553, 2), (key2391, 2), (key2542, 2), (key2770, 2), (key2591, 2), (key2878, 2)]

def rawRow9618 : Integer.Sparse Key := [(key2505, -6), (key2468, -6), (key2481, -6), (key2468, -6), (key2553, 2), (key2535, 2), (key2542, 2), (key2439, 2), (key2402, 2), (key2553, 2), (key2374, 2), (key2542, 2), (key2391, 2), (key2770, 2), (key2878, 2), (key2591, 2)]

def rawRow9619 : Integer.Sparse Key := [(key2481, -6), (key2505, -6), (key2468, -6), (key2468, -6), (key2542, 2), (key2553, 2), (key2535, 2), (key2542, 2), (key2553, 2), (key2391, 2), (key2439, 2), (key2374, 2), (key2402, 2), (key2878, 2), (key2591, 2), (key2770, 2)]

def rawRow9620 : Integer.Sparse Key := [(key2505, -6), (key2481, -6), (key2468, -6), (key2468, -6), (key2553, 2), (key2542, 2), (key2535, 2), (key2553, 2), (key2542, 2), (key2439, 2), (key2391, 2), (key2402, 2), (key2374, 2), (key2878, 2), (key2770, 2), (key2591, 2)]

def rawRow9621 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2809, -2), (key2809, -2), (key2829, -2), (key2829, -2), (key2835, -2), (key2835, -2), (key3012, -2), (key3017, -2), (key3017, -2), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2644, 1), (key2644, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1), (key2860, 1), (key2860, 1), (key2870, 1), (key2870, 1), (key2885, 1), (key2885, 1), (key3023, 1), (key3023, 1), (key3026, 1), (key3026, 1), (key3030, 1), (key3030, 1)]

def rawRow9622 : Integer.Sparse Key := [(key2612, -2), (key2618, -2), (key2616, -2), (key2829, -2), (key2835, -2), (key2809, -2), (key2835, -2), (key2809, -2), (key2829, -2), (key3017, -2), (key3012, -2), (key3017, -2), (key2640, 1), (key2644, 1), (key2632, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3030, 1), (key3023, 1), (key3026, 1)]

def rawRow9623 : Integer.Sparse Key := [(key2618, -2), (key2612, -2), (key2616, -2), (key2835, -2), (key2829, -2), (key2835, -2), (key2809, -2), (key2829, -2), (key2809, -2), (key3017, -2), (key3017, -2), (key3012, -2), (key2644, 1), (key2640, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key2885, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key2860, 1), (key3030, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key3023, 1)]

def rawRow9624 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2612, -2), (key2616, -2), (key2829, -2), (key2829, -2), (key3017, -2), (key3017, -2), (key2621, -2), (key2835, -2), (key2835, -2), (key2706, 1), (key2706, 1), (key2860, 1), (key2860, 1), (key3023, 1), (key3023, 1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2644, 1), (key2644, 1), (key2732, 1), (key2732, 1), (key2885, 1), (key2885, 1)]

def rawRow9625 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2948, -2), (key2960, -2), (key2612, -2), (key2960, -2), (key2616, -2), (key2829, -2), (key2835, -2), (key2621, -2), (key2835, -2), (key2860, 1), (key3023, 1), (key2706, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2885, 1), (key2644, 1), (key2732, 1)]

def rawRow9626 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2960, -2), (key2948, -2), (key2960, -2), (key2612, -2), (key2829, -2), (key2616, -2), (key2835, -2), (key2835, -2), (key2621, -2), (key3023, 1), (key2860, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2885, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2644, 1)]

def rawRow9627 : Integer.Sparse Key := [(key2948, -2), (key2950, -2), (key2960, -2), (key2612, -2), (key2618, -2), (key2805, -2), (key2950, -2), (key2831, -2), (key2960, -2), (key2616, -2), (key2809, -2), (key2829, -2), (key2726, 1), (key2732, 1), (key2870, 1), (key2885, 1), (key3026, 1), (key3030, 1), (key2640, 1), (key2644, 1), (key2860, 1), (key2885, 1), (key3023, 1), (key3030, 1), (key2632, 1), (key2644, 1), (key2706, 1), (key2732, 1), (key3023, 1), (key3026, 1), (key2632, 1), (key2640, 1), (key2706, 1), (key2726, 1), (key2860, 1), (key2870, 1)]

def rawRow9628 : Integer.Sparse Key := [(key2950, -2), (key2948, -2), (key2960, -2), (key2618, -2), (key2612, -2), (key2950, -2), (key2805, -2), (key2960, -2), (key2831, -2), (key2616, -2), (key2829, -2), (key2809, -2), (key2732, 1), (key2726, 1), (key2885, 1), (key2870, 1), (key3030, 1), (key3026, 1), (key2644, 1), (key2640, 1), (key2885, 1), (key2860, 1), (key3030, 1), (key3023, 1), (key2644, 1), (key2632, 1), (key2732, 1), (key2706, 1), (key3026, 1), (key3023, 1), (key2640, 1), (key2632, 1), (key2726, 1), (key2706, 1), (key2870, 1), (key2860, 1)]

def rawRow9629 : Integer.Sparse Key := [(key2948, -2), (key2960, -2), (key2950, -2), (key2805, -2), (key2831, -2), (key2612, -2), (key2960, -2), (key2618, -2), (key2950, -2), (key2809, -2), (key2616, -2), (key2829, -2), (key2870, 1), (key3026, 1), (key2726, 1), (key3030, 1), (key2732, 1), (key2885, 1), (key2860, 1), (key3023, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2706, 1), (key3023, 1), (key2632, 1), (key3026, 1), (key2644, 1), (key2732, 1), (key2706, 1), (key2860, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2726, 1)]

def rawRow9630 : Integer.Sparse Key := [(key2960, -2), (key2948, -2), (key2950, -2), (key2831, -2), (key2805, -2), (key2960, -2), (key2612, -2), (key2950, -2), (key2618, -2), (key2809, -2), (key2829, -2), (key2616, -2), (key3026, 1), (key2870, 1), (key3030, 1), (key2726, 1), (key2885, 1), (key2732, 1), (key3023, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key2885, 1), (key2644, 1), (key3023, 1), (key2706, 1), (key3026, 1), (key2632, 1), (key2732, 1), (key2644, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2726, 1), (key2640, 1)]

def rawRow9631 : Integer.Sparse Key := [(key2950, -2), (key2960, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2618, -2), (key2831, -2), (key2612, -2), (key2805, -2), (key2829, -2), (key2616, -2), (key2809, -2), (key2885, 1), (key3030, 1), (key2732, 1), (key3026, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2640, 1), (key2860, 1), (key2732, 1), (key3026, 1), (key2644, 1), (key3023, 1), (key2632, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2632, 1), (key2706, 1)]

def rawRow9632 : Integer.Sparse Key := [(key2960, -2), (key2950, -2), (key2948, -2), (key2960, -2), (key2950, -2), (key2831, -2), (key2618, -2), (key2805, -2), (key2612, -2), (key2829, -2), (key2809, -2), (key2616, -2), (key3030, 1), (key2885, 1), (key3026, 1), (key2732, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2885, 1), (key3023, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key3026, 1), (key2732, 1), (key3023, 1), (key2644, 1), (key2706, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key2860, 1), (key2640, 1), (key2706, 1), (key2632, 1)]

def rawRow9633 : Integer.Sparse Key := [(key2628, -2), (key2628, -2), (key2641, -2), (key2702, -2), (key2702, -2), (key2972, -2), (key2972, -2), (key2976, -2), (key2976, -2), (key2728, -2), (key2983, -2), (key2983, -2), (key2612, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2660, 1), (key2660, 1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1), (key2794, 1), (key2794, 1), (key2829, 1), (key2829, 1), (key2927, 1), (key2927, 1), (key3010, 1), (key3010, 1), (key3017, 1), (key3017, 1), (key3030, 1), (key3030, 1)]

def rawRow9634 : Integer.Sparse Key := [(key2628, -2), (key2641, -2), (key2628, -2), (key2972, -2), (key2976, -2), (key2702, -2), (key2976, -2), (key2702, -2), (key2972, -2), (key2983, -2), (key2728, -2), (key2983, -2), (key2646, 1), (key2653, 1), (key2612, 1), (key2653, 1), (key2616, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3017, 1)]

def rawRow9635 : Integer.Sparse Key := [(key2641, -2), (key2628, -2), (key2628, -2), (key2976, -2), (key2972, -2), (key2976, -2), (key2702, -2), (key2972, -2), (key2702, -2), (key2983, -2), (key2983, -2), (key2728, -2), (key2653, 1), (key2646, 1), (key2653, 1), (key2612, 1), (key2640, 1), (key2616, 1), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2927, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key2794, 1), (key3030, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key3010, 1)]

def rawRow9636 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2628, -2), (key2628, -2), (key2972, -2), (key2972, -2), (key2983, -2), (key2983, -2), (key2641, -2), (key2976, -2), (key2976, -2), (key2667, 1), (key2667, 1), (key2735, 1), (key2735, 1), (key2747, 1), (key2747, 1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2660, 1), (key2660, 1), (key2758, 1), (key2758, 1), (key2927, 1), (key2927, 1)]

def rawRow9637 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2972, -2), (key2983, -2), (key2628, -2), (key2983, -2), (key2628, -2), (key2972, -2), (key2976, -2), (key2641, -2), (key2976, -2), (key2735, 1), (key2747, 1), (key2667, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2758, 1)]

def rawRow9638 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2983, -2), (key2972, -2), (key2983, -2), (key2628, -2), (key2972, -2), (key2628, -2), (key2976, -2), (key2976, -2), (key2641, -2), (key2747, 1), (key2735, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2667, 1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2927, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2660, 1)]

def rawRow9639 : Integer.Sparse Key := [(key2972, -2), (key2976, -2), (key2983, -2), (key2628, -2), (key2641, -2), (key2702, -2), (key2976, -2), (key2728, -2), (key2983, -2), (key2628, -2), (key2702, -2), (key2972, -2), (key2936, 1), (key2943, 1), (key2948, 1), (key2998, 1), (key2960, 1), (key3000, 1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2612, 1), (key2653, 1), (key2667, 1), (key2943, 1), (key2747, 1), (key2960, 1), (key2616, 1), (key2640, 1), (key2671, 1), (key2726, 1), (key2794, 1), (key2829, 1)]

def rawRow9640 : Integer.Sparse Key := [(key2976, -2), (key2972, -2), (key2983, -2), (key2641, -2), (key2628, -2), (key2976, -2), (key2702, -2), (key2983, -2), (key2728, -2), (key2628, -2), (key2972, -2), (key2702, -2), (key2943, 1), (key2936, 1), (key2998, 1), (key2948, 1), (key3000, 1), (key2960, 1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2653, 1), (key2612, 1), (key2943, 1), (key2667, 1), (key2960, 1), (key2747, 1), (key2640, 1), (key2616, 1), (key2726, 1), (key2671, 1), (key2829, 1), (key2794, 1)]

def rawRow9641 : Integer.Sparse Key := [(key2972, -2), (key2983, -2), (key2976, -2), (key2702, -2), (key2728, -2), (key2628, -2), (key2983, -2), (key2641, -2), (key2976, -2), (key2702, -2), (key2628, -2), (key2972, -2), (key2948, 1), (key2960, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2667, 1), (key2747, 1), (key2612, 1), (key2960, 1), (key2653, 1), (key2943, 1), (key2671, 1), (key2794, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2726, 1)]

def rawRow9642 : Integer.Sparse Key := [(key2983, -2), (key2972, -2), (key2976, -2), (key2728, -2), (key2702, -2), (key2983, -2), (key2628, -2), (key2976, -2), (key2641, -2), (key2702, -2), (key2972, -2), (key2628, -2), (key2960, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2998, 1), (key2943, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2747, 1), (key2667, 1), (key2960, 1), (key2612, 1), (key2943, 1), (key2653, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2726, 1), (key2640, 1)]

def rawRow9643 : Integer.Sparse Key := [(key2976, -2), (key2983, -2), (key2972, -2), (key2976, -2), (key2983, -2), (key2641, -2), (key2728, -2), (key2628, -2), (key2702, -2), (key2972, -2), (key2628, -2), (key2702, -2), (key2998, 1), (key3000, 1), (key2943, 1), (key2960, 1), (key2936, 1), (key2948, 1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2943, 1), (key2960, 1), (key2653, 1), (key2747, 1), (key2612, 1), (key2667, 1), (key2726, 1), (key2829, 1), (key2640, 1), (key2794, 1), (key2616, 1), (key2671, 1)]

def rawRow9644 : Integer.Sparse Key := [(key2983, -2), (key2976, -2), (key2972, -2), (key2983, -2), (key2976, -2), (key2728, -2), (key2641, -2), (key2702, -2), (key2628, -2), (key2972, -2), (key2702, -2), (key2628, -2), (key3000, 1), (key2998, 1), (key2960, 1), (key2943, 1), (key2948, 1), (key2936, 1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2960, 1), (key2943, 1), (key2747, 1), (key2653, 1), (key2667, 1), (key2612, 1), (key2829, 1), (key2726, 1), (key2794, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

def rawRow9645 : Integer.Sparse Key := [(key2769, -24), (key2590, 6), (key2846, 6), (key2877, 6), (key2877, 6)]

def rawRow9646 : Integer.Sparse Key := [(key2769, -24), (key2590, 6), (key2877, 6), (key2846, 6), (key2877, 6)]

def rawRow9647 : Integer.Sparse Key := [(key2769, -24), (key2590, 6), (key2877, 6), (key2877, 6), (key2846, 6)]

def rawRow9648 : Integer.Sparse Key := [(key2769, -24), (key2846, 6), (key2590, 6), (key2877, 6), (key2877, 6)]

def rawRow9649 : Integer.Sparse Key := [(key2769, -24), (key2846, 6), (key2877, 6), (key2590, 6), (key2877, 6)]

def rawRow9650 : Integer.Sparse Key := [(key2769, -24), (key2846, 6), (key2877, 6), (key2877, 6), (key2590, 6)]

def rawRow9651 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2590, 6), (key2846, 6), (key2877, 6)]

def rawRow9652 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2590, 6), (key2877, 6), (key2846, 6)]

def rawRow9653 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2846, 6), (key2590, 6), (key2877, 6)]

def rawRow9654 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2846, 6), (key2877, 6), (key2590, 6)]

def rawRow9655 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2877, 6), (key2590, 6), (key2846, 6)]

def rawRow9656 : Integer.Sparse Key := [(key2769, -24), (key2877, 6), (key2877, 6), (key2846, 6), (key2590, 6)]

def rawRow9657 : Integer.Sparse Key := [(key2846, -24), (key2590, 6), (key2769, 6), (key2877, 6), (key2877, 6)]

def rawRow9658 : Integer.Sparse Key := [(key2846, -24), (key2590, 6), (key2877, 6), (key2769, 6), (key2877, 6)]

def rawRow9659 : Integer.Sparse Key := [(key2846, -24), (key2590, 6), (key2877, 6), (key2877, 6), (key2769, 6)]

def rawRow9660 : Integer.Sparse Key := [(key2846, -24), (key2769, 6), (key2590, 6), (key2877, 6), (key2877, 6)]

def rawRow9661 : Integer.Sparse Key := [(key2846, -24), (key2769, 6), (key2877, 6), (key2590, 6), (key2877, 6)]

def rawRow9662 : Integer.Sparse Key := [(key2846, -24), (key2769, 6), (key2877, 6), (key2877, 6), (key2590, 6)]

def rawRow9663 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2590, 6), (key2769, 6), (key2877, 6)]

def rawRow9664 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2590, 6), (key2877, 6), (key2769, 6)]

def rawRow9665 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2769, 6), (key2590, 6), (key2877, 6)]

def rawRow9666 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2769, 6), (key2877, 6), (key2590, 6)]

def rawRow9667 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2877, 6), (key2590, 6), (key2769, 6)]

def rawRow9668 : Integer.Sparse Key := [(key2846, -24), (key2877, 6), (key2877, 6), (key2769, 6), (key2590, 6)]

def rawRow9669 : Integer.Sparse Key := [(key2667, -2), (key2667, -2), (key2673, -2), (key2702, -2), (key2702, -2), (key2735, -2), (key2735, -2), (key2737, -2), (key2737, -2), (key2728, -2), (key2747, -2), (key2747, -2), (key2612, 2), (key2616, 2), (key2621, 2), (key2809, 2), (key2809, 2), (key2829, 2), (key2829, 2), (key2835, 2), (key2835, 2), (key3012, 2), (key3017, 2), (key3017, 2)]

def rawRow9670 : Integer.Sparse Key := [(key2667, -2), (key2673, -2), (key2667, -2), (key2735, -2), (key2737, -2), (key2702, -2), (key2737, -2), (key2702, -2), (key2735, -2), (key2747, -2), (key2728, -2), (key2747, -2), (key2612, 2), (key2618, 2), (key2616, 2), (key2829, 2), (key2835, 2), (key2809, 2), (key2835, 2), (key2809, 2), (key2829, 2), (key3017, 2), (key3012, 2), (key3017, 2)]

def rawRow9671 : Integer.Sparse Key := [(key2673, -2), (key2667, -2), (key2667, -2), (key2737, -2), (key2735, -2), (key2737, -2), (key2702, -2), (key2735, -2), (key2702, -2), (key2747, -2), (key2747, -2), (key2728, -2), (key2618, 2), (key2612, 2), (key2616, 2), (key2835, 2), (key2829, 2), (key2835, 2), (key2809, 2), (key2829, 2), (key2809, 2), (key3017, 2), (key3017, 2), (key3012, 2)]

def rawRow9672 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2667, -2), (key2667, -2), (key2735, -2), (key2735, -2), (key2747, -2), (key2747, -2), (key2673, -2), (key2737, -2), (key2737, -2), (key2805, 2), (key2805, 2), (key2831, 2), (key2612, 2), (key2616, 2), (key2829, 2), (key2829, 2), (key3017, 2), (key3017, 2), (key2621, 2), (key2835, 2), (key2835, 2)]

def rawRow9673 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2735, -2), (key2747, -2), (key2667, -2), (key2747, -2), (key2667, -2), (key2735, -2), (key2737, -2), (key2673, -2), (key2737, -2), (key2805, 2), (key2831, 2), (key2805, 2), (key2948, 2), (key2960, 2), (key2612, 2), (key2960, 2), (key2616, 2), (key2829, 2), (key2835, 2), (key2621, 2), (key2835, 2)]

def rawRow9674 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2747, -2), (key2735, -2), (key2747, -2), (key2667, -2), (key2735, -2), (key2667, -2), (key2737, -2), (key2737, -2), (key2673, -2), (key2831, 2), (key2805, 2), (key2805, 2), (key2960, 2), (key2948, 2), (key2960, 2), (key2612, 2), (key2829, 2), (key2616, 2), (key2835, 2), (key2835, 2), (key2621, 2)]

def rawRow9675 : Integer.Sparse Key := [(key2735, -2), (key2737, -2), (key2747, -2), (key2667, -2), (key2673, -2), (key2702, -2), (key2737, -2), (key2728, -2), (key2747, -2), (key2667, -2), (key2702, -2), (key2735, -2), (key2948, 2), (key2950, 2), (key2960, 2), (key2612, 2), (key2618, 2), (key2805, 2), (key2950, 2), (key2831, 2), (key2960, 2), (key2616, 2), (key2809, 2), (key2829, 2)]

def rawRow9676 : Integer.Sparse Key := [(key2737, -2), (key2735, -2), (key2747, -2), (key2673, -2), (key2667, -2), (key2737, -2), (key2702, -2), (key2747, -2), (key2728, -2), (key2667, -2), (key2735, -2), (key2702, -2), (key2950, 2), (key2948, 2), (key2960, 2), (key2618, 2), (key2612, 2), (key2950, 2), (key2805, 2), (key2960, 2), (key2831, 2), (key2616, 2), (key2829, 2), (key2809, 2)]

def rawRow9677 : Integer.Sparse Key := [(key2735, -2), (key2747, -2), (key2737, -2), (key2702, -2), (key2728, -2), (key2667, -2), (key2747, -2), (key2673, -2), (key2737, -2), (key2702, -2), (key2667, -2), (key2735, -2), (key2948, 2), (key2960, 2), (key2950, 2), (key2805, 2), (key2831, 2), (key2612, 2), (key2960, 2), (key2618, 2), (key2950, 2), (key2809, 2), (key2616, 2), (key2829, 2)]

def rawRow9678 : Integer.Sparse Key := [(key2747, -2), (key2735, -2), (key2737, -2), (key2728, -2), (key2702, -2), (key2747, -2), (key2667, -2), (key2737, -2), (key2673, -2), (key2702, -2), (key2735, -2), (key2667, -2), (key2960, 2), (key2948, 2), (key2950, 2), (key2831, 2), (key2805, 2), (key2960, 2), (key2612, 2), (key2950, 2), (key2618, 2), (key2809, 2), (key2829, 2), (key2616, 2)]

def rawRow9679 : Integer.Sparse Key := [(key2737, -2), (key2747, -2), (key2735, -2), (key2737, -2), (key2747, -2), (key2673, -2), (key2728, -2), (key2667, -2), (key2702, -2), (key2735, -2), (key2667, -2), (key2702, -2), (key2950, 2), (key2960, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2618, 2), (key2831, 2), (key2612, 2), (key2805, 2), (key2829, 2), (key2616, 2), (key2809, 2)]

def rawRow9680 : Integer.Sparse Key := [(key2747, -2), (key2737, -2), (key2735, -2), (key2747, -2), (key2737, -2), (key2728, -2), (key2673, -2), (key2702, -2), (key2667, -2), (key2735, -2), (key2702, -2), (key2667, -2), (key2960, 2), (key2950, 2), (key2948, 2), (key2960, 2), (key2950, 2), (key2831, 2), (key2618, 2), (key2805, 2), (key2612, 2), (key2829, 2), (key2809, 2), (key2616, 2)]

def rawRow9681 : Integer.Sparse Key := [(key2782, -2), (key2782, -2), (key2795, -2), (key2805, -2), (key2805, -2), (key2893, -2), (key2893, -2), (key2897, -2), (key2897, -2), (key2831, -2), (key2904, -2), (key2904, -2), (key2628, 2), (key2628, 2), (key2641, 2), (key2702, 2), (key2702, 2), (key2972, 2), (key2972, 2), (key2976, 2), (key2976, 2), (key2728, 2), (key2983, 2), (key2983, 2)]

def rawRow9682 : Integer.Sparse Key := [(key2782, -2), (key2795, -2), (key2782, -2), (key2893, -2), (key2897, -2), (key2805, -2), (key2897, -2), (key2805, -2), (key2893, -2), (key2904, -2), (key2831, -2), (key2904, -2), (key2628, 2), (key2641, 2), (key2628, 2), (key2972, 2), (key2976, 2), (key2702, 2), (key2976, 2), (key2702, 2), (key2972, 2), (key2983, 2), (key2728, 2), (key2983, 2)]

def rawRow9683 : Integer.Sparse Key := [(key2795, -2), (key2782, -2), (key2782, -2), (key2897, -2), (key2893, -2), (key2897, -2), (key2805, -2), (key2893, -2), (key2805, -2), (key2904, -2), (key2904, -2), (key2831, -2), (key2641, 2), (key2628, 2), (key2628, 2), (key2976, 2), (key2972, 2), (key2976, 2), (key2702, 2), (key2972, 2), (key2702, 2), (key2983, 2), (key2983, 2), (key2728, 2)]

def rawRow9684 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2782, -2), (key2782, -2), (key2893, -2), (key2893, -2), (key2904, -2), (key2904, -2), (key2795, -2), (key2897, -2), (key2897, -2), (key2702, 2), (key2702, 2), (key2728, 2), (key2628, 2), (key2628, 2), (key2972, 2), (key2972, 2), (key2983, 2), (key2983, 2), (key2641, 2), (key2976, 2), (key2976, 2)]

def rawRow9685 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2893, -2), (key2904, -2), (key2782, -2), (key2904, -2), (key2782, -2), (key2893, -2), (key2897, -2), (key2795, -2), (key2897, -2), (key2702, 2), (key2728, 2), (key2702, 2), (key2972, 2), (key2983, 2), (key2628, 2), (key2983, 2), (key2628, 2), (key2972, 2), (key2976, 2), (key2641, 2), (key2976, 2)]

def rawRow9686 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2904, -2), (key2893, -2), (key2904, -2), (key2782, -2), (key2893, -2), (key2782, -2), (key2897, -2), (key2897, -2), (key2795, -2), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, 2), (key2972, 2), (key2983, 2), (key2628, 2), (key2972, 2), (key2628, 2), (key2976, 2), (key2976, 2), (key2641, 2)]

def rawRow9687 : Integer.Sparse Key := [(key2893, -2), (key2897, -2), (key2904, -2), (key2782, -2), (key2795, -2), (key2805, -2), (key2897, -2), (key2831, -2), (key2904, -2), (key2782, -2), (key2805, -2), (key2893, -2), (key2972, 2), (key2976, 2), (key2983, 2), (key2628, 2), (key2641, 2), (key2702, 2), (key2976, 2), (key2728, 2), (key2983, 2), (key2628, 2), (key2702, 2), (key2972, 2)]

def rawRow9688 : Integer.Sparse Key := [(key2897, -2), (key2893, -2), (key2904, -2), (key2795, -2), (key2782, -2), (key2897, -2), (key2805, -2), (key2904, -2), (key2831, -2), (key2782, -2), (key2893, -2), (key2805, -2), (key2976, 2), (key2972, 2), (key2983, 2), (key2641, 2), (key2628, 2), (key2976, 2), (key2702, 2), (key2983, 2), (key2728, 2), (key2628, 2), (key2972, 2), (key2702, 2)]

def rawRow9689 : Integer.Sparse Key := [(key2893, -2), (key2904, -2), (key2897, -2), (key2805, -2), (key2831, -2), (key2782, -2), (key2904, -2), (key2795, -2), (key2897, -2), (key2805, -2), (key2782, -2), (key2893, -2), (key2972, 2), (key2983, 2), (key2976, 2), (key2702, 2), (key2728, 2), (key2628, 2), (key2983, 2), (key2641, 2), (key2976, 2), (key2702, 2), (key2628, 2), (key2972, 2)]

def rawRow9690 : Integer.Sparse Key := [(key2904, -2), (key2893, -2), (key2897, -2), (key2831, -2), (key2805, -2), (key2904, -2), (key2782, -2), (key2897, -2), (key2795, -2), (key2805, -2), (key2893, -2), (key2782, -2), (key2983, 2), (key2972, 2), (key2976, 2), (key2728, 2), (key2702, 2), (key2983, 2), (key2628, 2), (key2976, 2), (key2641, 2), (key2702, 2), (key2972, 2), (key2628, 2)]

def rawRow9691 : Integer.Sparse Key := [(key2897, -2), (key2904, -2), (key2893, -2), (key2897, -2), (key2904, -2), (key2795, -2), (key2831, -2), (key2782, -2), (key2805, -2), (key2893, -2), (key2782, -2), (key2805, -2), (key2976, 2), (key2983, 2), (key2972, 2), (key2976, 2), (key2983, 2), (key2641, 2), (key2728, 2), (key2628, 2), (key2702, 2), (key2972, 2), (key2628, 2), (key2702, 2)]

def rawRow9692 : Integer.Sparse Key := [(key2904, -2), (key2897, -2), (key2893, -2), (key2904, -2), (key2897, -2), (key2831, -2), (key2795, -2), (key2805, -2), (key2782, -2), (key2893, -2), (key2805, -2), (key2782, -2), (key2983, 2), (key2976, 2), (key2972, 2), (key2983, 2), (key2976, 2), (key2728, 2), (key2641, 2), (key2702, 2), (key2628, 2), (key2972, 2), (key2702, 2), (key2628, 2)]

def rawRow9693 : Integer.Sparse Key := [(key1296, -2), (key1296, -2), (key1303, -2), (key1573, -2), (key1573, -2), (key1788, -2), (key1788, -2), (key1791, -2), (key1791, -2), (key1597, -2), (key1799, -2), (key1799, -2), (key1316, 1), (key1316, 1), (key1337, 1), (key1337, 1), (key1340, 1), (key1340, 1), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1775, 1), (key1775, 1), (key1655, 1), (key1655, 1), (key1813, 1), (key1813, 1), (key1840, 1), (key1840, 1), (key1668, 1), (key1668, 1), (key1826, 1), (key1826, 1), (key1845, 1), (key1845, 1)]

def rawRow9694 : Integer.Sparse Key := [(key1296, -2), (key1303, -2), (key1296, -2), (key1788, -2), (key1791, -2), (key1573, -2), (key1791, -2), (key1573, -2), (key1788, -2), (key1799, -2), (key1597, -2), (key1799, -2), (key1337, 1), (key1340, 1), (key1316, 1), (key1340, 1), (key1316, 1), (key1337, 1), (key1772, 1), (key1775, 1), (key1546, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1813, 1), (key1840, 1), (key1655, 1), (key1840, 1), (key1655, 1), (key1813, 1), (key1826, 1), (key1845, 1), (key1668, 1), (key1845, 1), (key1668, 1), (key1826, 1)]

def rawRow9695 : Integer.Sparse Key := [(key1303, -2), (key1296, -2), (key1296, -2), (key1791, -2), (key1788, -2), (key1791, -2), (key1573, -2), (key1788, -2), (key1573, -2), (key1799, -2), (key1799, -2), (key1597, -2), (key1340, 1), (key1337, 1), (key1340, 1), (key1316, 1), (key1337, 1), (key1316, 1), (key1775, 1), (key1772, 1), (key1775, 1), (key1546, 1), (key1772, 1), (key1546, 1), (key1840, 1), (key1813, 1), (key1840, 1), (key1655, 1), (key1813, 1), (key1655, 1), (key1845, 1), (key1826, 1), (key1845, 1), (key1668, 1), (key1826, 1), (key1668, 1)]

def rawRow9696 : Integer.Sparse Key := [(key1573, -2), (key1573, -2), (key1597, -2), (key1296, -2), (key1296, -2), (key1788, -2), (key1788, -2), (key1799, -2), (key1799, -2), (key1303, -2), (key1791, -2), (key1791, -2), (key1546, 1), (key1546, 1), (key1655, 1), (key1655, 1), (key1668, 1), (key1668, 1), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1826, 1), (key1826, 1), (key1337, 1), (key1337, 1), (key1772, 1), (key1772, 1), (key1845, 1), (key1845, 1), (key1340, 1), (key1340, 1), (key1775, 1), (key1775, 1), (key1840, 1), (key1840, 1)]

def rawRow9697 : Integer.Sparse Key := [(key1573, -2), (key1597, -2), (key1573, -2), (key1788, -2), (key1799, -2), (key1296, -2), (key1799, -2), (key1296, -2), (key1788, -2), (key1791, -2), (key1303, -2), (key1791, -2), (key1655, 1), (key1668, 1), (key1546, 1), (key1668, 1), (key1546, 1), (key1655, 1), (key1813, 1), (key1826, 1), (key1316, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1772, 1), (key1845, 1), (key1337, 1), (key1845, 1), (key1337, 1), (key1772, 1), (key1775, 1), (key1840, 1), (key1340, 1), (key1840, 1), (key1340, 1), (key1775, 1)]

def rawRow9698 : Integer.Sparse Key := [(key1597, -2), (key1573, -2), (key1573, -2), (key1799, -2), (key1788, -2), (key1799, -2), (key1296, -2), (key1788, -2), (key1296, -2), (key1791, -2), (key1791, -2), (key1303, -2), (key1668, 1), (key1655, 1), (key1668, 1), (key1546, 1), (key1655, 1), (key1546, 1), (key1826, 1), (key1813, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1845, 1), (key1772, 1), (key1845, 1), (key1337, 1), (key1772, 1), (key1337, 1), (key1840, 1), (key1775, 1), (key1840, 1), (key1340, 1), (key1775, 1), (key1340, 1)]

def rawRow9699 : Integer.Sparse Key := [(key1788, -2), (key1791, -2), (key1799, -2), (key1296, -2), (key1303, -2), (key1573, -2), (key1791, -2), (key1597, -2), (key1799, -2), (key1296, -2), (key1573, -2), (key1788, -2), (key1772, 1), (key1775, 1), (key1813, 1), (key1840, 1), (key1826, 1), (key1845, 1), (key1337, 1), (key1340, 1), (key1655, 1), (key1840, 1), (key1668, 1), (key1845, 1), (key1316, 1), (key1340, 1), (key1546, 1), (key1775, 1), (key1668, 1), (key1826, 1), (key1316, 1), (key1337, 1), (key1546, 1), (key1772, 1), (key1655, 1), (key1813, 1)]

def rawRow9700 : Integer.Sparse Key := [(key1791, -2), (key1788, -2), (key1799, -2), (key1303, -2), (key1296, -2), (key1791, -2), (key1573, -2), (key1799, -2), (key1597, -2), (key1296, -2), (key1788, -2), (key1573, -2), (key1775, 1), (key1772, 1), (key1840, 1), (key1813, 1), (key1845, 1), (key1826, 1), (key1340, 1), (key1337, 1), (key1840, 1), (key1655, 1), (key1845, 1), (key1668, 1), (key1340, 1), (key1316, 1), (key1775, 1), (key1546, 1), (key1826, 1), (key1668, 1), (key1337, 1), (key1316, 1), (key1772, 1), (key1546, 1), (key1813, 1), (key1655, 1)]

def rawRow9701 : Integer.Sparse Key := [(key1788, -2), (key1799, -2), (key1791, -2), (key1573, -2), (key1597, -2), (key1296, -2), (key1799, -2), (key1303, -2), (key1791, -2), (key1573, -2), (key1296, -2), (key1788, -2), (key1813, 1), (key1826, 1), (key1772, 1), (key1845, 1), (key1775, 1), (key1840, 1), (key1655, 1), (key1668, 1), (key1337, 1), (key1845, 1), (key1340, 1), (key1840, 1), (key1546, 1), (key1668, 1), (key1316, 1), (key1826, 1), (key1340, 1), (key1775, 1), (key1546, 1), (key1655, 1), (key1316, 1), (key1813, 1), (key1337, 1), (key1772, 1)]

def rawRow9702 : Integer.Sparse Key := [(key1799, -2), (key1788, -2), (key1791, -2), (key1597, -2), (key1573, -2), (key1799, -2), (key1296, -2), (key1791, -2), (key1303, -2), (key1573, -2), (key1788, -2), (key1296, -2), (key1826, 1), (key1813, 1), (key1845, 1), (key1772, 1), (key1840, 1), (key1775, 1), (key1668, 1), (key1655, 1), (key1845, 1), (key1337, 1), (key1840, 1), (key1340, 1), (key1668, 1), (key1546, 1), (key1826, 1), (key1316, 1), (key1775, 1), (key1340, 1), (key1655, 1), (key1546, 1), (key1813, 1), (key1316, 1), (key1772, 1), (key1337, 1)]

def rawRow9703 : Integer.Sparse Key := [(key1791, -2), (key1799, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1303, -2), (key1597, -2), (key1296, -2), (key1573, -2), (key1788, -2), (key1296, -2), (key1573, -2), (key1840, 1), (key1845, 1), (key1775, 1), (key1826, 1), (key1772, 1), (key1813, 1), (key1840, 1), (key1845, 1), (key1340, 1), (key1668, 1), (key1337, 1), (key1655, 1), (key1775, 1), (key1826, 1), (key1340, 1), (key1668, 1), (key1316, 1), (key1546, 1), (key1772, 1), (key1813, 1), (key1337, 1), (key1655, 1), (key1316, 1), (key1546, 1)]

def rawRow9704 : Integer.Sparse Key := [(key1799, -2), (key1791, -2), (key1788, -2), (key1799, -2), (key1791, -2), (key1597, -2), (key1303, -2), (key1573, -2), (key1296, -2), (key1788, -2), (key1573, -2), (key1296, -2), (key1845, 1), (key1840, 1), (key1826, 1), (key1775, 1), (key1813, 1), (key1772, 1), (key1845, 1), (key1840, 1), (key1668, 1), (key1340, 1), (key1655, 1), (key1337, 1), (key1826, 1), (key1775, 1), (key1668, 1), (key1340, 1), (key1546, 1), (key1316, 1), (key1813, 1), (key1772, 1), (key1655, 1), (key1337, 1), (key1546, 1), (key1316, 1)]

def rawRow9705 : Integer.Sparse Key := [(key1316, -2), (key1316, -2), (key1330, -2), (key1424, -2), (key1424, -2), (key1813, -2), (key1813, -2), (key1818, -2), (key1818, -2), (key1448, -2), (key1826, -2), (key1826, -2), (key1296, 1), (key1296, 1), (key1337, 1), (key1337, 1), (key1346, 1), (key1346, 1), (key1391, 1), (key1391, 1), (key1772, 1), (key1772, 1), (key1781, 1), (key1781, 1), (key1455, 1), (key1455, 1), (key1788, 1), (key1788, 1), (key1842, 1), (key1842, 1), (key1467, 1), (key1467, 1), (key1799, 1), (key1799, 1), (key1845, 1), (key1845, 1)]

def rawRow9706 : Integer.Sparse Key := [(key1316, -2), (key1330, -2), (key1316, -2), (key1813, -2), (key1818, -2), (key1424, -2), (key1818, -2), (key1424, -2), (key1813, -2), (key1826, -2), (key1448, -2), (key1826, -2), (key1337, 1), (key1346, 1), (key1296, 1), (key1346, 1), (key1296, 1), (key1337, 1), (key1772, 1), (key1781, 1), (key1391, 1), (key1781, 1), (key1391, 1), (key1772, 1), (key1788, 1), (key1842, 1), (key1455, 1), (key1842, 1), (key1455, 1), (key1788, 1), (key1799, 1), (key1845, 1), (key1467, 1), (key1845, 1), (key1467, 1), (key1799, 1)]

def rawRow9707 : Integer.Sparse Key := [(key1330, -2), (key1316, -2), (key1316, -2), (key1818, -2), (key1813, -2), (key1818, -2), (key1424, -2), (key1813, -2), (key1424, -2), (key1826, -2), (key1826, -2), (key1448, -2), (key1346, 1), (key1337, 1), (key1346, 1), (key1296, 1), (key1337, 1), (key1296, 1), (key1781, 1), (key1772, 1), (key1781, 1), (key1391, 1), (key1772, 1), (key1391, 1), (key1842, 1), (key1788, 1), (key1842, 1), (key1455, 1), (key1788, 1), (key1455, 1), (key1845, 1), (key1799, 1), (key1845, 1), (key1467, 1), (key1799, 1), (key1467, 1)]

def rawRow9708 : Integer.Sparse Key := [(key1424, -2), (key1424, -2), (key1448, -2), (key1316, -2), (key1316, -2), (key1813, -2), (key1813, -2), (key1826, -2), (key1826, -2), (key1330, -2), (key1818, -2), (key1818, -2), (key1391, 1), (key1391, 1), (key1455, 1), (key1455, 1), (key1467, 1), (key1467, 1), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1799, 1), (key1799, 1), (key1337, 1), (key1337, 1), (key1772, 1), (key1772, 1), (key1845, 1), (key1845, 1), (key1346, 1), (key1346, 1), (key1781, 1), (key1781, 1), (key1842, 1), (key1842, 1)]

def rawRow9709 : Integer.Sparse Key := [(key1424, -2), (key1448, -2), (key1424, -2), (key1813, -2), (key1826, -2), (key1316, -2), (key1826, -2), (key1316, -2), (key1813, -2), (key1818, -2), (key1330, -2), (key1818, -2), (key1455, 1), (key1467, 1), (key1391, 1), (key1467, 1), (key1391, 1), (key1455, 1), (key1788, 1), (key1799, 1), (key1296, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1772, 1), (key1845, 1), (key1337, 1), (key1845, 1), (key1337, 1), (key1772, 1), (key1781, 1), (key1842, 1), (key1346, 1), (key1842, 1), (key1346, 1), (key1781, 1)]

def rawRow9710 : Integer.Sparse Key := [(key1448, -2), (key1424, -2), (key1424, -2), (key1826, -2), (key1813, -2), (key1826, -2), (key1316, -2), (key1813, -2), (key1316, -2), (key1818, -2), (key1818, -2), (key1330, -2), (key1467, 1), (key1455, 1), (key1467, 1), (key1391, 1), (key1455, 1), (key1391, 1), (key1799, 1), (key1788, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1845, 1), (key1772, 1), (key1845, 1), (key1337, 1), (key1772, 1), (key1337, 1), (key1842, 1), (key1781, 1), (key1842, 1), (key1346, 1), (key1781, 1), (key1346, 1)]

def rawRow9711 : Integer.Sparse Key := [(key1813, -2), (key1818, -2), (key1826, -2), (key1316, -2), (key1330, -2), (key1424, -2), (key1818, -2), (key1448, -2), (key1826, -2), (key1316, -2), (key1424, -2), (key1813, -2), (key1772, 1), (key1781, 1), (key1788, 1), (key1842, 1), (key1799, 1), (key1845, 1), (key1337, 1), (key1346, 1), (key1455, 1), (key1842, 1), (key1467, 1), (key1845, 1), (key1296, 1), (key1346, 1), (key1391, 1), (key1781, 1), (key1467, 1), (key1799, 1), (key1296, 1), (key1337, 1), (key1391, 1), (key1772, 1), (key1455, 1), (key1788, 1)]

def rawRow9712 : Integer.Sparse Key := [(key1818, -2), (key1813, -2), (key1826, -2), (key1330, -2), (key1316, -2), (key1818, -2), (key1424, -2), (key1826, -2), (key1448, -2), (key1316, -2), (key1813, -2), (key1424, -2), (key1781, 1), (key1772, 1), (key1842, 1), (key1788, 1), (key1845, 1), (key1799, 1), (key1346, 1), (key1337, 1), (key1842, 1), (key1455, 1), (key1845, 1), (key1467, 1), (key1346, 1), (key1296, 1), (key1781, 1), (key1391, 1), (key1799, 1), (key1467, 1), (key1337, 1), (key1296, 1), (key1772, 1), (key1391, 1), (key1788, 1), (key1455, 1)]

def rawRow9713 : Integer.Sparse Key := [(key1813, -2), (key1826, -2), (key1818, -2), (key1424, -2), (key1448, -2), (key1316, -2), (key1826, -2), (key1330, -2), (key1818, -2), (key1424, -2), (key1316, -2), (key1813, -2), (key1788, 1), (key1799, 1), (key1772, 1), (key1845, 1), (key1781, 1), (key1842, 1), (key1455, 1), (key1467, 1), (key1337, 1), (key1845, 1), (key1346, 1), (key1842, 1), (key1391, 1), (key1467, 1), (key1296, 1), (key1799, 1), (key1346, 1), (key1781, 1), (key1391, 1), (key1455, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1772, 1)]

def rawRow9714 : Integer.Sparse Key := [(key1826, -2), (key1813, -2), (key1818, -2), (key1448, -2), (key1424, -2), (key1826, -2), (key1316, -2), (key1818, -2), (key1330, -2), (key1424, -2), (key1813, -2), (key1316, -2), (key1799, 1), (key1788, 1), (key1845, 1), (key1772, 1), (key1842, 1), (key1781, 1), (key1467, 1), (key1455, 1), (key1845, 1), (key1337, 1), (key1842, 1), (key1346, 1), (key1467, 1), (key1391, 1), (key1799, 1), (key1296, 1), (key1781, 1), (key1346, 1), (key1455, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1772, 1), (key1337, 1)]

def rawRow9715 : Integer.Sparse Key := [(key1818, -2), (key1826, -2), (key1813, -2), (key1818, -2), (key1826, -2), (key1330, -2), (key1448, -2), (key1316, -2), (key1424, -2), (key1813, -2), (key1316, -2), (key1424, -2), (key1842, 1), (key1845, 1), (key1781, 1), (key1799, 1), (key1772, 1), (key1788, 1), (key1842, 1), (key1845, 1), (key1346, 1), (key1467, 1), (key1337, 1), (key1455, 1), (key1781, 1), (key1799, 1), (key1346, 1), (key1467, 1), (key1296, 1), (key1391, 1), (key1772, 1), (key1788, 1), (key1337, 1), (key1455, 1), (key1296, 1), (key1391, 1)]

def rawRow9716 : Integer.Sparse Key := [(key1826, -2), (key1818, -2), (key1813, -2), (key1826, -2), (key1818, -2), (key1448, -2), (key1330, -2), (key1424, -2), (key1316, -2), (key1813, -2), (key1424, -2), (key1316, -2), (key1845, 1), (key1842, 1), (key1799, 1), (key1781, 1), (key1788, 1), (key1772, 1), (key1845, 1), (key1842, 1), (key1467, 1), (key1346, 1), (key1455, 1), (key1337, 1), (key1799, 1), (key1781, 1), (key1467, 1), (key1346, 1), (key1391, 1), (key1296, 1), (key1788, 1), (key1772, 1), (key1455, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

def rawRow9717 : Integer.Sparse Key := [(key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2644, 1), (key2644, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1), (key2860, 1), (key2860, 1), (key2870, 1), (key2870, 1), (key2885, 1), (key2885, 1), (key3023, 1), (key3023, 1), (key3026, 1), (key3026, 1), (key3030, 1), (key3030, 1), (key2658, -2), (key2660, -2), (key2660, -2), (key2753, -2), (key2758, -2), (key2758, -2), (key2920, -2), (key2920, -2), (key2923, -2), (key2923, -2), (key2927, -2), (key2927, -2)]

def rawRow9718 : Integer.Sparse Key := [(key2640, 1), (key2644, 1), (key2632, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key2660, -2), (key2658, -2), (key2660, -2), (key2758, -2), (key2753, -2), (key2758, -2), (key2923, -2), (key2927, -2), (key2920, -2), (key2927, -2), (key2920, -2), (key2923, -2)]

def rawRow9719 : Integer.Sparse Key := [(key2644, 1), (key2640, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key2885, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key2860, 1), (key3030, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key3023, 1), (key2660, -2), (key2660, -2), (key2658, -2), (key2758, -2), (key2758, -2), (key2753, -2), (key2927, -2), (key2923, -2), (key2927, -2), (key2920, -2), (key2923, -2), (key2920, -2)]

def rawRow9720 : Integer.Sparse Key := [(key2706, 1), (key2706, 1), (key2860, 1), (key2860, 1), (key3023, 1), (key3023, 1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2644, 1), (key2644, 1), (key2732, 1), (key2732, 1), (key2885, 1), (key2885, 1), (key2753, -2), (key2920, -2), (key2920, -2), (key2658, -2), (key2923, -2), (key2923, -2), (key2660, -2), (key2660, -2), (key2758, -2), (key2758, -2), (key2927, -2), (key2927, -2)]

def rawRow9721 : Integer.Sparse Key := [(key2860, 1), (key3023, 1), (key2706, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2920, -2), (key2753, -2), (key2920, -2), (key2923, -2), (key2658, -2), (key2923, -2), (key2758, -2), (key2927, -2), (key2660, -2), (key2927, -2), (key2660, -2), (key2758, -2)]

def rawRow9722 : Integer.Sparse Key := [(key3023, 1), (key2860, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2885, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2644, 1), (key2920, -2), (key2920, -2), (key2753, -2), (key2923, -2), (key2923, -2), (key2658, -2), (key2927, -2), (key2758, -2), (key2927, -2), (key2660, -2), (key2758, -2), (key2660, -2)]

def rawRow9723 : Integer.Sparse Key := [(key2726, 1), (key2732, 1), (key2870, 1), (key2885, 1), (key3026, 1), (key3030, 1), (key2640, 1), (key2644, 1), (key2860, 1), (key2885, 1), (key3023, 1), (key3030, 1), (key2632, 1), (key2644, 1), (key2706, 1), (key2732, 1), (key3023, 1), (key3026, 1), (key2632, 1), (key2640, 1), (key2706, 1), (key2726, 1), (key2860, 1), (key2870, 1), (key2758, -2), (key2923, -2), (key2927, -2), (key2660, -2), (key2920, -2), (key2927, -2), (key2658, -2), (key2660, -2), (key2753, -2), (key2758, -2), (key2920, -2), (key2923, -2)]

def rawRow9724 : Integer.Sparse Key := [(key2732, 1), (key2726, 1), (key2885, 1), (key2870, 1), (key3030, 1), (key3026, 1), (key2644, 1), (key2640, 1), (key2885, 1), (key2860, 1), (key3030, 1), (key3023, 1), (key2644, 1), (key2632, 1), (key2732, 1), (key2706, 1), (key3026, 1), (key3023, 1), (key2640, 1), (key2632, 1), (key2726, 1), (key2706, 1), (key2870, 1), (key2860, 1), (key2758, -2), (key2927, -2), (key2923, -2), (key2660, -2), (key2927, -2), (key2920, -2), (key2660, -2), (key2658, -2), (key2758, -2), (key2753, -2), (key2923, -2), (key2920, -2)]

def rawRow9725 : Integer.Sparse Key := [(key2870, 1), (key3026, 1), (key2726, 1), (key3030, 1), (key2732, 1), (key2885, 1), (key2860, 1), (key3023, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2706, 1), (key3023, 1), (key2632, 1), (key3026, 1), (key2644, 1), (key2732, 1), (key2706, 1), (key2860, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2726, 1), (key2923, -2), (key2758, -2), (key2927, -2), (key2920, -2), (key2660, -2), (key2927, -2), (key2753, -2), (key2920, -2), (key2658, -2), (key2923, -2), (key2660, -2), (key2758, -2)]

def rawRow9726 : Integer.Sparse Key := [(key3026, 1), (key2870, 1), (key3030, 1), (key2726, 1), (key2885, 1), (key2732, 1), (key3023, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key2885, 1), (key2644, 1), (key3023, 1), (key2706, 1), (key3026, 1), (key2632, 1), (key2732, 1), (key2644, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2726, 1), (key2640, 1), (key2923, -2), (key2927, -2), (key2758, -2), (key2920, -2), (key2927, -2), (key2660, -2), (key2920, -2), (key2753, -2), (key2923, -2), (key2658, -2), (key2758, -2), (key2660, -2)]

def rawRow9727 : Integer.Sparse Key := [(key2885, 1), (key3030, 1), (key2732, 1), (key3026, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2640, 1), (key2860, 1), (key2732, 1), (key3026, 1), (key2644, 1), (key3023, 1), (key2632, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2632, 1), (key2706, 1), (key2927, -2), (key2758, -2), (key2923, -2), (key2927, -2), (key2660, -2), (key2920, -2), (key2758, -2), (key2923, -2), (key2660, -2), (key2920, -2), (key2658, -2), (key2753, -2)]

end MUB6.Certificate.GramRows

end OAI
end


